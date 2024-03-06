use crate::smp::{ExponentialBackoff};

use std::ptr::{null_mut};
use std::sync::{Arc};
use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering::*, fence};
use std::thread::{park};

/*
An implementation of concurrent work-stealing queues based on the Chase-Lev
algorithm, but with a fixed buffer capacity. For details:

- [CL05] D. Chase and Y. Lev. "Dynamic Circular Work-Stealing Deque."
  SPAA '05, 2005.
- [LPCN13] Nhat Minh L{\hat e}, Antoniu Pop, Albert Cohen, Francesco Zappa
  Nardelli. "Correct and Efficient Work-Stealing for Weak Memory Models."
  PPoPP '13, 2013.
*/

pub fn chan<T>(capacity: usize) -> (ChanTx<T>, ChanRx<T>) {
  let ch = Arc::new(Chan::with_capacity(capacity));
  let ch2 = ch.clone();
  (ChanTx{ch}, ChanRx{ch: ch2})
}

pub fn chan_blocking_rx<T>(capacity: usize) -> (ChanTx<T>, ChanBlockingRx<T>) {
  let ch = Arc::new(Chan::with_capacity(capacity));
  let ch2 = ch.clone();
  (ChanTx{ch}, ChanBlockingRx{ch: ch2})
}

pub struct ChanTx<T> {
  ch:   Arc<Chan<T>>,
}

impl<T> ChanTx<T> {
  pub fn push(&self, val: Box<T>) {
    self.ch.unguarded_push(val);
  }
}

pub struct ChanRx<T> {
  ch:   Arc<Chan<T>>,
}

impl<T> Clone for ChanRx<T> {
  fn clone(&self) -> ChanRx<T> {
    ChanRx{ch: self.ch.clone()}
  }
}

impl<T> ChanRx<T> {
  pub fn try_take(&self) -> Result<Option<Box<T>>, ()> {
    self.ch.unguarded_try_take()
  }
}

pub struct ChanBlockingRx<T> {
  ch:   Arc<Chan<T>>,
}

impl<T> Clone for ChanBlockingRx<T> {
  fn clone(&self) -> ChanBlockingRx<T> {
    ChanBlockingRx{ch: self.ch.clone()}
  }
}

impl<T> ChanBlockingRx<T> {
  pub fn take(&self) -> Box<T> {
    self.ch.unguarded_blocking_take()
  }
}

pub struct Chan<T> {
  mask: usize,
  bot:  AtomicUsize,
  top:  AtomicUsize,
  buf:  Box<[AtomicPtr<T>]>,
}

impl<T> Drop for Chan<T> {
  fn drop(&mut self) {
    loop {
      match self.unguarded_try_take() {
        Err(()) => {
          panic!("Chan::drop: unexpected cas failure");
        }
        Ok(Some(_)) => {}
        Ok(None) => {
          return;
        }
      }
    }
  }
}

impl<T> Chan<T> {
  pub fn with_capacity(cap: usize) -> Chan<T> {
    let mask = match cap.checked_next_power_of_two() {
      None => {
        panic!("Chan::with_capacity: overflow: c={}", cap);
      }
      Some(n) => n - 1
    };
    let mut buf = Vec::with_capacity(mask + 1);
    for _ in 0 .. mask + 1 {
      buf.push(AtomicPtr::new(null_mut()));
    }
    Chan{
      mask,
      bot:  AtomicUsize::new(0),
      top:  AtomicUsize::new(0),
      buf:  buf.into_boxed_slice(),
    }
  }

  pub fn unguarded_push(&self, val: Box<T>) {
    let b = self.bot.load(Relaxed);
    let t = self.top.load(Acquire);
    if t > b || b - t > self.mask {
      panic!("Chan::unguarded_push: overflow: b={} t={} m={}", b, t, self.mask);
    }
    let x = Box::into_raw(val);
    if x.is_null() {
      panic!("Chan::unguarded_push: null");
    }
    self.buf[b & self.mask].store(x, Relaxed);
    fence(Release);
    self.bot.store(b + 1, Release);
  }

  pub fn unguarded_try_take(&self) -> Result<Option<Box<T>>, ()> {
    let t = self.top.load(Acquire);
    fence(SeqCst);
    let b = self.bot.load(Acquire);
    if t > b {
      panic!("Chan::unguarded_take: overflow: b={} t={}", b, t);
    } else if t == b {
      return Ok(None);
    }
    fence(Acquire);
    let x = self.buf[t & self.mask].load(Relaxed);
    match self.top.compare_exchange(t, t + 1, SeqCst, Relaxed) {
      Err(_) => Err(()),
      Ok(_) => {
        if x.is_null() {
          panic!("Chan::unguarded_take: null");
        }
        unsafe { Ok(Some(Box::from_raw(x))) }
      }
    }
  }

  pub fn unguarded_blocking_take(&self) -> Box<T> {
    let back = ExponentialBackoff::default();
    loop {
      match self.unguarded_try_take() {
        Err(_) => {
          back.snooze();
        }
        Ok(None) => {
          if back.block() {
            park();
          } else {
            back.snooze();
          }
        }
        Ok(Some(val)) => {
          return val;
        }
      }
    }
  }
}
