#[cfg(any(target_os = "linux", target_os = "macos"))]
use libc::{CLOCK_MONOTONIC, CLOCK_REALTIME};
use libc::{clock_gettime, timespec};

use std::io::{Error};
use std::mem::{zeroed};

pub type MonotonicStopwatch = Stopwatch<MonotonicInstant>;
pub type WallclockStopwatch = Stopwatch<WallclockInstant>;

#[derive(Clone, Copy)]
pub struct Stopwatch<I> {
  start:    I,
}

impl<I: Instant> Default for Stopwatch<I> {
  fn default() -> Stopwatch<I> {
    let start = <I as Instant>::now().unwrap();
    Stopwatch{
      start,
    }
  }
}

impl<I: Instant> Stopwatch<I> {
  pub fn lap(&mut self) -> Duration {
    let lap = <I as Instant>::now().unwrap();
    let d = lap.checked_duration_since(&self.start).unwrap();
    self.start = lap;
    d
  }

  pub fn snapshot(&self) -> Duration {
    let lap = <I as Instant>::now().unwrap();
    lap.checked_duration_since(&self.start).unwrap()
  }
}

pub trait Instant {
  fn now() -> Result<Self, Error> where Self: Sized;
  fn checked_duration_since(&self, rhs: &Self) -> Option<Duration> where Self: Sized;
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct MonotonicInstant {
  tv:   timespec,
}

impl Instant for MonotonicInstant {
  #[cfg(any(target_os = "linux", target_os = "macos"))]
  fn now() -> Result<MonotonicInstant, Error> {
    unsafe {
      let mut tv: timespec = zeroed();
      if clock_gettime(CLOCK_MONOTONIC, &mut tv) == 0 {
        Ok(MonotonicInstant{tv})
      } else {
        Err(Error::last_os_error())
      }
    }
  }

  fn checked_duration_since(&self, rhs: &MonotonicInstant) -> Option<Duration> {
    let sd_nsec = self.tv.tv_nsec - rhs.tv.tv_nsec;
    let (d_sec, d_nsec) = if sd_nsec < 0 {
      (self.tv.tv_sec - rhs.tv.tv_sec - 1, sd_nsec + 1_000_000_000)
    } else {
      (self.tv.tv_sec - rhs.tv.tv_sec, sd_nsec)
    };
    if d_sec < 0 || d_nsec < 0 {
      None
    } else {
      Some(Duration{s: d_sec, ns: d_nsec})
    }
  }
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct WallclockInstant {
  tv:   timespec,
}

impl Instant for WallclockInstant {
  #[cfg(any(target_os = "linux", target_os = "macos"))]
  fn now() -> Result<WallclockInstant, Error> {
    unsafe {
      let mut tv: timespec = zeroed();
      if clock_gettime(CLOCK_REALTIME, &mut tv) == 0 {
        Ok(WallclockInstant{tv})
      } else {
        Err(Error::last_os_error())
      }
    }
  }

  fn checked_duration_since(&self, rhs: &WallclockInstant) -> Option<Duration> {
    let sd_nsec = self.tv.tv_nsec - rhs.tv.tv_nsec;
    let (d_sec, d_nsec) = if sd_nsec < 0 {
      (self.tv.tv_sec - rhs.tv.tv_sec - 1, sd_nsec + 1_000_000_000)
    } else {
      (self.tv.tv_sec - rhs.tv.tv_sec, sd_nsec)
    };
    if d_sec < 0 || d_nsec < 0 {
      None
    } else {
      Some(Duration{s: d_sec, ns: d_nsec})
    }
  }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
#[repr(C)]
pub struct Duration {
  pub s:    i64,
  pub ns:   i64,
}

impl Duration {
  #[inline(always)]
  pub fn as_scalar(&self) -> f64 {
    let x = self.s as f64 + 1.0e-9 * self.ns as f64;
    x
  }
}

#[derive(Clone, Copy)]
pub struct DurationStats {
  m:    f64,
  m2:   f64,
  a:    f64,
  z:    f64,
  n:    f64,
}

impl Default for DurationStats {
  fn default() -> DurationStats {
    DurationStats{
      m:    0.0,
      m2:   0.0,
      a:    0.0,
      z:    f64::INFINITY,
      n:    0.0,
    }
  }
}

impl DurationStats {
  pub fn append_new(&self, d: Duration) -> DurationStats {
    let mut stats = self.clone();
    stats.append(d);
    stats
  }

  pub fn append(&mut self, d: Duration) {
    let x = d.as_scalar();
    let dx = x - self.m;
    let np = self.n + 1.0;
    let mp = self.m + dx / np;
    let m2p = self.m2 + dx * (x - mp);
    self.m = mp;
    self.m2 = m2p;
    self.a = self.a.max(x);
    self.z = self.z.min(x);
    self.n = np;
  }

  pub fn sum(&self) -> f64 {
    self.m * self.n
  }

  pub fn mean(&self) -> f64 {
    self.m
  }

  pub fn std_dev(&self) -> f64 {
    (self.m2 / (self.n - 1.0)).sqrt()
  }

  pub fn max(&self) -> f64 {
    self.a
  }

  pub fn min(&self) -> f64 {
    self.z
  }
}
