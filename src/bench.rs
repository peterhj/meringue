use crate::timer::*;

use std::cell::{Cell};

thread_local! {
  static PATCH_ON:    Cell<bool> = Cell::new(false);
  static PATCH_STATS: Cell<DurationStats> = Cell::new(DurationStats::default());
  static PATCH_TMP:   Cell<Option<MonotonicStopwatch>> = Cell::new(None);
}

#[derive(Clone, Copy, Debug)]
#[repr(usize)]
pub enum BenchIdx {
  Patch,
}

pub fn bench_patch_on() {
  PATCH_ON.with(|on| {
    on.set(true);
  });
}

pub fn bench_patch_start() {
  PATCH_ON.with(|on| {
    if on.get() {
      PATCH_TMP.with(|tmp| {
        tmp.set(Some(MonotonicStopwatch::default()));
      });
    }
  });
}

pub fn bench_patch_stop() {
  PATCH_ON.with(|on| {
    if on.get() {
      let d = PATCH_TMP.with(|tmp| {
        tmp.get().unwrap().snapshot()
      });
      PATCH_STATS.with(|stats| {
        stats.set(stats.get().append_new(d));
      });
    }
  });
}

pub fn bench_patch_dump() {
  PATCH_ON.with(|on| {
    if on.get() {
      PATCH_STATS.with(|stats| {
        let stats = stats.get();
        println!("TRACE: bench: patch: sum={:.03} mean={:.06}+/-{:.06} range=[{:.06}, {:.06}]", stats.sum(), stats.mean(), stats.std_dev(), stats.min(), stats.max());
      });
    }
  });
}
