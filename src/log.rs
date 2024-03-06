use std::cell::{Cell};
use std::io::{Write, stdout};

thread_local! {
  static LOG_LEVEL: Cell<i32> = Cell::new(0);
  static TMP_LEVEL: Cell<i32> = Cell::new(0);
  static TMP_ON:    Cell<bool> = Cell::new(false);
}

const LEVEL_WARNING:    i32 = 1;
const LEVEL_DEBUG:      i32 = 2;
const LEVEL_TRACE:      i32 = 3;
const LEVEL_TRACE_V:    i32 = 4;
const LEVEL_TRACE_VV:   i32 = 5;
const LEVEL_TRACE_VVV:  i32 = 6;

pub fn config_log_level(new_level: i32) -> i32 {
  LOG_LEVEL.with(|level| {
    let old_level = level.get();
    level.set(new_level);
    old_level
  })
}

pub fn config_tmp_log_level(new_level: i32) {
  TMP_LEVEL.with(|level| {
    level.set(new_level);
  });
}

pub fn enable_tmp_log() {
  TMP_ON.with(|on| {
    on.set(true);
  });
}

pub fn disable_tmp_log() {
  TMP_ON.with(|on| {
    on.set(false);
  });
}

pub fn config_log_quiet() -> i32 {
  config_log_level(0)
}

pub fn config_log_default() -> i32 {
  config_log_level(LEVEL_WARNING)
}

pub fn config_log_warning() -> i32 {
  config_log_level(LEVEL_WARNING)
}

pub fn config_log_debug() -> i32 {
  config_log_level(LEVEL_DEBUG)
}

pub fn config_log_trace() -> i32 {
  config_log_level(LEVEL_TRACE)
}

pub fn config_log_trace_v() -> i32 {
  config_log_level(LEVEL_TRACE_V)
}

pub fn config_log_trace_vv() -> i32 {
  config_log_level(LEVEL_TRACE_VV)
}

pub fn config_log_trace_vvv() -> i32 {
  config_log_level(LEVEL_TRACE_VVV)
}

pub fn config_tmp_log_trace() {
  config_tmp_log_level(LEVEL_TRACE);
}

pub fn flush_log() {
  stdout().lock().flush().unwrap();
}

pub fn log_warn() -> bool {
  LOG_LEVEL.with(|level| {
    level.get() >= LEVEL_WARNING
  })
}

pub fn log_warning() -> bool {
  LOG_LEVEL.with(|level| {
    level.get() >= LEVEL_WARNING
  })
}

pub fn log_debug() -> bool {
  LOG_LEVEL.with(|level| {
    level.get() >= LEVEL_DEBUG
  })
}

pub fn log_trace() -> bool {
  LOG_LEVEL.with(|level| {
    level.get() >= LEVEL_TRACE
  })
}

pub fn log_trace_v() -> bool {
  LOG_LEVEL.with(|level| {
    level.get() >= LEVEL_TRACE_V
  })
}

pub fn log_trace_vv() -> bool {
  LOG_LEVEL.with(|level| {
    level.get() >= LEVEL_TRACE_VV
  })
}

pub fn log_trace_vvv() -> bool {
  LOG_LEVEL.with(|level| {
    level.get() >= LEVEL_TRACE_VVV
  })
}

pub fn tmp_log_trace() -> bool {
  TMP_LEVEL.with(|level| {
    level.get() >= LEVEL_TRACE
  })
}
