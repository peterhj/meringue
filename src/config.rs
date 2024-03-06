use std::env::{var};

thread_local! {
  static TL_RT_CFG: RuntimeConfig = RuntimeConfig::from_env_vars();
}

#[derive(Clone, Copy, Debug)]
pub struct RuntimeConfig {
  pub parallel: i32,
}

impl RuntimeConfig {
  pub fn cached() -> RuntimeConfig {
    TL_RT_CFG.with(|cfg| {
      *cfg
    })
  }

  pub fn from_env_vars() -> RuntimeConfig {
    RuntimeConfig{
      parallel: var("MERINGUE_PARALLEL").ok()
                  .and_then(|s| i32::from_str_radix(&s, 10).ok())
                  .unwrap_or(1),
    }
  }
}
