thread_local! {
  static TL_CPU_ARCH_INFO: CpuArchInfo = CpuArchInfo::new();
}

#[cfg(not(target_arch = "x86_64"))]
#[derive(Clone, Copy, Debug)]
pub struct CpuArchInfo {
}

#[cfg(target_arch = "x86_64")]
#[derive(Clone, Copy, Debug)]
pub struct CpuArchInfo {
  pub rdseed:   bool,
}

impl CpuArchInfo {
  pub fn cached() -> CpuArchInfo {
    TL_CPU_ARCH_INFO.with(|info| *info)
  }
}

#[cfg(not(target_arch = "x86_64"))]
impl CpuArchInfo {
  pub fn new() -> CpuArchInfo {
    CpuArchInfo{}
  }
}

#[cfg(target_arch = "x86_64")]
impl CpuArchInfo {
  pub fn new() -> CpuArchInfo {
    CpuArchInfo{
      rdseed:   is_x86_feature_detected!("rdseed"),
    }
  }
}
