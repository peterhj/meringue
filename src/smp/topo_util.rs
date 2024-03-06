use crate::log::*;

use std::io::{BufRead, Cursor};
use std::process::{Command};

thread_local! {
  static TL_CPU_TOPO_INFO: CpuTopoInfo = CpuTopoInfo::new();
}

#[derive(Clone, Copy, Debug)]
pub struct CpuTopoInfo {
  pub numcores: usize,
}

impl CpuTopoInfo {
  pub fn cached() -> CpuTopoInfo {
    TL_CPU_TOPO_INFO.with(|info| *info)
  }

  pub fn solo() -> CpuTopoInfo {
    CpuTopoInfo{
      numcores: 1,
    }
  }
}

#[cfg(not(target_os = "linux"))]
impl CpuTopoInfo {
  pub fn new() -> CpuTopoInfo {
    CpuTopoInfo::solo()
  }
}

#[cfg(target_os = "linux")]
impl CpuTopoInfo {
  pub fn new() -> CpuTopoInfo {
    let mut info = CpuTopoInfo::solo();
    let out = match Command::new("cat").arg("/proc/cpuinfo").output() {
      Err(_) => {
        panic!("bug: smp: topo_util: failed to `cat /proc/cpuinfo`");
      }
      Ok(out) => out
    };
    for line in Cursor::new(out.stdout).lines() {
      let line = line.unwrap();
      if line.is_empty() {
        break;
      }
      let mut line_parts = line.splitn(2, ':');
      match line_parts.next() {
        None => {
          panic!("bug: smp: topo_util: missing key");
        }
        Some(key) => {
          let bkey = key.as_bytes();
          if bkey.len() < 9 {
            continue;
          } else if &bkey[ .. 9] != b"cpu cores" {
            continue;
          }
        }
      }
      match line_parts.next() {
        None => {
          panic!("bug: smp: topo_util: missing value");
        }
        Some(val) => {
          let mut val_parts = val.split_whitespace();
          match val_parts.next() {
            None => unreachable!(),
            Some(v) => {
              let numcores: usize = v.parse().unwrap();
              if log_debug() {
                println!("DEBUG: smp: numcores={}", numcores);
              }
              info.numcores = numcores;
              break;
            }
          }
        }
      }
    }
    info
  }
}
