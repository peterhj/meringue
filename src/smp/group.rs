use crate::smp::topo_util::{CpuTopoInfo};

use std::thread::{JoinHandle, Thread, current, park, spawn};

pub struct ThreadPeer {
  rank: usize,
  size: usize,
  host: Thread,
}

impl ThreadPeer {
  pub fn peer_rank(&self) -> usize {
    self.rank
  }

  pub fn num_peers(&self) -> usize {
    self.size
  }

  pub fn host(&self) -> &Thread {
    &self.host
  }

  pub fn block(&self) {
    park();
  }

  pub fn unblock_host(&self) {
    self.host.unpark();
  }
}

pub struct ThreadGroup {
  size: usize,
  host: Thread,
  peer: Vec<JoinHandle<()>>,
}

impl ThreadGroup {
  pub fn full_rank() -> usize {
    let topo_info = CpuTopoInfo::cached();
    topo_info.numcores
  }

  pub fn new_full_rank() -> ThreadGroup {
    let topo_info = CpuTopoInfo::cached();
    ThreadGroup::new(topo_info.numcores)
  }

  pub fn new(num_peers: usize) -> ThreadGroup {
    ThreadGroup{
      size: num_peers,
      host: current(),
      peer: Vec::with_capacity(num_peers),
    }
  }

  pub fn join(self) {
    for h in self.peer.into_iter() {
      if h.join().is_err() {
        panic!("ThreadGroup::join: join failure");
      }
    }
  }

  pub fn split<F: 'static + FnOnce(ThreadPeer) + Send>(&mut self, f: F) -> usize {
    let rank = self.peer.len();
    let size = self.size;
    if rank >= size {
      panic!();
    }
    let host = self.host.clone();
    let peer = ThreadPeer{
      rank,
      size,
      host,
    };
    let h = spawn(move || (f)(peer));
    self.peer.push(h);
    rank
  }

  pub fn num_peers(&self) -> usize {
    self.size
  }

  pub fn unblock_peers(&self) {
    for h in self.peer.iter() {
      h.thread().unpark();
    }
  }
}
