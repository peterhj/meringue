pub mod chan;
pub mod group;
pub mod topo_util;

/* `ExponentialBackoff` is derived from crossbeam:

The MIT License (MIT)

Copyright (c) 2019 The Crossbeam Project Developers

Permission is hereby granted, free of charge, to any
person obtaining a copy of this software and associated
documentation files (the "Software"), to deal in the
Software without restriction, including without
limitation the rights to use, copy, modify, merge,
publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software
is furnished to do so, subject to the following
conditions:

The above copyright notice and this permission notice
shall be included in all copies or substantial portions
of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF
ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT
SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR
IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
DEALINGS IN THE SOFTWARE. */

const SPIN_LIMIT: u32 = 6;
const YIELD_LIMIT: u32 = 10;

pub struct ExponentialBackoff {
  step: std::cell::Cell<u32>,
}

impl Default for ExponentialBackoff {
  fn default() -> ExponentialBackoff {
    ExponentialBackoff{step: std::cell::Cell::new(0) }
  }
}

impl ExponentialBackoff {
  pub fn reset(&self) {
    self.step.set(0);
  }

  pub fn snooze(&self) {
    if self.step.get() <= SPIN_LIMIT {
      for _ in 0 .. (1 << self.step.get()) {
        std::hint::spin_loop();
      }
    } else {
      std::thread::yield_now();
    }
    if self.step.get() <= YIELD_LIMIT {
      self.step.set(self.step.get() + 1);
    }
  }

  pub fn block(&self) -> bool {
    self.step.get() > YIELD_LIMIT
  }
}
