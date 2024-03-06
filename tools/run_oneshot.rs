extern crate meringue;

use meringue::cg2::*;
use meringue::ir::*;
use meringue::lang::{parse_new_htree_from_path};
use meringue::log::*;
use meringue::mach::*;
use meringue::timer::*;

use std::env;
use std::path::{PathBuf};

fn main() {
  let argv: Vec<_> = env::args().collect();
  if argv.len() <= 2 {
    println!("usage: run_oneshot <path-to-theory-file> <path-to-problem-file> [<seed>]");
    return;
  }
  config_log_debug();
  //config_log_trace();
  //config_log_trace_vvv();
  let theory_path = PathBuf::from(&argv[1]);
  let problem_path = PathBuf::from(&argv[2]);
  println!("DEBUG: run: theory file  = {:?}", theory_path);
  println!("DEBUG: run: problem file = {:?}", problem_path);
  if argv.len() > 3 {
    let seed = match u64::from_str_radix(&argv[3], 10) {
      Err(_) => {
        println!("ERROR: invalid seed: must be representable as u64");
        return;
      }
      Ok(x) => x
    };
    println!("DEBUG: run: seed = {}", seed);
    init_tl_rng_seed(seed);
  }
  let theory_htree = parse_new_htree_from_path(theory_path).unwrap();
  let problem_htree = parse_new_htree_from_path(problem_path).unwrap();
  let theory = lower_new_theory(theory_htree, ITheoryEnv::default());
  let theory = lower_new_theory(problem_htree, theory);
  let theory = flatten_new_theory(theory);
  let theory = index0_new_theory(theory);
  let theory = resolve_new_theory(theory);
  let mut theory = normalize_new_theory(theory);
  let frame = gen_frame_(&mut theory);
  let mut mach = XPMach::new();
  mach = mach.solve(frame.into());
  let mut stats = DurationStats::default();
  let mut watch = WallclockStopwatch::default();
  let iterct = 1000;
  let mut iterctr = 0;
  let mut tr = false;
  for _ in 0 .. iterct {
    mach = mach.step(&theory);
    stats.append(watch.lap());
    iterctr += 1;
    if log_debug() {
      println!("DEBUG: run: iter: {}/{}", iterctr, iterct);
      /*println!("DEBUG: run:   dump tups (\"similar\")...");
      mach.env.trace_dump_tups(25);*/
    }
    match mach.terminal() {
      None => {}
      Some(_) => {
        if tr {
          break;
        } else {
          tr = true;
          mach = mach.trace();
        }
      }
    }
  }
  if log_debug() && !tr {
    println!("DEBUG: run: unsat, timed out; try restarting the search");
  }
  if log_debug() {
    println!("DEBUG: run: iters: {}/{}", iterctr, iterct);
    println!("DEBUG: run: stats: sum={:.03} mean={:.06}+/-{:.06} range=[{:.06}, {:.06}]",
        stats.sum(), stats.mean(), stats.std_dev(), stats.min(), stats.max());
  }
}
