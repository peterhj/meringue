This is a prototype geometry solver based on a forward-chaining
theorem prover.
The basic forward-chaining design is analogous to the
deductive database described in [Chou00],
in which the prover operates by alternating steps:
(1) fixed-point computation of logical inferences, and 
(2) choosing a valid geometric construction.
However, our prover also contains an implementation of
_exploration-based_ forward-chaining,
by which we choose a construction by maximizing an intrinsic
exploration-based metric during the fixed-point stage,
and selecting the construction that maximizes the metric.
This form of exploration alone turns out to be sufficient to
solve a hard reduction of an olympiad-level geometry problem,
which even the deductive database plus geometry domain-specific
algebraic reasoning ([Trinh24]) cannot solve.
Please see the
[blog post](https://peterhj.github.io/notes/exp.html)
for more details.

## Instructions

### Building for testing and development

Note: These build instructions assume a unix-like system.

1.  Create a workspace directory, and clone this repository
    into the workspace:

        mkdir meringue-workspace
        cd meringue-workspace
        git clone https://github.com/peterhj/meringue

2.  Run the bootstrap script in this repository to checkout
    the vendored dependencies into the workspace:

        cd meringue
        ./bootstrap.sh

3.  The default Makefile target is for a release build:

        make

    or, you may target a debug build:

        make debug

### Running on the reduced IMO 2009 P2 test cases

After following the above build instructions, running any of
the three scripts `run_reduced_imo_2009_p2_v{1,2,3}.sh`
will run the prover one-shot on the triple
`(theory, problem, random seed)`.
The default theory is located at `data/geometry.txt` and
contains Horn clause-style rules sufficient for proving our
reduced versions of IMO 2009 P2.
The reduced problem definitions are located at
`data/reduced_imo_2009_p2_v{1,2,3}.txt`.

Note that the reduced problems are ordered by increasing
difficulty.
So, v1 should be very easy to solve,
v2 should take some more iterations (often 30-40),
while v3 may require restarting the solver with a different
seed to get a result within a reasonable time.

We also experimented with running DD+AR only
(from AlphaGeometry [Trinh24])
on our reduced versions of IMO 2009 P2.
We found that DD+AR in fact fails to solve the v3 reduction.
Please see our branch at
https://github.com/peterhj/alphageo-experiments/tree/exp
for our implementation of the experiment.

## Related Work

- [Newclid](https://github.com/LMCRC/Newclid):
  Vladmir Sicca, Tianxiang Xia, Mathïs Fédérico,
  Philip John Gorinski, Simon Frieder, Shangling Jui
  [[arXiv:2411.11938](https://arxiv.org/abs/2411.11938)]

## References

[Chou00] Shang-Ching Chou, Xiao-Shan Gao, and Jing-Zhong Shang.
A Deductive Database Approach to Automated Geometry Theorem
Proving and Discovering. _Journal of Automated Reasoning_,
25. 2000.

[Trinh24] Trieu H. Trinh, Yuhuai Wu, Quoc V. Le, He He, and
Thang Luong. Solving olympiad geometry without human
demonstrations. _Nature_, 625. 2024.
