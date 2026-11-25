# Independent second review of the explicit follow-up discoveries

This component independently checks the two strongest eligible written claims from functional-L2_E2_D1_V0-r1, timely prefix0003. It preserves the original submission and experiment outcomes.

- Assuming the named analytic source inputs, every real x in [4, exp(174)] has a prime strictly between x and x + 0.8√x log(x).
- With the different frozen w4 affine window, every real x ≥ 4 has a prime strictly between x and x + 0.851062√x log(x).

Both are externally checked, written mathematical results (E tier), **not Lean theorems or source-first PV**, and neither is promoted to the verified IEANTN network. The 0.8 claim covers a bounded slab, so it does not contradict the fixed-penalty eventual-functional obstruction. No optimality or best-known claim is made.

The independent route uses the pinned primary supplement's integer FFT/twiddle engine, then a different norm integration rule: the global linear-interpolation error from the paper's Lemma 5, equation (quadrature), instead of the submission's local-curvature/Simpson aggregation. The Fap slab uses 131,072 samples; the new w4 ray uses 16,777,216 samples. Sample errors and all remaining scalar calculations use exact integers/rationals. No computed norm, log moment or margin is hardcoded as an answer. The two immutable coefficient files and exact original FFT source are included.

The slab calculation gives norm ≤ 0.7817960157900848 and endpoint margins above 1.9947600097 and 0.0049753370. Concavity gives positivity throughout the log-domain [42,174]. The w4 calculation gives norm ≤ 0.7813568381304104, positive leading coefficient and margin above 2.3848425186 at log(x)=42; monotonicity covers the full ray. The complete independently recomputed error totals are below 0.000066675 and 0.000097402, respectively, within the reserved 0.0012.

For strict upper endpoints we retain the original half-open prime count from the Mellin formula. Its conservative lower bounds exceed 54,528 on the slab and 108,345,254 on the ray. Removing a possible prime at the upper endpoint leaves at least one prime. The source prime-gap computation covers the finite join because exp(42) < 4·10¹⁸. The actual small intervals starting at 4,5,7 are checked separately. The historical gap computation is a declared literature-backed input, not recomputed here.

Exact source/formula/normalization and assumption notes are in REVIEW.json. A minor locator error is corrected there without editing the submission: the Montgomery–Vaughan interval estimate is CMS equation (6.10), not (6.8). The original Montgomery–Vaughan Theorem 2, printed page121, equations (1.10)/(1.12), was fetched from the author's site and read visually. Its non-strict bound suffices for all calculations.

From this directory, using Python 3.11 on Linux with `/usr/bin/time` and `prlimit`:

```sh
python3 reproduce.py --run /fresh/explicit-global-chord
python3 review_profiles.py --run /fresh/explicit-global-chord-profiles
python3 test_controls.py --run /fresh/explicit-global-chord-controls
```

The first command regenerates both dense numerical computations, checks every error-budget/endpoint/finite-join condition, and writes atomic receipts with exact inputs, source hashes, commands, execution time and peak RAM. It requires at least 320GiB available RAM as a conservative admission rule, preserving 256GiB beyond a 64GiB address-space ceiling; actual peak RAM was about 2.74GiB. Separate free disk admission is 1GiB; actual retained evidence was about 318KB. Array values live in memory and are discarded on normal exit, so no large prime lists, numerical arrays or caches require storage cleanup. The full clean-folder replay actually passed in about120seconds, with no OOM or signal kill.

`--slab-only` runs the inexpensive slab subset and labels it as a subset. The profile command freshly recomputes the Fap norm at 524,288 samples and checks the other six recorded explicit profiles. The control command makes three fresh slab replays, three complete profile replays, three ray applicability rechecks of the included full-run numerical receipt, and fifteen negative cases, in normal, -O and -OO modes. It does not claim three fresh 16-million-point ray runs. These validators use explicit errors rather than Python assertions.

Remaining trust includes Python's integer/Fraction implementation, the OS and hardware, the manually audited FFT/error/calculus argument and the named analytic and historical-computation source inputs. No Lean verification, C/C++/CUDA source correspondence or compiled-program execution model is asserted for this new Python computation. The separate existing C45 source-first result is unchanged.

The supplementary profiles independently pass at 0.78 through exp(70), 0.777 through exp(65), 0.74 through exp(63), 0.75 through exp(70), 0.85113 on the whole ray, and the weaker recorded 0.8 slab through exp(114). The 0.74 and 0.75 statements start at x=11: they do not hold at x=7. Their originally half-open endpoint claims are preserved; the independent count bound additionally justifies a separately labeled posthoc strict-endpoint upgrade. The other finite profiles start at x=4. This is a profile-specific review, not an exhaustive audit of candidate.md or every upstream proof.
