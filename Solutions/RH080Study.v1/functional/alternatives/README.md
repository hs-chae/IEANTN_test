# Bounded alternatives to the fixed Fourier functional

`SOURCE_PARAMETER_ARGUMENT.json` tracks every budget in the actual 2026 paper's
explicit method, Eqs(15)–(21), physical pp11–14. The printed theorem fixes
c=681/800; it does not print0.811. Retaining its old upper envelopes while
allowing smaller c preserves geometry, pole loss, zero-count remainder,
exterior component costs, prime powers and trivial zeros. The actual c remains
in the main and logarithmic terms. The use of the lower norm bound multiplying
the logarithm additionally requires a positive logarithm; this holds on the
stated applied domain0.8≤c≤681/800 and log(x)≥44.

Together with the existing kernel proof that the conservative retuned0.811
scalar margin is at least0.0007 throughout44≤log(x)≤60, this supplies a written
parameterized corollary for(x,x+0.811√x log(x)]. The analytic parameter argument
is written mathematics; the original Mellin, zero, arithmetic and numerical
source ingredients have not been re-proved in Lean. It is not promoted as a
new complete Lean prime theorem. A strict-open0.8111 corollary needs the
separate endpoint shift and reduced range recorded by the predecessor review.

`RetunedBudgetBarrier.lean` proves a different, new scalar fact: this particular
conservative margin at c=0.8 is at most−0.05 for every real log(x)≥44. This
closes a complete continuum statement with the ordinary kernel and standard
three axioms. A negative sufficient lower bound is neither a prime
counterexample nor a universal obstruction or optimality theorem.

`probe.py` actually evaluates the retuned budgets at several coefficients and
logarithmic heights with192-bit Arb. It also evaluates exact sensitivity for
the fixed new degree56 witness. Sufficient ways for these conservative certified budgets to reach0.8 are
A≤2.0575784904…, or a uniform spectral-phase envelope at most0.9592953641…
times the current norm envelope (about4.0705% improvement). These are not
necessary conditions for the actual witness or for other methods. The precise missing
zero-sum inequality is recorded in the output. Those are sufficient budget diagnostics, not new
proved analytic estimates or assumptions inserted into the network. Separate
experiments show an externally certified pure-functional value below0.8 at
hypothetical A=2.4, while an external dual excludes it for A≥2.5. No applicable
ordinary-RH short-interval estimate with A≤2.4 was obtained.

The bounded probe also checks the elementary0.8 scalar transfers for the
paper's finite prefix. That prefix still depends on the paper's cited finite
prime-gap computation and its precise domain; no new exhaustive certificate
is claimed here. No original experimental outcome is changed.

To reproduce both the kernel scalar theorem and the external probes:

```sh
python3 -OO Solutions/RH080Study.v1/functional/alternatives/reproduce.py \
  --context /absolute/pinned/checked_generic_context.json \
  --flint-python /absolute/python-flint-0.9.0/environment/bin/python \
  --out /absolute/fresh/scratch/alternative-budgets
```

The context supplies the pinned Lean compiler and generic Mathlib paths only.
The script checks the compiler SHA and python-flint version, snapshots both
sources, compiles the theorem, verifies the axiom closure, runs the actual Arb
probe, records commands/hashes and GNU time, and then writes a fresh receipt.
This uses32GiB per-process address-space allowances with a separately checked
256GiB available-host reserve. It is a small scalar investigation; its external
numerical computations are not source-first PV.
