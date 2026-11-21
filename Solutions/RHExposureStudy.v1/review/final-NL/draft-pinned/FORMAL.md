# Evidence / proof-layer audit

* **Executable source and formal functional semantics.**
  PrimeSieveExec.lean is the same sparse quotient sieve used by RunPrime.lean
  and compiled with pinned Lean/leanc. PrimeCountProgram.lean proves
  count_correct, with Lean's recursion semantics, actual Std.HashMap get/insert
  state updates, descending quotient-key order, closure of all divisions,
  least-factor survivor sets, exact cardinal recurrence, and the mapping
  to Mathlib Nat.primeCounting. This is correspondence for the *actual
  Lean program*, not a reimplementation spec of the C++ driver. The theorem
  does not prove compiler, runtime, I/O formatting, or OS correctness.
* **Mathematical consumer.** RationalLog.lean proves directed rational
  log/exp programs correct using Mathlib's analytic lemmas. RealConsumers.lean
  proves the strict real-interval transfer, exact floor handling, and the
  monotonic factor. CertifiedCrossing.lean combines them, checks the
  rational endpoint signs and the x/e floor without native evaluation via
  decide +kernel, and proves the intermediate-value crossing and both real
  signs conditional on the two executions taking the displayed values.
* **Large execution separately native-assisted.** prime_lean_native.out
  is the actual compiled Lean run on the two endpoint queries and the
  1,630,650,290,176 coarsened top of the finite C++ sieve, whose reported
  count agrees. NativeCrossing.lean closes the two value hypotheses with
  native_decide. Its printed axiom list contains the two native_decide
  axioms; this is explicitly native-assisted, not a purely kernel-reduced
  verification of the big count. A trial even at n=100 did not reduce
  through the HashMap implementation by decide +kernel; see FAILURES.md.
* **Exact rational certificate checker.** RationalEnvelope.lean contains
  the actual executable Boolean cell-list program, its small operational
  Run semantics, and real-valued soundness theorem for the signed
  polynomial. EnvelopeData.lean instantiates all 28 exact cells with
  decide +kernel. The external scaled-error/penalty bounds are verified
  by mathematical monotonicity and the separate exact Python enclosures.
  The checker is not a formal proof of the Bessel, zeta, quadrature,
  exponential or analytic PNT input, nor a verification of the
  Python interpreter. It is kernel-checked arithmetic of the stated
  rational data with a formal real consumer.
* **Other runs.** finite_ram.cpp/out displays the full verified-range
  computation with exact integer comparisons. Accompanying proofs of
  its mathematical invariants, overflow guards and real endpoint logic
  are not a formal C++ execution semantics. Rerunning or checking only
  its endpoint count does not certify all its intermediate prefix counts.
  bounds.py/out, parabola.py/out, last_real.py/out and weighted_small.py/out
  have exact arithmetic algorithms and analytical enclosures, but are
  also not claimed as source-first PV of Python or its libraries.
* **Remaining unformalized** imports include the explicit formula, zero
  count, Brun–Titchmarsh, the finite RH verification, the Lee–Nosal
  and Büthe estimates, and the analytic propagation in the four notes.
  No RH conclusion is declared without a hypothesis when it uses RH.
