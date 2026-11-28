# Verification record (assigned named-estimate exposure)

Run under non-login /bin/bash:
```sh
/bin/lean /work/submission/Transfer.lean
/usr/bin/python3.10 /work/submission/check.py
```

`Transfer.lean` imports `RH080EstimatePack`. The axiom queries at the end
audit major exported claims: the reported dependencies are
`propext, Classical.choice, Quot.sound`. The analytic predicates and
ordinary RH are theorem arguments, not new global axioms. No native
numerical oracle, admitted proof, execution result, or source status label
is a premise of the transfer. The Fraction test independently checks
exact rational constants, not analytic inequalities about primes.

## Input locators and trust layers

- `/task/COMMON_FACTS.md`, results (1)–(3) and “Original comparison”:
  supplied hypotheses, baseline range, and explicit onset. Baseline
  cross-reference: `/corpus/literature/BASELINE_THEOREM_MATRIX.md`,
  around lines 414–462. The transfer checks the leading arithmetic only;
  it does not re-prove the explicit octic estimate or its analytic inputs.
- `/source_pv/ESTIMATE_NAMES.md`,
  `/source_pv/objects/RH080EstimatePack.olean`; exact trees in
  `/source_pv/FLAT_FACTS.json` (see `SHARED_FACTS.json`);
  readable `FLAT_FACTS.txt` declarations at lines 58793–58803 for
  `RH080Exposure.Estimates.flat/gaussian/sparse`. The definitions of
  the named analytic predicates are found by declaration name at lines
  332 (norm), 383 (uniform), and 441 (CMS), and the width monotonicity
  lemma is `RHOnePrime.CMSFunctional.goodCoefficient_mono`
  (actual flat-text line 3351297).
- Frozen CMS `CMS1708.04122v2.pdf`, Theorem 3, (1.13), with the
  preceding functional definitions and proof §5.2; text mirror around
  lines 271–274 and 1056ff. Frozen Blanquer–Robles
  `Blanquer_Robles_2026.pdf`, §2.1, (4) and its norm derivation,
  and §3 (in particular §3.4 combining the population estimates);
  text mirror lines 128–155 and 475ff. These locate the analytic
  ingredients, not a literal attribution of the supplied three curves
  or a new proof matching each exact Lean predicate to the paper.
- Mathlib `Mathlib/NumberTheory/PrimeCounting.lean`: definitions
  51–58, nth/count/order 72–85 and 104–106, prime finsets 128–132,
  cardinalities 254–262. The transfer itself derives the real-cutoff and
  prime-rank consequences.
- Assigned exposure is `B_named`. The common packet reports separate
  completed source-first C routes for (2) and (3), but the present
  artifact consumes ordinary kernel estimates, not those routes.
  The assigned C files are present, not recompiled or executed here.
  Source/AST correspondence, the verified semantics of the particular
  C port and modeled execution-to-numerics bridge do not by themselves
  verify every compiler, runtime, OS, floating-point environment, or
  hardware execution. No general C++, CUDA, or original FFT PV
  conclusion is made. Gaussian is kernel-only. No claim about relative
  representation-arm effectiveness is made.

## Retained negative results / limitations

- G-F intersection is not a frontier breakpoint. A zero Gaussian epsilon
  is unavailable; no proof of failure of the actual prime bound at
  that width follows. No known numerical margin or explicit eventual
  threshold was extracted, and no proof of true optimality is offered.
- A real-valued conditional-lattice liminf proof would need an
  appropriate boundedness hypothesis to exclude the unbounded-above
  convention. The checked epsilon lower-limit statement avoids that
  issue; no such boundedness is assumed.
- During Lean development the proposed identifiers
  `mul_nonpos_iff_of_pos_left` and `Set.setOf_congr` did not resolve;
  replaced by sign arguments and `Set.ext`. Rewriting endpoint membership
  with a proposed `trans_eq` on a finset membership proof failed;
  replaced by rewriting the floor equality. An initial rational
  transcription of the Gaussian-branch octic gain failed `ring`;
  the checked intercept is the difference `oldWidth 0 - q`.
- Not attempted: re-establish the named analytic inputs, verify C
  execution from source, or find a new witness. Only the stated curves and
  preserved comparator enter the numeric transfer.

Assigned C source pins (SHA-256):

- `/source_pv/population_norm.c`: `92c5832d3ecfdd08d7c4143ac155e47e61ee9f58700634cf4f04e7cf8fc84b09`
- `/source_pv/flat_population_norm.c`: `2556f5eddca7d218a5e6565b4defed53aab957063ffbfadf5104f511a5fc82d9`
