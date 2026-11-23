# Retained attempts and interpretation

- `dev-001`: initial two-IBP proof rejected missing beta-reduction and wrong integral division lemma; no acceptance.
- `dev-002`: rejected syntactically swapped factors in cosine integral; corrected by explicit commutative normalization. `dev-003` passed all printed standard-axiom checks.
- `convergence-001`: rejected an unapplied definition rewrite and an extra tactic; `convergence-002` passed. `convergence-003` rejected an undetermined constant in Tendsto subtraction; `convergence-004` passed after supplying its actual zeroTerm value.
- `probe-001`: deliberately queried unavailable lemma names; not a proof result.
- `mollifier-001` to `mollifier-004`: rejected measure/bilinear inference and norm coercion. The pinned Mathlib ContDiff index has analytic omega above smooth infinity: using bare top accidentally requested analyticity, which a nonzero compactly supported function cannot satisfy. Corrected the intended signature to C-infinity, preserving the actual task; no rejected proof was accepted.
- LSP initially lacked custom application imports. Root provided a development-only overlay of accepted pinned banks. Explicit CLI receipts retain the exact source/compiler/bank identities; a fresh final closure is separate.
- Coarse Nicolas full-zero bound is O(1/delta), too large for the fixed2.15 target; it proves actual absolute convergence/tail transport, not the sharp logarithmic inequality.
- Numerical moment caps are directed Arb computations with written analytic remainders; no Lean or source-first PV status is claimed.

## Subsequent analytic closure and source corrections

- Green's smooth Mellin decay was initially cited as Proposition7.1 in one comment.
  Independent primary review identified Lemma7.1, printedpp43–44, eq7.8–7.11.
  Corrected only the comment, preserved green-002, compiled green-003 and recorded
  the old/new source SHA revision in the EF freeze. The mathematical input did not change.
- Derivative and infinite-transport developmental failures concerned beta-reduction,
  function multiplication notation, real module-instance inference for inverse
  derivatives, an `abs_sub_le` API mismatch, and unresolved finite-set endpoints.
  Each rejected run is retained; final derivative-009, bpt-infinite-003,
  bpt-special-004, zero-pairing-006, derivative-moments-007,
  fourier-moments-003 and moment-transport-004 all passed standard-axiom checks.
- The earlier written sharp route used a tighter32δ/9 negative-log allowance.
  The final proof deliberately uses a simpler fully proved64δ/9 allowance.
  The extra32δ/9 fits the ORIGINAL residual0.024 throughoutδ≤1/6000;
  the full real-C family residual0.15 also holds throughoutδ≤3/2500.
- The primary BPT final PDF confirms the closed upper endpoint convention in its
  Lehman sum and full multiplicities. It lacks a standalone N(T) jump-point
  definition. A separate actual Lean right-limit proof now removes that ambiguity:
  non-ordinate source bound implies unchanged closed bound at every height.
- Stronger-frontier-002 accepted A1.821; before source freeze it was strengthened
  to1.8208 using the SAME rational M0≤5.72 bound and exactπ>3.1415. That earlier
  successful snapshot remains retained. A failed positivity tactic in -005 was
  repaired using explicit nonnegative interval width; final -006 passed.
- Some `congr` branches emit informational `ring` suggestions while overall
  compilation succeeds. These are not kernel errors; exact return codes and final
  axiom outputs, rather than searching for the word "failed", determine status.

- A subsequent independent numeric-review preview accidentally printed giant single-line RArray literals and was truncated. No unseen array value was used as acceptance evidence. Re-read only bounded declaration tails, pinned whole-file hashes, and the actual all-row/kernel soundness/assembly contracts; arrays remain checked by genuine full kernel proofs.

- The refreshed HTML first linked the defining EvenKernel module under an inferred analytic path. The explicit offline link gate rejected it before acceptance. Replaced it with the actual pinned pi/frozen-source/EvenKernel.lean path, then reran the full browser/link checks. No mathematical source changed.

- The read-only final source-marker audit first used an invalid mid-alternation Python regex flag and then correctly rejected a comment-only false positive (a documentation line beginning “axiom or…”). Neither emitted an acceptance receipt. Reran with explicit MULTILINE and nested/line comment removal; all31 source hashes and actual code-marker gates passed. Existing printed dependency-axiom audits remain the authoritative proof-closure evidence. No Lean source changed.
