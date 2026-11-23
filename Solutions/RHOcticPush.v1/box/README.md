# Box/Mellin research package

This package contains eight mathematical Lean modules and one audit module.
The new mathematical sources compile in pinned Lean 4.34.0-rc2; all48 newly
written proof declarations have only the three standard Lean axioms. The
scoped development replay reuses the pinned previously accepted application
object bank. The campaign's separate central source replay must rebuild that
foundation before end-to-end publication. These are separate evidence scopes.

The four complete analytic source obligations remain open. This package does
not claim that an assumed Mellin identity, explicit formula or zero estimate
has been proved merely because an arithmetic consumer compiles.

## What is proved

* `BoxIntegrability.lean` proves unconditional absolute integrability of both
  actual regularized box moments. The proof covers the complete positive real
  domain, using a cubic sine remainder near zero and an integrable power tail.
  The two equivalence theorems isolate the exact value identities still needed.
* `BoxMellinBridge.lean` proves differentiation of the actual regularized
  Mellin integral at zero. Its derivative is the actual first logarithmic
  moment; a uniform majorant covers the entire infinite integration domain
  and every parameter in the stated neighborhood.
* `BoxMellinNormalization.lean` proves absolute convergence on the full Mellin
  strip, identifies its pole and regularized part, and fixes the exact constant
  normalization at zero.
* `BoxMellinCoefficients.lean` proves that the actual moments are the constant
  and linear finite-part coefficients, as right limits. No desired numerical
  moment value or Laurent coefficient is assumed in those theorems.
* `BoxFourierCoefficients.lean` proves the actual absolute-sine mean integral
  and every positive-frequency real cosine coefficient. Reconstruction of the
  infinite positive Fourier expansion is still pending.
* `BoxTail.lean` proves a positive lower correction to the old truncated
  logarithmic series. The finite block telescopes; positivity pays the whole
  omitted infinite complement. The only numerical log used in the new block
  is the already source-verified log at128. Monotonicity controls every larger
  index, so no C execution outside its proved input domain is being reused.
* `BoxTailScalars.lean` checks the exact rational improved cap in the kernel.
* `BoxImproved.lean` consumes the unchanged C-log execution/accuracy theorems,
  improves the conditional moment cap from0.70875 to0.70871, and proves actual
  whole-real-ray Chebyshev and ordinary-prime-counting consequences. It also
  proves the unchanged canonical box conclusion from the improved result.

The complete functions and their exact differences, all domains and explicit
analytic/source hypotheses are in `RESULTS.json` and the actual Lean statements.
The ordinary-prime-counting theorem uses offset Li2, not an uncorrected PV-li
normalization. It retains the named GM and two Büthe source inputs.

## Remaining mathematics

The full box averaged explicit formula and infinite zero estimate are not
closed. The moment value evaluations still require reconstruction of the
absolute-sine Fourier expansion, justified Laplace/Gamma evaluation, locally
uniform series differentiation and identification of the actual Stieltjes
limit with the relevant zeta Laurent coefficient. The integrability,
normalization, dominated differentiation and coefficient-extraction steps
listed above are completed kernel proofs and must not be counted as open again.

The small moment-cap gain is a same-premise improvement of this provider's
whole function. This track has not established that it strictly improves the
active minimum of every network consumer, or that it is a best-known bound.
It is not a substitute for completing the four main analytic obligations.

## Program and trust status

The prior actual restricted-C logarithm program, manual AST/source link,
execution semantics, helper/loop/overflow proofs and two-sided accuracy result
are reused unchanged on inputs2..128. The new analytic correction requires no
new source program and does not extend that input domain. Kernel rational
checking, Mellin/Fourier analysis and the Python build harness are not new
source-first program verification. The existing compiler, integer ABI,
runtime, OS, hardware and source/build/run association contracts remain.

## Evidence and reproduction

`BASELINE.json` predates new mathematical work. `THEOREM_LEDGER.json` keys all48
new proof declarations by actual file, line and fully qualified name.
`AXIOM_AUDIT.json` joins them to the actual compiler's48 axiom printouts and
records every accepted new source/object/log hash and command.
`BoxAudit.lean` reproduces the printed closure census.

The files under `evidence/` preserve all available development attempts,
including rejected syntax, elaboration and arithmetic proof attempts. Old
failed source revisions are represented by their recorded hashes where a full
copy was not saved; no acceptance depends on those revisions. Logs are
losslessly compressed and do not change scientific source identities.
The accepted objects are retained in the experiment-owned data directory.

For a scoped rebuild, compile in this order with the pinned generic libraries
and the source-rebuilt baseline application's object directory on LEAN_PATH:

```
BoxIntegrability
BoxTail
BoxTailScalars
BoxImproved
BoxMellinBridge
BoxMellinNormalization
BoxMellinCoefficients
BoxFourierCoefficients
BoxAudit
```

The exact executed commands are in the accepted receipts. A clean campaign
replay must regenerate the baseline from the bundled pinned sources, rather
than silently relying on this development cache. The orchestrator owns that
combined reproduction route and final resource/source/include identity gate.

Independent mathematical/source reviews of the orchestrator's Nicolas,
GM, four-scale and correlated two-height results are in `root-review/`, with
exact primary PDFs, locators, declaration/source hashes, sign derivations,
comparison qualifications and the separation from compiler receipts.

### Precise source/model boundary

The reused C-log component establishes execution and arithmetic correctness for
the chosen formal model and exact rendered-source identity. Relating that
renderer to independently parsed C syntax remains an explicit renderer/model
interpretation contract; independent parser soundness is not proved in this
campaign. This is not a new fully established source-first PV result or a
whole-pipeline PV claim. Compiler, runtime, integer ABI, OS and hardware
contracts also remain. All new interval, tail and Fourier results are ordinary
kernel proofs, not PV. This qualification applies to every source-model
reference in this package; historical receipts retain their original wording.
