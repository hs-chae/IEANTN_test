# Kernel closure of weighted zero partial summation

The former generalized zero partial-summation premise is now an ordinary Lean theorem:

```lean
RH080Next.Explicit.cms_zero_partial_summation_kernel :
  RH080Next.Explicit.SourceCMSZeroPartialSummationProofScheme
```

The additive exact canonical adapter proves `CMSExplicitInputs.v1.zero_partial_summation`. The old source node, old finite claims, locked inputs and historical experimental outcomes are unchanged. The literal CMS zero-counting estimate remains an explicit input *inside the proved rule*. This is not a new proof of that published zero-counting estimate.

The primary source is Carneiro–Milinovich–Soundararajan, [arXiv:1708.04122v2](https://arxiv.org/pdf/1708.04122v2), Section 6.1, printed pp. 23–24: Lemma 9 and its following unnumbered partial-summation display. The paper specializes that display to its selected test function. Our general extension is independently proved in Lean, rather than silently attributed to a universally quantified source theorem. The exact canonical correspondence is [CMSExplicitInputs.v1.zero_partial_summation](../../../IEANTN/Nodes/CMSExplicitInputs/v1/Conclusions.lean); there is no separate traditional Blueprint label.

## What is proved

The proof first establishes finite-cutoff FTC/Fubini for the actual right-closed weighted zero count. It subtracts the ordinary main-count integral at finite cutoff. Smooth modulus approximation then removes differentiability problems at zeros of the test function: the smoothing parameter tends to zero at fixed cutoff, before the cutoff tends to infinity. Bounds on arbitrary finite subsums establish actual positive-series summability. Exact scale/Jacobian transformations produce the required normalized terms. Conjugation of the actual zeta function, its meromorphic orders and zero multiplicities supplies the negative-zero half. No assumed zero enumeration, convergence, generalized integration-by-parts theorem or negative-zero oracle is introduced.

The nine final consumers in `ExplicitCMSKernelConsumers.lean` and `ExplicitCMSKernelFapConsumers.lean` actually pass this kernel theorem. Six retain their explicit numerical norm argument; the three original N17 finite consumers discharge that numerical norm using the previously accepted kernel FFT route. Those three historical numerical routes remain **kernel-only**, not source-first PV. The subsequent canonical v2 evolution connects the separate actual C source norm provider; its evidence is recorded separately.

## Evidence

`CMS_ZERO_KERNEL_COMPLETION_MANIFEST.json` records exact source and receipt hashes, resource measurements, and the scope of each run. `evidence/cms-zero-kernel/` preserves their plans/results and the independent source/math/type review.

| Run | Compilation | Time | Peak Lean RSS | OOM |
|---|---|---:|---:|---:|
| General theorem | 43 fresh application sources, no application-object fallback | 141.93 s | 4,399,612 KiB | 0 |
| Exact canonical proposition | 48 fresh application sources, no application-object fallback | 168.29 s | 4,401,196 KiB | 0 |
| Nine final consumers | 5 fresh sources over 199 validated, receipt-associated dependencies | 137.08 s | 5,427,280 KiB | 0 |

The third row is a source-associated overlay, not a claim that all 204 modules were freshly recompiled in that run. The independent review checked the original source PDF, all 43 cold and 5 overlay compiler routes, 199 dependency associations, 60 actual compiled declaration types and all nine final consumption paths. All accepted proof closures use only `propext`, `Classical.choice` and `Quot.sound`; there are no native execution axioms or admitted proof leaves.

Strict source-cold acceptance checks every actual compiler child, source snapshot, import, object and diagnostic/resource log. Both validators passed their actual CLIs under normal Python, `-O` and `-OO`; acceptance does not depend on Python assertions.

## Reproduce from a clean environment

Use the repository's pinned `lean-toolchain`, `lake-manifest.json` and `pv/DEPENDENCIES.json`. Install/build exactly those eight generic dependencies. Create the generic-only context with the existing `pv/make_context.py`; it rejects compiler-byte, compiler-version and dependency-commit mismatches. No application objects are supplied to the following source-cold replay.

From the repository root, choose fresh absolute paths for `CONTEXT` and `RUN`:

```sh
python Solutions/RH080Next.v1/pv/make_context.py \
  --compiler /absolute/path/to/the/pinned/bin/lean \
  --mathlib /absolute/path/to/pinned/mathlib \
  --packages /absolute/path/to/pinned/packages \
  --output "$CONTEXT"
python Solutions/RH080Next.v1/pv/reproduce_lean.py \
  --context "$CONTEXT" --run "$RUN" --root ExplicitCMSCanonicalZeroAudit
python Solutions/RH080Next.v1/explicit/verify_cms_canonical_zero.py \
  --context "$CONTEXT" --run "$RUN" --out "${RUN}-strict"
```

For the generic 43-source theorem alone, select `ExplicitCMSZeroKernelAudit` and use `verify_cms_zero_kernel.py`. Repeat the validator with `python -O` and `python -OO`, choosing fresh output paths. The source-cold compiler's raw success is not by itself acceptance; run the strict validator.

To replay the nine numerical consumers, first regenerate the unchanged N17 mathematical forest using the existing `primal/finite/reproduce_finite_nodes.py` pipeline. `export_fap_math_bank.py` validates and format-exports its exact interrupted/resumed lineage for the shared receipt-associated compiler; this export is neither a new numerical proof nor source-first PV. The manifest preserves the original compiler receipts and generated-forest hashes. A full new numerical source-first replay is described by the canonical v2 evidence, rather than inferred from this kernel-only consumer run.

No large numerical data or compilation caches are newly committed by this completion. Accepted proof artifacts remain in the recorded experiment-owned banks. They must not be removed merely because a later run exists. Reconstruct generic caches and numerical forests with their deterministic reproduction scripts before considering cleanup.
