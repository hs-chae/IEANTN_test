# Real-density flat-family asymptotic

The three `AnalyticFlatFamilyAsymptotic*.lean` modules prove the full real-density limit and its actual prime-population consequences. Every positive additive coefficient allowance gives, for all sufficiently large real densities, both an actual `GoodCoefficient` and a nonempty population coefficient set with the stated infimum bound. The positive integer mesh is chosen by the natural floor in `mesh`.

This is kernel-only analytic mathematics, not source-first PV. The only mathematical inputs remain `SourceBRFourierNormFive`, `SourceBRUniformPopulationQ1`, and RH. Density is fixed before the eventual prime-variable threshold; there is no uniform onset in density, zero-allowance endpoint, originality, or optimality claim. The exact constant and formulas are statically rendered in the private reading companion and stated directly in the Lean declarations.

`ANALYTIC_FLAT_FAMILY_ASYMPTOTIC_MANIFEST.json` records fresh source-only normal, `-O`, and `-OO` replays, all 15 new theorem roots with the three standard axioms, strict CLI controls, source identities, and the preserved earlier family inputs. The new proof's author checks are separate from the completed independent audit of the older fixed64/family modules; the new proof requires the parent's independent review before publication acceptance.

Reproduce from this checkout with the pinned compiler/library context:

```bash
python3 Solutions/RH080Next.v1/explicit/reproduce_analytic_flat_family_asymptotic.py --context /path/to/clean_proof_context.json --run /fresh/experiment-owned/directory
```

Only generic pinned library objects are reused; every application module in the import closure is compiled from source into the fresh directory. The source-only receipts report measured per-compiler maximum RSS. They do not claim an aggregate cgroup peak or an independently measured zero OOM count.
