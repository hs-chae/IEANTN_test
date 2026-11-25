# Degree80 Fourier witness and v2 asymptotic consumers

This lane connects the new actual polynomial-Gaussian pair to the existing
general CMS source reductions. Its raw witness uses the exact proved bounds
mass ≤ 0.74901918, full positive exterior leakage ≤ 0.03111791, and
F(0) ≥ 0.999999999. The conservative denominator is at least
9879755229/11000000000, giving the exact ratio
2746403660/3293251743. The ratio is strictly below 0.833948898, the preserved
v1 coefficient 0.834021, and the fixed printed 2026 coefficient 0.834050619151.
None of those scalar comparisons is a global record or optimality claim.

`Primal80Objective.lean` derives positivity and exact division from the raw
integral-witness argument. `Primal80CanonicalConsumers.lean` consumes that
objective argument in the unchanged general CMS gap and population reductions.
`Primal80ActualConsumers.lean` supplies the actual new numerical/Fourier proof
values. The resulting coefficient is asymptotic: every positive epsilon gives
an eventual bound. The population width also retains positive epsilon and counts
the source interval (x,x+c√x log(x)]. No explicit onset or 0.8 result follows.

The new canonical versions are `GaussianFourierWitness.v2` and
`RHAsymptoticGaussian.v2`. Their v1 versions remain untouched. The final audit
checks exact theorem types, 15 axiom closures, 12 proof-value edges, consumption
of the source/RH/numerical arguments, and absence of every old actual witness
leaf. New numerical bounds are never substituted as assumptions.

Run the complete source-only joint replay after the numerical source is frozen:

```sh
python3 -OO Solutions/RH080Study.v1/primal80_gap/reproduce_joint.py \
  --context /absolute/path/to/checked_generic_context.json \
  --lean-cert-source /absolute/path/to/source/root/containing/LeanCert \
  --out /absolute/fresh/joint/run --workers 8 --worker-memory-gib 32
python3 -OO Solutions/RH080Study.v1/primal80_gap/test_joint_controls.py \
  --accepted /absolute/fresh/joint/run --out /absolute/fresh/controls/run \
  --context /absolute/path/to/checked_generic_context.json
```

The coordinator authorized eight 32 GiB compiler workers, with an aggregate
256 GiB address-space allowance, after independently checking RAM and disk.
A 256 GiB available-host reserve is required. This cold proof reproduction is
outside the frozen experimental trials; their four-CPU/64 GiB budgets are
unchanged. Every new cell, imported generic LeanCert source, actual Fourier
proof, and canonical adapter is rebuilt. Only pinned Mathlib libraries are
cached. The run records each GNU maximum process RSS and samples the sum of
RSS over its own controller and descendant processes every 0.5 seconds.
Shared pages may be counted in multiple process RSS values; sampled aggregate
RSS is not exact peak physical memory. Output-directory size is not peak disk.

The mathematical chain, twenty controls and corrected no-reuse full clean
reproduction all passed. All eighty local modules were newly compiled, including
every numerical leaf; consult `HANDOFF.json` for exact source and run identities. Official
Comparator approval, source-first PV, and an independent review of this new
implementation are separate from ordinary kernel checking. The only analytic
source premises in the final ANT results are the unchanged general CMS
gap/population predicates and ordinary RH.
