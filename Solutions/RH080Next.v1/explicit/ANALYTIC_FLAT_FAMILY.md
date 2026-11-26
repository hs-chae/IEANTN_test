# Arbitrary flat-mesh analytic RH population family

This extension is **kernel-only analytic, not PV**. It adds general theorems in new `AnalyticFlatFamily*.lean` files and leaves the sealed fixed64 result unchanged.

For every integer m ≥ 1 define

**cₘ(α) = [2m/(2m−1)] [α + (1 + log(4m−2))/π].**

Under the same explicit `SourceBRFourierNormFive`, `SourceBRUniformPopulationQ1`, and RH hypotheses as the fixed64 result, Lean proves:

- For every real α ≥ 0 and every ε > 0, `GoodCoefficient α (cₘ(α)+ε)` holds. Thus the actual half-open prime count has a strictly positive eventual margin above α√x at that width.
- The actual set of good coefficients is nonempty and bounded below, and its infimum is at most cₘ(α).

The infimum theorem **does not assert that cₘ(α) itself attains a strict positive population margin**. The positive ε in the first theorem is necessary for the argument from the weak analytic norm bound. There is no explicit finite onset, optimality assertion, or best-known-result claim.

The exact rational witness has 5m+1 stored nodes: 1 at indices 0 through m−1, then 0 through index 5m. Its actual even affine window has maximum 1, no positive leakage beyond absolute frequency 1, and F(0) = (2m−1)/m. Actual Fourier eligibility, the polynomial identity, and these mass/leak/maximum facts are all proved for arbitrary m ≥ 1.

The general polynomial is Pₘ(t) = 1 + 2 Σⱼ₌₁ᵐ⁻¹ cos(2πjt). Lean proves sin(πt) Pₘ(t) = sin((2m−1)πt), the bound |Pₘ| ≤ 2m−1, and the reflection identity. Splitting at 1/((2m−1)π), the same genuine csc primitive and FTC used in the sealed fixed64 proof give

**∫₀¹ |Pₘ(t)| dt ≤ (2/π)(1 + log(4m−2)).**

The exact algebraic identity cₘ(α)·[(2m−1)/m] − normCap(m) = 2α then transfers this bound through the existing general q = 1 population consumer. Every derivative domain, denominator positivity, terminal node, and nonempty-infimum obligation is discharged in Lean. No finite numerical leaves or new source hypotheses are introduced.

The two externally attributed mathematical inputs are the existing literal BR v2 norm identity (Lemma 5, equation (4), printed page 3) and population proposition (Proposition 6, equation (6), printed page 7, with conductor-one RH specialization on printed page 10). Their exact contracts and Blueprint correspondence are in the existing final/supplemental named-input ledgers. Their published proofs remain explicit source hypotheses, rather than newly claimed kernel formalizations.

Reproduce from a clean application proof environment using the same pinned compiler and eight generic library context described in `ANALYTIC_FLAT64.md`:

```sh
python3 Solutions/RH080Next.v1/explicit/reproduce_analytic_flat_family.py \
  --context /absolute/path/to/clean_proof_context.json \
  --run /absolute/path/to/a/new/experiment-owned/run \
  --memory-gib 32
```

The command rebuilds the complete application import closure from source, with no application object fallback, and checks 22 typed theorem roots and the actual prime-consumer proof dependencies. The standalone manifest records accepted receipts, source hashes, actual time and peak compiler RAM. No random seeds, C program, numerical arrays, prime lists, or external numerical data are used. Lean/compiler/runtime/OS/hardware infrastructure remains trusted; the mathematical dependency audit permits only `propext`, `Classical.choice`, and `Quot.sound`.
