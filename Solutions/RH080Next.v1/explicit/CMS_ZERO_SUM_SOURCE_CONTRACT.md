# Historical source-contract memo — generalized scheme now kernel-proved

**Resolved on 2026-11-26.** The memo below records the earlier source audit and its then-open proof obligation. Its original content and source pins are preserved. Its phrases “under development” and “named source-backed input” describe that historical stage, not the current final proof.

The general rule is now proved by `RH080Next.Explicit.cms_zero_partial_summation_kernel` in `ExplicitCMSZeroKernel.lean`, with the exact canonical adapter in `ExplicitCMSCanonicalZero.lean`. The nine replacement consumers actually use that proof. See [the completed proof and reproduction account](CMS_ZERO_KERNEL_COMPLETION.md) and [its source/resource/receipt manifest](CMS_ZERO_KERNEL_COMPLETION_MANIFEST.json). The literal CMS Lemma 9 zero-counting proposition remains an explicit mathematical input; no generalized integration-by-parts premise remains unproved on these paths.

Original historical memo SHA256: `e056e66933199826c1a5eea45133354e4ce0f1b8a3f2d42b18d382384ea46d99`.

---

# General zero-summation source contract under development

This is an audit of an additional general analytic source input, not a claim
that CMS Lemma 9 has been re-proved or that any explicit prime bound is closed.
No new Blueprint label exists; the actual zero index is imported from
IEANTN/Vocabulary/Zeta.lean through ExplicitGuinandWeilApplication.lean.

Primary: Carneiro–Milinovich–Soundararajan, arXiv:1708.04122v2, Section 6.1,
printed pages 23–24, immediately after Lemma 9 and before equation (6.9).
Pinned extracted text SHA256:
62311c94fd73cce32d21676e3c12ea729f7ae29e9df8cf83d6e79761ccbdeda1.
The passage begins at byte/character offset approximately 71,000 in the
pinned extraction. Exact formulas must be checked in the PDF if extraction
loses absolute-value bars or fractions.

The source defines N(T) as the multiplicity count of nontrivial zeros with
0 < γ ≤ T. This is right-closed and differs from the pre-existing zetaN
vocabulary's open upper endpoint. We must not replace it by that vocabulary
without an endpoint argument. Its comparison function is

Q(T) = [T/(2π)] log[T/(2πe)] + 7/8,

and Lemma 9 states |N(T) − Q(T)| ≤ 0.15 log T + 3 for T ≥ e.
Its proof separately uses N(10) = 0. The source then selects the root
x₀ = 9.676… with Q(x₀) = 0. Because e ≤ x₀ < 10, N(x₀) = 0 also holds;
this is a separate zero-count fact, not a consequence of the error bound.

For f(x) = Δ F(Δx), the displayed summation-by-parts calculation is

Σ(γ > 0) |f(γ)|
 = ∫(x₀,∞) [log(x/(2π))/(2π)] |f(x)| dx
   − ∫(x₀,∞) [N(x) − Q(x)] (|f|)′(x) dx
 ≤ ∫(x₀,∞) [log(x/(2π))/(2π)] |f(x)| dx
   + ∫(x₀,∞) [0.15 log x + 3] |f′(x)| dx.

After u = Δx its last displayed line becomes

Σ(γ > 0) |Δ F(Δγ)|
 ≤ (1/(2π)) ∫(Δx₀,∞) log[u/(2πΔ)] |F(u)| du
   + Δ ∫(Δx₀,∞) [0.15 log(u/Δ) + 3] |F′(u)| du.

The following paragraph applies the same bound to negative ordinates.
A correct full-zero application must account for any zero at ordinate zero;
N(10) as defined above alone does not do this. Nonvanishing on the real
critical strip (under RH, just ζ(1/2) ≠ 0) is closed by ExplicitRealZetaNonzero using the separately named general
DLMF 25.5.E3 integral formula and proved positivity. It is actually consumed
by cms_full_zero_bound_from_sources.

This displayed calculation occurs in a section that has already chosen a
particular F = H(x/λ), H(x) = cos(2πx)/(1−16x²). We will label its use for
other functions a general specialization of the source's proof scheme,
not a literal universally quantified theorem printed in CMS. The source
input must expose the full hypotheses under which that same calculation
works: continuously differentiable f (or locally absolutely continuous
modulus), local finiteness and multiplicities of the actual zero count,
absolutely convergent zero sum, integrability of both displayed terms,
and vanishing boundary terms |f(T)|Q(T) and |f(T)|[N(T)−Q(T)] at infinity.
The base terms vanish because both N(x₀) and Q(x₀) vanish. The exact root
existence in (9,10) is now kernel-proved by ExplicitCMSZeroRoot, with no
approximate-value oracle. Every C1, tail, actual integral and infinity-limit
field is now proved for the actual affine inverse in ExplicitAffineZeroAdmissible;
none is hidden in a final numerical zero-error assumption.

No numerical window, support radius, norm cap, signed-log cap, final
0.0012 allowance or prime-interval conclusion is permitted in this source
contract. All such applications remain separate kernel proof obligations.
