import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Star
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Complex Filter Set
open scoped Topology ComplexConjugate
namespace RH080Next.Explicit.CMSConjugation

theorem conj_tendsto_nhds (z : ℂ) : Tendsto conj (𝓝 (conj z)) (𝓝 z) := by
  simpa only [Complex.conj_conj] using Complex.continuous_conj.tendsto (conj z)

theorem conj_tendsto_nhdsNE (z : ℂ) : Tendsto conj (𝓝[≠] (conj z)) (𝓝[≠] z) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨(conj_tendsto_nhds z).mono_left nhdsWithin_le_nhds,?_⟩
  filter_upwards [self_mem_nhdsWithin] with w hw
  simp only [Set.mem_compl_iff,Set.mem_singleton_iff] at hw ⊢
  intro eq
  exact hw (by simpa only [Complex.conj_conj] using congrArg conj eq)

theorem analyticAt_conjugate {g : ℂ → ℂ} {z : ℂ} (analytic : AnalyticAt ℂ g z) :
    AnalyticAt ℂ (fun w=>conj (g (conj w))) (conj z) := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [(conj_tendsto_nhds z).eventually
    (Complex.analyticAt_iff_eventually_differentiableAt.mp analytic)] with w hw
  simpa only [Function.comp_def] using (differentiableAt_conj_conj_iff.mpr hw)

/-- Conjugation preserves the actual meromorphic order, including the locally
zero case. The proof conjugates the local analytic normal form. -/
theorem order_conj {f : ℂ → ℂ} (symmetric : ∀z,f (conj z)=conj (f z))
    {z : ℂ} (meromorphic : MeromorphicAt f z) (meromorphicConj : MeromorphicAt f (conj z)) :
    meromorphicOrderAt f (conj z)=meromorphicOrderAt f z := by
  cases order : meromorphicOrderAt f z with
  | top =>
    rw [meromorphicOrderAt_eq_top_iff] at order ⊢
    filter_upwards [(conj_tendsto_nhdsNE z).eventually order] with w hw
    simpa only [symmetric,Complex.conj_conj,map_zero] using congrArg conj hw
  | coe n =>
    obtain ⟨g,analytic,nonzero,normal⟩ := (meromorphicOrderAt_eq_int_iff meromorphic).mp order
    apply (meromorphicOrderAt_eq_int_iff meromorphicConj).mpr
    refine ⟨fun w=>conj (g (conj w)),analyticAt_conjugate analytic,?_,?_⟩
    · simpa only [Complex.conj_conj,map_ne_zero] using nonzero
    · filter_upwards [(conj_tendsto_nhdsNE z).eventually normal] with w hw
      simpa [Algebra.smul_def,symmetric] using congrArg conj hw

theorem riemannZeta_order_conj (z : ℂ) :
    meromorphicOrderAt riemannZeta (conj z)=meromorphicOrderAt riemannZeta z := by
  by_cases eq : z=1
  · simp only [eq,map_one]
  · have conjNe : conj z≠1 := by
      intro impossible
      exact eq (by simpa only [Complex.conj_conj,map_one] using congrArg conj impossible)
    exact order_conj riemannZeta_conj
      (analyticOn_riemannZeta z eq).meromorphicAt (analyticOn_riemannZeta (conj z) conjNe).meromorphicAt

#print axioms order_conj
#print axioms riemannZeta_order_conj
end RH080Next.Explicit.CMSConjugation
