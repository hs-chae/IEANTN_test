/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitCMSZeroSource
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace RH080Next.Explicit.ZeroSummation

/-- One real atom, with the right-closed count convention. Endpoint values of
its indicator are transferred only through volume-singleton zero. -/
theorem atom_cutoff_ibp (a T γ w : ℝ) (hγ : w≠0 → a<γ ∧ γ≤ T)
    (g g' : ℝ → ℝ) (hd : ∀x,HasDerivAt g (g' x) x) (hc : Continuous g') :
    w*g γ=w*g T-∫t in Ioc a T,(if γ≤ t then w*g' t else 0):=by
  by_cases zero : w=0
  · simp [zero]
  obtain ⟨ha,hT⟩:=hγ zero
  have eq : Ici γ ∩ Ioc a T=Icc γ T:=by
    ext x
    simp only [mem_inter_iff,mem_Ici,mem_Ioc,mem_Icc]
    constructor
    · rintro ⟨h1,h2,h3⟩;exact ⟨h1,h3⟩
    · rintro ⟨h1,h2⟩;exact ⟨h1,lt_of_lt_of_le ha h1,h2⟩
  have integ : (∫t in Ioc a T,(if γ≤ t then w*g' t else 0))=w*(g T-g γ):=by
    change (∫t in Ioc a T,(Ici γ).indicator (fun t=> w*g' t) t)=_
    rw [integral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici,eq,
      integral_Icc_eq_integral_Ioc,integral_const_mul]
    have ftc:=intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=γ) (b:=T) (fun x _=> hd x) (hc.intervalIntegrable γ T)
    rw [intervalIntegral.integral_of_le hT] at ftc
    rw [ftc]
  rw [integ]
  ring

def countStep {ι : Type*} (w γ : ι → ℝ) (t : ℝ) : ℝ:=∑'i,if γ i≤ t then w i else 0

theorem countStep_bound {ι : Type*} (w γ : ι → ℝ) (hw : Summable w) (t : ℝ) :
    |countStep w γ t|≤∑'i,|w i|:=by
  change ‖∑'i,if γ i≤t then w i else 0‖≤∑'i,|w i|
  apply tsum_of_norm_bounded hw.abs.hasSum
  intro i
  by_cases h : γ i≤ t <;> simp [h]

theorem countStep_measurable {ι : Type*} [Countable ι] (w γ : ι → ℝ) : Measurable (countStep w γ):=by
  apply Measurable.tsum
  intro i
  exact measurable_const.indicator measurableSet_Ici

/-- Integrability against a locally finite weighted count comes from its
summable actual atomic masses, not from an assumed Stieltjes formula. -/
theorem countStep_mul_integrable {ι : Type*} [Countable ι] (w γ : ι → ℝ) (hw : Summable w)
    (g' : ℝ → ℝ) (hc : Continuous g') (a T : ℝ) :
    IntegrableOn (fun t=> countStep w γ t*g' t) (Ioc a T):=by
  apply ((hc.abs.integrableOn_Ioc).const_mul (∑'i,|w i|)).mono'
  · exact ((countStep_measurable w γ).mul hc.measurable).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_right (countStep_bound w γ hw t) (abs_nonneg _)

/-- Finite-cutoff ordinary FTC and a justified interchange of the actual
atomic series with the Lebesgue integral. No source summation scheme is used. -/
theorem countable_cutoff_ibp {ι : Type*} [Countable ι] (w γ : ι → ℝ) (hw : Summable w)
    (a T : ℝ) (hγ : ∀i,w i≠0 → a<γ i ∧ γ i≤ T)
    (g g' : ℝ → ℝ) (hd : ∀x,HasDerivAt g (g' x) x) (hc : Continuous g') :
    Summable (fun i=> w i*g (γ i)) ∧
      (∑'i,w i*g (γ i))=g T*(∑'i,w i)-∫t in Ioc a T,countStep w γ t*g' t:=by
  let K : ι → ℝ → ℝ:=fun i t=> if γ i≤ t then w i*g' t else 0
  have ki (i : ι) : IntegrableOn (K i) (Ioc a T):=by
    exact (hc.integrableOn_Ioc.const_mul (w i)).indicator measurableSet_Ici
  have kb (i : ι) (t : ℝ) : ‖K i t‖≤|w i| * |g' t|:=by
    dsimp [K]
    split_ifs <;> simp [Real.norm_eq_abs,abs_mul] <;> positivity
  have ksum : Summable (fun i=>∫t in Ioc a T,‖K i t‖):=by
    apply Summable.of_nonneg_of_le (fun i=> integral_nonneg fun t=> norm_nonneg _) (fun i=>?_) (hw.abs.mul_right (∫t in Ioc a T,|g' t|))
    rw [←integral_const_mul]
    exact setIntegral_mono_on (ki i).norm (hc.abs.integrableOn_Ioc.const_mul _) measurableSet_Ioc (fun t _=> kb i t)
  have sumIntegral:=hasSum_integral_of_summable_integral_norm ki ksum
  have perAtom (i : ι) : w i*g (γ i)=w i*g T-∫t in Ioc a T,K i t:=atom_cutoff_ibp a T (γ i) (w i) (hγ i) g g' hd hc
  have summable : Summable (fun i=> w i*g (γ i)):=((hw.mul_right (g T)).sub sumIntegral.summable).congr (fun i=>(perAtom i).symm)
  have same (t : ℝ) : (∑'i,K i t)=countStep w γ t*g' t:=by
    rw [countStep,←tsum_mul_right]
    apply tsum_congr
    intro i
    dsimp [K]
    split_ifs <;> simp
  refine ⟨summable,?_⟩
  calc
    (∑'i,w i*g (γ i))=∑'i,(w i*g T-∫t in Ioc a T,K i t):=tsum_congr perAtom
    _=(∑'i,w i*g T)-(∑'i,∫t in Ioc a T,K i t):=(hw.mul_right _).tsum_sub sumIntegral.summable
    _=g T*(∑'i,w i)-∫t in Ioc a T,countStep w γ t*g' t:=by
      rw [tsum_mul_right,sumIntegral.tsum_eq]
      simp_rw [same]
      ring

#print axioms atom_cutoff_ibp
#print axioms countable_cutoff_ibp
end RH080Next.Explicit.ZeroSummation
