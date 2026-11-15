/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerDensityA.DirectCHJ
import ZetaReal01
namespace WinnerDirectKernel
open Real Set MeasureTheory IEANTN Complex
open CH2QRH
set_option maxHeartbeats 0

/-- The primary CHJTheorem1.2 Eq1.5, alpha=1/2, Table4 firstrow.
The source's exact coefficient is6.431 and its threshold islogx>=40.
Both real and ordinate cutoffs describe the actual nontrivial zeros. -/
def OriginalCHJSource : Prop := ∀ x T : ℝ, Real.exp 40≤x → max 51 (Real.log x)<T →
    T<(Real.sqrt x-2)/2 →
    |Chebyshev.psi x-x+(IEANTN.zetaZeroesSum (Ioo 0 1) (Icc (-T) T)
      (fun rho : ℂ=>(x:ℂ)^rho/rho)).re|≤(6431/1000)*x*Real.log x/T

 theorem signed_im_ne_zero {T : ℝ} {rho : ℂ}
    (hr : rho∈IEANTN.zetaZeroesIn (Ioo 0 1) (Icc (-T) T)) : rho.im≠0 := by
  intro hi
  have he : rho=(rho.re:ℂ) := by apply Complex.ext <;> simp [hi]
  have hz:=CH2ZetaReal.riemannZeta_ne_zero_Ico hr.1.1.le hr.1.2
  exact hz (by rw [←he];exact hr.2.2)

 theorem pair_mem_signed (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {T : ℝ} {q : ℂ×Bool} (hq : q∈pairedZeros T) :
    pairZ q∈IEANTN.zetaZeroesIn (Ioo 0 1) (Icc (-T) T) := by
  have hm:=Finset.mem_product.mp hq
  have hp:=positive_mem hm.1
  have hre0:=positive_re_lower hqrh hm.1
  have hre1:=CH2QRH.re_le_boundary hqrh hp.2.2 hp.2.1.1
  rcases q with ⟨rho,b⟩
  cases b
  · simp only [pairZ,Bool.false_eq_true,ite_false]
    refine ⟨?_,?_,?_⟩
    · simpa only [Complex.conj_re,mem_Ioo] using And.intro (by linarith : 0<rho.re) (by linarith : rho.re<1)
    · simp only [Complex.conj_im,mem_Icc]
      constructor <;> linarith [hp.2.1.1,hp.2.1.2]
    · change riemannZeta ((starRingEnd ℂ) rho)=0
      rw [riemannZeta_conj,hp.2.2,map_zero]
  · simp only [pairZ,ite_true]
    refine ⟨⟨by linarith,by linarith⟩,⟨?_,hp.2.1.2⟩,hp.2.2⟩
    linarith [hp.2.1.1,hp.2.1.2]

 theorem signed_has_pair {T : ℝ} {rho : ℂ}
    (hr : rho∈IEANTN.zetaZeroesIn (Ioo 0 1) (Icc (-T) T)) :
    ∃q∈pairedZeros T,pairZ q=rho := by
  have hi:=signed_im_ne_zero hr
  by_cases hp : 0<rho.im
  · refine ⟨(rho,true),?_,by simp [pairZ]⟩
    apply Finset.mem_product.mpr
    constructor
    · apply (Set.Finite.mem_toFinset _).mpr
      exact ⟨trivial,⟨hp,hr.2.1.2⟩,hr.2.2⟩
    · simp
  · have hn : rho.im<0 := lt_of_le_of_ne (le_of_not_gt hp) hi
    refine ⟨((starRingEnd ℂ) rho,false),?_,by simp [pairZ]⟩
    apply Finset.mem_product.mpr
    constructor
    · apply (Set.Finite.mem_toFinset _).mpr
      refine ⟨trivial,?_,?_⟩
      · simp only [Complex.conj_im,mem_Ioc]
        constructor <;> linarith [hr.2.1.1]
      · change riemannZeta ((starRingEnd ℂ) rho)=0
        rw [riemannZeta_conj,hr.2.2,map_zero]
    · simp

 theorem signed_finite (T : ℝ) :
    (IEANTN.zetaZeroesIn (Ioo 0 1) (Icc (-T) T)).Finite := by
  apply ((pairedZeros T).finite_toSet.image pairZ).subset
  intro rho hr
  obtain ⟨q,hq,he⟩:=signed_has_pair hr
  exact ⟨q,hq,he⟩

 theorem pair_injective {T : ℝ} {q r : ℂ×Bool}
    (hq : q∈pairedZeros T) (hr : r∈pairedZeros T) (he : pairZ q=pairZ r) : q=r := by
  have hqi:=(positive_mem (Finset.mem_product.mp hq).1).2.1.1
  have hri:=(positive_mem (Finset.mem_product.mp hr).1).2.1.1
  rcases q with ⟨q,b⟩
  rcases r with ⟨r,c⟩
  cases b <;> cases c
  · simp only [pairZ,Bool.false_eq_true,ite_false] at he
    have hh:=congrArg (starRingEnd ℂ) he
    simpa using hh
  · have hh:=congrArg Complex.im he
    simp only [pairZ,Bool.false_eq_true,ite_false,ite_true,Complex.conj_im] at hh
    linarith
  · have hh:=congrArg Complex.im he
    simp only [pairZ,Bool.false_eq_true,ite_false,ite_true,Complex.conj_im] at hh
    linarith
  · simpa only [pairZ,ite_true] using congrArg (fun z=>(z,true)) he

 theorem signed_sum_complex (T : ℝ) (f : ℂ→ℂ) :
    IEANTN.zetaZeroesSum (Ioo 0 1) (Icc (-T) T) f=
      ∑rho∈(signed_finite T).toFinset,f rho*(IEANTN.zetaOrder rho:ℂ) := by
  classical
  unfold IEANTN.zetaZeroesSum
  rw [tsum_subtype (IEANTN.zetaZeroesIn (Ioo 0 1) (Icc (-T) T))
      (fun rho=>f rho*(IEANTN.zetaOrder rho:ℂ)),
    tsum_eq_sum (s:=(signed_finite T).toFinset)]
  · exact Finset.sum_congr rfl (fun rho hr=>Set.indicator_of_mem ((Set.Finite.mem_toFinset _).mp hr) _)
  · intro rho hr
    exact Set.indicator_of_notMem (fun h=>hr ((Set.Finite.mem_toFinset _).mpr h)) _

 theorem exp_real_cpow (u : ℝ) (rho : ℂ) : (Real.exp u:ℂ)^rho=zexp rho u := by
  have he : (Real.exp u:ℂ)≠0 := by exact_mod_cast (Real.exp_pos u).ne'
  rw [Complex.cpow_def_of_ne_zero he,←Complex.ofReal_log (Real.exp_pos u).le,Real.log_exp]
  unfold zexp
  congr 1
  ring

 theorem signed_sum_eq_paired (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8)) (T u : ℝ) :
    IEANTN.zetaZeroesSum (Ioo 0 1) (Icc (-T) T) (fun rho : ℂ=>(Real.exp u:ℂ)^rho/rho)=
      zeroSum (pairedZeros T) pairZ pairW u := by
  classical
  rw [signed_sum_complex]
  symm
  unfold zeroSum
  apply Finset.sum_bij (fun q _=>pairZ q)
  · intro q hq
    exact (Set.Finite.mem_toFinset _).mpr (pair_mem_signed hqrh hq)
  · intro q hq r hr he
    exact pair_injective hq hr he
  · intro rho hr
    obtain ⟨q,hq,he⟩:=signed_has_pair ((Set.Finite.mem_toFinset _).mp hr)
    exact ⟨q,hq,he⟩
  · intro q hq
    rw [exp_real_cpow]
    have hm : (IEANTN.zetaOrder (pairZ q):ℝ)=pairW q := by
      rcases q with ⟨rho,b⟩
      cases b <;> simp [pairZ,pairW,CH2Section6.zetaOrder_conj]
    have hmC : (IEANTN.zetaOrder (pairZ q):ℂ)=(pairW q:ℂ) := by exact_mod_cast hm
    rw [hmC]
    ring

 theorem original_CHJ_to_paired (h : OriginalCHJSource)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8)) : CHJSource := by
  intro u T hu hT hUpper
  have hp:=h (Real.exp u) T (Real.exp_le_exp.mpr hu)
    (by simpa only [Real.log_exp] using hT) (by rw [←Real.exp_half];exact hUpper)
  rw [signed_sum_eq_paired hqrh] at hp
  simp only [Real.log_exp] at hp
  change |psiResidual u+(zeroSum (pairedZeros T) pairZ pairW u).re|≤_
  apply hp.trans
  have hTp : 0<T := by have hh:= (le_max_left (51:ℝ) u).trans_lt hT;linarith
  have hcoef : (6431/1000:ℝ)≤13/2 := by norm_num
  have hh:=mul_le_mul_of_nonneg_right hcoef (show 0≤Real.exp u*u/T by positivity)
  convert! hh using 1 <;> ring

#print axioms signed_sum_eq_paired
#print axioms original_CHJ_to_paired
end WinnerDirectKernel
