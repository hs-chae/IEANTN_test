import SynergyAnalytic.ActualReciprocal
import SynergyAnalytic.HeightEnvelope
import SynergyAnalytic.CoarseTwoThousand
namespace SynergyAnalytic
open Real Set MeasureTheory WinnerOriginalScalars WinnerNewHeightSource
set_option maxHeartbeats 0

/-- The output contract of the NEW whole-cell numerical constructor. Every
real height in each actual cell must satisfy both inequalities. These are
point-function residuals, not new analytic/density/moment premises. -/
def HeightCellCaps (a c D : ℕ→ℝ) (n : ℕ) : Prop := ∀i<n,∀T∈Icc (a i) (a (i+1)),
  continuousMain (3681/10000) (3599/10000) (373/200) (1273/2000) (129/250) (7/8) T ≤ c i ∧
    continuousSlope (3599/10000) (373/200) (1273/2000) (129/250) T ≤ D i

noncomputable def reciprocalProfile (a c D : ℕ→ℝ) (n : ℕ) (sigma : ℝ) : ℝ :=
  (∑i∈Finset.range n,((1/a i-1/a (i+1))*c i)*Real.exp (D i*((7/8)-sigma)))+
    (1/500000:ℝ)*Real.exp (160*((7/8)-sigma))+1/100000000

/-- Complete actual reciprocal-zero bound from the original8 source relations,
original RH height, three universal Jcaps, and certified whole-cell outputs.
The infinite height tail and source6log² boundary are discharged internally. -/
theorem source_reciprocal_profile {a c D : ℕ→ℝ} {n : ℕ} {sigma T : ℝ}
    (ha : Monotone a) (ha0 : a 0=height) (han : a n=Real.exp 60)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hcaps : UniversalBasisCaps (373/200) (1273/2000) (129/250))
    (hcells : HeightCellCaps a c D n) (hRH : IEANTN.RiemannHypothesisUpTo height)
    (hs : (3/4:ℝ) ≤ sigma) (hs' : sigma ≤ 7/8) (hT : height ≤ T) :
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun rho=>1/rho.im) ≤
      reciprocalProfile a c D n sigma := by
  have hcell : ∀i<n,∀u∈Icc (a i) (a (i+1)),
      IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 u) (fun _=>(1:ℝ)) ≤
        (c i*Real.exp (D i*((7/8)-sigma)))+6*Real.log u^2 := by
    intro i hin u hu
    have huH : height ≤ u := by rw [←ha0];exact (ha (Nat.zero_le i)).trans hu.1
    exact height_cell_actual_count h hcaps (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) hRH hs hs' huH
      (hcells i hin u hu).1 (hcells i hin u hu).2
  have h60 : height ≤ Real.exp (60:ℝ) := by
    calc
      height = Real.exp (Real.log height) := (Real.exp_log (by norm_num [height] : (0:ℝ)<height)).symm
      _ ≤ Real.exp 60 := Real.exp_le_exp.mpr (source_log_le32.trans (by norm_num))
  have hcoarse : ∀u,Real.exp 60 ≤ u →
      IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 u) (fun _=>(1:ℝ)) ≤
        (2000:ℝ)*u^(8*(1-sigma)/3)*Real.log u^(5-2*sigma)+6*Real.log u^2 := by
    intro u hu
    exact source_coarse_density_closed h hcaps hRH hs hs' (h60.trans hu)
  have hh := actual_reciprocal_from_count_caps ha ha0 han (by norm_num : (0:ℝ) ≤ 2000)
    hRH hs hs' hT hcell hcoarse
  convert hh using 1
  unfold reciprocalProfile
  congr 2
  · apply Finset.sum_congr rfl
    intro i hin
    ring
  · norm_num

#print axioms source_reciprocal_profile
end SynergyAnalytic
