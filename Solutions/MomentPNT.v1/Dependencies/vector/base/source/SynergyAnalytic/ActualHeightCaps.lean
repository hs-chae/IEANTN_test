import SynergyAnalytic.EndpointCells
import SynergyAnalytic.TangentCertifiedBasis
namespace SynergyAnalytic
open Real Set MeasureTheory WinnerOriginalScalars WinnerNewHeightSource
set_option maxHeartbeats 0

theorem source_reciprocal_from_count_cells {a c D : ℕ → ℝ} {n : ℕ} {sigma T : ℝ}
    (ha : Monotone a) (ha0 : a 0=height) (han : a n=Real.exp 60)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hcaps : UniversalBasisCaps (373/200) (1273/2000) (129/250))
    (hcells : ∀i < n,∀u∈Icc (a i) (a (i+1)),
      IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 u) (fun _=>(1:ℝ))  ≤ 
        c i*Real.exp (D i*((7/8)-sigma))+6*Real.log u^2) (hRH : IEANTN.RiemannHypothesisUpTo height)
    (hs : (3/4:ℝ)  ≤  sigma) (hs' : sigma  ≤  7/8) (hT : height  ≤  T) :
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun rho=>1/rho.im)  ≤ 
      reciprocalProfile a c D n sigma := by
  have h60 : height  ≤  Real.exp (60:ℝ) := by
    calc
      height = Real.exp (Real.log height) := (Real.exp_log (by norm_num [height] : (0:ℝ) < height)).symm
      _  ≤  Real.exp 60 := Real.exp_le_exp.mpr (source_log_le32.trans (by norm_num))
  have hcoarse : ∀u,Real.exp 60  ≤  u  → 
      IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 u) (fun _=>(1:ℝ))  ≤ 
        (2000:ℝ)*u^(8*(1-sigma)/3)*Real.log u^(5-2*sigma)+6*Real.log u^2 := by
    intro u hu
    exact source_coarse_density_closed h hcaps hRH hs hs' (h60.trans hu)
  have hh := actual_reciprocal_from_count_caps ha ha0 han (by norm_num : (0:ℝ)  ≤  2000)
    hRH hs hs' hT hcells hcoarse
  convert hh using 1
  unfold reciprocalProfile
  congr 2
  · apply Finset.sum_congr rfl
    intro i hin
    ring
  · norm_num

/-- The interface consumed by the actual reciprocal/ordinate/PNT pipeline.
It states whole-cell counts, permitting either whole-cell interval evaluation
or the proved endpoint transport, with identical mathematical assumptions. -/
def ActualHeightCaps (a c D : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀sigma,(3/4:ℝ) ≤ sigma  →  sigma ≤ 7/8  →  ∀i < n,∀u∈Icc (a i) (a (i+1)),
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 u) (fun _=>(1:ℝ))  ≤ 
      c i*Real.exp (D i*((7/8)-sigma))+6*Real.log u^2

theorem endpoint_actual_height_caps {a c D : ℕ → ℝ} {n : ℕ}
    (ha : Monotone a) (ha0 : a 0=height) (han : a n=Real.exp 60)
    (hwidth : ∀i < n,Real.log (a (i+1))-Real.log (a i) ≤ 1)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hpoint : EndpointHeightCaps a c D n) (hRH : IEANTN.RiemannHypothesisUpTo height) :
    ActualHeightCaps a (fun i=>c i+726) D n := by
  intro sigma hs hs'
  exact endpoint_actual_count_cells ha ha0 han hwidth h tangent256_universal_basis_caps hpoint hRH hs hs'

#print axioms source_reciprocal_from_count_cells
#print axioms endpoint_actual_height_caps
end SynergyAnalytic
