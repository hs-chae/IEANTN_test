import SynergyAnalytic.ActualHeightCaps
namespace SynergyAnalytic
open Real Set MeasureTheory WinnerOriginalScalars WinnerNewHeightSource
set_option maxHeartbeats 0

/-- Wider cells are also valid: the source boundary at a right endpoint below
exp60 is at most21600. This slightly larger explicit allowance removes every
mesh-width requirement and allows an aggressively nonuniform numerical mesh. -/
theorem count_endpoint_any_width {sigma T R c D : ℝ}
    (hTR : T ≤ R) (hT : 1 ≤ T) (hR : Real.log R ≤ 60)
    (hs : sigma ≤ 7/8) (hD : 0 ≤ D)
    (hpoint : IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 R) (fun _ => (1:ℝ)) ≤
      c*Real.exp (D*((7/8)-sigma))+6*Real.log R^2) :
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun _ => (1:ℝ)) ≤
      (c+21600)*Real.exp (D*((7/8)-sigma))+6*Real.log T^2 := by
  have hR0 : 0 ≤ Real.log R := Real.log_nonneg (hT.trans hTR)
  have hboundary : 6*Real.log R^2 ≤ 21600 := by nlinarith
  have hexp : 1 ≤ Real.exp (D*((7/8)-sigma)) := Real.one_le_exp (mul_nonneg hD (sub_nonneg.mpr hs))
  have hh := (closed_count_mono hTR).trans hpoint
  nlinarith [sq_nonneg (Real.log T)]

theorem endpoint_any_width_actual_height_caps {a c D : ℕ → ℝ} {n : ℕ}
    (ha : Monotone a) (ha0 : a 0=height) (han : a n=Real.exp 60)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hpoint : EndpointHeightCaps a c D n) (hRH : IEANTN.RiemannHypothesisUpTo height) :
    ActualHeightCaps a (fun i=>c i+21600) D n := by
  intro sigma hs hs' i hi T hT
  have hH : height ≤ a i := by rw [←ha0];exact ha (Nat.zero_le i)
  have hR : height ≤ a (i+1) := hH.trans (ha (Nat.le_succ i))
  have hc := height_cell_actual_count h tangent256_universal_basis_caps
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hRH hs hs' hR (hpoint i hi).1 (hpoint i hi).2.1
  have hR60 : Real.log (a (i+1)) ≤ 60 := by
    have hbound : a (i+1) ≤ Real.exp 60 := by rw [←han];exact ha hi
    have hpos : 0 < a (i+1) := (by norm_num [height] : (0:ℝ)<height).trans_le hR
    simpa only [Real.log_exp] using Real.log_le_log hpos hbound
  exact count_endpoint_any_width hT.2
    ((by norm_num [height] : (1:ℝ) ≤ height).trans (hH.trans hT.1)) hR60 hs' (hpoint i hi).2.2 hc

#print axioms count_endpoint_any_width
#print axioms endpoint_any_width_actual_height_caps
end SynergyAnalytic
