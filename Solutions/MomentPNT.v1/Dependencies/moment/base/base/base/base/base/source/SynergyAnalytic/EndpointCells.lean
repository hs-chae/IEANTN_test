import SynergyAnalytic.SourceReciprocal
namespace SynergyAnalytic
open Real Set MeasureTheory WinnerOriginalScalars WinnerNewHeightSource CH2QRH
set_option maxHeartbeats 0

/-- Monotonicity of the actual closed-height zero count. This is a finite-sum
inclusion fact about zeta zeroes, not monotonicity of a numerical density cap. -/
theorem closed_count_mono {sigma T R : ℝ} (hTR : T ≤ R) :
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun _ => (1:ℝ)) ≤
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 R) (fun _ => (1:ℝ)) := by
  classical
  have hT := finite_zero_rectangle (Ioo sigma 1) (T:=T)
  have hR := finite_zero_rectangle (Ioo sigma 1) (T:=R)
  rw [rectangle_sum_eq hT,rectangle_sum_eq hR]
  simp only [one_mul]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro rho hrho
    have hz := (Set.Finite.mem_toFinset hT).mp hrho
    exact (Set.Finite.mem_toFinset hR).mpr
      ⟨hz.1,⟨hz.2.1.1,hz.2.1.2.trans hTR⟩,hz.2.2⟩
  · intro rho hrho _
    have hz := (Set.Finite.mem_toFinset hR).mp hrho
    exact CH2Section7Z.zetaOrder_nonneg_of_mem (J:=Ioo 0 (R+1)) Set.Ioo_subset_Ioi_self
      ⟨trivial,⟨hz.2.1.1,lt_of_le_of_lt hz.2.1.2 (by linarith)⟩,hz.2.2⟩

/-- A point bound at R supplies an entire count cell when logarithmic width
is at most one. The explicit726 is6*(2*60+1); no c/D monotonicity is assumed. -/
theorem count_endpoint_transport {sigma T R c D : ℝ}
    (hTR : T ≤ R) (hT : 1 ≤ T) (hR : Real.log R ≤ 60)
    (hstep : Real.log R-Real.log T ≤ 1)
    (hs : sigma ≤ 7/8) (hD : 0 ≤ D)
    (hpoint : IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 R) (fun _ => (1:ℝ)) ≤
      c*Real.exp (D*((7/8)-sigma))+6*Real.log R^2) :
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun _ => (1:ℝ)) ≤
      (c+726)*Real.exp (D*((7/8)-sigma))+6*Real.log T^2 := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hmono := Real.log_le_log hT0 hTR
  have hgap : 6*Real.log R^2 ≤ 6*Real.log T^2+726 := by
    have hp : 0 ≤ Real.log R-Real.log T := sub_nonneg.mpr hmono
    have hsum : Real.log R+Real.log T ≤ 120 := by linarith
    have hprod := mul_le_mul hstep hsum (by linarith : 0 ≤ Real.log R+Real.log T) (by norm_num : (0:ℝ) ≤ 1)
    nlinarith
  have hexp : 1 ≤ Real.exp (D*((7/8)-sigma)) := Real.one_le_exp (mul_nonneg hD (sub_nonneg.mpr hs))
  have hh := (closed_count_mono hTR).trans hpoint
  nlinarith

/-- Exact numerical point-output obligations. All source mathematical
premises remain in the caller; these inequalities must be proved by execution. -/
def EndpointHeightCaps (a c D : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ i < n,
    continuousMain (3681/10000) (3599/10000) (373/200) (1273/2000) (129/250) (7/8) (a (i+1)) ≤ c i ∧
    continuousSlope (3599/10000) (373/200) (1273/2000) (129/250) (a (i+1)) ≤ D i ∧
    0 ≤ D i

/-- Whole-cell actual counts from point numerical enclosures. This is the
new program interface: it avoids interval evaluation over the whole cell. -/
theorem endpoint_actual_count_cells {a c D : ℕ → ℝ} {n : ℕ} {sigma : ℝ}
    (ha : Monotone a) (ha0 : a 0=height) (han : a n=Real.exp 60)
    (hwidth : ∀ i<n,Real.log (a (i+1))-Real.log (a i) ≤ 1)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hcaps : UniversalBasisCaps (373/200) (1273/2000) (129/250))
    (hpoint : EndpointHeightCaps a c D n) (hRH : IEANTN.RiemannHypothesisUpTo height)
    (hs : (3/4:ℝ) ≤ sigma) (hs' : sigma ≤ 7/8) :
    ∀ i<n,∀ T ∈ Icc (a i) (a (i+1)),
      IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun _ => (1:ℝ)) ≤
        (c i+726)*Real.exp (D i*((7/8)-sigma))+6*Real.log T^2 := by
  intro i hi T hT
  have hH : height ≤ a i := by rw [←ha0];exact ha (Nat.zero_le i)
  have hR : height ≤ a (i+1) := hH.trans (ha (Nat.le_succ i))
  have hpointCount := height_cell_actual_count h hcaps (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hRH hs hs' hR (hpoint i hi).1 (hpoint i hi).2.1
  have hR60 : Real.log (a (i+1)) ≤ 60 := by
    have hbound : a (i+1) ≤ Real.exp 60 := by rw [←han];exact ha hi
    have hpos : 0 < a (i+1) := (by norm_num [height] : (0:ℝ)<height).trans_le hR
    simpa only [Real.log_exp] using Real.log_le_log hpos hbound
  have hstep : Real.log (a (i+1))-Real.log T ≤ 1 := by
    have hlo := Real.log_le_log ((by norm_num [height] : (0:ℝ)<height).trans_le hH) hT.1
    linarith [hwidth i hi]
  exact count_endpoint_transport hT.2
    ((by norm_num [height] : (1:ℝ) ≤ height).trans (hH.trans hT.1)) hR60 hstep hs' (hpoint i hi).2.2 hpointCount

#print axioms closed_count_mono
#print axioms count_endpoint_transport
#print axioms endpoint_actual_count_cells
end SynergyAnalytic
