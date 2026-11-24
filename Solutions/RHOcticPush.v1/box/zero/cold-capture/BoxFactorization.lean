import GammaBoxSeries
import BoxHSeries
import BoxPrefactor

/-! Actual full-strip Box Mellin factorization into zeta and a convergent correction. -/
namespace RHOcticPush.BoxGamma
open Real Set Filter
open scoped Topology
set_option maxHeartbeats 0

noncomputable def zetaSeries (s : ℝ) : ℝ := ∑' n : ℕ,((n:ℝ)+1)^(-1-s)

lemma zetaSeries_summable {s : ℝ} (hs : 0<s) :
    Summable (fun n : ℕ => ((n:ℝ)+1)^(-1-s)) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 (1+s)).mpr (by linarith)
  convert! h using 1
  funext n
  rw [abs_of_pos (by positivity : (0:ℝ)<(n:ℝ)+1),one_div,
    ←Real.rpow_neg (by positivity : (0:ℝ)≤(n:ℝ)+1)]
  congr 1;ring

lemma boxTerm_factor {s : ℝ} (hs0 : 0<s) (hs1 : s<1) (n : ℕ+) :
    boxTermValue s n = prefactor s *
      ((n:ℝ)^(-1-s)+(n:ℝ)^(-1-s)/(4*(n:ℝ)^2-1)) := by
  have hn : 0<(n:ℝ) := by exact_mod_cast n.pos
  have hpow : (n:ℝ)^(1-s)=(n:ℝ)^2*(n:ℝ)^(-1-s) := by
    rw [←Real.rpow_two,←Real.rpow_add hn]
    congr 1;ring
  have htwo : (2:ℝ)^(1-s)=2*(2:ℝ)^(-s) := by
    rw [show 1-s=(1:ℝ)+(-s) by ring,Real.rpow_add (by norm_num),Real.rpow_one]
  unfold boxTermValue prefactor
  rw [Real.mul_rpow (by norm_num) hn.le,htwo,hpow]
  have hn1 : (1:ℝ)≤n := by exact_mod_cast n.pos
  have hd : 4*(n:ℝ)^2-1 ≠ 0 := by nlinarith [sq_nonneg (n:ℝ)]
  have hr : 4*(n:ℝ)^2*(4*(n:ℝ)^2-1)⁻¹ = 1+(4*(n:ℝ)^2-1)⁻¹ := by
    calc
      _ = ((4*(n:ℝ)^2-1)+1)*(4*(n:ℝ)^2-1)⁻¹ := by ring
      _ = _ := by rw [add_mul,mul_inv_cancel₀ hd,one_mul]
  simp only [div_eq_mul_inv,mul_inv_rev]
  calc
    _ = (2:ℝ)^(-s)*(n:ℝ)^(-1-s)*(Real.Gamma (2-s))⁻¹*
        (Real.cos (Real.pi*s/2))⁻¹*(4*(n:ℝ)^2*(4*(n:ℝ)^2-1)⁻¹) := by ring
    _ = _ := by rw [hr];ring

/-- Full actual factorization, not a moment-value premise. -/
theorem actual_box_factorization {s : ℝ} (hs0 : 0<s) (hs1 : s<1) :
    BoxMellin.mellin s = prefactor s * (zetaSeries s+hSeries s) := by
  have hZ : HasSum (fun n : ℕ+ => (n:ℝ)^(-1-s)) (zetaSeries s) := by
    apply (hasSum_pnat_iff_hasSum_succ (f := fun n : ℕ => (n:ℝ)^(-1-s))).mpr
    simpa [zetaSeries,Nat.cast_add,Nat.cast_one] using (zetaSeries_summable hs0).hasSum
  have hH : HasSum (fun n : ℕ+ => (n:ℝ)^(-1-s)/(4*(n:ℝ)^2-1)) (hSeries s) := by
    apply (hasSum_pnat_iff_hasSum_succ (f := fun n : ℕ => (n:ℝ)^(-1-s)/(4*(n:ℝ)^2-1))).mpr
    convert! (hTerm_summable (s := s) (by linarith)).hasSum using 1
    ext n
    simp [hTerm,Nat.cast_add,Nat.cast_one]
  have h := ((hZ.add hH).mul_left (prefactor s)).congr_fun
    (fun n => boxTerm_factor hs0 hs1 n)
  exact (actual_box_mellin_hasSum hs0 hs1).unique h

/-- The real Dirichlet series in the factorization is the actual zeta value. -/
theorem zetaSeries_eq {s : ℝ} (hs : 0<s) :
    (zetaSeries s : ℂ) = riemannZeta ((1+s:ℝ):ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using (show 1<1+s by linarith)),
    zetaSeries,Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  change Complex.ofReal (((n:ℝ)+1)^(-1-s)) =
    (1:ℂ)/((((n:ℝ)+1):ℂ)^((1+s:ℝ):ℂ))
  rw [Complex.ofReal_cpow (by positivity : (0:ℝ)≤(n:ℝ)+1)]
  rw [show ((-1-s:ℝ):ℂ) = -((1+s:ℝ):ℂ) by push_cast;ring,
    Complex.cpow_neg,one_div]
  push_cast
  rfl

#print axioms actual_box_factorization
#print axioms zetaSeries_eq
end RHOcticPush.BoxGamma
