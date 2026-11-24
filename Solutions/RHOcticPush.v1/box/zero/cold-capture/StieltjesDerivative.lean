import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.PSeries

/-! Genuine differentiation of the actual zeta-asymptotic integral series. -/
namespace RHOcticPush.StieltjesZeta
open Real Set MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 0

noncomputable def derivativePacket (n : ℕ) (s x : ℝ) : ℝ :=
  -(x-n)*Real.log x*x^(-(s+1))
noncomputable def termDerivative (n : ℕ) (s : ℝ) : ℝ :=
  ∫ x in (n:ℝ)..((n:ℝ)+1),derivativePacket n s x

lemma derivativePacket_bound {n : ℕ} (hn : 0<n) {s x : ℝ} (hs : 3/4<s)
    (hx : x ∈ uIcc (n:ℝ) ((n:ℝ)+1)) :
    ‖derivativePacket n s x‖ ≤ 4*(n:ℝ)^(-3/2:ℝ) := by
  rw [uIcc_of_le (by linarith : (n:ℝ)≤(n:ℝ)+1)] at hx
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hx1 : 1≤x := hn1.trans hx.1
  have hx0 : 0<x := hn0.trans_le hx.1
  have hsub : 0≤x-n ∧ x-n≤1 := by constructor <;> linarith [hx.1,hx.2]
  have hl : 0≤log x := Real.log_nonneg hx1
  have hl' := Real.log_le_rpow_div hx0.le (by norm_num : (0:ℝ)<1/4)
  have hp : x^((1/4:ℝ)-(s+1))≤x^(-3/2:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hnPow : x^(-3/2:ℝ)≤(n:ℝ)^(-3/2:ℝ) :=
    Real.rpow_le_rpow_of_nonpos hn0 hx.1 (by norm_num)
  unfold derivativePacket
  rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_neg,abs_of_nonneg hsub.1,
    abs_of_nonneg hl,abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
  calc
    _ ≤ log x*x^(-(s+1)) := by gcongr;nlinarith [mul_le_mul_of_nonneg_right hsub.2 hl]
    _ ≤ (x^(1/4:ℝ)/(1/4))*x^(-(s+1)) := by gcongr
    _ = 4*x^((1/4:ℝ)-(s+1)) := by
      rw [sub_eq_add_neg,Real.rpow_add hx0]
      ring
    _ ≤ 4*x^(-3/2:ℝ) := by gcongr
    _ ≤ _ := by gcongr

lemma packet_hasDerivAt {n : ℕ} {x s : ℝ} (hx : 0<x) :
    HasDerivAt (fun s : ℝ => (x-n)/x^(s+1)) (derivativePacket n s x) s := by
  have he : (fun s : ℝ => (x-n)/x^(s+1)) =
      (fun s : ℝ => (x-n)*x^(-(s+1))) := by
    ext s
    rw [Real.rpow_neg hx.le]
    rfl
  rw [he]
  have h := (HasDerivAt.const_rpow hx ((hasDerivAt_id s).add_const 1).neg).const_mul (x-n)
  dsimp only [id_eq,Pi.neg_apply] at h
  exact h.congr_deriv (by unfold derivativePacket;ring)

/-- Actual differentiation under each finite interval integral, with an explicit
parameter-independent integrable bound on the open strip s>3/4. -/
theorem term_hasDerivAt {n : ℕ} (hn : 0<n) {s : ℝ} (hs : 3/4<s) :
    HasDerivAt (ZetaAsymptotics.term n) (termDerivative n s) s := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hm (r : ℝ) : Measurable (fun x : ℝ => (x-n)/x^(r+1)) := by fun_prop
  have hd (r : ℝ) : Measurable (derivativePacket n r) := by unfold derivativePacket;fun_prop
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r x : ℝ => (x-n)/x^(r+1)) (F' := derivativePacket n)
    (bound := fun _ : ℝ => 4*(n:ℝ)^(-3/2:ℝ))
    (a := (n:ℝ)) (b := (n:ℝ)+1)
    (Ioi_mem_nhds hs)
    (Eventually.of_forall (fun r => (hm r).aestronglyMeasurable))
    (ZetaAsymptotics.term_welldef hn (by linarith))
    ((hd s).aestronglyMeasurable)
    (Eventually.of_forall (fun x hx r hr => derivativePacket_bound hn hr (uIoc_subset_uIcc hx)))
    intervalIntegrable_const
    (Eventually.of_forall (fun x hx r _ => by
      apply packet_hasDerivAt
      have hx' : x ∈ Ioc (n:ℝ) ((n:ℝ)+1) := by
        simpa only [uIoc_of_le (by linarith : (n:ℝ)≤(n:ℝ)+1)] using hx
      exact hn0.trans hx'.1))
  exact h.2

lemma termDerivative_bound {n : ℕ} (hn : 0<n) {s : ℝ} (hs : 3/4<s) :
    ‖termDerivative n s‖ ≤ 4*(n:ℝ)^(-3/2:ℝ) := by
  unfold termDerivative
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun x hx => derivativePacket_bound hn hs (uIoc_subset_uIcc hx))
  simpa using h

/-- Full actual series derivative; convergence is inherited from the proved
actual sum at1, while uniform derivative domination is proved for every s>3/4. -/
theorem actual_termTSum_hasDerivAt :
    HasDerivAt ZetaAsymptotics.termTSum (∑' n : ℕ,termDerivative (n+1) 1) 1 := by
  have hr : Summable (fun n : ℕ => (n:ℝ)^(-3/2:ℝ)) :=
    summable_nat_rpow.mpr (by norm_num)
  have hshift : Summable (fun n : ℕ => (((n+1:ℕ):ℝ))^(-3/2:ℝ)) :=
    (summable_nat_add_iff 1).mpr hr
  have hu : Summable (fun n : ℕ => 4*(((n+1:ℕ):ℝ))^(-3/2:ℝ)) := hshift.mul_left 4
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi isPreconnected_Ioi
    (fun n s hs => term_hasDerivAt (by omega : 0<n+1) hs)
    (fun n s hs => termDerivative_bound (by omega : 0<n+1) hs)
    (show (1:ℝ)∈Ioi (3/4) by norm_num) ZetaAsymptotics.term_tsum_one.summable
    (show (1:ℝ)∈Ioi (3/4) by norm_num)

#print axioms term_hasDerivAt
#print axioms actual_termTSum_hasDerivAt
end RHOcticPush.StieltjesZeta
