import BoxZeroMoments
import BoxZeroScalar

/-! Actual log-scale normalization and full Box density transport. -/
namespace RHOcticPush.BoxZero
open Real Set MeasureTheory Filter
open RHLimit.BPTZeroCount IEANTN.RHSmoothing
set_option maxHeartbeats 0

noncomputable def mainMoment (d : ℝ) : ℝ :=
  ((log (1/(2*Real.pi*d)))^2 +
    2*J box 0*log (1/(2*Real.pi*d)) + 2*J box 1)/(2*Real.pi)

lemma box_scaled_density {d : ℝ} (hd : 0<d) :
    2*(∫ t in Ioi (12:ℝ),|kernel d t| * density t) =
      (1/Real.pi)*(∫ y in Ioi (12*d),|F y|/y*log (y/(2*Real.pi*d))) := by
  let g := fun y : ℝ => |F y|/y*log (y/(2*Real.pi*d))
  have he : (∫ t in Ioi (12:ℝ),|kernel d t| * density t) =
      ∫ t in Ioi (12:ℝ),(d/(2*Real.pi))*g (d*t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0<t := by linarith [ht.out]
    have hr : (d*t)/(2*Real.pi*d)=t/(2*Real.pi) := by field_simp
    dsimp [kernel,density,g]
    rw [abs_div,abs_of_pos ht0,hr]
    field_simp
  rw [he,integral_const_mul,integral_comp_mul_left_Ioi g 12 hd]
  simp only [smul_eq_mul]
  rw [mul_comm d 12]
  dsimp [g]
  field_simp

lemma box_cutoff_log {d : ℝ} (hd : 0<d) :
    log ((12*d)/(2*Real.pi*d)) ≤ 1 := by
  have he : (12*d)/(2*Real.pi*d) = 6/Real.pi := by field_simp;ring
  rw [he]
  have hp : (6:ℝ)/Real.pi ≤ 2 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_gt_three]
  exact (Real.log_le_log (by positivity) hp).trans
    (by linarith [Real.log_two_lt_d9])

/-- Complete main density bound. The negative cutoff constant is retained;
the full small interval costs at most4d², rather than being dropped. -/
theorem box_scaled_density_bound {d : ℝ} (hd : 0<d) (hsmall : 12*d≤1) :
    2*(∫ t in Ioi (12:ℝ),|kernel d t| * density t) ≤
      mainMoment d - (log (12/(2*Real.pi)))^2/(2*Real.pi) + 4*d^2 := by
  have hc : 0<12*d := by positivity
  have hq : 0<2*Real.pi*d := by positivity
  have he := actualWeight_integral hc hsmall hq
  have hl := regularWeight_low_lower hc hsmall hq (box_cutoff_log hd)
  have hratio : (12*d)/(2*Real.pi*d) = 12/(2*Real.pi) := by field_simp
  rw [hratio] at he
  have hlog : log (1/(2*Real.pi*d)) = -log (2*Real.pi*d) := by
    rw [Real.log_div (by norm_num : (1:ℝ)≠0) hq.ne',Real.log_one]
    ring
  have hslack : (12*d)^2/(12*Real.pi) ≤ 4*d^2 := by
    apply (div_le_iff₀ (by positivity : 0<12*Real.pi)).mpr
    nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr Real.pi_gt_three.le)]
  rw [box_scaled_density hd,he]
  unfold mainMoment
  have hlow := mul_le_mul_of_nonneg_left hl (le_of_lt (one_div_pos.mpr Real.pi_pos))
  have hneg : -(1/Real.pi*(∫ y in Ioc (0:ℝ) (12*d),regularWeight (2*Real.pi*d) y)) ≤
      (12*d)^2/(12*Real.pi) := by
    calc
      _ ≤ -(1/Real.pi*(-((12*d)^2/12))) := neg_le_neg hlow
      _ = _ := by ring
  rw [hlog]
  have hcancellation :
      1/Real.pi*(J box 1-log (2*Real.pi*d)*J box 0 +
        ((-log (2*Real.pi*d))^2-(log (12/(2*Real.pi)))^2)/2) =
      ((-log (2*Real.pi*d))^2+2*J box 0*(-log (2*Real.pi*d))+2*J box 1)/
        (2*Real.pi) - (log (12/(2*Real.pi)))^2/(2*Real.pi) := by ring
  calc
    _ ≤ 1/Real.pi*(J box 1-log (2*Real.pi*d)*J box 0 +
        ((-log (2*Real.pi*d))^2-(log (12/(2*Real.pi)))^2)/2) +
        (12*d)^2/(12*Real.pi) := by
      rw [mul_sub]
      exact add_le_add le_rfl hneg
    _ ≤ _ := by rw [hcancellation]; exact add_le_add le_rfl hslack

lemma actual_delta_scale {L : ℝ} (hL : 0<L) :
    log (1/(2*Real.pi*delta L)) = v L := by
  have hd : 0<delta L := by unfold delta; positivity
  have he : 2*Real.pi*delta L = L/Real.exp (L/2) := by
    unfold delta
    rw [sqrt_exp_half]
    field_simp
  rw [he,Real.log_div (by norm_num : (1:ℝ)≠0) (div_ne_zero hL.ne' (Real.exp_ne_zero _)),
    Real.log_one,Real.log_div hL.ne' (Real.exp_ne_zero _),Real.log_exp]
  unfold v
  ring

lemma actual_mainMoment {L : ℝ} (hL : 0<L) :
    mainMoment (delta L) = (v L^2+2*J box 0*v L+2*J box 1)/(2*Real.pi) := by
  simp only [mainMoment,actual_delta_scale hL]

#print axioms box_scaled_density_bound
#print axioms actual_delta_scale
end RHOcticPush.BoxZero
