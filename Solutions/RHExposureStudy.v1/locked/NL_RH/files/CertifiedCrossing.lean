import PrimeCountProgram
import RationalLog
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Exact source-level rational tests for the local crossing.
The analytic big-x coverage is not formalized in this file. -/
namespace Crossing
open Real Set RHLog

def K : ℕ := 38358837682
def Y : ℕ := 14111427770
def P : ℕ := 1644673232
def Q : ℕ := 632207037
def lo : ℚ := (38358837682:ℚ) + (21792636514465:ℚ)/10^14
def hi : ℚ := (38358837682:ℚ) + (21792636514466:ℚ)/10^14

set_option maxRecDepth 4096
set_option maxHeartbeats 0

private theorem ylo : (Y:ℚ)*eHi 34 < (K:ℚ) := by decide +kernel
private theorem yhi : (K:ℚ)+1 < (Y+1:ℕ)*eLo 34 := by decide +kernel
private theorem signs :
    certifyNeg 34 35 34 lo P Q = true ∧ certifyPos 34 35 34 hi P Q = true :=
  ⟨by decide +kernel,by decide +kernel⟩
private theorem elo : (2:ℚ)^35 ≤ lo := by decide +kernel
private theorem ehi : (2:ℚ)^35 ≤ hi := by decide +kernel
private theorem kLo : (K:ℚ) < lo := by decide +kernel
private theorem hiK : hi < (K:ℚ)+1 := by decide +kernel
private theorem loHi : lo < hi := by decide +kernel

theorem shifted_floor {x : ℝ} (hx₀ : (K:ℝ) ≤ x) (hx₁ : x ≤ (K:ℝ)+1) :
    ⌊x/exp 1⌋₊ = Y := by
  have hl : (Y:ℝ)*(eHi 34 : ℝ) < (K:ℝ) := by exact_mod_cast ylo
  have hh : (K:ℝ)+1 < ((Y:ℝ)+1)*(eLo 34 : ℝ) := by exact_mod_cast yhi
  have E := e_correct (show (0:ℕ)<34 by decide +kernel)
  refine (Nat.floor_eq_iff (div_nonneg ((Nat.cast_nonneg K).trans hx₀) (exp_pos 1).le)).mpr
    ⟨(le_div_iff₀ (exp_pos 1)).mpr ?_,(div_lt_iff₀ (exp_pos 1)).mpr ?_⟩
  · exact (mul_le_mul_of_nonneg_left E.2 (Nat.cast_nonneg Y)).trans (hl.le.trans hx₀)
  · exact hx₁.trans_lt (hh.trans_le (mul_le_mul_of_nonneg_left E.1 (by positivity)))

theorem gap_eq_branch {x : ℝ} (hx₀ : (K:ℝ) ≤ x) (hx₁ : x < (K:ℝ)+1)
    (hp : LocalPrimeSieve.count K = P) (hq : LocalPrimeSieve.count Y = Q) :
    RHReal.Gap x = branch x P Q := by
  have hP := (LocalPrimeSieve.count_correct K).symm.trans hp
  have hQ := (LocalPrimeSieve.count_correct Y).symm.trans hq
  have pp := RHReal.pcount_natcell K hx₀ hx₁
  have qq : RHReal.pcount (x/exp 1) = (Y.primeCounting:ℝ) := by
    unfold RHReal.pcount
    rw [shifted_floor hx₀ hx₁.le]
  simp only [RHReal.Gap,branch,pp,qq,hP,hQ]

theorem crossing (hp : LocalPrimeSieve.count K = P) (hq : LocalPrimeSieve.count Y = Q) :
    ∃ r : ℝ, (lo:ℝ) < r ∧ r < (hi:ℝ) ∧ RHReal.Gap r = 0 ∧
      (∀ x ∈ Ico (K:ℝ) ((K:ℝ)+1), x < r → RHReal.Gap x < 0) ∧
      (∀ x ∈ Ico (K:ℝ) ((K:ℝ)+1), r < x → 0 < RHReal.Gap x) := by
  have H0 : exp 1 < (K:ℝ) := exp_one_lt_three.trans (by norm_num [K])
  have H1 : (K:ℝ) < (lo:ℝ) := by exact_mod_cast kLo
  have H2 : (hi:ℝ) < (K:ℝ)+1 := by exact_mod_cast hiK
  have H3 : (lo:ℝ) < (hi:ℝ) := by exact_mod_cast loHi
  have Hx : ∀ x ∈ Icc (lo:ℝ) (hi:ℝ), exp 1 ≤ x := fun x hx =>
    H0.le.trans (H1.le.trans hx.1)
  have hl : ∀ x ≥ exp (1:ℝ), 0 < log x := fun x hx =>
    log_pos ((one_lt_exp_iff.mpr (by norm_num)).trans_le hx)
  have xpos : ∀ x ∈ Icc (lo:ℝ) (hi:ℝ), 0 < x := fun x hx =>
    (exp_pos 1).trans_le (Hx x hx)
  have hn := cert_neg_sound elo (hl _ (H0.le.trans H1.le)) (show 0<34 by decide +kernel) signs.1
  have hp' := cert_pos_sound ehi (hl _ (H0.le.trans (H1.le.trans H3.le)))
    (show 0<34 by decide +kernel) signs.2
  have hc : ContinuousOn (fun x => branch x P Q) (Icc (lo:ℝ) (hi:ℝ)) := by
    unfold branch RHReal.coeff
    fun_prop (disch :=
      first
      | exact fun x hx => (xpos x hx).ne'
      | exact fun x hx => (hl x (Hx x hx)).ne')
  have hs : StrictMonoOn (fun x => branch x P Q) (Ici (exp 1)) := by
    intro x hx y hy hxy
    apply sub_lt_sub_right
    exact mul_lt_mul_of_pos_right (RHReal.coeff_strict hx hy hxy) (by norm_num [Q])
  have hz : (0:ℝ) ∈ Icc (branch (lo:ℝ) P Q) (branch (hi:ℝ) P Q) := ⟨hn.le,hp'.le⟩
  obtain ⟨r,hr,hev⟩ := intermediate_value_Icc H3.le hc hz
  have hrl : (lo:ℝ)<r := lt_of_le_of_ne hr.1 (by intro he; rw [←he] at hev; linarith)
  have hrr : r<(hi:ℝ) := lt_of_le_of_ne hr.2 (by intro he; rw [he] at hev; linarith)
  have hrL : (K:ℝ) ≤ r := (H1.trans hrl).le
  have hrR : r<(K:ℝ)+1 := hrr.trans H2
  refine ⟨r,hrl,hrr,?_,?_,?_⟩
  · rwa [gap_eq_branch hrL hrR hp hq]
  · intro x hx hxr
    rw [gap_eq_branch hx.1 hx.2 hp hq, ←hev]
    exact hs (H0.le.trans hx.1) (H0.le.trans hrL) hxr
  · intro x hx hrx
    rw [gap_eq_branch hx.1 hx.2 hp hq, ←hev]
    exact hs (H0.le.trans hrL) (H0.le.trans hx.1) hrx

#print axioms shifted_floor
#print axioms crossing
end Crossing
