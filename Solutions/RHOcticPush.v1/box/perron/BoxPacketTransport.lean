import BoxWindowTransport
import BoxZeroPacketIdentity
import BoxZeroTransport
import Mathlib.Analysis.Real.Pi.Bounds

/-! Exact source-linked packet transport on the actual Box physical interval. -/
namespace RHOcticPush.BoxPerron
open Real Set MeasureTheory IEANTN.RHSmoothing
set_option maxHeartbeats 0

lemma box_delta_pos {L : ℝ} (hL : 0 < L) : 0 < delta L := by
  unfold delta
  positivity

lemma box_window_domain {L s : ℝ} (hL : 35 ≤ L) (hs : s = -1 ∨ s = 1) :
    1 < exp L*exp ((s-1)*delta L) ∧
      exp L*exp ((s-1)*delta L) ≤ exp L*exp ((s+1)*delta L) := by
  have hL0 : 0 < L := by linarith
  have hd := box_delta_pos hL0
  have hsq : 1 ≤ sqrt (exp L) := by
    exact (Real.le_sqrt (by norm_num) (exp_pos L).le).mpr
      (by simpa using Real.one_le_exp hL0.le)
  have hden : 4 ≤ 2*Real.pi*sqrt (exp L) := by nlinarith [Real.pi_gt_three]
  have hsmall : delta L ≤ L/4 := by
    exact div_le_div_of_nonneg_left hL0.le (by norm_num : (0:ℝ) < 4) hden
  refine ⟨?_, window_endpoints (exp_pos L) hd s⟩
  rw [←exp_add]
  apply Real.one_lt_exp_iff.mpr
  rcases hs with rfl | rfl <;> nlinarith

/-- Actual packet equality, including the original exponent, multiplicity,
normalization and both physical boundary terms. -/
theorem scaled_zero_transport {L : ℝ} (hL : 0 < L) (s : ℝ)
    (r : IEANTN.RHSmoothing.Zero) :
    (1/(2*delta L):ℂ)*transport (exp L*exp ((s-1)*delta L))
      (exp L*exp ((s+1)*delta L)) (fun x => zeroPrimitive x r) =
        zeroPacket box s L r := by
  have hd := box_delta_pos hL
  have hab := window_endpoints (exp_pos L) hd s
  have hc : ContinuousOn (fun x : ℝ => Complex.exp ((r:ℂ)*(Real.log x:ℂ))*
      (IEANTN.zetaOrder r:ℂ)/(r:ℂ))
      (uIcc (exp L*exp ((s-1)*delta L)) (exp L*exp ((s+1)*delta L))) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity : 0 < exp L*exp ((s-1)*delta L))
      (by simpa only [min_eq_left hab] using hx.1)
    have hlog : ContinuousAt Real.log x := Real.continuousAt_log hx0.ne'
    apply ContinuousAt.continuousWithinAt
    fun_prop
  rw [scaled_transport_box (exp_pos L) hd s
    (fun x hx => zeroPrimitive_hasDerivAt (lt_of_lt_of_le
      (by positivity : 0 < exp L*exp ((s-1)*delta L))
      (by simpa only [min_eq_left hab] using hx.1)) r) hc.intervalIntegrable]
  exact zero_packet_identity r L s

#print axioms box_window_domain
#print axioms scaled_zero_transport
end RHOcticPush.BoxPerron
