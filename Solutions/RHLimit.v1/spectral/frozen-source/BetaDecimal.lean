import NicolasSpectralMass
import ActualGMClosed
namespace RHLimit.NicolasMass
open Real
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"
lemma harmonic_1024_upper : harmonic 1024 < (18773/2500 : ℚ) := by
  norm_num [harmonic, Finset.sum_range_succ]
lemma gamma_upper : Real.eulerMascheroniConstant < (2889/5000 : ℝ) := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 1024
  have hH : (harmonic 1024 : ℝ) < (18773/2500 : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).2 harmonic_1024_upper
    norm_num at h ⊢
  have hlog : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    rw [show (1024:ℝ)=(2:ℝ)^10 by norm_num, Real.log_pow]
    norm_num
  norm_num only [Real.eulerMascheroniSeq', Nat.cast_ofNat, ite_false,show ¬ (1024:ℕ)=0 by norm_num] at h
  rw [hlog] at h
  linarith [Real.log_two_gt_d9]
lemma log_pi_lower : (11447/10000 : ℝ) < Real.log Real.pi := by
  interval_decide 80 (trust := kernel)
lemma beta_lt_047 : NicolasContinuation.beta < (47/1000 : ℝ) := by
  unfold NicolasContinuation.beta
  linarith [gamma_upper,log_pi_lower,Real.log_two_gt_d9]
theorem mass_lt_047 (hRH : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) :
    (∑' z : Zero, weight z) < (47/1000 : ℝ) :=
  (mass_le_beta hRH hN).trans_lt beta_lt_047
#print axioms gamma_upper
#print axioms beta_lt_047
#print axioms mass_lt_047
end RHLimit.NicolasMass
