import RealConsumers
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Order.IntermediateValue

/-! Directed rational transcendental comparisons, actual executable source.
The approximation programs are expressed as finite rational sums; their
results are related to Real.log and Real.exp by proved Mathlib estimates. -/
namespace RHLog
open Real Finset

def uarg (a : ℚ) : ℚ := (a-1)/(a+1)

def logSeries (u : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ range n, u^(2*i+1) / (2*i+1 : ℕ)

def logULo (n : ℕ) (a : ℚ) : ℚ := 2*logSeries (uarg a) n

def logUHi (n : ℕ) (a : ℚ) : ℚ :=
  let u := uarg a
  2*(logSeries u n + u^(2*n+1)/(1-u^2))

theorem cast_logSeries (u : ℚ) (n : ℕ) :
    (logSeries u n : ℝ) = ∑ i ∈ range n, (u:ℝ)^(2*i+1) / (2*(i:ℝ)+1) := by
  simp [logSeries, Rat.cast_sum]

theorem log_unit_correct (n : ℕ) {a : ℚ} (h : 1 ≤ a) :
    (logULo n a : ℝ) ≤ log (a:ℝ) ∧ log (a:ℝ) ≤ logUHi n a := by
  let u := uarg a
  have ha : 1 ≤ (a:ℝ) := by exact_mod_cast h
  have harg : (u:ℝ) = ((a:ℝ)-1)/((a:ℝ)+1) := by simp [u,uarg]
  have he : 0 < (a:ℝ)+1 := by linarith
  have h₀ : 0 ≤ (u:ℝ) := by rw [harg]; exact div_nonneg (by linarith) he.le
  have h₁ : (u:ℝ) < 1 := by rw [harg,div_lt_one he]; linarith
  have hr : (1+(u:ℝ))/(1-(u:ℝ)) = (a:ℝ) := by
    rw [div_eq_iff (by linarith)]
    rw [harg]
    field_simp
    <;> ring
  have hl := sum_range_le_log_div h₀ h₁ n
  have hh := log_div_le_sum_range_add h₀ h₁ n
  rw [hr,←cast_logSeries] at hl hh
  constructor
  · simp only [logULo,Rat.cast_mul,Rat.cast_ofNat]
    change 2*(logSeries u n : ℝ) ≤ _
    linarith
  · simp only [logUHi,Rat.cast_mul,Rat.cast_add,Rat.cast_sub,Rat.cast_div,
      Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one]
    change _ ≤ 2*((logSeries u n : ℝ)+(u:ℝ)^(2*n+1)/(1-(u:ℝ)^2))
    linarith

def logLo (n k : ℕ) (a : ℚ) : ℚ :=
  k * logULo n 2 + logULo n (a/2^k)

def logHi (n k : ℕ) (a : ℚ) : ℚ :=
  k * logUHi n 2 + logUHi n (a/2^k)

theorem log_correct (n k : ℕ) {a : ℚ} (ha : (2:ℚ)^k ≤ a) :
    (logLo n k a : ℝ) ≤ log (a:ℝ) ∧ log (a:ℝ) ≤ logHi n k a := by
  set z := a/2^k with hz
  have h₀ : 1 ≤ z := (one_le_div₀ (by positivity)).mpr ha
  obtain ⟨hL,hH⟩ := log_unit_correct n h₀
  obtain ⟨hL₂,hH₂⟩ := log_unit_correct n (by norm_num : (1:ℚ)≤2)
  have hz' : (a : ℝ) = (2:ℝ)^k * (z:ℝ) := by
    rw [hz]
    push_cast
    field_simp
  have hz0 : 0 < (z:ℝ) := by exact_mod_cast (zero_lt_one.trans_le h₀)
  have hzlog : log (a:ℝ) = k*log 2 + log (z:ℝ) := by
    rw [hz',log_mul (by positivity) hz0.ne',log_pow]
  simp only [logLo,logHi,Rat.cast_add,Rat.cast_mul,Rat.cast_natCast]
  rw [←hz,hzlog]
  exact ⟨add_le_add (mul_le_mul_of_nonneg_left hL₂ (by positivity)) hL,
    add_le_add (mul_le_mul_of_nonneg_left hH₂ (by positivity)) hH⟩

def eLo (n : ℕ) : ℚ := ∑ i ∈ range n, (1:ℚ)/i.factorial
def eHi (n : ℕ) : ℚ := eLo n + (n+1 : ℕ)/(n.factorial*n : ℕ)

theorem e_correct {n : ℕ} (hn : 0 < n) :
    (eLo n : ℝ) ≤ exp 1 ∧ exp 1 ≤ eHi n := by
  have h₁ := sum_le_exp_of_nonneg (by norm_num : 0 ≤ (1:ℝ)) n
  have h₂ := exp_bound' (by norm_num : 0 ≤ (1:ℝ)) le_rfl hn
  constructor
  · simpa [eLo,Rat.cast_sum] using h₁
  · simpa [eHi,eLo,Rat.cast_sum] using h₂

def certifyNeg (n k ne : ℕ) (x : ℚ) (P Q : ℕ) : Bool :=
  decide (eHi ne*x*Q < logLo n k x * (P:ℚ)^2)

def certifyPos (n k ne : ℕ) (x : ℚ) (P Q : ℕ) : Bool :=
  decide (logHi n k x*(P:ℚ)^2 < eLo ne*x*Q)

noncomputable def branch (x : ℝ) (P Q : ℕ) : ℝ := RHReal.coeff x * Q - (P:ℝ)^2

theorem cert_neg_sound {n k ne : ℕ} {x : ℚ} {P Q : ℕ}
    (hx : (2:ℚ)^k ≤ x) (hlog : 0 < log (x:ℝ)) (he : 0 < ne)
    (h : certifyNeg n k ne x P Q = true) : branch (x:ℝ) P Q < 0 := by
  have ht := of_decide_eq_true h
  have hh : (eHi ne : ℝ)*(x:ℝ)*Q < (logLo n k x:ℝ)*(P:ℝ)^2 := by exact_mod_cast ht
  have hx0 : 0 ≤ (x:ℝ) := by exact_mod_cast ((by positivity : 0 ≤ (2:ℚ)^k).trans hx)
  have H := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (e_correct he).2 hx0) (Nat.cast_nonneg (α:=ℝ) Q)
  have G := mul_le_mul_of_nonneg_right (log_correct n k hx).1 (sq_nonneg (P:ℝ))
  apply sub_neg.mpr
  unfold RHReal.coeff
  rw [show exp 1*((x:ℝ)/log (x:ℝ))*Q =
    (exp 1*(x:ℝ)*Q)/log (x:ℝ) by ring]
  exact (div_lt_iff₀ hlog).mpr (by
    simpa [mul_comm] using H.trans_lt (hh.trans_le G))

theorem cert_pos_sound {n k ne : ℕ} {x : ℚ} {P Q : ℕ}
    (hx : (2:ℚ)^k ≤ x) (hlog : 0 < log (x:ℝ)) (he : 0 < ne)
    (h : certifyPos n k ne x P Q = true) : 0 < branch (x:ℝ) P Q := by
  have ht := of_decide_eq_true h
  have hh : (logHi n k x:ℝ)*(P:ℝ)^2 < (eLo ne : ℝ)*(x:ℝ)*Q := by exact_mod_cast ht
  have hx0 : 0 ≤ (x:ℝ) := by exact_mod_cast ((by positivity : 0 ≤ (2:ℚ)^k).trans hx)
  have H := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (e_correct he).1 hx0) (Nat.cast_nonneg (α:=ℝ) Q)
  have G := mul_le_mul_of_nonneg_right (log_correct n k hx).2 (sq_nonneg (P:ℝ))
  apply sub_pos.mpr
  unfold RHReal.coeff
  rw [show exp 1*((x:ℝ)/log (x:ℝ))*Q =
    (exp 1*(x:ℝ)*Q)/log (x:ℝ) by ring]
  exact (lt_div_iff₀ hlog).mpr (by
    simpa [mul_comm] using G.trans_lt (hh.trans_le H))

#print axioms cert_neg_sound
#print axioms cert_pos_sound
end RHLog
