import NicolasFourPoint

/-! A finite multiplicative block contains an improved actual Euler-product
value; the conclusion is existential among four explicit arguments. -/
namespace RHOcticPush.Nicolas
open Real NicolasContinuation
set_option maxHeartbeats 0

/-- Among x,x²,x³,x⁴ at least one normalized actual prime-product log has
coefficient2-beta/4, instead of the one-point scalar2-beta. -/
theorem actual_product_block (hRH : RiemannHypothesis) (h119 : SourceNicolas119)
    (h219 : SourceNicolas219) {x : ℝ} (hx : 599 < x) :
    ∃ k : ℕ, k ∈ ({1, 2, 3, 4} : Finset ℕ) ∧
      2 - beta / 4 - penalty (x ^ k) ≤ scaledLogProduct (x ^ k) := by
  have hsum := actual_product_four hRH h119 h219 hx
  have h : 2 - beta / 4 - penalty x ≤ scaledLogProduct x ∨
      2 - beta / 4 - penalty (x ^ 2) ≤ scaledLogProduct (x ^ 2) ∨
      2 - beta / 4 - penalty (x ^ 3) ≤ scaledLogProduct (x ^ 3) ∨
      2 - beta / 4 - penalty (x ^ 4) ≤ scaledLogProduct (x ^ 4) := by
    by_contra h
    push_neg at h
    rcases h with ⟨h1, h2, h3, h4⟩
    unfold fourEnvelope at hsum
    linarith
  rcases h with h | h | h | h
  · exact ⟨1, by simp, by simpa using h⟩
  · exact ⟨2, by simp, h⟩
  · exact ⟨3, by simp, h⟩
  · exact ⟨4, by simp, h⟩

lemma block_coefficient_gain : (0 : ℝ) < (2 - beta / 4) - (2 - beta) := by
  linarith [beta_pos]

#print axioms actual_product_block
#print axioms block_coefficient_gain
end RHOcticPush.Nicolas
