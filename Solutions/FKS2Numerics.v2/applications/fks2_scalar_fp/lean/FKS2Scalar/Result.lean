import FKS2Scalar.Enclosure

namespace FKS2Scalar

def E : Rat := 1 / 10 ^ 15
def Bpoc : Rat := 6339 / 10 ^ 10

theorem rational_certificate :
    q - E ≤ nuLo ∧ nuHi ≤ q + E ∧ 0 ≤ E ∧ E ≤ 1 / 10 ^ 12 ∧
    q + E ≤ Bpoc ∧ 63376 / 10 ^ 11 < q - E := by
  native_decide

theorem forward_error : |(q : ℝ) - exactTarget| ≤ (E : ℝ) := by
  have hc := rational_certificate
  have hl : (q : ℝ) - (E : ℝ) ≤ (nuLo : ℝ) := by
    simpa only [Rat.cast_sub] using (Rat.cast_le (K := ℝ)).2 hc.1
  have hu : (nuHi : ℝ) ≤ (q : ℝ) + (E : ℝ) := by
    simpa only [Rat.cast_add] using (Rat.cast_le (K := ℝ)).2 hc.2.1
  rw [abs_le]
  constructor <;> linarith [target_enclosure.1, target_enclosure.2]

theorem source_result_unique {out : Rat} (h : ExecC selectedAST out) : out = q := by
  exact Option.some.inj (h.symm.trans fixed_execution)

theorem selected_source_error {out : Rat} (h : ExecC selectedAST out) :
    |(out : ℝ) - FKS2Numerics.v1.nuAsympE30| ≤ (E : ℝ) := by
  rw [source_result_unique h]
  exact forward_error

theorem poc_upper_bound : FKS2Numerics.v1.nuAsympE30 ≤ (6339 : ℝ) / 10 ^ 10 := by
  have hb : (q : ℝ) + (E : ℝ) ≤ (6339 : ℝ) / 10 ^ 10 := by
    have h := (Rat.cast_le (K := ℝ)).2 rational_certificate.2.2.2.2.1
    simpa [Bpoc] using h
  have he := (abs_sub_le_iff.mp forward_error).2
  change exactTarget ≤ _
  linarith

theorem original_threshold_discrepancy : ¬ FKS2Numerics.v1.nu_asymp_e30_le := by
  have hg : (63376 : ℝ) / 10 ^ 11 < (q : ℝ) - (E : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).2 rational_certificate.2.2.2.2.2
    simpa using h
  have he := (abs_sub_le_iff.mp forward_error).1
  unfold FKS2Numerics.v1.nu_asymp_e30_le
  rw [upstream_margin_zero]
  change ¬ exactTarget ≤ 1 * 6.3376e-7
  linarith

/-- All fixed-instance data are provided, without an assumed successful execution or
mathematical accuracy hypothesis. The source interpretation is the generic restricted model. -/
theorem connected_result : sourceChecked = true ∧ ExecC selectedAST q ∧
    finiteBits outputBits = true ∧
    |(q : ℝ) - FKS2Numerics.v1.nuAsympE30| ≤ (E : ℝ) ∧
    (0 : Rat) ≤ E ∧ E ≤ 1 / 10 ^ 12 ∧ q + E ≤ Bpoc := by
  exact ⟨source_checked, fixed_execution, output_finite, forward_error,
    rational_certificate.2.2.1, rational_certificate.2.2.2.1,
    rational_certificate.2.2.2.2.1⟩

end FKS2Scalar
