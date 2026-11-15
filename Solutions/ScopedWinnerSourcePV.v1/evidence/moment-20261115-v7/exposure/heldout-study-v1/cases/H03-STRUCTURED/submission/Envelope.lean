import TaskDefinitions
namespace ExposureTask
open Real
lemma exp_small {D : ℝ} (hD : D ≤ 163) :
    Real.exp (-(330-D)/8) ≤ 1/1048576 := by
  have h1 : (2:ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ)
    linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h1 20
  have he : (1048576:ℝ) ≤ Real.exp ((330-D)/8) := by
    have hh : (20:ℝ) ≤ (330-D)/8 := by linarith
    have hm := Real.exp_le_exp.mpr hh
    rw [show (20:ℝ) = (20:ℕ) * (1:ℝ) by norm_num, Real.exp_nat_mul] at hm
    norm_num only [show (2:ℝ)^20 = 1048576 by norm_num] at hp
    exact le_trans hp hm
  rw [show -(330-D)/8 = -((330-D)/8) by ring, Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1048576) he

noncomputable def inflate : ℝ := 1048576/1048575
noncomputable def futureRatio (L : ℝ) : ℝ := inflate * (253*L/(330*(L-77)))
noncomputable def backwardRatio (L : ℝ) : ℝ := inflate * (167*L/(330*(L-163)))
noncomputable def envelope (L : ℝ) : ℝ := finiteCap * futureRatio L

lemma paired_upper {D L : ℝ} (hD : 0 ≤ D) (hLD : D < L) :
    paired D L ≤ L/(L-D) := by
  unfold paired
  have : 0 ≤ D/(L-D)*Real.exp (-(L-D)/8) :=
    mul_nonneg (div_nonneg hD (by linarith)) (Real.exp_pos _).le
  linarith

lemma paired_lower {D : ℝ} (h0 : 0 ≤ D) (hD : D ≤ 163) :
    (1048575/1048576:ℝ) * (330/(330-D)) ≤ paired D 330 := by
  have he := exp_small hD
  have hd : 0 < 330-D := by linarith
  have hm := mul_le_mul_of_nonneg_left he (div_nonneg h0 hd.le)
  unfold paired
  have hh : D/(330-D)*(1/1048576) ≤ (330/(330-D))*(1/1048576) := by
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    exact div_le_div_of_nonneg_right (by linarith) hd.le
  linarith

lemma future_factor {D L : ℝ} (hlo : 77 ≤ D) (hhi : D ≤ 163) (hL : 330 ≤ L) :
    paired D L ≤ futureRatio L * paired D 330 := by
  have hd : 0 < L-D := by linarith
  have h77 : 0 < L-77 := by linarith
  have h330 : 0 < 330-D := by linarith
  have hr : 0 ≤ futureRatio L := by
    unfold futureRatio inflate
    positivity
  have hu := paired_upper (by linarith : 0 ≤ D) (by linarith : D < L)
  have hl := mul_le_mul_of_nonneg_left (paired_lower (by linarith) hhi) hr
  have hc : L/(L-D) ≤ futureRatio L * ((1048575/1048576:ℝ)*(330/(330-D))) := by
    unfold futureRatio inflate
    field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hlo)]
  exact hu.trans (hc.trans hl)

lemma backward_factor {D L : ℝ} (hlo : 77 ≤ D) (hhi : D ≤ 163)
    (hL : 300 ≤ L) (hL' : L ≤ 330) :
    paired D L ≤ backwardRatio L * paired D 330 := by
  have hd : 0 < L-D := by linarith
  have h163 : 0 < L-163 := by linarith
  have h330 : 0 < 330-D := by linarith
  have hr : 0 ≤ backwardRatio L := by
    unfold backwardRatio inflate
    positivity
  have hu := paired_upper (by linarith : 0 ≤ D) (by linarith : D < L)
  have hl := mul_le_mul_of_nonneg_left (paired_lower (by linarith) hhi) hr
  have hc : L/(L-D) ≤ backwardRatio L * ((1048575/1048576:ℝ)*(330/(330-D))) := by
    unfold backwardRatio inflate
    field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hL') (sub_nonneg.mpr hhi)]
  exact hu.trans (hc.trans hl)

noncomputable def finiteSum {n : ℕ} (w D : Fin n → ℝ) (L : ℝ) : ℝ :=
  ∑ i, w i * paired (D i) L

lemma sum_transfer {n : ℕ} (w D : Fin n → ℝ) (L r : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hr : 0 ≤ r)
    (hf : ∀ i, paired (D i) L ≤ r * paired (D i) 330)
    (hcap : finiteSum w D 330 ≤ finiteCap) :
    finiteSum w D L ≤ finiteCap*r := by
  calc
    finiteSum w D L ≤ ∑ i, w i * (r * paired (D i) 330) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hf i) (hw i)
    _ = r * finiteSum w D 330 := by
      unfold finiteSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ r * finiteCap := mul_le_mul_of_nonneg_left hcap hr
    _ = finiteCap * r := mul_comm _ _

theorem future_envelope {n : ℕ} (w D : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hlo : ∀ i, 77 ≤ D i) (hhi : ∀ i, D i ≤ 163)
    (hcap : finiteSum w D 330 ≤ finiteCap) {L : ℝ} (hL : 330 ≤ L) :
    finiteSum w D L ≤ envelope L := by
  apply sum_transfer w D L (futureRatio L) hw _ _ hcap
  · have : 0 < L-77 := by linarith
    have : 0 < L := by linarith
    unfold futureRatio inflate
    positivity
  · intro i
    exact future_factor (hlo i) (hhi i) hL

theorem backward_envelope {n : ℕ} (w D : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hlo : ∀ i, 77 ≤ D i) (hhi : ∀ i, D i ≤ 163)
    (hcap : finiteSum w D 330 ≤ finiteCap) {L : ℝ}
    (hL : 300 ≤ L) (hL' : L ≤ 330) :
    finiteSum w D L ≤ finiteCap * backwardRatio L := by
  apply sum_transfer w D L (backwardRatio L) hw _ _ hcap
  · have : 0 < L-163 := by linarith
    have : 0 < L := by linarith
    unfold backwardRatio inflate
    positivity
  · intro i
    exact backward_factor (hlo i) (hhi i) hL hL'

lemma quotient_decreasing {a X L : ℝ} (ha : 0 ≤ a) (hX : a < X) (hL : X ≤ L) :
    L/(L-a) ≤ X/(X-a) := by
  apply (div_le_div_iff₀ (by linarith) (by linarith)).2
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hL)]

lemma envelope_decreasing {X L : ℝ} (hX : 330 ≤ X) (hL : X ≤ L) :
    envelope L ≤ envelope X := by
  have hq := quotient_decreasing (a := 77) (by norm_num) (by linarith) hL
  unfold envelope futureRatio inflate finiteCap
  have heq (t : ℝ) : 253*t/(330*(t-77)) = (253/330:ℝ)*(t/(t-77)) := by rw [mul_div_mul_comm]
  rw [heq, heq]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (by norm_num)) (by norm_num))
    (by norm_num)

lemma strict_improvement {L : ℝ} (hL : 500 ≤ L) : envelope L < finiteCap := by
  have hm := envelope_decreasing (X := 500) (by norm_num) hL
  have hc : envelope 500 < finiteCap := by
    norm_num [envelope, finiteCap, futureRatio, inflate]
  exact hm.trans_lt hc

noncomputable def remainder (L : ℝ) : ℝ :=
  (4/1000000:ℝ)*L/(L-160) + 2/100000000 +
  (1/1000000000000:ℝ)*L/(L-880/3) + 2/1000000000000
noncomputable def consumerRHS (f L : ℝ) : ℝ :=
  (1+1/1000000000:ℝ)*(f+remainder L)+1/1000000000000+1/100000000
noncomputable def epiEnvelope (L : ℝ) : ℝ := consumerRHS (envelope L) L

lemma remainder_decreasing {X L : ℝ} (hX : 330 ≤ X) (hL : X ≤ L) :
    remainder L ≤ remainder X := by
  have h1 := quotient_decreasing (a := 160) (by norm_num) (by linarith) hL
  have h2 := quotient_decreasing (a := 880/3) (by norm_num) (by linarith) hL
  unfold remainder
  simp only [mul_div_assoc]
  nlinarith

lemma epiEnvelope_decreasing {X L : ℝ} (hX : 330 ≤ X) (hL : X ≤ L) :
    epiEnvelope L ≤ epiEnvelope X := by
  have h1 := envelope_decreasing hX hL
  have h2 := remainder_decreasing hX hL
  unfold epiEnvelope consumerRHS
  linarith

theorem actual_epi_envelope {n : ℕ} (w D : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hlo : ∀ i, 77 ≤ D i) (hhi : ∀ i, D i ≤ 163)
    (hcap : finiteSum w D 330 ≤ finiteCap)
    (consumer : ∀ L : ℝ, 330 ≤ L →
      Epi (Real.exp L) * Real.exp (L/8) ≤ consumerRHS (finiteSum w D L) L)
    {L : ℝ} (hL : 330 ≤ L) :
    Epi (Real.exp L) ≤ epiEnvelope L * Real.exp (-L/8) := by
  have hf := future_envelope w D hw hlo hhi hcap hL
  have hc := consumer L hL
  have hb : Epi (Real.exp L) * Real.exp (L/8) ≤ epiEnvelope L := by
    unfold epiEnvelope consumerRHS at *
    linarith
  have ht := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-L/8)).le
  have he : Real.exp (L/8) * Real.exp (-L/8) = 1 := by
    rw [← Real.exp_add]
    rw [show L/8 + -L/8 = 0 by ring, Real.exp_zero]
  simpa only [mul_assoc, he, mul_one] using ht

lemma checkpoint_500 : epiEnvelope 500 < (765/100000:ℝ) := by
  norm_num [epiEnvelope, consumerRHS, remainder, envelope, finiteCap, futureRatio, inflate]
lemma checkpoint_1000 : epiEnvelope 1000 < (702/100000:ℝ) := by
  norm_num [epiEnvelope, consumerRHS, remainder, envelope, finiteCap, futureRatio, inflate]
lemma checkpoint_10000 : epiEnvelope 10000 < (653/100000:ℝ) := by
  norm_num [epiEnvelope, consumerRHS, remainder, envelope, finiteCap, futureRatio, inflate]


lemma epiEnvelope_ray {X L q : ℝ} (hX : 330 ≤ X) (hL : X ≤ L)
    (hq : epiEnvelope X < q) : epiEnvelope L < q :=
  (epiEnvelope_decreasing hX hL).trans_lt hq

lemma checkpoint_rays {L : ℝ} :
    (500 ≤ L → epiEnvelope L < (765/100000:ℝ)) ∧
    (1000 ≤ L → epiEnvelope L < (702/100000:ℝ)) ∧
    (10000 ≤ L → epiEnvelope L < (653/100000:ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hL
    exact epiEnvelope_ray (by norm_num) hL checkpoint_500
  · intro hL
    exact epiEnvelope_ray (by norm_num) hL checkpoint_1000
  · intro hL
    exact epiEnvelope_ray (by norm_num) hL checkpoint_10000

theorem actual_epi_checkpoints {n : ℕ} (w D : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hlo : ∀ i, 77 ≤ D i) (hhi : ∀ i, D i ≤ 163)
    (hcap : finiteSum w D 330 ≤ finiteCap)
    (consumer : ∀ L : ℝ, 330 ≤ L →
      Epi (Real.exp L) * Real.exp (L/8) ≤ consumerRHS (finiteSum w D L) L)
    {L : ℝ} :
    (500 ≤ L → Epi (Real.exp L) < (765/100000:ℝ)*Real.exp (-L/8)) ∧
    (1000 ≤ L → Epi (Real.exp L) < (702/100000:ℝ)*Real.exp (-L/8)) ∧
    (10000 ≤ L → Epi (Real.exp L) < (653/100000:ℝ)*Real.exp (-L/8)) := by
  have main (hL : 330 ≤ L) := actual_epi_envelope w D hw hlo hhi hcap consumer hL
  refine ⟨?_, ?_, ?_⟩
  · intro hL
    exact (main (by linarith)).trans_lt
      (mul_lt_mul_of_pos_right (checkpoint_rays.1 hL) (Real.exp_pos _))
  · intro hL
    exact (main (by linarith)).trans_lt
      (mul_lt_mul_of_pos_right (checkpoint_rays.2.1 hL) (Real.exp_pos _))
  · intro hL
    exact (main (by linarith)).trans_lt
      (mul_lt_mul_of_pos_right (checkpoint_rays.2.2 hL) (Real.exp_pos _))

theorem envelope_nonconstant : envelope 500 < envelope 330 := by
  norm_num [envelope, finiteCap, futureRatio, inflate]

lemma backward_denominators {D L : ℝ} (hD : D ≤ 163) (hL : 300 ≤ L) :
    0 < L-D ∧ 0 < L-163 ∧ 0 < 330-D := by
  exact ⟨by linarith, by linarith, by linarith⟩

lemma backward_uniform {L : ℝ} (hL : 300 ≤ L) :
    finiteCap * backwardRatio L < (935/100000:ℝ) := by
  have hq := quotient_decreasing (a := 163) (X := 300) (by norm_num) (by norm_num) hL
  have hh : finiteCap * backwardRatio L ≤ finiteCap * backwardRatio 300 := by
    unfold finiteCap backwardRatio inflate
    have heq (t : ℝ) : 167*t/(330*(t-163)) = (167/330:ℝ)*(t/(t-163)) := by
      rw [mul_div_mul_comm]
    rw [heq, heq]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (by norm_num)) (by norm_num))
      (by norm_num)
  exact hh.trans_lt (by norm_num [finiteCap, backwardRatio, inflate])

-- Explicit whole-domain denominator certificate, including both remainder poles.
theorem denominators {D L : ℝ} (hD : D ≤ 163) (hL : 330 ≤ L) :
    0 < L-D ∧ 0 < L-77 ∧ 0 < L-160 ∧ 0 < L-880/3 ∧ 0 < 330-D := by
  constructor <;> try linarith
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

#print axioms future_envelope
#print axioms backward_envelope
#print axioms actual_epi_envelope
#print axioms actual_epi_checkpoints
end ExposureTask



