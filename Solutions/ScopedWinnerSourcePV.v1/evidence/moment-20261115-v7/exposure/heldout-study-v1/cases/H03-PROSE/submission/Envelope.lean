import Mathlib
noncomputable section
namespace ExposureTask
open Real MeasureTheory
open scoped Nat
noncomputable def pi (x : ℝ) : ℝ := Nat.primeCounting ⌊x⌋₊
noncomputable def Li2 (x : ℝ) : ℝ := ∫ t in (2:ℝ)..x, 1/Real.log t
noncomputable def Epi (x : ℝ) : ℝ := |pi x-Li2 x|/(x/Real.log x)
noncomputable def paired (D L : ℝ) : ℝ := L/(L-D)-(D/(L-D))*Real.exp (-(L-D)/8)
def finiteCap : ℝ := 8433850764/1000000000000
end ExposureTask

namespace ExposureTask
open Real
noncomputable def F {n : ℕ} (w D : Fin n → ℝ) (L : ℝ) :=
  ∑ i, w i * paired (D i) L
noncomputable def B (L : ℝ) : ℝ :=
  finiteCap * (1000000/999999) * (253*L/(330*(L-77)))
noncomputable def Back (L : ℝ) : ℝ :=
  finiteCap * (1000000/999999) * (167*L/(330*(L-163)))

lemma exp_small {D : ℝ} (hD : D ≤ 163) :
    Real.exp (-(330-D)/8) ≤ (1:ℝ)/1000000 := by
  have h1 : (2:ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ)
    linarith
  have h20 : (1000000:ℝ) ≤ Real.exp 20 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h1 20
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp ⊢
    linarith
  have hm : Real.exp 20 ≤ Real.exp ((330-D)/8) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [show -(330-D)/8 = -((330-D)/8) by ring, Real.exp_neg, one_div]
  exact (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr (h20.trans hm)

lemma paired_upper {D L : ℝ} (hD : 0 ≤ D) (hL : D < L) :
    paired D L ≤ L/(L-D) := by
  unfold paired
  have : 0 ≤ D/(L-D)*Real.exp (-(L-D)/8) :=
    mul_nonneg (div_nonneg hD (by linarith)) (Real.exp_pos _).le
  linarith

lemma paired_base_lower {D : ℝ} (hlo : 77 ≤ D) (hhi : D ≤ 163) :
    (999999/1000000:ℝ) * (330/(330-D)) ≤ paired D 330 := by
  have hd : 0 < 330-D := by linarith
  have he := exp_small hhi
  have hd0 : 0 ≤ D/(330-D) := div_nonneg (by linarith) hd.le
  have hh := mul_le_mul_of_nonneg_left he hd0
  unfold paired
  apply (le_sub_iff_add_le).mpr
  apply le_trans (add_le_add_right hh _)
  field_simp
  nlinarith

lemma ratio_future {D L : ℝ} (hlo : 77 ≤ D) (hhi : D ≤ 163)
    (hL : 330 ≤ L) :
    L/(L-D) ≤ (253*L/(330*(L-77))) * (330/(330-D)) := by
  have h1 : 0 < L-D := by linarith
  have h2 : 0 < L-77 := by linarith
  have h3 : 0 < 330-D := by linarith
  apply (div_le_iff₀ h1).mpr
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hL)]

lemma ratio_back {D L : ℝ} (hlo : 77 ≤ D) (hhi : D ≤ 163)
    (hL : 300 ≤ L) (hL' : L ≤ 330) :
    L/(L-D) ≤ (167*L/(330*(L-163))) * (330/(330-D)) := by
  have h1 : 0 < L-D := by linarith
  have h2 : 0 < L-163 := by linarith
  have h3 : 0 < 330-D := by linarith
  apply (div_le_iff₀ h1).mpr
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (sub_nonneg.mpr hL')]

lemma point_transfer {D L a : ℝ} (hlo : 77 ≤ D) (hhi : D ≤ 163)
    (hL : D < L) (ha : 0 ≤ a)
    (hr : L/(L-D) ≤ a*(330/(330-D))) :
    paired D L ≤ a*(1000000/999999)*paired D 330 := by
  have hb := paired_base_lower hlo hhi
  have hb' : 330/(330-D) ≤ (1000000/999999:ℝ)*paired D 330 := by
    nlinarith
  calc
    paired D L ≤ L/(L-D) := paired_upper (by linarith) hL
    _ ≤ a*(330/(330-D)) := hr
    _ ≤ a*((1000000/999999)*paired D 330) := mul_le_mul_of_nonneg_left hb' ha
    _ = _ := by ring

lemma sum_transfer {n : ℕ} (w D : Fin n → ℝ) (L t : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ht : 0 ≤ t)
    (hp : ∀ i, paired (D i) L ≤ t*paired (D i) 330)
    (hcap : F w D 330 ≤ finiteCap) : F w D L ≤ t*finiteCap := by
  calc
    F w D L ≤ ∑ i, w i*(t*paired (D i) 330) := by
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hp i) (hw i))
    _ = t * F w D 330 := by unfold F; rw [Finset.mul_sum]; congr 1; ext i; ring
    _ ≤ t*finiteCap := mul_le_mul_of_nonneg_left hcap ht

theorem future_envelope {n : ℕ} (w D : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hlo : ∀ i, 77 ≤ D i) (hhi : ∀ i, D i ≤ 163)
    (hcap : F w D 330 ≤ finiteCap) {L : ℝ} (hL : 330 ≤ L) :
    F w D L ≤ B L := by
  have hden : 0 < L-77 := by linarith
  have hpos : 0 < L := by linarith
  have ha : 0 ≤ 253*L/(330*(L-77)) := by positivity
  have hh := sum_transfer w D L ((253*L/(330*(L-77)))*(1000000/999999)) hw
    (mul_nonneg ha (by norm_num))
    (fun i => point_transfer (hlo i) (hhi i) (by linarith [hhi i]) ha
      (ratio_future (hlo i) (hhi i) hL)) hcap
  unfold B
  convert hh using 1 <;> ring

theorem backward_envelope {n : ℕ} (w D : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hlo : ∀ i, 77 ≤ D i) (hhi : ∀ i, D i ≤ 163)
    (hcap : F w D 330 ≤ finiteCap) {L : ℝ} (hL : 300 ≤ L) (hL' : L ≤ 330) :
    F w D L ≤ Back L := by
  have hden : 0 < L-163 := by linarith
  have hpos : 0 < L := by linarith
  have ha : 0 ≤ 167*L/(330*(L-163)) := by positivity
  have hh := sum_transfer w D L ((167*L/(330*(L-163)))*(1000000/999999)) hw
    (mul_nonneg ha (by norm_num))
    (fun i => point_transfer (hlo i) (hhi i) (by linarith [hhi i]) ha
      (ratio_back (hlo i) (hhi i) hL hL')) hcap
  unfold Back
  convert hh using 1 <;> ring

noncomputable def H (L : ℝ) : ℝ :=
  (1+1/10^9)*(B L + (4/10^6)*L/(L-160) + 2/10^8 +
    (1/10^12)*L/(L-880/3) + 2/10^12) + 1/10^12 + 1/10^8

def Consumer {n : ℕ} (w D : Fin n → ℝ) : Prop :=
  ∀ L : ℝ, 330 ≤ L → Epi (Real.exp L)*Real.exp (L/8) ≤
  (1+1/10^9)*(F w D L + (4/10^6)*L/(L-160) + 2/10^8 +
    (1/10^12)*L/(L-880/3) + 2/10^12) + 1/10^12 + 1/10^8

theorem actual_Epi_envelope {n : ℕ} (w D : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hlo : ∀ i, 77 ≤ D i) (hhi : ∀ i, D i ≤ 163)
    (hcap : F w D 330 ≤ finiteCap) (hc : Consumer w D)
    {L : ℝ} (hL : 330 ≤ L) :
    Epi (Real.exp L) ≤ H L * Real.exp (-L/8) := by
  have hf := future_envelope w D hw hlo hhi hcap hL
  have he : Epi (Real.exp L)*Real.exp (L/8) ≤ H L := by
    have hh := hc L hL
    unfold H
    nlinarith
  have hd := (le_div_iff₀ (Real.exp_pos (L/8))).mpr he
  calc
    Epi (Real.exp L) ≤ H L / Real.exp (L/8) := hd
    _ = H L * Real.exp (-L/8) := by rw [div_eq_mul_inv, ← Real.exp_neg]; congr 2 <;> ring

lemma rational_mono {d A L : ℝ} (hd : 0 ≤ d) (hA : d < A) (hL : A ≤ L) :
    L/(L-d) ≤ A/(A-d) := by
  apply (div_le_div_iff₀ (by linarith : 0 < L-d) (by linarith : 0 < A-d)).mpr
  nlinarith [mul_nonneg hd (sub_nonneg.mpr hL)]

lemma B_antitone {A L : ℝ} (hA : 330 ≤ A) (hL : A ≤ L) : B L ≤ B A := by
  have hr := rational_mono (by norm_num : (0:ℝ) ≤ 77) (by linarith : 77 < A) hL
  have hk : 0 ≤ finiteCap*(1000000/999999)*(253/330) := by norm_num [finiteCap]
  have hh := mul_le_mul_of_nonneg_left hr hk
  have ha0 : A-77 ≠ 0 := by linarith
  have hl0 : L-77 ≠ 0 := by linarith
  unfold B
  convert hh using 1 <;> (try rfl) <;> (try field_simp) <;> (try ring)

lemma H_antitone {A L : ℝ} (hA : 330 ≤ A) (hL : A ≤ L) : H L ≤ H A := by
  have hb := B_antitone hA hL
  have h160 := rational_mono (by norm_num : (0:ℝ) ≤ 160) (by linarith : 160 < A) hL
  have h880 := rational_mono (by norm_num : (0:ℝ) ≤ 880/3) (by linarith : 880/3 < A) hL
  unfold H
  simp only [mul_div_assoc]
  nlinarith

theorem strict_improvement {L : ℝ} (hL : 500 ≤ L) : B L < finiteCap := by
  have hh := B_antitone (by norm_num : (330:ℝ) ≤ 500) hL
  have hn : B 500 < finiteCap := by norm_num [B, finiteCap]
  exact hh.trans_lt hn

theorem checkpoint500 {L : ℝ} (hL : 500 ≤ L) : H L < 7649/1000000 := by
  exact (H_antitone (by norm_num : (330:ℝ) ≤ 500) hL).trans_lt
    (by norm_num [H, B, finiteCap])
theorem checkpoint1000 {L : ℝ} (hL : 1000 ≤ L) : H L < 7011/1000000 := by
  exact (H_antitone (by norm_num : (330:ℝ) ≤ 1000) hL).trans_lt
    (by norm_num [H, B, finiteCap])
theorem checkpoint2000 {L : ℝ} (hL : 2000 ≤ L) : H L < 6730/1000000 := by
  exact (H_antitone (by norm_num : (330:ℝ) ≤ 2000) hL).trans_lt
    (by norm_num [H, B, finiteCap])
theorem checkpoint10000 {L : ℝ} (hL : 10000 ≤ L) : H L < 6521/1000000 := by
  exact (H_antitone (by norm_num : (330:ℝ) ≤ 10000) hL).trans_lt
    (by norm_num [H, B, finiteCap])

theorem denominators {D L : ℝ} (hD : D ≤ 163) (hL : 330 ≤ L) :
    0 < L-D ∧ 0 < 330-D ∧ 0 < L-77 ∧ 0 < L-160 ∧ 0 < L-880/3 := by
  constructor; linarith
  constructor; linarith
  constructor; linarith
  constructor <;> linarith

theorem actual_checkpoint {n : ℕ} (w D : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hlo : ∀ i, 77 ≤ D i) (hhi : ∀ i, D i ≤ 163)
    (hcap : F w D 330 ≤ finiteCap) (hc : Consumer w D)
    {A q L : ℝ} (hA : 330 ≤ A) (hL : A ≤ L) (hq : H A < q) :
    Epi (Real.exp L) < q * Real.exp (-L/8) := by
  have he := actual_Epi_envelope w D hw hlo hhi hcap hc (hA.trans hL)
  exact he.trans_lt (mul_lt_mul_of_pos_right
    ((H_antitone hA hL).trans_lt hq) (Real.exp_pos _))

theorem actual_checkpoints {n : ℕ} (w D : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hlo : ∀ i, 77 ≤ D i) (hhi : ∀ i, D i ≤ 163)
    (hcap : F w D 330 ≤ finiteCap) (hc : Consumer w D) :
    (∀ L : ℝ, 500 ≤ L → Epi (Real.exp L) < (7649/1000000)*Real.exp (-L/8)) ∧
    (∀ L : ℝ, 1000 ≤ L → Epi (Real.exp L) < (7011/1000000)*Real.exp (-L/8)) ∧
    (∀ L : ℝ, 2000 ≤ L → Epi (Real.exp L) < (6730/1000000)*Real.exp (-L/8)) ∧
    (∀ L : ℝ, 10000 ≤ L → Epi (Real.exp L) < (6521/1000000)*Real.exp (-L/8)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro L hL
    exact actual_checkpoint w D hw hlo hhi hcap hc (by norm_num : (330:ℝ) ≤ 500) hL
      (by norm_num [H, B, finiteCap])
  · intro L hL
    exact actual_checkpoint w D hw hlo hhi hcap hc (by norm_num : (330:ℝ) ≤ 1000) hL
      (by norm_num [H, B, finiteCap])
  · intro L hL
    exact actual_checkpoint w D hw hlo hhi hcap hc (by norm_num : (330:ℝ) ≤ 2000) hL
      (by norm_num [H, B, finiteCap])
  · intro L hL
    exact actual_checkpoint w D hw hlo hhi hcap hc (by norm_num : (330:ℝ) ≤ 10000) hL
      (by norm_num [H, B, finiteCap])

lemma Back_uniform {L : ℝ} (hL : 300 ≤ L) : Back L < 9347/1000000 := by
  have hr := rational_mono (by norm_num : (0:ℝ) ≤ 163) (by norm_num : (163:ℝ) < 300) hL
  have hk : 0 ≤ finiteCap*(1000000/999999)*(167/330) := by norm_num [finiteCap]
  have hh := mul_le_mul_of_nonneg_left hr hk
  have hb : Back L ≤ Back 300 := by
    unfold Back
    convert hh using 1 <;> (try rfl) <;> (try field_simp) <;> (try ring)
  exact hb.trans_lt (by norm_num [Back, finiteCap])

lemma exp_future_small {D L : ℝ} (hD : D ≤ 163) (hL : 330 ≤ L) :
    0 < Real.exp (-(L-D)/8) ∧ Real.exp (-(L-D)/8) ≤ (1:ℝ)/1000000 := by
  refine ⟨Real.exp_pos _, ?_⟩
  exact (Real.exp_le_exp.mpr (by linarith : -(L-D)/8 ≤ -(330-D)/8)).trans
    (exp_small hD)

lemma backward_denominators {D L : ℝ} (hD : D ≤ 163) (hL : 300 ≤ L) :
    0 < L-D ∧ 0 < L-163 ∧ 0 < 330-D := by
  constructor; linarith
  constructor <;> linarith

theorem B_nonconstant : B 330 ≠ B 500 := by norm_num [B, finiteCap]

-- These diagnostics list every axiom used by the principal kernel theorems.
#print axioms future_envelope
#print axioms backward_envelope
#print axioms actual_Epi_envelope
#print axioms actual_checkpoints
#print axioms Back_uniform
#print axioms exp_future_small
#print axioms B_nonconstant
end ExposureTask
