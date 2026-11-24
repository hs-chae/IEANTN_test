import BoxHSeries
import IEANTN.Nodes.BoxMellinInputs.v1.Conclusions
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Actual derivative of the complete correction series, linked to the original q. -/
namespace RHOcticPush.BoxGamma
open Real Set Filter
open scoped Topology
set_option maxHeartbeats 0

noncomputable def hTermD (n : ℕ) (s : ℝ) : ℝ :=
  -(Real.log ((n:ℝ)+1)*((n:ℝ)+1)^(-1-s))/(4*((n:ℝ)+1)^2-1)

lemma hTerm_hasDerivAt (n : ℕ) (s : ℝ) :
    HasDerivAt (fun s => hTerm s n) (hTermD n s) s := by
  have hn : (0:ℝ)<(n:ℝ)+1 := by positivity
  have h := (HasDerivAt.const_rpow hn
    ((hasDerivAt_id s).const_sub (-1))).div_const (4*((n:ℝ)+1)^2-1)
  dsimp only [id_eq] at h
  convert! h using 1 <;> dsimp only [hTermD] <;> ring

lemma hTermD_bound (n : ℕ) {s : ℝ} (hs : -1/2<s) :
    ‖hTermD n s‖ ≤ 2/((n:ℝ)+1)^2 := by
  have hn0 : (0:ℝ)<(n:ℝ)+1 := by positivity
  have hn1 : (1:ℝ)≤(n:ℝ)+1 := by nlinarith [(Nat.cast_nonneg n : (0:ℝ)≤n)]
  have hd : 0<4*((n:ℝ)+1)^2-1 := by nlinarith [(Nat.cast_nonneg n : (0:ℝ)≤n)]
  have hl : 0≤log ((n:ℝ)+1) := Real.log_nonneg hn1
  have hp := Real.rpow_le_rpow_of_exponent_le hn1
    (show -1-s≤(-1/2:ℝ) by linarith)
  have hlog := Real.log_le_rpow_div hn0.le (by norm_num : (0:ℝ)<1/2)
  have hm : log ((n:ℝ)+1)*((n:ℝ)+1)^(-1-s) ≤ 2 := by
    calc
      _ ≤ (((n:ℝ)+1)^(1/2:ℝ)/(1/2))*((n:ℝ)+1)^(-1/2:ℝ) :=
        mul_le_mul hlog hp (by positivity) (by positivity)
      _ = 2 := by
        have hp : ((n:ℝ)+1)^(1/2:ℝ)*((n:ℝ)+1)^(-1/2:ℝ)=1 := by
          rw [←Real.rpow_add hn0]
          norm_num
        calc
          _ = 2*(((n:ℝ)+1)^(1/2:ℝ)*((n:ℝ)+1)^(-1/2:ℝ)) := by ring
          _ = _ := by rw [hp];ring
  unfold hTermD
  rw [Real.norm_eq_abs,abs_div,abs_neg,abs_mul,abs_of_nonneg hl,
    abs_of_pos (Real.rpow_pos_of_pos hn0 _),abs_of_pos hd]
  calc
    _ ≤ 2/(4*((n:ℝ)+1)^2-1) := div_le_div_of_nonneg_right hm hd.le
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by nlinarith [(Nat.cast_nonneg n : (0:ℝ)≤n)])

lemma hTermD_zero (n : ℕ) : hTermD n 0 = -BoxMellinInputs.v1.qTerm (n+1) := by
  by_cases hn : n=0
  · subst n
    norm_num [hTermD,BoxMellinInputs.v1.qTerm]
  · have hn' : ¬n+1<2 := by omega
    unfold hTermD BoxMellinInputs.v1.qTerm
    rw [if_neg hn']
    push_cast
    norm_num only [sub_zero,Real.rpow_neg_one]
    field_simp

/-- Full actual derivative at zero. The original actual logarithmic series q is
consumed, rather than a newly chosen constant or an assumed Mellin identity. -/
theorem hSeries_hasDerivAt : HasDerivAt hSeries (-BoxMellinInputs.v1.q) 0 := by
  have hu : Summable (fun n : ℕ => 2/((n:ℝ)+1)^2) := by
    convert! hMajorant_summable.mul_left 2 using 1
    ext n
    ring
  have hd := hasDerivAt_tsum_of_isPreconnected (g := fun n s => hTerm s n)
    (g' := hTermD) hu isOpen_Ioi isPreconnected_Ioi
    (fun n s _ => hTerm_hasDerivAt n s) (fun n s hs => hTermD_bound n hs)
    (show (0:ℝ)∈Ioi (-1/2) by norm_num) (hTerm_summable (by norm_num : (-1:ℝ)≤0))
    (show (0:ℝ)∈Ioi (-1/2) by norm_num)
  have hdSum : Summable (fun n => hTermD n 0) :=
    hu.of_norm_bounded (fun n => hTermD_bound n (by norm_num : (-1/2:ℝ)<0))
  have hQShift : Summable (fun n : ℕ => BoxMellinInputs.v1.qTerm (n+1)) :=
    hdSum.neg.congr (fun n => by rw [hTermD_zero,neg_neg])
  have hQ : Summable BoxMellinInputs.v1.qTerm := (summable_nat_add_iff 1).mp hQShift
  have hq : (∑' n : ℕ,BoxMellinInputs.v1.qTerm (n+1)) = BoxMellinInputs.v1.q := by
    simpa [BoxMellinInputs.v1.q,BoxMellinInputs.v1.qTerm] using hQ.tsum_eq_zero_add.symm
  have he : (∑' n : ℕ,hTermD n 0) = -BoxMellinInputs.v1.q := by
    simp_rw [hTermD_zero]
    rw [tsum_neg,hq]
  rw [he] at hd
  exact hd

#print axioms hSeries_hasDerivAt
end RHOcticPush.BoxGamma
