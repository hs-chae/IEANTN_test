/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import FKSComputationLed.BaselineProgram
namespace FKSComputationLed.BaselineSound
open BaselineProgram CellProgram PointProgram Real RealBounds LeanCert.Core

/-- A deliberately smaller comparison profile than the full old π* transfer.
It discards every prime-power correction beyond the square term and subtracts2
to cover either sign of a normalization constant of absolute value at most2.
This is a LOWER comparison profile, not asserted to be a PNT upper bound. -/
noncomputable def squareLower (x : ℝ) : ℝ :=
  1+(IEANTN.primeCounting (sqrt x)/2-2)*weight x
noncomputable def directLower (x : ℝ) : ℝ :=
  195/100+(39/10)/log x+(195/10)/(log x)^2-2*weight x

lemma check_sound (z : BaselineProgram.Cell)
    (hc : check (Sieve.oddPrimeList 40000) z=true)
    (x : ℝ) (hax : (z.a:ℝ)≤x) (hxb : x≤(z.b:ℝ)) :
    (19/10:ℝ) ≤ (9/10)*squareLower x ∧ log x≤24 := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,and_assoc] at hc
  rcases hc with ⟨hn,hnU,hna,hc4,hr,hv,hl⟩
  have hcount := RankSound.rankCheck_sound (by norm_num : 40000≤2000000000) hn hnU hr
  obtain ⟨hb,hlb,hlbU,hLiB,hWB⟩ := PointSound.pointInfo_sound z.b hv
  have hB0 : (0:ℝ)<(z.b:ℝ) := by exact_mod_cast (by omega : 0<z.b)
  have hnreal : (0:ℝ)≤(z.n:ℝ) := Nat.cast_nonneg _
  have hnxsq : (z.n:ℝ)^2≤x := by
    have hh : (z.n:ℝ)*(z.n:ℝ)≤(z.a:ℝ) := by exact_mod_cast hna
    nlinarith
  have hx0 : 0<x := by
    have hh : (3:ℝ)≤(z.n:ℝ) := by exact_mod_cast hn
    nlinarith [sq_nonneg (z.n:ℝ)]
  have hns : (z.n:ℝ)≤ sqrt x := (le_sqrt hnreal hx0.le).mpr hnxsq
  have hpi := pi_mono hns
  have hepi : IEANTN.primeCounting (z.n:ℝ)=(z.c:ℝ) := by
    simpa [IEANTN.primeCounting] using congrArg (fun n:Nat=>(n:ℝ)) hcount
  rw [hepi] at hpi
  have hcm : (0:ℝ)≤(z.c:ℝ)/2-2 := by
    have hh : (4:ℝ)≤(z.c:ℝ) := by exact_mod_cast hc4
    linarith
  have hconst : (z.c:ℝ)/2-2 ∈ IntervalDyadic.ofIntervalRat
      ⟨(z.c:ℚ)/2-2,(z.c:ℚ)/2-2,le_rfl⟩ cfg.precision := by
    apply IntervalDyadic.mem_ofIntervalRat (prec:=cfg.precision) (hprec:=by decide)
    simp [IntervalRat.mem_def]
  have hm := IntervalDyadic.mem_mul hconst hWB
  have hlower : (10/9:ℝ)≤((z.c:ℝ)/2-2)*weight (z.b:ℝ) := by
    have hh := (IntervalDyadic.lowerBoundedBy_spec hl).trans (IntervalDyadic.lo_le_of_mem hm)
    simpa only [Rat.cast_div,Rat.cast_ofNat,weight] using hh
  have hlogx : 2≤log x := by
    have hn3 : (3:ℝ)≤(z.n:ℝ) := by exact_mod_cast hn
    have hx9 : (9:ℝ)≤x := by nlinarith
    have hl9 : 2≤log (9:ℝ) := by
      have h3 : (1:ℝ)<log 3 := (lt_log_iff_exp_lt (by norm_num)).mpr exp_one_lt_three
      have h9 : log (9:ℝ)=2*log 3 := by rw [show (9:ℝ)=3^2 by norm_num,log_pow];norm_num
      linarith
    exact hl9.trans (log_le_log (by norm_num) hx9)
  have hwx0 : 0≤weight x := div_nonneg (by linarith) (sqrt_nonneg _)
  have hwB : weight (z.b:ℝ)≤weight x := weight_antitone hx0 hlogx hxb
  have hmul1 := mul_le_mul_of_nonneg_left hwB hcm
  have hmul2 := mul_le_mul_of_nonneg_right (show (z.c:ℝ)/2-2≤IEANTN.primeCounting (sqrt x)/2-2 by linarith) hwx0
  constructor
  · unfold squareLower
    linarith
  · exact (log_le_log hx0 hxb).trans hlbU

lemma all_square_Ioc {xs : List BaselineProgram.Cell} {p : Nat}
    (hs : shape p xs=true)
    (hc : ∀z∈xs, check (Sieve.oddPrimeList 40000) z=true) :
    ∀x:ℝ, (p:ℝ)<x → x≤1000000000 →
      (19/10:ℝ)≤(9/10)*squareLower x ∧ log x≤24 := by
  induction xs generalizing p with
  | nil =>
    simp only [shape,decide_eq_true_eq] at hs
    subst p
    intro x h1 h2
    norm_num at h1
    linarith
  | cons z zs ih =>
    simp only [shape,Bool.and_eq_true,decide_eq_true_eq] at hs
    rcases hs with ⟨⟨rfl,hab,hbU⟩,hs⟩
    intro x h1 h2
    by_cases hxb : x≤(z.b:ℝ)
    · exact check_sound z (hc z (by simp)) x h1.le hxb
    · exact ih hs (fun z hz=>hc z (by simp [hz])) x (lt_of_not_ge hxb) h2

theorem square_comparison (x : ℝ) (hx : (100000000:ℝ)≤x) (hxU : x≤1000000000) :
    (19/10:ℝ)≤(9/10)*squareLower x ∧ log x≤24 := by
  have hc : ∀z∈cells, check (Sieve.oddPrimeList 40000) z=true :=
    List.all_eq_true.mp checked
  by_cases hgt : (100000000:ℝ)<x
  · exact all_square_Ioc covered hc x hgt hxU
  · have hxe : x=100000000 := by linarith
    rw [hxe]
    exact check_sound ⟨100000000,101000000,10000,1229⟩
      (hc _ (List.mem_cons_self)) _ le_rfl (by norm_num)

theorem direct_comparison (x : ℝ) (hx : (100000000:ℝ)≤x) (hxU : x≤1000000000) :
    (19/10:ℝ)≤(9/10)*directLower x := by
  have hL24 := (square_comparison x hx hxU).2
  have hx0 : 0<x := by linarith
  have hL0 : 0<log x := log_pos (by linarith)
  have hs : (10000:ℝ)≤ sqrt x := (le_sqrt (by norm_num) hx0.le).mpr (by norm_num;exact hx)
  have hw : weight x≤(24/10000:ℝ) := by
    unfold weight
    exact (div_le_div_of_nonneg_right hL24 (sqrt_nonneg _)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs)
  have h1 : (39/240:ℝ)≤(39/10)/log x := by
    apply (le_div_iff₀ hL0).mpr
    nlinarith
  have h2 : (195/5760:ℝ)≤(195/10)/(log x)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hL0)).mpr
    nlinarith [sq_nonneg (24-log x)]
  unfold directLower
  linarith

/-- At least10percent below BOTH old analytic-route comparison profiles, uniformly.
The square profile is smaller than the full π* transfer; no sampled minimum is used. -/
theorem both_comparison (x : ℝ) (hx : (100000000:ℝ)≤x) (hxU : x≤1000000000) :
    (19/10:ℝ)≤(9/10)*min (squareLower x) (directLower x) := by
  by_cases h : squareLower x≤directLower x
  · rw [min_eq_left h]
    exact (square_comparison x hx hxU).1
  · rw [min_eq_right (le_of_not_ge h)]
    exact direct_comparison x hx hxU

#print axioms both_comparison
end FKSComputationLed.BaselineSound
