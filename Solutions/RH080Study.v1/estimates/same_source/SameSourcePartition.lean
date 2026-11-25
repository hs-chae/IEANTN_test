/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SameSourceCube
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080.SameSource
open Real Set Finset

lemma open_primes_subset {a b c d:ℝ} (hca:c≤a) (hbd:b≤d) : P a b⊆P c d := by
  classical
  intro p hp
  obtain ⟨hpB,hap,hpb⟩:=Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨?_,hca.trans_lt hap,hpb.trans_le hbd⟩
  exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hpB).1.trans (Nat.floor_le_floor hbd),(Nat.mem_primesLE.mp hpB).2⟩

lemma open_count_add {a b c:ℝ} (hab:a≤b) (hbc:b≤c) :
    (P a b).card+(P b c).card≤(P a c).card := by
  classical
  have hd:Disjoint (P a b) (P b c):=by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp':=(Finset.mem_filter.mp hp).2.2
    have hq':=(Finset.mem_filter.mp hq).2.1
    linarith
  rw [←Finset.card_union_of_disjoint hd]
  apply Finset.card_le_card
  exact Finset.union_subset (open_primes_subset le_rfl hbc) (open_primes_subset hab le_rfl)

/-- The old disjoint-open-cell argument, copied with the same exact prime set. -/
lemma tiled_count {a H m:ℝ} (hH:0≤H) (k:ℕ)
    (hc:∀ i<k,m<((P (a+i*H) (a+(i+1)*H)).card:ℝ)) :
    (k:ℝ)*m≤((P a (a+k*H)).card:ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hi:=ih (fun i hi=>hc i (Nat.lt_succ_of_lt hi))
    have hcell:=hc k (Nat.lt_succ_self k)
    have had:=open_count_add (a:=a) (b:=a+k*H) (c:=a+(k+1)*H)
      (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg k) hH)) (by nlinarith)
    have had':((P a (a+k*H)).card:ℝ)+((P (a+k*H) (a+(k+1)*H)).card:ℝ)≤
        ((P a (a+(k+1)*H)).card:ℝ):=by exact_mod_cast had
    push_cast
    nlinarith

lemma cube_cell_bounds {n u:ℝ} (hn:exp 8≤n) (hu:n^3≤u) (hub:u≤(n+1)^3) :
    exp 24≤u ∧ 3*log n≤log u ∧ log u≤3*log (n+1) ∧
    n*sqrt n≤sqrt u ∧ sqrt u≤(1001/1000:ℝ)*n*sqrt n := by
  obtain ⟨hn2,hL,hΔ,hΔhi,hsb,hlb⟩:=geometry hn
  have hn0:0<n:=by linarith
  have hpow:=pow_le_pow_left₀ (exp_nonneg 8) hn 3
  have ha:exp 24≤n^3:=by simpa only [←exp_nat_mul,show (3:ℕ)*(8:ℝ)=24 by norm_num] using hpow
  have hu0:0<u:=(exp_pos _).trans_le (ha.trans hu)
  have hlo:=log_le_log (pow_pos hn0 3) hu
  rw [log_pow] at hlo
  have hhi:=log_le_log hu0 hub
  rw [log_pow] at hhi
  have hslo:=sqrt_le_sqrt hu
  rw [show n^3=n^2*n by ring,sqrt_mul (sq_nonneg n),sqrt_sq hn0.le] at hslo
  exact ⟨ha.trans hu,by simpa using hlo,by simpa using hhi,hslo,(sqrt_le_sqrt hub).trans hsb⟩

/-- Source count for a full equal cell, preserving its exact H/log(u) main term. -/
lemma exact_cell_common_lower (hf:Family) {n u H:ℝ} (hn:exp 8≤n)
    (hu:n^3≤u) (hub:u≤(n+1)^3) (hH:0<H)
    (hC:H/(sqrt u*log u)∈Icc (103/100:ℝ) 16) :
    (8/9:ℝ)*H/(3*log (n+1))-
      (18203/20000-(7/5)/log (n+1))*sqrt ((n+1)^3) < ((P u (u+H)).card:ℝ) := by
  obtain ⟨hn2,hL,hΔ,hΔhi,hsb,hlb⟩:=geometry hn
  obtain ⟨hua,hlou,hhiu,hslo,hshi⟩:=cube_cell_bounds hn hu hub
  have hn0:0<n:=by linarith
  have hL0:0<log n:=by linarith
  have hu0:0<u:=(exp_pos _).trans_le hua
  have hlu0:0<log u:=by linarith
  have hlp:log n≤log (n+1):=log_le_log hn0 (by linarith)
  have hlp0:0<log (n+1):=by linarith
  have hs0:0<sqrt u:=sqrt_pos.mpr hu0
  let C:=H/(sqrt u*log u)
  have hwidth:C*sqrt u*log u=H:=by dsimp [C];field_simp
  have hfamily:=hf C hC u hua
  rw [hwidth] at hfamily
  have heq:((8/9:ℝ)*C-18203/20000+(21/5)/log u)*sqrt u=
      (8/9:ℝ)*H/log u-(18203/20000-(21/5)/log u)*sqrt u:=by
    dsimp [C]
    field_simp
    ring
  rw [heq] at hfamily
  have hmain:(8/9:ℝ)*H/(3*log (n+1))≤(8/9:ℝ)*H/log u:=by
    apply (div_le_div_iff₀ (by positivity:0<3*log (n+1)) hlu0).mpr
    nlinarith [mul_nonneg (show 0≤(8/9:ℝ)*H by positivity) (sub_nonneg.mpr hhiu)]
  have heta:(7/5:ℝ)/log (n+1)≤(21/5:ℝ)/log u:=by
    apply (div_le_div_iff₀ hlp0 hlu0).mpr
    nlinarith
  have hsmall:(7/5:ℝ)/log (n+1)≤7/40:=by
    apply (div_le_iff₀ hlp0).mpr
    nlinarith
  have hd:0≤(18203/20000:ℝ)-(7/5)/log (n+1):=by linarith
  have hmEta:=mul_le_mul_of_nonneg_right heta hs0.le
  have hsupper:sqrt u≤sqrt ((n+1)^3):=sqrt_le_sqrt hub
  have hcost:=mul_le_mul_of_nonneg_left hsupper hd
  change _ < ((IEANTN.PrimeWindows.primesBetween u (u+H)).card:ℝ)
  nlinarith
end RH080.SameSource
#print axioms RH080.SameSource.exact_cell_common_lower
