/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SameSourcePartition
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080.SameSource
open Real Set Finset
noncomputable def C0 (n:ℝ):ℝ:=((n+1)^3-n^3)/(3*n*sqrt n*log n)
noncomputable def cells (n:ℝ):ℕ:=⌈C0 n/16⌉₊
noncomputable def costCoefficient (n:ℝ):ℝ:=(18203/20000:ℝ)-(7/5)/log (n+1)

lemma cell_number_bounds {n:ℝ} (hn:exp 8≤n) (hC:16<C0 n) :
    (0:ℝ)<cells n ∧ C0 n/16≤(cells n:ℝ) ∧
    (cells n:ℝ)<C0 n/16+1 ∧ (cells n:ℝ)<C0 n/8 := by
  have hlo:C0 n/16≤(cells n:ℝ):=Nat.le_ceil _
  have hhi:(cells n:ℝ)<C0 n/16+1:=Nat.ceil_lt_add_one (by positivity)
  exact ⟨by linarith,hlo,hhi,by linarith⟩

lemma c0_mul_base {n:ℝ} (hn:exp 8≤n) :
    C0 n*(3*n*sqrt n*log n)=(n+1)^3-n^3 := by
  obtain ⟨hn2,hL,_,_,_,_⟩:=geometry hn
  have hn0:0<n:=by linarith
  have hl0:0<log n:=by linarith
  unfold C0
  field_simp

lemma tiling_lower (hf:Family) {n:ℝ} (hn:exp 8≤n) (hC:16<C0 n) :
    (8/9:ℝ)*((n+1)^3-n^3)/(3*log (n+1))-
      (cells n:ℝ)*costCoefficient n*sqrt ((n+1)^3) ≤ ((P (n^3) ((n+1)^3)).card:ℝ) := by
  obtain ⟨hn2,hL,hΔ,hΔhi,hsb,hlb⟩:=geometry hn
  have hn0:0<n:=by linarith
  have hL0:0<log n:=by linarith
  have hs0:0<sqrt n:=sqrt_pos.mpr hn0
  have hs2:=sq_sqrt hn0.le
  have hlp:log n≤log (n+1):=log_le_log hn0 (by linarith)
  have hlp0:0<log (n+1):=by linarith
  obtain ⟨hk0,hklo,hkhi,hkhi2⟩:=cell_number_bounds hn hC
  let k:=cells n
  let H:=((n+1)^3-n^3)/(k:ℝ)
  have hkpos:0<(k:ℝ):=hk0
  have hH:0<H:=div_pos (by nlinarith) hkpos
  have hkH:(k:ℝ)*H=(n+1)^3-n^3:=by dsimp [H];field_simp
  let m:=(8/9:ℝ)*H/(3*log (n+1))-costCoefficient n*sqrt ((n+1)^3)
  have hc:∀ i<k,m<((P (n^3+i*H) (n^3+(i+1)*H)).card:ℝ):=by
    intro i hi
    have hik:(i+1:ℝ)≤(k:ℝ):=by exact_mod_cast Nat.succ_le_iff.mpr hi
    let u:=n^3+(i:ℝ)*H
    have hu:n^3≤u:=by dsimp [u];nlinarith [mul_nonneg (show (0:ℝ)≤(i:ℝ) from Nat.cast_nonneg i) hH.le]
    have hub:u≤(n+1)^3:=by dsimp [u];nlinarith [show (0:ℝ)≤(i:ℝ) from Nat.cast_nonneg i]
    have huend:n^3+(i+1:ℝ)*H≤(n+1)^3:=by nlinarith
    obtain ⟨hua,hlou,hhiu,hslo,hshi⟩:=cube_cell_bounds hn hu hub
    have hu0:0<u:=(exp_pos _).trans_le hua
    have hlu0:0<log u:=by linarith
    have hsu0:0<sqrt u:=sqrt_pos.mpr hu0
    have hluTop:log u≤(3001/1000:ℝ)*log n:=by
      have hm:=log_le_log hu0 hub
      exact hm.trans hlb
    have hlo:3*n*sqrt n*log n≤sqrt u*log u:=by
      have hm:=mul_le_mul hslo hlou (by positivity:0≤3*log n) (sqrt_nonneg u)
      nlinarith
    have hhi:sqrt u*log u≤2*(3*n*sqrt n*log n):=by
      have hm:=mul_le_mul hshi hluTop (log_nonneg (show 1≤u by
        have hh:=exp_le_exp.mpr (by norm_num:(0:ℝ)≤24)
        have hh1:(1:ℝ)≤exp 24:=by simpa only [exp_zero] using hh
        exact hh1.trans hua)) (by positivity:0≤(1001/1000:ℝ)*n*sqrt n)
      have hx:0≤n*sqrt n*log n:=by positivity
      nlinarith only [hm,hx]
    have heC:=c0_mul_base hn
    have hmk:=mul_lt_mul_of_pos_right hkhi2 (show 0<8*(3*n*sqrt n*log n) by positivity)
    have hmklo:=mul_le_mul_of_nonneg_right hklo (show 0≤16*(3*n*sqrt n*log n) by positivity)
    have hkmul:=mul_le_mul_of_nonneg_right hhi hkpos.le
    have hkmullo:=mul_le_mul_of_nonneg_right hlo (show 0≤16*(k:ℝ) by positivity)
    have hxpos:0≤(k:ℝ)*(3*n*sqrt n*log n):=by positivity
    have hClo:(103/100:ℝ)≤H/(sqrt u*log u):=by
      apply (le_div_iff₀ (by positivity:0<sqrt u*log u)).mpr
      apply (le_div_iff₀ hkpos).mpr
      nlinarith only [hmk,hkmul,heC,hxpos]
    have hChi:H/(sqrt u*log u)≤16:=by
      apply (div_le_iff₀ (by positivity:0<sqrt u*log u)).mpr
      apply (div_le_iff₀ hkpos).mpr
      nlinarith only [hmklo,hkmullo,heC]
    have hbound:=exact_cell_common_lower hf hn hu hub hH ⟨hClo,hChi⟩
    have he:u+H=n^3+(i+1:ℝ)*H:=by dsimp [u];ring
    rw [he] at hbound
    exact hbound
  have ht:=tiled_count hH.le k hc
  rw [show n^3+(k:ℝ)*H=(n+1)^3 by linarith] at ht
  have he:(k:ℝ)*m=(8/9:ℝ)*((n+1)^3-n^3)/(3*log (n+1))-
      (cells n:ℝ)*costCoefficient n*sqrt ((n+1)^3):=by
    dsimp [m,H,k]
    field_simp
  rwa [he] at ht

lemma main_cube_budget {n:ℝ} (hn:exp 8≤n) :
    n^2/log n ≤ ((n+1)^3-n^3)/(3*log (n+1)) := by
  obtain ⟨hn2,hL,_,_,_,_⟩:=geometry hn
  have hn0:0<n:=by linarith
  have hl0:0<log n:=by linarith
  have hlp0:0<log (n+1):=log_pos (by linarith)
  have hlstep:=log_step hn0
  have hm:=mul_le_mul_of_nonneg_right hlstep hn0.le
  have hid:(log n+1/n)*n=n*log n+1:=by field_simp
  rw [hid] at hm
  have hm2:=mul_le_mul_of_nonneg_left hm (show 0≤3*n by positivity)
  apply (div_le_div_iff₀ hl0 (by positivity:0<3*log (n+1))).mpr
  nlinarith [mul_nonneg (show 0≤3*n+1 by positivity) (show 0≤log n-1 by linarith)]

lemma cost_positive {n:ℝ} (hn:exp 8≤n) : 0<costCoefficient n ∧ costCoefficient n≤18203/20000 := by
  obtain ⟨hn2,hL,_,_,_,_⟩:=geometry hn
  have hn0:0<n:=by linarith
  have hlp:log n≤log (n+1):=log_le_log hn0 (by linarith)
  have hlp0:0<log (n+1):=by linarith
  have he:(7/5:ℝ)/log (n+1)≤7/40:=by apply (div_le_iff₀ hlp0).mpr;nlinarith
  have hpos:0<(7/5:ℝ)/log (n+1):=by positivity
  unfold costCoefficient
  constructor <;> linarith

lemma cost_small {n:ℝ} (hn:exp 8≤n) (hC:16<C0 n) (hLhi:log n≤12) :
    (cells n:ℝ)*costCoefficient n*sqrt ((n+1)^3)*log n < (199/2000:ℝ)*n^2 := by
  obtain ⟨hn2,hL,hΔ,hΔhi,hsb,hlb⟩:=geometry hn
  have hn0:0<n:=by linarith
  have hL0:0<log n:=by linarith
  have hs0:0<sqrt n:=sqrt_pos.mpr hn0
  obtain ⟨hkpos,hklo,hkhi,hkhi2⟩:=cell_number_bounds hn hC
  obtain ⟨hdpos,hdhi⟩:=cost_positive hn
  have hq:1/n≤(1/2000:ℝ):=by apply (div_le_iff₀ hn0).mpr;linarith
  have hlp:log n≤log (n+1):=log_le_log hn0 (by linarith)
  have hlp0:0<log (n+1):=by linarith
  have hstep:=log_step hn0
  have hd:costCoefficient n≤(397/500:ℝ):=by
    have hrat:(18203/20000-397/500:ℝ)≤(7/5)/log (n+1):=by
      apply (le_div_iff₀ hlp0).mpr
      nlinarith
    unfold costCoefficient
    linarith
  have heC:=c0_mul_base hn
  have hm:=mul_lt_mul_of_pos_right hkhi2 (show 0<3*n*sqrt n*log n by positivity)
  have hk:(cells n:ℝ)*n*sqrt n*log n<((n+1)^3-n^3)/24:=by nlinarith
  have hgeom:=mul_le_mul_of_nonneg_left hsb
    (show 0≤(cells n:ℝ)*costCoefficient n*log n by positivity)
  have hh:=mul_lt_mul_of_pos_left hk (show 0<(1001/1000:ℝ)*costCoefficient n by positivity)
  have hD0:0<(n+1)^3-n^3:=by nlinarith
  have hdlt:=mul_le_mul_of_nonneg_right hd (show 0≤(1001/1000:ℝ)*((n+1)^3-n^3)/24 by positivity)
  have hmain:=mul_le_mul_of_nonneg_left hΔhi (by norm_num:(0:ℝ)≤(1001/1000)*(397/500)/24)
  have hn2pos:0<n^2:=sq_pos_of_pos hn0
  nlinarith only [hgeom,hh,hdlt,hmain,hn2pos]

lemma cost_late {n:ℝ} (hn:exp 8≤n) (hC:16<C0 n) (hLlo:12≤log n) :
    (cells n:ℝ)*costCoefficient n*sqrt ((n+1)^3)*log n < (211/2500:ℝ)*n^2 := by
  obtain ⟨hn2,hL,hΔ,hΔhi,hsb,hlb⟩:=geometry hn
  have hn0:0<n:=by linarith
  have hL0:0<log n:=by linarith
  have hs0:0<sqrt n:=sqrt_pos.mpr hn0
  have hs2:=sq_sqrt hn0.le
  obtain ⟨hkpos,hklo,hkhi,hkhi2⟩:=cell_number_bounds hn hC
  obtain ⟨hdpos,hdhi⟩:=cost_positive hn
  have hn12:exp 12≤n:=by
    have h:=exp_le_exp.mpr hLlo
    simpa only [exp_log hn0] using h
  have hb:=log_div_sqrt_budget12 hn12
  have hbmul:=mul_lt_mul_of_pos_left hb (show 0<n*sqrt n by positivity)
  have hb':n*sqrt n*log n<(3/100:ℝ)*n^2:=by nlinarith
  have heC:=c0_mul_base hn
  have hm:=mul_lt_mul_of_pos_right hkhi (show 0<3*n*sqrt n*log n by positivity)
  have hk:(cells n:ℝ)*n*sqrt n*log n<((n+1)^3-n^3)/48+n*sqrt n*log n:=by nlinarith
  have hk':(cells n:ℝ)*n*sqrt n*log n<((1001/16000:ℝ)+3/100)*n^2:=by nlinarith
  have hgeom:=mul_le_mul_of_nonneg_left hsb
    (show 0≤(cells n:ℝ)*costCoefficient n*log n by positivity)
  have hdlt:=mul_le_mul_of_nonneg_right hdhi
    (show 0≤(1001/1000:ℝ)*(cells n:ℝ)*n*sqrt n*log n by positivity)
  have hmain:=mul_lt_mul_of_pos_left hk' (by norm_num:(0:ℝ)<(1001/1000)*(18203/20000))
  have hn2pos:0<n^2:=sq_pos_of_pos hn0
  nlinarith only [hgeom,hdlt,hmain,hn2pos]

/-- Complete non-single-window case; the original equal-ceiling cells cover all
of the cube, with no discarded remainder and no strengthened analytic input. -/
theorem tiled_0789 (hf:Family) {n:ℝ} (hn:exp 8≤n) (hC:16<C0 n) :
    (789/1000:ℝ)*n^2/log n < ((P (n^3) ((n+1)^3)).card:ℝ) := by
  obtain ⟨hn2,hL,_,_,_,_⟩:=geometry hn
  have hn0:0<n:=by linarith
  have hL0:0<log n:=by linarith
  have ht:=tiling_lower hf hn hC
  have hm:=main_cube_budget hn
  have hm':=(mul_le_mul_of_nonneg_left hm (by norm_num:(0:ℝ)≤8/9))
  have hml:=mul_le_mul_of_nonneg_right hm' hL0.le
  have hid:((8/9:ℝ)*(n^2/log n))*log n=(8/9:ℝ)*n^2:=by field_simp
  rw [hid] at hml
  have hidmain:(8/9:ℝ)*(((n+1)^3-n^3)/(3*log (n+1)))*log n=
      ((8/9:ℝ)*((n+1)^3-n^3)/(3*log (n+1)))*log n:=by ring
  rw [hidmain] at hml
  have htl:=mul_le_mul_of_nonneg_right ht hL0.le
  have hgoal:(789/1000:ℝ)*n^2 < ((P (n^3) ((n+1)^3)).card:ℝ)*log n:=by
    by_cases hsmall:log n≤12
    · have hc:=cost_small hn hC hsmall
      nlinarith [sq_pos_of_pos hn0]
    · have hc:=cost_late hn hC (le_of_not_ge hsmall)
      nlinarith [sq_pos_of_pos hn0]
  exact (div_lt_iff₀ hL0).mpr hgoal

/-- The stronger late branch stated in the frozen prospective argument. -/
theorem tiled_0804_late (hf:Family) {n:ℝ} (hn:exp 8≤n) (hC:16<C0 n)
    (hLlo:12≤log n) :
    (201/250:ℝ)*n^2/log n < ((P (n^3) ((n+1)^3)).card:ℝ) := by
  obtain ⟨hn2,hL,_,_,_,_⟩:=geometry hn
  have hn0:0<n:=by linarith
  have hL0:0<log n:=by linarith
  have ht:=tiling_lower hf hn hC
  have hm:=main_cube_budget hn
  have hm':=mul_le_mul_of_nonneg_left hm (by norm_num:(0:ℝ)≤8/9)
  have hml:=mul_le_mul_of_nonneg_right hm' hL0.le
  have hid:((8/9:ℝ)*(n^2/log n))*log n=(8/9:ℝ)*n^2:=by field_simp
  rw [hid] at hml
  have hidmain:(8/9:ℝ)*(((n+1)^3-n^3)/(3*log (n+1)))*log n=
      ((8/9:ℝ)*((n+1)^3-n^3)/(3*log (n+1)))*log n:=by ring
  rw [hidmain] at hml
  have htl:=mul_le_mul_of_nonneg_right ht hL0.le
  have hc:=cost_late hn hC hLlo
  apply (div_lt_iff₀ hL0).mpr
  nlinarith [sq_pos_of_pos hn0]

/-- The exact prospective .78146 result, now completed posthoc in Lean.
Its only analytic premise is the original canonical optimized Octic family. -/
theorem cube_density_078146 (hf:Family) {n:ℝ} (hn:exp 8≤n) :
    (39073/50000:ℝ)*n^2/log n < ((P (n^3) ((n+1)^3)).card:ℝ) := by
  by_cases hC:C0 n≤16
  · exact single_window_078146 hf hn hC
  · have ht:=tiled_0789 hf hn (lt_of_not_ge hC)
    obtain ⟨hn2,hL,_,_,_,_⟩:=geometry hn
    have hn0:0<n:=by linarith
    have hp:0<n^2/log n:=div_pos (sq_pos_of_pos hn0) (by linarith)
    have hcoef:=mul_lt_mul_of_pos_right (by norm_num:(39073/50000:ℝ)<789/1000) hp
    calc
      (39073/50000:ℝ)*n^2/log n=(39073/50000:ℝ)*(n^2/log n):=by ring
      _ < (789/1000:ℝ)*(n^2/log n):=hcoef
      _ = (789/1000:ℝ)*n^2/log n:=by ring
      _ < _:=ht
end RH080.SameSource
#print axioms RH080.SameSource.tiling_lower
#print axioms RH080.SameSource.cost_small
#print axioms RH080.SameSource.cost_late
#print axioms RH080.SameSource.tiled_0789
#print axioms RH080.SameSource.cube_density_078146

#print axioms RH080.SameSource.tiled_0804_late
