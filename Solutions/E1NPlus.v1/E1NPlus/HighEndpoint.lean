/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1NPlus.Bands
namespace E1NPlus
open Real Set MeasureTheory
set_option maxHeartbeats 0
noncomputable def bandDelta (s:ℝ):ℝ:=7/8-s
noncomputable def lambda0:ℝ:=(11/25)*330+B

theorem factor4_eq_g4 (s u:ℝ) :
    E1FrozenN.Interval.factor4 s u=g4 (q s) (b s*u) := by
  rfl

theorem main330_eq {s:ℝ} (hs:s∈Icc (3/4:ℝ) (7/8:ℝ)) :
    mainRay s 330=(2*K*330/b s)*exp (-(363/20:ℝ))*exp (log k/3)*
      ((ulog 330)^3*exp (log (ulog 330)/4))*
      exp (((8/3)*log k+2*log (ulog 330)-lambda0)*bandDelta s)*
      g4 (q s) (b s*ulog 330) := by
  have hu:0<ulog 330:=by linarith [u330_bounds.1]
  have he3:exp (3*log (ulog 330))=(ulog 330)^3 := by
    calc
      _ = exp (log (ulog 330)+log (ulog 330)+log (ulog 330)) := by congr 1;ring
      _ = _ := by rw [exp_add,exp_add,exp_log hu];ring
  have heq:B*(s-7/8)+p s*log k+(-rate s*330)+log (ulog 330)*q s=
      -(363/20:ℝ)+log k/3+(3*log (ulog 330)+log (ulog 330)/4)+
      ((8/3)*log k+2*log (ulog 330)-lambda0)*bandDelta s := by
    dsimp [B,p,q,rate,lambda0,bandDelta]
    ring
  calc
    _ = (2*K*330/b s)*
        exp (B*(s-7/8)+p s*log k+(-rate s*330)+log (ulog 330)*q s)*
        E1FrozenN.Interval.factor4 s (ulog 330) := by
      unfold mainRay coeff
      rw [rpow_def_of_pos hu]
      simp only [exp_add]
      ring
    _ = _ := by
      rw [heq,factor4_eq_g4]
      simp only [exp_add]
      rw [he3]
      ring

theorem main330_band {s a C G:ℝ} (hs:s∈Icc (3/4:ℝ) (7/8:ℝ))
    (ha:a<1/4) (hd:bandDelta s ≤ a) (hG0:0 ≤ G)
    (hg:g4 (q s) (b s*ulog 330) ≤ G)
    (hC:(4/(1-4*a))+(8/3)*log k+2*log (ulog 330) ≤ C) :
    mainRay s 330 ≤ mainPref*G*exp (-(lambda0-C)*bandDelta s) := by
  have hd0:0 ≤ bandDelta s:=by dsimp [bandDelta];linarith [hs.2]
  have hb:0<b s:=by dsimp [b,p];linarith [hs.1]
  have hu:0<ulog 330:=by linarith [u330_bounds.1]
  have hf0:0 ≤ g4 (q s) (b s*ulog 330) := by
    rw [←factor4_eq_g4]
    exact E1FrozenN.Interval.factor4_nonneg hs hu
  have hi:1/b s ≤ (3/2:ℝ)*exp ((4/(1-4*a))*bandDelta s) := by
    have hbEq:b s=(2/3:ℝ)*(1-4*bandDelta s) := by dsimp [b,p,bandDelta];ring
    calc
      _ = (3/2:ℝ)*(1/(1-4*bandDelta s)) := by
        rw [hbEq]
        simp only [one_div,mul_inv_rev]
        norm_num
        ring
      _  ≤  _ := mul_le_mul_of_nonneg_left (reciprocal_band hd0 hd ha) (by norm_num)
  have hup:(ulog 330)^3 ≤ (1403/20:ℝ)^3:=pow_le_pow_left₀ hu.le u330_bounds.2 3
  have huq:=u_quarter_root_upper hu u330_bounds.2
  have hp:0 ≤ mainPref:=by unfold mainPref;positivity
  calc
    _ = (2*K*330)*exp (-(363/20:ℝ))*exp (log k/3)*
        ((ulog 330)^3*exp (log (ulog 330)/4))*g4 (q s) (b s*ulog 330)*
        (1/b s)*exp (((8/3)*log k+2*log (ulog 330)-lambda0)*bandDelta s) := by
      rw [main330_eq hs]
      ring
    _  ≤  (2*K*330)*(1/76250000)*(663/500)*
        ((1403/20)^3*(579/200))*G*
        ((3/2)*exp ((4/(1-4*a))*bandDelta s))*
        exp (((8/3)*log k+2*log (ulog 330)-lambda0)*bandDelta s) := by
      gcongr
      · exact inverse_exp18
      · exact k_cube_root_upper
    _ = mainPref*G*exp (((4/(1-4*a))+(8/3)*log k+2*log (ulog 330)-lambda0)*bandDelta s) := by
      unfold mainPref
      rw [show ((4/(1-4*a))+(8/3)*log k+2*log (ulog 330)-lambda0)*bandDelta s=
        ((4/(1-4*a))*bandDelta s)+(((8/3)*log k+2*log (ulog 330)-lambda0)*bandDelta s) by ring,
        exp_add]
      ring
    _  ≤  _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hp hG0)
      apply exp_le_exp.mpr
      nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hC)]

theorem main330_near {s:ℝ} (hs:s∈Icc (69/80:ℝ) (7/8:ℝ)) :
    mainRay s 330 ≤ mainPref*nearG*exp (-a1*bandDelta s) := by
  have hs0:s∈Icc (3/4:ℝ) (7/8:ℝ) := by constructor <;> linarith [hs.1,hs.2]
  have hd:bandDelta s ≤ (1/80:ℝ) := by dsimp [bandDelta];linarith [hs.1]
  have hb:(19/30:ℝ) ≤ b s := by dsimp [b,p];linarith [hs.1]
  have hb0:0 ≤ b s:=by linarith
  have hz:(133/3:ℝ) ≤ b s*ulog 330 := by
    have hh:=mul_le_mul hb u330_bounds.1 (by norm_num : (0:ℝ) ≤ 70) hb0
    nlinarith
  have hq:3 ≤ q s:=by dsimp [q];linarith [hs.2]
  have hQ:q s ≤ (131/40:ℝ):=by dsimp [q];linarith [hs.1]
  have hg:g4 (q s) (b s*ulog 330) ≤ nearG :=
    g4_mono hq hQ (by norm_num : (0:ℝ)<133/3) hz
  have hC:(4/(1-4*(1/80:ℝ)))+(8/3)*log k+2*log (ulog 330) ≤ (15:ℝ) := by
    norm_num
    linarith [log_k_bounds.2,log_u330_upper]
  have hh:=main330_band (a:=(1/80:ℝ)) (C:=(15:ℝ)) (G:=nearG) hs0
    (by norm_num) hd (by norm_num [nearG,g4]) hg hC
  have heq:lambda0-(15:ℝ)=a1:=by norm_num [lambda0,B,a1]
  rwa [heq] at hh

theorem main330_mid {s:ℝ} (hs:s∈Icc (17/20:ℝ) (69/80:ℝ)) :
    mainRay s 330 ≤ mainPref*midG*exp (-a2*bandDelta s) := by
  have hs0:s∈Icc (3/4:ℝ) (7/8:ℝ) := by constructor <;> linarith [hs.1,hs.2]
  have hd:bandDelta s ≤ (1/40:ℝ) := by dsimp [bandDelta];linarith [hs.1]
  have hb:(3/5:ℝ) ≤ b s := by dsimp [b,p];linarith [hs.1]
  have hb0:0 ≤ b s:=by linarith
  have hz:(42:ℝ) ≤ b s*ulog 330 := by
    have hh:=mul_le_mul hb u330_bounds.1 (by norm_num : (0:ℝ) ≤ 70) hb0
    nlinarith
  have hq:3 ≤ q s:=by dsimp [q];linarith [hs.2]
  have hQ:q s ≤ (33/10:ℝ):=by dsimp [q];linarith [hs.1]
  have hg:g4 (q s) (b s*ulog 330) ≤ midG :=
    g4_mono hq hQ (by norm_num : (0:ℝ)<42) hz
  have hC:(4/(1-4*(1/40:ℝ)))+(8/3)*log k+2*log (ulog 330) ≤ (761/50:ℝ) := by
    norm_num
    linarith [log_k_bounds.2,log_u330_upper]
  have hh:=main330_band (a:=(1/40:ℝ)) (C:=(761/50:ℝ)) (G:=midG) hs0
    (by norm_num) hd (by norm_num [midG,g4]) hg hC
  have heq:lambda0-(761/50:ℝ)=a2:=by norm_num [lambda0,B,a2]
  rwa [heq] at hh

theorem main330_far {s:ℝ} (hs:s∈Icc (3/4:ℝ) (17/20:ℝ)) :
    mainRay s 330 ≤ mainPref*farG*exp (-a3*bandDelta s) := by
  have hs0:s∈Icc (3/4:ℝ) (7/8:ℝ) := by constructor <;> linarith [hs.1,hs.2]
  have hd:bandDelta s ≤ (1/8:ℝ) := by dsimp [bandDelta];linarith [hs.1]
  have hb:(1/3:ℝ) ≤ b s := by dsimp [b,p];linarith [hs.1]
  have hb0:0 ≤ b s:=by linarith
  have hz:(70/3:ℝ) ≤ b s*ulog 330 := by
    have hh:=mul_le_mul hb u330_bounds.1 (by norm_num : (0:ℝ) ≤ 70) hb0
    nlinarith
  have hq:3 ≤ q s:=by dsimp [q];linarith [hs.2]
  have hQ:q s ≤ (7/2:ℝ):=by dsimp [q];linarith [hs.1]
  have hg:g4 (q s) (b s*ulog 330) ≤ farG :=
    g4_mono hq hQ (by norm_num : (0:ℝ)<70/3) hz
  have hC:(4/(1-4*(1/8:ℝ)))+(8/3)*log k+2*log (ulog 330) ≤ (1877/100:ℝ) := by
    norm_num
    linarith [log_k_bounds.2,log_u330_upper]
  have hh:=main330_band (a:=(1/8:ℝ)) (C:=(1877/100:ℝ)) (G:=farG) hs0
    (by norm_num) hd (by norm_num [farG,g4]) hg hC
  have heq:lambda0-(1877/100:ℝ)=a3:=by norm_num [lambda0,B,a3]
  rwa [heq] at hh

#print axioms main330_band
end E1NPlus
