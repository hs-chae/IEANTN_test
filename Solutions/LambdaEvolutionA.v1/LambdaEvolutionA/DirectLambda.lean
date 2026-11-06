/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import LambdaEvolutionA.RawSigma
import PVEvolutionA.Recovery.Spectral
import PVEvolutionA.Recovery.MixedProgram
import PVEvolutionA.Recovery.MixedRun
import PVEvolutionA.Recovery.GaussianBasisRun
/-! Direct CH2 weighted consumer. The original finite formula is uniform for
0≤σ<1, with a single chosen height. Existing proved limits supplyσ=1.
No Abel-tail allowance, prime-counting reinterpretation or new source premise
is used. The density and finite-RH hypotheses stay explicit. -/
namespace LambdaEvolutionA
open Complex Filter Topology Set MeasureTheory Real WinnerDensityA
open CH2QRH CH2.v7 CH2Section6 CH2Section81 CH2Section9
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Packaging of exactly the thirteen existing namedCH2 source statements. -/
structure DirectCH2Inputs : Prop where
  hfe : ZetaLogDeriv.v1.logDeriv_functional_equation
  hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip
  h24u : CH2.v2.proposition_2_4_upper
  h24l : CH2.v2.proposition_2_4_lower
  hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating
  hneg : ZetaLogDerivValues.v1.logDeriv_neg_one
  h2v : ZetaLogDerivValues.v1.logDeriv_two
  hv : ZetaLogDerivValues.v1.logDeriv_three_halves
  hcs : CotangentSeries.v1.cot_series_zeta_values
  hrvm : ZeroCount.v1.rvm_error_bound
  hsmall : ZeroCount.v1.rvm_error_small
  hlow : LowZeroes.v1.no_zeroes_below_first_ordinate
  hH : ZetaHadamard.v1.logDeriv_partial_fractions

noncomputable def weightedRemainder (T t x : ℝ) : ℝ :=
  Real.pi/t +
    2*(horizontalCorrection T t x+Real.eulerMascheroniConstant/Real.log x^2+
      1.8/Real.log x^3)/t^2+
    2*Real.pi/(t*x)*((1+t/(4*Real.pi))*(x^(-2:ℝ)/(1-x^(-2:ℝ))))

/-- The exact weighted sum after the common-heightσ→1 limit. -/
theorem direct_lambda_at_height (hs : DirectCH2Inputs)
    {T x : ℝ} (hT : 3*(10:ℝ)^(12:ℕ)+1≤T) (hR : 16≤Real.log T)
    (hx1 : 1000000≤x) (hxlog : 1≤Real.log x) :
    ∃t∈Icc (T-1/2) T,
      |CH2.v1.lambdaSum x-(Real.log x-Real.eulerMascheroniConstant)|≤
        rawSpectral t x+weightedRemainder T t x := by
  obtain ⟨t,ht,huniform⟩ := raw_sigma_transfer_at_height hs.hfe hs.hdig hs.h24u hs.h24l
    hs.hk hs.hneg hs.h2v hs.hv hs.hcs hs.hrvm hs.hsmall hs.hlow hs.hH hT hR hx1 hxlog
  have ht0 : 0<t := by linarith [ht.1]
  have hx0 : 0<x := by linarith
  have hlim := ((CH2Section9.tendsto_Svm hx0).sub (CH2Section9.tendsto_main ht0 hx0)).abs
  have hbound : |(∑n∈Finset.Iic ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n:ℝ)/(n:ℝ))-
      (Real.log x-Real.eulerMascheroniConstant)|≤
      Real.pi/t+rawSpectral t x+
        2*(horizontalCorrection T t x+Real.eulerMascheroniConstant/Real.log x^2+
          1.8/Real.log x^3)/t^2+
        2*Real.pi/(t*x)*((1+t/(4*Real.pi))*(x^(-2:ℝ)/(1-x^(-2:ℝ)))) := by
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with σ hσ hσ0
    exact huniform σ hσ0.le hσ
  refine ⟨t,ht,?_⟩
  change |(∑n∈Finset.Iic ⌊x⌋₊,(ArithmeticFunction.vonMangoldt n:ℝ)/(n:ℝ))-
    (Real.log x-Real.eulerMascheroniConstant)|≤_
  unfold weightedRemainder
  linarith only [hbound]

/-- The oldψ finite remainder safely dominates the direct weighted remainder. -/
theorem weightedRemainder_le {t T x : ℝ} (hT : 2000≤T)
    (ht1 : T-1/2≤t) (ht2 : t≤T) (hx : 1000000≤x) :
    weightedRemainder T t x≤finiteRemainder T x := by
  have h := density_remainder_at_height_le hT ht1 ht2 hx
  have hx0 : 0<x := by linarith
  have hlog : 0≤Real.log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hA : 0≤Real.pi^2/(3*t^2) := by positivity
  have hB : 0≤Real.log (2*Real.pi)/x := div_nonneg hlog hx0.le
  unfold weightedRemainder
  linarith only [h,hA,hB]

/-- Direct weighted finite transfer with exactly the existingCH2 source package. -/
theorem direct_lambda_finite (hs : DirectCH2Inputs)
    {T x : ℝ} (hT : 3*(10:ℝ)^(12:ℕ)+1≤T) (hR : 16≤Real.log T)
    (hx1 : 1000000≤x) (hxlog : 1≤Real.log x) :
    ∃t∈Icc (T-1/2) T,
      |CH2.v1.lambdaSum x-(Real.log x-Real.eulerMascheroniConstant)|≤
        finiteRemainder T x+rawSpectral t x := by
  obtain ⟨t,ht,h⟩ := direct_lambda_at_height hs hT hR hx1 hxlog
  refine ⟨t,ht,?_⟩
  have hr := weightedRemainder_le (by norm_num at hT;linarith : 2000≤T) ht.1 ht.2 hx1
  linarith only [h,hr]

/-- The direct weighted consumer retains the actual8192-cap density profile.
FiniteRH ends at3e12; the much larger selected truncation height is unrestricted.
The pre-existing numerical expression includes the proved finite-remainder cap. -/
theorem direct_lambda_row_normalized (hs : DirectCH2Inputs)
    (accepted : ∀j:Fin 18,WinnerProgramA.acceptUpper
      (PVEvolutionA.Recovery.GaussianBasis.output j)
      [(PVEvolutionA.Recovery.GaussianBasis.spec j).cap]=true)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {n:ℕ} (hn:0<n) {x:ℝ} (hx:Real.exp (330:ℝ)≤x) :
    |CH2.v1.lambdaSum x-(Real.log x-Real.eulerMascheroniConstant)| *x^((1:ℝ)/8)≤
      PVEvolutionA.Recovery.Numerical.coefficient n 330 100 := by
  have hx0 : 0<x := (Real.exp_pos 330).trans_le hx
  let L := Real.log x
  let k : ℝ := 1/3
  let T : ℝ := Real.exp (k*L)+1/2
  have hL : (330:ℝ)≤L := by
    have hh := Real.log_le_log (Real.exp_pos 330) hx
    simpa only [Real.log_exp] using hh
  have hL64 : 64≤Real.log x := by dsimp [L] at hL;linarith
  have hk : k≤7/10 := by norm_num [k]
  have hsep : 34≤k*Real.log x-Real.log x/8 := by dsimp [k];dsimp [L] at hL;linarith
  obtain ⟨hTlo,hR,hxlo,_,_,hlogT⟩ := density_height_parameters hx0 hL64 hk hsep
  obtain ⟨t,ht,hE⟩ := direct_lambda_finite hs hTlo hR hxlo (by linarith)
  have h100 : H≤Real.exp (100:ℝ) := by
    have hh := (CH2Section7A.exp_nat_bounds 44).1
    have he := Real.exp_le_exp.mpr (show (44:ℝ)≤100 by norm_num)
    norm_num [H] at hh ⊢
    linarith
  have htexp : Real.exp (100:ℝ)≤t := by
    have he : Real.exp (100:ℝ)≤Real.exp (k*L) := Real.exp_le_exp.mpr (by dsimp [k];linarith)
    exact he.trans (show Real.exp (k*L)≤t by simpa only [T,add_sub_cancel_right] using ht.1)
  have ht1 : 1≤t := (Real.one_le_exp (by norm_num : (0:ℝ)≤100)).trans htexp
  have htlog : Real.log t≤((110:ℝ)/330)*L+(1:ℝ)/10^9 := by
    have htT : t≤T := ht.2
    have hb := (Real.log_le_log (by linarith : 0<t) htT).trans hlogT
    norm_num only [show (110:ℝ)/330=1/3 by norm_num]
    convert! hb using 1 <;> norm_num [k,L]
  have hbase := density_count_base_row (by norm_num : (64:ℝ)≤330) hL
    (by norm_num : (44:ℝ)≤110) ht1 htlog
  have hrem := density_remainder_coefficient hx0 hL64 hk hsep
  have ha := PVEvolutionA.graded_monotone n
  have ha0 := PVEvolutionA.graded_zero hn
  have han := PVEvolutionA.graded_last n
  have hQ : ∀i≤n,(2*Real.pi/t)*IEANTN.zetaZeroesSum
      (Ioo (PVEvolutionA.gradedGrid n i) 1) (Ioc 0 t)
      (fun rho↦t/Real.pi*(1/rho.im)+2)≤
        PVEvolutionA.Recovery.Model.envelope (PVEvolutionA.gradedGrid n i) 100 := by
    intro i hi
    have hlo : (3/4:ℝ)≤PVEvolutionA.gradedGrid n i := by rw [←ha0];exact ha (Nat.zero_le i)
    have hhi : PVEvolutionA.gradedGrid n i≤(7/8:ℝ) := by rw [←han];exact ha hi
    exact PVEvolutionA.Recovery.Model.source_ordinate_envelope accepted h hRH hlo hhi
      (by norm_num) h100 htexp
  have hspec := spectral_grid_abstract hs.hrvm hs.hsmall hs.hlow
    (by have hh:=h100.trans htexp;norm_num [H] at hh;linarith : 1000≤t)
    hx0 (by norm_num : (0:ℝ)≤330) hL hqrh
    (PVEvolutionA.gradedGrid n) ha n ha0 han
    (fun s↦PVEvolutionA.Recovery.Model.envelope s 100) hQ
  have hscaled := mul_le_mul_of_nonneg_right hE (Real.rpow_pos_of_pos hx0 ((1:ℝ)/8)).le
  rw [add_mul] at hscaled
  unfold PVEvolutionA.Recovery.Numerical.coefficient
  dsimp only [L,T,k] at *
  norm_num only [show (330:ℝ)/3=110 by norm_num]
  linarith only [hscaled,hspec,hbase,hrem]

/-- Actual weighted sum, directly using the previously executed spectral program.
This proves a weighted consumer, not a relabeling of the existingπ theorem. -/
theorem direct_lambda330 (hs : DirectCH2Inputs)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {x:ℝ} (hx:Real.exp (330:ℝ)≤x) :
    |CH2.v1.lambdaSum x-(Real.log x-Real.eulerMascheroniConstant)|≤
      (1826923053/200000000000:ℝ)*x^(-(1:ℝ)/8) := by
  have hp := direct_lambda_row_normalized hs PVEvolutionA.Recovery.GaussianBasis.accepted
    h hRH hqrh (n:=PVEvolutionA.Recovery.Ray.sigmaCells)
    (by norm_num [PVEvolutionA.Recovery.Ray.sigmaCells]) hx
  have hc := PVEvolutionA.Recovery.Mixed.coefficient_of_checks
    PVEvolutionA.Recovery.Mixed.base_checked PVEvolutionA.Recovery.Mixed.checked_all
  have hx0 : 0<x := (Real.exp_pos 330).trans_le hx
  have hb := hp.trans hc
  rw [show -(1:ℝ)/8=-((1:ℝ)/8) by ring,Real.rpow_neg hx0.le]
  exact (le_mul_inv_iff₀ (Real.rpow_pos_of_pos hx0 _)).mpr hb

/-- A strict comparison of stated allowances with the flat9C transfer of the
friendly0.009134616 genuineψ envelope. This does not compare actual errors. -/
theorem direct_allowance_strict_vs_flat {x:ℝ} (hx:0<x) :
    (1826923053/200000000000:ℝ)*x^(-(1:ℝ)/8)<
      (9*(9134616/1000000000:ℝ))*x^(-(1:ℝ)/8) := by
  exact mul_lt_mul_of_pos_right (by norm_num) (Real.rpow_pos_of_pos hx _)

#print axioms direct_lambda_at_height
#print axioms direct_lambda_finite
#print axioms direct_lambda_row_normalized
#print axioms direct_lambda330
end LambdaEvolutionA
