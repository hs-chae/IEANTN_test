import OcticGreenSource
import OcticZeroDecomposition
import OcticTrivialSeries
import OcticTrivialNormalize
import OcticPoleNormalization
import OcticTwoInputs
import OcticPrimePowers

/-!
Proof transports adapted from assigned sources OcticGreenSource.lean,
OcticExplicitFormula.lean, OcticPrimePowers.lean and OcticTrivial.lean.
Copyright (c) 2026 IEANTN contributors. Apache-2.0; authors OpenAI (Codex)
of the originals. The change removes the forward-window C cap where geometry
only needs local positivity, and uses no new analytic input.
-/
namespace CubeDirect
open RHOcticPush.ExplicitFormula
open Real Complex Set Filter MeasureTheory
open scoped Topology
open RHOcticPush.GreenSource RHOcticPush.PhysicalWeight RHOcticPush.PopulationLimit
open RHOcticPush.Mollifier RHOcticPush.FourierMollifier RHOcticPush.IntegralLimits
open RHOcticPush.ZeroDecomposition RHOcticPush.TrivialSeries RHOcticPush.TrivialNormalize
open RHOcticPush.PoleNormalization RHOcticPush.Convergence
set_option maxHeartbeats 0

theorem smooth_formula_from_Green_general (hGreen : SourceGreenSmooth) (j : ℕ) {C L : ℝ}
    (hδ : 0 < EvenKernel.δ C L) (hsupp : 1 ≤ L - 2 * EvenKernel.δ C L) :
    Summable (sourcePacket (greenWeight j C L) 2) ∧
      (smoothPopulation j C L : ℂ) =
        ((2 * ∫ t : ℝ, greenWeight j C L t : ℝ) : ℂ) -
          ∑' z : ProperZero, sourcePacket (greenWeight j C L) 2 z := by
  have ha : 2 ≤ Real.exp (L - 2 * EvenKernel.δ C L) :=
    (show (2 : ℝ) ≤ Real.exp 1 by linarith [Real.add_one_le_exp (1 : ℝ)]).trans
      (Real.exp_le_exp.mpr hsupp)
  obtain ⟨hs, hc, hp, hX⟩ := greenWeight_admissible j hδ ha
  have h := hGreen (greenWeight j C L) hs hc hp 2 hX
  rw [green_mangoldt_sum j hδ] at h
  exact h

theorem complete_trivial_sum_general (hGreen : SourceGreenSmooth) (j : ℕ) {C L : ℝ}
    (hδ : 0 < EvenKernel.δ C L) (hsupp : 1 ≤ L - 2 * EvenKernel.δ C L) :
    (∑' n : ℕ, sourcePacket (greenWeight j C L) 2 (trivialZero n)) =
      (smoothTrivial j C L : ℂ) := by
  have hc := (smooth_formula_from_Green_general hGreen j hδ hsupp).1.comp_injective trivial_injective
  have hr : Summable (fun n : ℕ => ∫ t in Set.Ioi (0 : ℝ), term j C L n t) := by
    simpa only [Function.comp_def, trivial_source_packet, Complex.ofReal_re, term] using
      (Complex.hasSum_re hc.hasSum).summable
  simp_rw [trivial_source_packet]
  rw [← Complex.ofReal_tsum]
  exact congrArg Complex.ofReal (integrated_geometric_sum j hδ (by linarith) hr)

theorem smooth_exact_formula_general (hGreen : SourceGreenSmooth) (rh : RiemannHypothesis)
    (j : ℕ) {C L : ℝ} (hδ : 0 < EvenKernel.δ C L) (hsupp : 1 ≤ L - 2 * EvenKernel.δ C L) :
    smoothPopulation j C L = smoothMain j C L -
      (∑' z : PsiSmoothing.Zero, actualSmoothZeroPacket j C L z).re - smoothTrivial j C L := by
  have hg := smooth_formula_from_Green_general hGreen j hδ hsupp
  have h := hg.2
  rw [all_zero_sum rh _ hg.1] at h
  have hz : (∑' z : PsiSmoothing.Zero,
      sourcePacket (greenWeight j C L) 2 (properOfStrip z)) =
        ∑' z : PsiSmoothing.Zero, actualSmoothZeroPacket j C L z := by
    apply tsum_congr
    intro z
    exact RHOcticPush.MellinNormalize.critical_source_packet rh j hδ z
  rw [hz, complete_trivial_sum_general hGreen j hδ hsupp,
    source_pole_eq_smoothMain j hδ] at h
  have hr := congrArg Complex.re h
  simp only [Complex.ofReal_re, Complex.sub_re, Complex.add_re] at hr
  linarith

/-- Exact original predicate on its full parameter ray. The formal proof really
passes the complete zero family, finite prime-power population, source pole and
all trivial zeros through the same mollifier limit. General Green and Nicolas
are disclosed literature inputs, not newly assumed octic source targets. -/
theorem explicit_formula_general
    (hGreen : SourceGreenSmooth) (hN : NicolasContinuation.SourceNicolas119)
    (rh : RiemannHypothesis) {C L : ℝ}
    (hδ : 0 < EvenKernel.δ C L) (hsupp : 1 ≤ L - 2 * EvenKernel.δ C L) :
    Summable (EvenKernel.zeroPacket 4 C L) ∧
      EvenKernel.mangoldtPopulation 4 C L =
        EvenKernel.mainTerm 4 C L - (EvenKernel.zeroTerm 4 C L).re -
          EvenKernel.trivialCost 4 C L := by
  refine ⟨packet_summable rh hN hδ, ?_⟩
  have hleft := smoothPopulation_tends hδ
  have hzero := Complex.continuous_re.continuousAt.tendsto.comp
    (actualSmoothFullZeroLimit rh hN hδ)
  have hright := ((smoothMain_tends C L).sub hzero).sub (smoothTrivial_tends hδ (by linarith))
  have hleft' : Tendsto (fun j : ℕ => smoothPopulation j C L) atTop
      (𝓝 (EvenKernel.mainTerm 4 C L - (EvenKernel.zeroTerm 4 C L).re -
        EvenKernel.trivialCost 4 C L)) := by
    have he : (fun j : ℕ => smoothPopulation j C L) = fun j =>
        smoothMain j C L - (∑' z : PsiSmoothing.Zero, actualSmoothZeroPacket j C L z).re -
          smoothTrivial j C L := funext (fun j => smooth_exact_formula_general hGreen rh j hδ hsupp)
    rw [he]
    exact hright
  exact tendsto_nhds_unique hleft hleft'


section Powers
open Real Finset
open RHLimit.OcticPrimePowers
theorem exponent_weighted_bound_general (n : ℕ) {C L : ℝ}
    {k : ℕ} (hk : 2 ≤ k) :
    (∑ p ∈ Ioc 0 ⌊(EvenKernel.b C L) ^ (1 / (k : ℝ))⌋₊ with p.Prime,
      gateWeight n C L (p ^ k)) ≤
        (log (EvenKernel.b C L) / sqrt (EvenKernel.a C L)) / (k : ℝ) *
          ((rootPrimes (EvenKernel.a C L) (EvenKernel.b C L) k).card : ℝ) := by
  let P := (Ioc 0 ⌊(EvenKernel.b C L) ^ (1 / (k : ℝ))⌋₊).filter Nat.Prime
  let w : ℕ → ℝ := fun p => EvenKernel.kernel n
    ((log ((p ^ k : ℕ) : ℝ) - L) / EvenKernel.δ C L) *
      ((ArithmeticFunction.vonMangoldt (p ^ k) : ℝ) / sqrt ((p ^ k : ℕ) : ℝ))
  have heq : (∑ p ∈ P, gateWeight n C L (p ^ k)) =
      ∑ p ∈ rootPrimes (EvenKernel.a C L) (EvenKernel.b C L) k, w p := by
    symm
    unfold rootPrimes
    rw [sum_filter]
    rfl
  change (∑ p ∈ P, gateWeight n C L (p ^ k)) ≤ _
  rw [heq]
  have ha : 0 < EvenKernel.a C L := exp_pos _
  have hsa : 0 < sqrt (EvenKernel.a C L) := Real.sqrt_pos.mpr ha
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  calc
    _ ≤ ∑ _p ∈ rootPrimes (EvenKernel.a C L) (EvenKernel.b C L) k,
        (log (EvenKernel.b C L) / sqrt (EvenKernel.a C L)) / (k : ℝ) := by
      apply sum_le_sum
      intro p hp
      have hgate := (mem_filter.mp hp).2
      have hprime := (mem_filter.mp (mem_filter.mp hp).1).2
      have hpk : 0 < ((p ^ k : ℕ) : ℝ) := ha.trans hgate.1
      have hs : 0 < sqrt ((p ^ k : ℕ) : ℝ) := Real.sqrt_pos.mpr hpk
      have hlp : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast hprime.one_le)
      have hl := Real.log_le_log hpk hgate.2.le
      rw [Nat.cast_pow, Real.log_pow] at hl
      have hlb : log (p : ℝ) ≤ log (EvenKernel.b C L) / (k : ℝ) :=
        (le_div_iff₀ hkR).mpr (by nlinarith)
      have hroot := Real.sqrt_le_sqrt hgate.1.le
      dsimp [w]
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : k ≠ 0),
        ArithmeticFunction.vonMangoldt_apply_prime hprime]
      calc
        _ ≤ log (p : ℝ) / sqrt ((p ^ k : ℕ) : ℝ) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right
            (EvenKernel.kernel_le_one n _) (div_nonneg hlp hs.le)
        _ ≤ log (p : ℝ) / sqrt (EvenKernel.a C L) :=
          div_le_div_of_nonneg_left hlp hsa hroot
        _ ≤ (log (EvenKernel.b C L) / (k : ℝ)) / sqrt (EvenKernel.a C L) :=
          div_le_div_of_nonneg_right hlb hsa.le
        _ = _ := by ring
    _ = _ := by simp [sum_const, nsmul_eq_mul, mul_comm]

theorem root_span_bound_general {C L : ℝ} (hd : 0 ≤ EvenKernel.δ C L)
    (hL : 1 ≤ L) {k : ℕ} (hk : 2 ≤ k) :
    (EvenKernel.b C L) ^ (1 / (k : ℝ)) - (EvenKernel.a C L) ^ (1 / (k : ℝ)) ≤
      (2 * EvenKernel.δ C L / (k : ℝ)) * sqrt (EvenKernel.b C L) := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 ≤ L + EvenKernel.δ C L := by linarith
  have hre : ∀ x : ℝ, (exp x) ^ (1 / (k : ℝ)) = exp (x / (k : ℝ)) := by
    intro x
    rw [Real.rpow_def_of_pos (exp_pos _), Real.log_exp]
    congr 1
    ring
  unfold EvenKernel.a EvenKernel.b
  rw [hre, hre]
  have h := exp_sub_le ((L + EvenKernel.δ C L) / (k : ℝ))
    ((L - EvenKernel.δ C L) / (k : ℝ))
  have heq : (L + EvenKernel.δ C L) / (k : ℝ) -
      (L - EvenKernel.δ C L) / (k : ℝ) = 2 * EvenKernel.δ C L / (k : ℝ) := by ring
  rw [heq] at h
  calc
    _ ≤ (2 * EvenKernel.δ C L / (k : ℝ)) * exp ((L + EvenKernel.δ C L) / (k : ℝ)) := h
    _ ≤ (2 * EvenKernel.δ C L / (k : ℝ)) * exp ((L + EvenKernel.δ C L) / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      exact div_le_div_of_nonneg_left hpos (by norm_num) hk2
    _ = _ := by rw [Real.exp_half]

theorem primepower_cost_envelope_general (n : ℕ) {C L : ℝ}
    (hd : 0 ≤ EvenKernel.δ C L) (hL : 1 ≤ L) :
    EvenKernel.mangoldtPopulation n C L - EvenKernel.population n C L ≤
      (log (EvenKernel.b C L) / sqrt (EvenKernel.a C L)) *
        (2 * EvenKernel.δ C L * sqrt (EvenKernel.b C L) +
          log (⌊log (EvenKernel.b C L) / log 2⌋₊ : ℝ)) := by
  let a := EvenKernel.a C L
  let b := EvenKernel.b C L
  let K := ⌊log b / log 2⌋₊
  let pref := log b / sqrt a
  let S : ℕ → ℝ := fun k => ∑ p ∈ Ioc 0 ⌊b ^ (1 / (k : ℝ))⌋₊ with p.Prime,
    gateWeight n C L (p ^ k)
  have ha : 0 < a := exp_pos _
  have hab : a ≤ b := by
    dsimp [a, b, EvenKernel.a, EvenKernel.b]
    apply Real.exp_le_exp.mpr
    linarith
  have hlb : log b = L + EvenKernel.δ C L := Real.log_exp _
  have hlogb : 0 < log b := by rw [hlb]; linarith
  have hpref : 0 ≤ pref := div_nonneg hlogb.le (sqrt_nonneg _)
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlog2u : log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hK : 1 ≤ K := by
    apply (Nat.one_le_floor_iff _).mpr
    apply (one_le_div hlog2).mpr
    rw [hlb]
    linarith
  have hterm : ∀ k ∈ Icc 2 K, S k ≤
      pref * (2 * EvenKernel.δ C L * sqrt b / (k : ℝ) ^ 2 + 1 / (k : ℝ)) := by
    intro k hk
    have hk2 := (mem_Icc.mp hk).1
    have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hc := rootPrimes_card ha hab hk2
    have hr := root_span_bound_general hd hL hk2
    have hw := exponent_weighted_bound_general n (C := C) (L := L) hk2
    change S k ≤ (pref / (k : ℝ)) *
      ((rootPrimes a b k).card : ℝ) at hw
    calc
      S k ≤ (pref / (k : ℝ)) * ((rootPrimes a b k).card : ℝ) := hw
      _ ≤ (pref / (k : ℝ)) * (b ^ (1 / (k : ℝ)) - a ^ (1 / (k : ℝ)) + 1) :=
        mul_le_mul_of_nonneg_left hc (div_nonneg hpref hkR.le)
      _ ≤ (pref / (k : ℝ)) * ((2 * EvenKernel.δ C L / (k : ℝ)) * sqrt b + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hpref hkR.le)
      _ = _ := by field_simp [hkR.ne'] <;> ring
  have hsquare : (∑ k ∈ Icc 2 K, 1 / (k : ℝ) ^ 2) ≤ 1 := by
    have hh := reciprocal_square_tail_le hK
    have hz : 0 ≤ 1 / (K : ℝ) := by positivity
    linarith
  have hharm := reciprocal_tail_le_log hK
  have hsum : (∑ k ∈ Icc 2 K, S k) ≤
      pref * (2 * EvenKernel.δ C L * sqrt b + log (K : ℝ)) := by
    calc
      _ ≤ ∑ k ∈ Icc 2 K,
          pref * (2 * EvenKernel.δ C L * sqrt b / (k : ℝ) ^ 2 + 1 / (k : ℝ)) :=
        sum_le_sum hterm
      _ = pref * (2 * EvenKernel.δ C L * sqrt b *
          (∑ k ∈ Icc 2 K, 1 / (k : ℝ) ^ 2) + (∑ k ∈ Icc 2 K, 1 / (k : ℝ))) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum,
          div_eq_mul_inv, one_mul, mul_assoc]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hpref
        have hm := mul_le_mul_of_nonneg_left hsquare
          (show 0 ≤ 2 * EvenKernel.δ C L * sqrt b by positivity)
        linarith
  have hsplit : (∑ k ∈ Icc 1 K, S k) = S 1 + ∑ k ∈ Icc 2 K, S k := by
    rw [← Finset.sum_erase_add (Icc 1 K) S (left_mem_Icc.mpr hK)]
    have heq : (Icc 1 K).erase 1 = Icc 2 K := by ext k; simp; omega
    rw [heq]
    ring
  have hs1 : S 1 = EvenKernel.population n C L := by
    dsimp [S]
    norm_num only [Nat.cast_one, div_one, Real.rpow_one]
    exact exponent_one_population n C L
  have hM : EvenKernel.mangoldtPopulation n C L =
      EvenKernel.population n C L + ∑ k ∈ Icc 2 K, S k := by
    rw [mangoldt_eq_exponent_sum]
    change (∑ k ∈ Icc 1 K, S k) = _
    rw [hsplit, hs1]
  change _ ≤ pref * (2 * EvenKernel.δ C L * sqrt b + log (K : ℝ))
  linarith


end Powers

section Trivial
theorem trivial_cost_general (n : ℕ) {C L : ℝ} (hδ0 : 0 < EvenKernel.δ C L)
    (ha : 24 ≤ EvenKernel.a C L) (hb : EvenKernel.b C L ≤ 3 * EvenKernel.a C L) :
    EvenKernel.trivialCost n C L ≤ 1 / 1000 := by
  let a := EvenKernel.a C L
  let b := EvenKernel.b C L
  let f : ℝ → ℝ := fun t => EvenKernel.kernel n ((log t - L) / EvenKernel.δ C L) /
    (sqrt t * t * (t ^ 2 - 1))
  change 24 ≤ a at ha
  have ha0 : 0 < a := by linarith
  change b ≤ 3 * a at hb
  have hab : a ≤ b := by
    dsimp [a, b, EvenKernel.a, EvenKernel.b]
    apply Real.exp_le_exp.mpr
    linarith
  have hc : ContinuousOn f (uIcc a b) := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht24 : (24 : ℝ) ≤ t := ha.trans ht.1
    have ht0 : 0 < t := by linarith
    have hs0 : sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht0).ne'
    have htne : t ≠ 0 := ht0.ne'
    have hsq : t ^ 2 - 1 ≠ 0 := by nlinarith
    have hden : sqrt t * t * (t ^ 2 - 1) ≠ 0 := mul_ne_zero (mul_ne_zero hs0 htne) hsq
    dsimp [f, EvenKernel.kernel]
    fun_prop (disch := first | assumption | exact hδ0.ne')
  have hpoint : ∀ t ∈ Icc a b, f t ≤ 1 / (2300 * a) := by
    intro t ht
    have ht24 : (24 : ℝ) ≤ t := ha.trans ht.1
    have ht0 : 0 < t := by linarith
    have hst : (4 : ℝ) ≤ sqrt t := by
      have hh := Real.sqrt_le_sqrt (show (16 : ℝ) ≤ t by linarith)
      norm_num at hh
      exact hh
    have hsq : (575 : ℝ) ≤ t ^ 2 - 1 := by nlinarith
    have hm1 := mul_le_mul_of_nonneg_right hst ht0.le
    have hm2 := mul_le_mul hm1 hsq (by norm_num : (0 : ℝ) ≤ 575)
      (show 0 ≤ sqrt t * t by positivity)
    have hden : 2300 * a ≤ sqrt t * t * (t ^ 2 - 1) := by nlinarith [ht.1]
    have hden0 : 0 < sqrt t * t * (t ^ 2 - 1) :=
      (by positivity : (0 : ℝ) < 2300 * a).trans_le hden
    have hk := EvenKernel.kernel_le_one n ((log t - L) / EvenKernel.δ C L)
    dsimp [f]
    calc
      _ ≤ 1 / (sqrt t * t * (t ^ 2 - 1)) := div_le_div_of_nonneg_right hk hden0.le
      _ ≤ 1 / (2300 * a) := one_div_le_one_div_of_le (by positivity) hden
  change (∫ t in a..b, f t) ≤ 1 / 1000
  calc
    (∫ t in a..b, f t) ≤ ∫ t in a..b, (1 / (2300 * a) : ℝ) :=
      intervalIntegral.integral_mono_on hab hc.intervalIntegrable intervalIntegrable_const hpoint
    _ = (b - a) / (2300 * a) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    _ ≤ (2 * a) / (2300 * a) := div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = 1 / 1150 := by
      field_simp [ha0.ne'] <;> norm_num
    _ ≤ 1 / 1000 := by norm_num


end Trivial
#print axioms explicit_formula_general
#print axioms primepower_cost_envelope_general
#print axioms trivial_cost_general
end CubeDirect
