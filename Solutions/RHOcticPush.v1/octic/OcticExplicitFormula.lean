import OcticGreenSource
import OcticZeroDecomposition
import OcticTrivialSeries
import OcticTrivialNormalize
import OcticPoleNormalization
import OcticTwoInputs

/-! The original octic explicit formula is derived from an independently stated
general smooth Mellin explicit formula and the existing Nicolas source. These
two genuine literature premises remain explicit; neither is asserted as an
axiom or relabelled as a pure-RH Lean theorem. The actual sharp zero estimate
is separate and remains open. No new numerical leaf enters this chain. -/
namespace RHOcticPush.ExplicitFormula
open Real Complex Set Filter MeasureTheory
open scoped Topology
open RHOcticPush.GreenSource RHOcticPush.PhysicalWeight RHOcticPush.PopulationLimit
open RHOcticPush.Mollifier RHOcticPush.FourierMollifier RHOcticPush.IntegralLimits
open RHOcticPush.ZeroDecomposition RHOcticPush.TrivialSeries RHOcticPush.TrivialNormalize
open RHOcticPush.PoleNormalization RHOcticPush.Convergence
set_option maxHeartbeats 0

lemma parameter_conditions {C L : ℝ} (hC : C ∈ Set.Icc (103 / 100 : ℝ) 16)
    (hL : 24 ≤ L) : 0 < EvenKernel.δ C L ∧ 0 < L - 2 * EvenKernel.δ C L := by
  have hd : 0 < EvenKernel.D C L := by unfold EvenKernel.D; nlinarith [hC.1]
  have hδ : 0 < EvenKernel.δ C L := mul_pos hd (Real.exp_pos _)
  have hs := RHLimit.OcticGeometry.delta_small hC hL
  exact ⟨hδ, by linarith⟩

lemma trivial_injective : Function.Injective trivialZero := by
  intro n m h
  apply Sum.inr_injective
  apply encode_injective
  exact h

theorem complete_trivial_sum (hGreen : SourceGreenSmooth) (j : ℕ) {C L : ℝ}
    (hC : C ∈ Set.Icc (103 / 100 : ℝ) 16) (hL : 24 ≤ L) :
    (∑' n : ℕ, sourcePacket (greenWeight j C L) 2 (trivialZero n)) =
      (smoothTrivial j C L : ℂ) := by
  have hc := (smooth_formula_from_Green hGreen j hC hL).1.comp_injective trivial_injective
  have hr : Summable (fun n : ℕ => ∫ t in Set.Ioi (0 : ℝ), term j C L n t) := by
    simpa only [Function.comp_def, trivial_source_packet, Complex.ofReal_re, term] using
      (Complex.hasSum_re hc.hasSum).summable
  have hp := parameter_conditions hC hL
  simp_rw [trivial_source_packet]
  rw [← Complex.ofReal_tsum]
  exact congrArg Complex.ofReal (integrated_geometric_sum j hp.1 hp.2 hr)

theorem smooth_exact_formula (hGreen : SourceGreenSmooth) (rh : RiemannHypothesis)
    (j : ℕ) {C L : ℝ} (hC : C ∈ Set.Icc (103 / 100 : ℝ) 16) (hL : 24 ≤ L) :
    smoothPopulation j C L = smoothMain j C L -
      (∑' z : PsiSmoothing.Zero, actualSmoothZeroPacket j C L z).re - smoothTrivial j C L := by
  have hg := smooth_formula_from_Green hGreen j hC hL
  have h := hg.2
  have hp := parameter_conditions hC hL
  rw [all_zero_sum rh _ hg.1] at h
  have hz : (∑' z : PsiSmoothing.Zero,
      sourcePacket (greenWeight j C L) 2 (properOfStrip z)) =
        ∑' z : PsiSmoothing.Zero, actualSmoothZeroPacket j C L z := by
    apply tsum_congr
    intro z
    exact RHOcticPush.MellinNormalize.critical_source_packet rh j hp.1 z
  rw [hz, complete_trivial_sum hGreen j hC hL,
    source_pole_eq_smoothMain j hp.1] at h
  have hr := congrArg Complex.re h
  simp only [Complex.ofReal_re, Complex.sub_re, Complex.add_re] at hr
  linarith

/-- Exact original predicate on its full parameter ray. The formal proof really
passes the complete zero family, finite prime-power population, source pole and
all trivial zeros through the same mollifier limit. General Green and Nicolas
are disclosed literature inputs, not newly assumed octic source targets. -/
theorem explicit_formula_from_general_sources
    (hGreen : SourceGreenSmooth) (hN : NicolasContinuation.SourceNicolas119)
    {C : ℝ} (hC : C ∈ Set.Icc (103 / 100 : ℝ) 16) : EvenKernel.ExplicitFormula 4 C := by
  intro rh L hL
  have hp := parameter_conditions hC hL
  refine ⟨packet_summable rh hN hp.1, ?_⟩
  have hleft := smoothPopulation_tends hp.1
  have hzero := Complex.continuous_re.continuousAt.tendsto.comp
    (actualSmoothFullZeroLimit rh hN hp.1)
  have hright := ((smoothMain_tends C L).sub hzero).sub (smoothTrivial_tends hp.1 hp.2)
  have hleft' : Tendsto (fun j : ℕ => smoothPopulation j C L) atTop
      (𝓝 (EvenKernel.mainTerm 4 C L - (EvenKernel.zeroTerm 4 C L).re -
        EvenKernel.trivialCost 4 C L)) := by
    have he : (fun j : ℕ => smoothPopulation j C L) = fun j =>
        smoothMain j C L - (∑' z : PsiSmoothing.Zero, actualSmoothZeroPacket j C L z).re -
          smoothTrivial j C L := funext (fun j => smooth_exact_formula hGreen rh j hC hL)
    rw [he]
    exact hright
  exact tendsto_nhds_unique hleft hleft'

theorem prime_count_215_one_open_analytic_input
    (hGreen : SourceGreenSmooth) (hN : NicolasContinuation.SourceNicolas119)
    (rh : RiemannHypothesis)
    (hz : EvenKernel.ZeroEstimate 4 (43 / 20) (911 / 500) (3 / 2) (3 / 125)) :
    ∀ u : ℝ, Real.exp 24 ≤ u →
      (9001 / 9000 + (29 / 5) / Real.log u) * Real.sqrt u <
        QuarticWindow.primeCounting (u + 43 / 20 * Real.sqrt u * Real.log u) -
          QuarticWindow.primeCounting u :=
  RHLimit.OcticTwoInputs.prime_count_215 rh
    (explicit_formula_from_general_sources hGreen hN (by norm_num)) hz

#print axioms complete_trivial_sum
#print axioms smooth_exact_formula
#print axioms explicit_formula_from_general_sources
#print axioms prime_count_215_one_open_analytic_input
#check @explicit_formula_from_general_sources
end RHOcticPush.ExplicitFormula
