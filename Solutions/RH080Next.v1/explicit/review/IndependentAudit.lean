import AnalyticFlat64Population
import AnalyticFlatFamilyPopulation
import IEANTN.Nodes.BRFourierInput.v1.Conclusions
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
noncomputable section
open Lean Elab Command Real MeasureTheory Filter
open scoped FourierTransform
open RH080Next.Explicit

example : SourceBRFourierNormFive = BRFourierInput.v1.norm_identity := rfl
example : SourceBRUniformPopulationQ1 = BRFourierInput.v1.uniform_population_q1 := rfl
example (hN:SourceBRFourierNormFive) (hU:SourceBRUniformPopulationQ1) (hR:RiemannHypothesis)
 (a:ℝ) (ha:0≤a) :
  0 < (21/10:ℝ)+(128/127)*a ∧ ∃d:ℝ, 0<d ∧ ∀ᶠ x:ℝ in atTop,
    a+d ≤ ((IEANTN.CMSFunctional.piReal (x+((21/10:ℝ)+(128/127)*a)*sqrt x*Real.log x)-
      IEANTN.CMSFunctional.piReal x:ℕ):ℝ)/sqrt x :=
  RH080Next.AnalyticFlat64.actual_population_curve hN hU hR a ha
example (hN:SourceBRFourierNormFive) (hU:SourceBRUniformPopulationQ1) (hR:RiemannHypothesis)
 (m:ℕ) (hm:0<m) (a e:ℝ) (ha:0≤a) (he:0<e) :
  IEANTN.CMSFunctional.GoodCoefficient a
    ((2*(m:ℝ)/(2*(m:ℝ)-1))*(a+(1+Real.log (4*(m:ℝ)-2))/Real.pi)+e) :=
  RH080Next.AnalyticFlatFamily.actual_population_curve hN hU hR m hm a e ha he
example (hN:SourceBRFourierNormFive) (hU:SourceBRUniformPopulationQ1) (hR:RiemannHypothesis)
 (m:ℕ) (hm:0<m) (a:ℝ) (ha:0≤a) :
  (IEANTN.CMSFunctional.goodCoefficients a).Nonempty ∧
   sInf (IEANTN.CMSFunctional.goodCoefficients a) ≤
    (2*(m:ℝ)/(2*(m:ℝ)-1))*(a+(1+Real.log (4*(m:ℝ)-2))/Real.pi) :=
  RH080Next.AnalyticFlatFamily.actual_population_infimum hN hU hR m hm a ha
example (m:ℕ) (hm:0<m) :
  𝓕 (fun u:ℝ => (inverseCosine (affineSpectrum (RH080Next.AnalyticFlatFamily.nodes m) m) u:ℂ)) =
  (fun v:ℝ => (affineSpectrum (RH080Next.AnalyticFlatFamily.nodes m) m v:ℂ)) :=
  (RH080Next.AnalyticFlatFamily.actual_eligible m hm).fourier

private def val : ConstantInfo→Option Expr
| .thmInfo i=>some i.value
| .defnInfo i=>some i.value
| .opaqueInfo i=>some i.value
| _=>none
private partial def proofTypeClosure (env : Environment) (todo : List Name) (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then proofTypeClosure env rest seen else
      let seen := seen.insert n
      match env.find? n with
      | none => proofTypeClosure env rest seen
      | some info =>
        let deps := info.type.getUsedConstants.toList
        match val info with
        | some body => proofTypeClosure env (body.getUsedConstants.toList ++ deps ++ rest) seen
        | none => proofTypeClosure env (deps ++ rest) seen

#check RH080Next.AnalyticFlat64.poly

#check RH080Next.AnalyticFlat64.continuous_poly

#check RH080Next.AnalyticFlat64.poly_abs_le

#check RH080Next.AnalyticFlat64.sin_mul_poly

#check RH080Next.AnalyticFlat64.sin_positive_half

#check RH080Next.AnalyticFlat64.poly_abs_le_csc

#check RH080Next.AnalyticFlat64.poly_reflect

#check RH080Next.AnalyticFlat64.periodic_norm_eq_twice_half

#check RH080Next.AnalyticFlat64.cut

#check RH080Next.AnalyticFlat64.cscPrimitive

#check RH080Next.AnalyticFlat64.cut_pos

#check RH080Next.AnalyticFlat64.cut_le_half

#check RH080Next.AnalyticFlat64.half_angle_pos

#check RH080Next.AnalyticFlat64.cscPrimitive_hasDerivAt

#check RH080Next.AnalyticFlat64.integral_csc_cut_half

#check RH080Next.AnalyticFlat64.periodic_norm_bound

#check RH080Next.AnalyticFlat64.nodes

#check RH080Next.AnalyticFlat64.nodes_length

#check RH080Next.AnalyticFlat64.node_eq

#check RH080Next.AnalyticFlat64.terminal_zero

#check RH080Next.AnalyticFlat64.sum_node_mul

#check RH080Next.AnalyticFlat64.polynomial_identity

#check RH080Next.AnalyticFlat64.normalization

#check RH080Next.AnalyticFlat64.actual_F0

#check RH080Next.AnalyticFlat64.window_bound

#check RH080Next.AnalyticFlat64.attained_maximum

#check RH080Next.AnalyticFlat64.leakage_zero

#check RH080Next.AnalyticFlat64.denominator

#check RH080Next.AnalyticFlat64.width

#check RH080Next.AnalyticFlat64.actual_eligible

#check RH080Next.AnalyticFlat64.analytic_intercept_strict

#check RH080Next.AnalyticFlat64.actual_norm_strict

#check RH080Next.AnalyticFlat64.actual_population_curve

#check RH080Next.AnalyticFlat64.actual_population_eventual

#check RH080Next.AnalyticFlat64.width_forty

#check RH080Next.AnalyticFlat64.actual_population_forty

#check RH080Next.AnalyticFlat64.improves_previous_flat

#check RH080Next.AnalyticFlat64.forty_improves_previous_flat

#check RH080Next.AnalyticFlatFamily.order

#check RH080Next.AnalyticFlatFamily.poly

#check RH080Next.AnalyticFlatFamily.order_ge_one

#check RH080Next.AnalyticFlatFamily.continuous_poly

#check RH080Next.AnalyticFlatFamily.poly_abs_le

#check RH080Next.AnalyticFlatFamily.sin_mul_poly

#check RH080Next.AnalyticFlatFamily.poly_abs_le_csc

#check RH080Next.AnalyticFlatFamily.poly_reflect

#check RH080Next.AnalyticFlatFamily.periodic_norm_eq_twice_half

#check RH080Next.AnalyticFlatFamily.cut

#check RH080Next.AnalyticFlatFamily.cut_pos

#check RH080Next.AnalyticFlatFamily.cut_le_half

#check RH080Next.AnalyticFlatFamily.integral_csc_cut_half

#check RH080Next.AnalyticFlatFamily.periodic_norm_bound

#check RH080Next.AnalyticFlatFamily.nodes

#check RH080Next.AnalyticFlatFamily.nodes_length

#check RH080Next.AnalyticFlatFamily.node_eq

#check RH080Next.AnalyticFlatFamily.terminal_zero

#check RH080Next.AnalyticFlatFamily.sum_node_mul

#check RH080Next.AnalyticFlatFamily.polynomial_identity

#check RH080Next.AnalyticFlatFamily.normalization

#check RH080Next.AnalyticFlatFamily.actual_F0

#check RH080Next.AnalyticFlatFamily.window_bound

#check RH080Next.AnalyticFlatFamily.attained_maximum

#check RH080Next.AnalyticFlatFamily.leakage_zero

#check RH080Next.AnalyticFlatFamily.denominator

#check RH080Next.AnalyticFlatFamily.actual_eligible

#check RH080Next.AnalyticFlatFamily.normCap

#check RH080Next.AnalyticFlatFamily.width

#check RH080Next.AnalyticFlatFamily.actual_norm_le

#check RH080Next.AnalyticFlatFamily.width_positive

#check RH080Next.AnalyticFlatFamily.width_mass_identity

#check RH080Next.AnalyticFlatFamily.actual_population_curve

#check RH080Next.AnalyticFlatFamily.actual_population_infimum

#check RH080Next.AnalyticFlat64.log254_lt

run_cmd do
 let env←getEnv
 let allowed:=#[`propext,`Classical.choice,`Quot.sound]
 let roots:=#[`RH080Next.AnalyticFlat64.continuous_poly,
  `RH080Next.AnalyticFlat64.poly_abs_le,
  `RH080Next.AnalyticFlat64.sin_mul_poly,
  `RH080Next.AnalyticFlat64.sin_positive_half,
  `RH080Next.AnalyticFlat64.poly_abs_le_csc,
  `RH080Next.AnalyticFlat64.poly_reflect,
  `RH080Next.AnalyticFlat64.periodic_norm_eq_twice_half,
  `RH080Next.AnalyticFlat64.cut_pos,
  `RH080Next.AnalyticFlat64.cut_le_half,
  `RH080Next.AnalyticFlat64.half_angle_pos,
  `RH080Next.AnalyticFlat64.cscPrimitive_hasDerivAt,
  `RH080Next.AnalyticFlat64.integral_csc_cut_half,
  `RH080Next.AnalyticFlat64.periodic_norm_bound,
  `RH080Next.AnalyticFlat64.nodes_length,
  `RH080Next.AnalyticFlat64.node_eq,
  `RH080Next.AnalyticFlat64.terminal_zero,
  `RH080Next.AnalyticFlat64.sum_node_mul,
  `RH080Next.AnalyticFlat64.polynomial_identity,
  `RH080Next.AnalyticFlat64.normalization,
  `RH080Next.AnalyticFlat64.actual_F0,
  `RH080Next.AnalyticFlat64.window_bound,
  `RH080Next.AnalyticFlat64.attained_maximum,
  `RH080Next.AnalyticFlat64.leakage_zero,
  `RH080Next.AnalyticFlat64.denominator,
  `RH080Next.AnalyticFlat64.actual_eligible,
  `RH080Next.AnalyticFlat64.analytic_intercept_strict,
  `RH080Next.AnalyticFlat64.actual_norm_strict,
  `RH080Next.AnalyticFlat64.actual_population_curve,
  `RH080Next.AnalyticFlat64.actual_population_eventual,
  `RH080Next.AnalyticFlat64.width_forty,
  `RH080Next.AnalyticFlat64.actual_population_forty,
  `RH080Next.AnalyticFlat64.improves_previous_flat,
  `RH080Next.AnalyticFlat64.forty_improves_previous_flat,
  `RH080Next.AnalyticFlatFamily.order_ge_one,
  `RH080Next.AnalyticFlatFamily.continuous_poly,
  `RH080Next.AnalyticFlatFamily.poly_abs_le,
  `RH080Next.AnalyticFlatFamily.sin_mul_poly,
  `RH080Next.AnalyticFlatFamily.poly_abs_le_csc,
  `RH080Next.AnalyticFlatFamily.poly_reflect,
  `RH080Next.AnalyticFlatFamily.periodic_norm_eq_twice_half,
  `RH080Next.AnalyticFlatFamily.cut_pos,
  `RH080Next.AnalyticFlatFamily.cut_le_half,
  `RH080Next.AnalyticFlatFamily.integral_csc_cut_half,
  `RH080Next.AnalyticFlatFamily.periodic_norm_bound,
  `RH080Next.AnalyticFlatFamily.nodes_length,
  `RH080Next.AnalyticFlatFamily.node_eq,
  `RH080Next.AnalyticFlatFamily.terminal_zero,
  `RH080Next.AnalyticFlatFamily.sum_node_mul,
  `RH080Next.AnalyticFlatFamily.polynomial_identity,
  `RH080Next.AnalyticFlatFamily.normalization,
  `RH080Next.AnalyticFlatFamily.actual_F0,
  `RH080Next.AnalyticFlatFamily.window_bound,
  `RH080Next.AnalyticFlatFamily.attained_maximum,
  `RH080Next.AnalyticFlatFamily.leakage_zero,
  `RH080Next.AnalyticFlatFamily.denominator,
  `RH080Next.AnalyticFlatFamily.actual_eligible,
  `RH080Next.AnalyticFlatFamily.actual_norm_le,
  `RH080Next.AnalyticFlatFamily.width_positive,
  `RH080Next.AnalyticFlatFamily.width_mass_identity,
  `RH080Next.AnalyticFlatFamily.actual_population_curve,
  `RH080Next.AnalyticFlatFamily.actual_population_infimum,
  `RH080Next.AnalyticFlat64.log254_lt]
 for root in roots do
  let some (.thmInfo info):=env.find? root | throwError "missing theorem {root}"
  let ax←collectAxioms root
  unless ax.all allowed.contains do throwError "nonstandard axiom {root}: {ax}"
  logInfo m!"INDEPENDENT_AXIOMS {root}: {ax}"
 for root in #[`RH080Next.AnalyticFlat64.actual_population_curve,`RH080Next.AnalyticFlatFamily.actual_population_infimum] do
  let used:=proofTypeClosure env [root]
  for required in #[`RH080Next.Explicit.brQ1Error_tendsto_zero,
    `RH080Next.Explicit.source_BR_population_goodCoefficient,
    `IEANTN.CMSFunctional.piReal,`Nat.primeCounting,
    `RH080Next.AnalyticFlat64.cscPrimitive_hasDerivAt] do
   unless used.contains required do throwError "actual source/count/analytic consumer absent {root}: {required}"
  for forbidden in #[`IEANTN.CMSFunctional.SourceCMSPopulation,`IEANTN.CMSFunctional.SourceCMSFunctional,
    `sorryAx,`Lean.ofReduceBool,`Lean.trustCompiler] do
   if used.contains forbidden then throwError "forbidden dependency {root}: {forbidden}"
  for n in used.toList do
   if n.toString.startsWith "Lean.ofReduceBool" || n.toString.startsWith "Lean.trustCompiler" then
    throwError "native dependency {root}: {n}"
  logInfo m!"INDEPENDENT_CLOSURE {root}: {used.toList.length}"
 for root in #[`RH080Next.AnalyticFlat64.actual_eligible,`RH080Next.AnalyticFlatFamily.actual_eligible] do
  let used:=proofTypeClosure env [root]
  unless used.contains `RH080Next.Explicit.fourier_affine_inverse_eq_window do throwError "no actual Fourier inversion {root}"
 logInfo m!"INDEPENDENT_REVIEW_PASS theorem_count={roots.size} canonical_interfaces_rfl actual_pi no_extra_CMS_source no_native Std3"
