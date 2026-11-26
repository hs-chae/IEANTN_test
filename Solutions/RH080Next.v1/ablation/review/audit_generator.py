"""Independent type/dependency checks; never alters a submitted source file."""
TYPE_TESTS={
'fixed_width-B_named-r1':r'''
open IEANTN.CMSFunctional Filter
example (hN : BRFourierInput.v1.norm_identity) (hU : BRFourierInput.v1.uniform_population_q1)
    (rh : RiemannHypothesis) : GoodCoefficient (685251/387796) 3 := PopulationTransfer.good_three hN hU rh
example (hN : BRFourierInput.v1.norm_identity) (hU : BRFourierInput.v1.uniform_population_q1)
    (rh : RiemannHypothesis) : GoodCoefficient (465/128) 5 := PopulationTransfer.good_five hN hU rh
example (hN : BRFourierInput.v1.norm_identity) (hU : BRFourierInput.v1.uniform_population_q1)
    (rh : RiemannHypothesis) (K : ℝ) :
    ∀ᶠ x : ℝ in atTop, (685251/387796)*Real.sqrt x+K < (PopulationTransfer.openCount 3 x : ℝ) :=
  PopulationTransfer.strict_three hN hU rh K
example (hN : BRFourierInput.v1.norm_identity) (hU : BRFourierInput.v1.uniform_population_q1)
    (rh : RiemannHypothesis) (K : ℝ) :
    ∀ᶠ x : ℝ in atTop, (465/128)*Real.sqrt x+K < (PopulationTransfer.openCount 5 x : ℝ) :=
  PopulationTransfer.strict_five hN hU rh K
''',
'fixed_width-C_network-r0':r'''
open IEANTN.CMSFunctional Filter
example (hN : BRFourierInput.v1.norm_identity) (hU : BRFourierInput.v1.uniform_population_q1)
    (rh : RiemannHypothesis) : GoodCoefficient (685251/387796) 3 := RH080Transfer.width3 hN hU rh
example (hN : BRFourierInput.v1.norm_identity) (hU : BRFourierInput.v1.uniform_population_q1)
    (rh : RiemannHypothesis) : GoodCoefficient (465/128) 5 := RH080Transfer.width5 hN hU rh
example (hN : BRFourierInput.v1.norm_identity) (hU : BRFourierInput.v1.uniform_population_q1)
    (rh : RiemannHypothesis) {a : ℝ} (ha : a < 193269011844967139/109374342622661960) :
    GoodCoefficient a 3 := RH080Transfer.witness_width3 hN hU rh ha
example (hN : BRFourierInput.v1.norm_identity) (hU : BRFourierInput.v1.uniform_population_q1)
    (rh : RiemannHypothesis) {a : ℝ} (ha : a < 31036198331144443607/8533333333333333328) :
    GoodCoefficient a 5 := RH080Transfer.witness_width5 hN hU rh ha
example {a c : ℝ} : RH080Transfer.GoodOpen a c ↔ GoodCoefficient a c := RH080Transfer.goodOpen_iff
''',
'prime_index-B_named-r1':r'''
open IEANTN.CMSFunctional Filter
example (rh : RiemannHypothesis) (hC : CMSFunctionalInput.v1.population_reduction)
    (hN : BRFourierInput.v1.norm_identity) (hU : BRFourierInput.v1.uniform_population_q1)
    {β ε : ℝ} (hb : 0 ≤ β) (he : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀j : ℕ, 1 ≤ j → j ≤ ⌊β*Real.sqrt (GrowingRank.p n)⌋₊+1 →
      GrowingRank.p (n+j)-GrowingRank.p n <
        min ((20582561296/24680948495)*(1+2*β)+ε)
          (min (RHWeightedPopulation.v1.sparseLine β) (RHWeightedPopulation.v1.flatLine β)) *
        (Real.sqrt (GrowingRank.p n)*Real.log (GrowingRank.p n)) :=
  GrowingRank.fixed_cap rh hC hN hU hb he
example (rh : RiemannHypothesis) (hC : CMSFunctionalInput.v1.population_reduction)
    (hN : BRFourierInput.v1.norm_identity) (hU : BRFourierInput.v1.uniform_population_q1)
    {β η : ℝ} (hb : 0 ≤ β) (he : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀j : ℕ, 1 ≤ j → j ≤ ⌊β*Real.sqrt (GrowingRank.p n)⌋₊+1 →
      GrowingRank.p (n+j)-GrowingRank.p n <
        (GrowingRank.envelope 0 (GrowingRank.rankParameter n j)+η)*GrowingRank.scale (GrowingRank.p n) :=
  GrowingRank.adaptive rh hC hN hU hb he
example (bt : ∀x y : ℝ, 1 < x → 1 < y →
    (IEANTN.CMSFunctional.piReal (x+y) : ℝ)-(IEANTN.CMSFunctional.piReal x : ℝ) ≤ 2*y/Real.log y)
    {a c : ℝ} (h : GoodCoefficient a c) : ∃d, d<c ∧ GoodCoefficient a d := GrowingRank.can_shave bt h
example (bt : GrowingRank.BrunTitchmarsh) (rh : RiemannHypothesis)
    (hN : BRFourierInput.v1.norm_identity) (hU : BRFourierInput.v1.uniform_population_q1)
    {β : ℝ} (hb : 0 ≤ β) :
    ∃κ> (0:ℝ), ∀ᶠ n : ℕ in atTop, ∀j : ℕ, 1 ≤ j → j ≤ ⌊β*Real.sqrt (GrowingRank.p n)⌋₊+1 →
      GrowingRank.p (n+j)-GrowingRank.p n <
        (GrowingRank.BR (GrowingRank.rankParameter n j)-κ)*GrowingRank.scale (GrowingRank.p n) :=
  GrowingRank.br_uniform_saving bt rh hN hU hb
'''}
REQUIRED={
'fixed_width-B_named-r1':{
 'PopulationTransfer.good_three':['RH080Exposure.Estimates.sparse'],
 'PopulationTransfer.good_five':['RH080Exposure.Estimates.flat'],
 'PopulationTransfer.of_direct':['RH080Exposure.Estimates.gaussian','RH080Exposure.Estimates.sparse','RH080Exposure.Estimates.flat'],
 'PopulationTransfer.strict_three':['PopulationTransfer.card_loss','PopulationTransfer.eventual_margin'],
 'PopulationTransfer.prime_rank_three':['PopulationTransfer.prime_rank_iff']},
'fixed_width-C_network-r0':{
 'RH080Transfer.width3':['RH080Exposure.Estimates.sparse'],
 'RH080Transfer.width5':['RH080Exposure.Estimates.flat'],
 'RH080Transfer.witness_width3':['RH080Next.PopulationCanonical.kernel_only_sparse_witness','RH080Next.Explicit.source_BR_population_goodCoefficient'],
 'RH080Transfer.witness_width5':['RH080Next.PopulationCanonical.kernel_only_flat_witness','RH080Next.Explicit.source_BR_population_goodCoefficient'],
 'RH080Transfer.goodOpen_iff':['RH080Transfer.endpoints']},
'prime_index-B_named-r1':{
 'GrowingRank.fixed_cap':['GrowingRank.transport_floor','RH080Exposure.Estimates.gaussian','RH080Exposure.Estimates.sparse','RH080Exposure.Estimates.flat'],
 'GrowingRank.adaptive':['GrowingRank.transport_profile_margin','GrowingRank.envelope_perturb'],
 'GrowingRank.br_uniform_saving':['GrowingRank.transport_profile_margin','GrowingRank.can_shave','GrowingRank.loss_bound','GrowingRank.br_gc']}}

def audit_source(trial,module):
    import json
    requirements=REQUIRED[trial]
    pairs='['+','.join('(`'+root+',['+','.join('`'+n for n in children)+'])' for root,children in requirements.items())+']'
    return 'import '+module+'\nimport Lean\nset_option maxHeartbeats 0\nset_option maxRecDepth 2000000\nset_option pp.fullNames true\n'+TYPE_TESTS[trial]+r'''
open Lean Elab Command Meta
private def exposureProofValue? : ConstantInfo → Option Expr
  | .thmInfo info=>some info.value
  | .defnInfo info=>some info.value
  | .opaqueInfo info=>some info.value
  | _=>none
private partial def exposureProofClosure (env : Environment) (pending : List Name) (seen : NameSet := {}) : NameSet :=
  match pending with
  | []=>seen
  | n::rest=>if seen.contains n then exposureProofClosure env rest seen else
    let seen:=seen.insert n
    match env.find? n with
    | some info=>match exposureProofValue? info with
      | some body=>exposureProofClosure env (body.getUsedConstants.toList++rest) seen
      | none=>exposureProofClosure env rest seen
    | none=>exposureProofClosure env rest seen
private def applicationName (n : Name) : Bool :=
  ["RH080","RHOnePrime","RHWeightedPopulation","RHAsymptoticGaussian","IEANTN","AffineFourierPrograms","GrowingRank","PopulationTransfer","BRFourierInput","CMSFunctionalInput"].any (fun stem=>n.toString.startsWith stem)
run_cmd do
  let env←getEnv
  let moduleName : Name:=`MODULE
  let constants:=env.constants.toList.filter (fun pair=>match env.getModuleIdxFor? pair.1 with
    | some i=>env.header.moduleNames[i]! == moduleName
    | none=>false)
  let allowed:=#[`propext,`Classical.choice,`Quot.sound]
  let mut rows : Array Json:=#[]
  for (name,info) in constants do
    if let .axiomInfo _ := info then throwError "Submitted axiom {name}"
    if let .thmInfo _ := info then
      let axioms←collectAxioms name
      unless axioms.all allowed.contains do throwError "Nonstandard theorem axiom {name}: {axioms}"
      let dependencies:=exposureProofClosure env [name]
      let rendered←liftTermElabM <| Meta.ppExpr info.type
      let direct:=match exposureProofValue? info with | some value=>value.getUsedConstants.toList.map toString | none=>[]
      rows:=rows.push (Json.mkObj [("declaration",toJson name.toString),("type",toJson rendered.pretty),
        ("axioms",toJson (axioms.map toString)),("direct_dependencies",toJson direct),
        ("application_closure",toJson (dependencies.toList.filter applicationName |>.map toString)),
        ("closure_count",toJson dependencies.toList.length)])
  let required : List (Name×List Name):=REQUIREMENTS
  for (root,children) in required do
    let some (.thmInfo _) := env.find? root | throwError "Missing expected theorem {root}"
    let dependencies:=exposureProofClosure env [root]
    for child in children do
      unless dependencies.contains child do throwError "Missing real proof dependency {root} -> {child}"
  unless rows.size>0 do throwError "Empty submitted theorem universe"
  liftIO <| IO.FS.writeFile "/work/submission/THEOREMS.json" (Json.compress (toJson rows))
  logInfo m!"INDEPENDENT_EXPOSURE_AUDIT_PASS module={moduleName} theorem_count={rows.size} standard3 expected-types actual-proof-dependencies"
'''.replace('MODULE',module).replace('REQUIREMENTS',pairs)
