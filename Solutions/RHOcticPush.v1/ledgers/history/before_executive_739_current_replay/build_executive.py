#!/usr/bin/env python3
"""Leading-claim index, not a replacement for the complete provenance ledgers.

Each identity is file/declaration/physical-LF-line; no short-name census joins.
This records proof status honestly and never accepts a numerical computation.
"""
import csv
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
CAMPAIGN = HERE.parent
REPO = CAMPAIGN.parents[1]
PREFIX = 'Solutions/RHOcticPush.v1/'
research = json.loads((HERE / 'RESEARCH_LEDGER.json').read_text())
entries = {r['id']: r for r in research['entries']}
ram = json.loads((CAMPAIGN / 'ramanujan/RESULTS.json').read_text())['source_inputs']
octic = ['RiemannHypothesis', 'SourceGreenSmooth', 'SourceNicolas119',
         'SourceBPTOffOrdinate']
gm = ['SharedRH.hypothesis', 'GM_Q_Theorem1_1', 'Buthe.v1.theorem_2_psi',
      'Buthe.v1.theorem_2_li_minus_riemann_pi']
box = ['RiemannHypothesis', 'IntegratedPerron.v1.formula',
       'Nicolas.v1.spectral_bound', 'BPTOffOrdinate.v1.bound']
spectral = ['RiemannHypothesis', 'NicolasContinuation.SourceNicolas119',
            'SourceIntegratedPsi (normalization from IntegratedPerron.v1.formula proved)']


def identity(path, declaration):
    p = REPO / path
    data = p.read_bytes()
    pattern = re.compile(r'^(?:noncomputable\s+)?(?:theorem|lemma|def)\s+' +
                         re.escape(declaration) + r'(?:\s|\{|\(|:|$)')
    lines = [i for i, s in enumerate(data.decode().split('\n'), 1) if pattern.match(s)]
    if len(lines) != 1:
        raise ValueError(f'Ambiguous or absent written identity: {path}/{declaration}')
    return dict(file=path, declaration=declaration, line=lines[0],
                sha256=hashlib.sha256(data).hexdigest())


rows = []


def add(id, family, path, declaration, **details):
    entry = entries[family]
    row = dict(id=id, partition='this_campaign_coordinator_synthesis_post_lock',
               status=entry['status'], source_first_PV=False,
               identity=identity(PREFIX + path, declaration), **details)
    rows.append(row)


add('OCTIC-215', 'OCTIC-215', 'octic/OcticFinalSourceConsumer.lean',
    'prime_count_215',
    old='Exact fixed2.15 target conditional on two octic analytic premises',
    new='Same target, both analytic premises proved; strict-endpoint and ordinary-pi variants',
    domain='Every real u>=exp24; prime-power budgets .0155 fixed/.058 family unchanged',
    premises=octic, tier='B+D', same_premises='Old octic-specific targets discharged from genuine general literature inputs',
    method='Smooth explicit-formula limit, full BPT tail and exact kernel-certified actual moments',
    certificate='moments/endpoint/SOURCE_ROOTS.json; M0<=5.72,M1<=4.6;7301 endpoints/7300cells/115blocks',
    consumers='PrimeInterval/PrimeQuantile/RichPrimeInterval/GoldbachCount',
    literature='CMS one-prime .88 is a different objective; CPdL alpha=1 asymptotic coefficient<2.5074',
    limitation='RH plus three explicit literature propositions, not Mathlib-only RH or a global record')
add('OCTIC-STRONG', 'OCTIC-215', 'octic/OcticOptimizedCertified.lean', 'strict_count_2149_uniform',
    old='2.15 width, leading9001/9000+5.8/logu',
    new='Same2.15:180173/180000+5.8/logu;2.149:180013/180000+4.2/logu;2.14891875:1+4.2/logu; family8C/9-.91015+4.2/logu',
    domain='All real u>=exp24,1.03<=C<=16', premises=octic, tier='B+D', same_premises=True,
    method='Stronger moment caps and exact full-ray scalar budget',
    certificate='OcticStrongMomentCaps:M0<=3574/625,M1<=572/125; same frozen endpoints',
    consumers='Actual strict prime counts, ordinary pi and sorted Goldbach triples',
    literature='Lee2403.11814v4 can beat the large-C region; Lee QJM2023 later-onset family constrains asymptotic record claims',
    limitation='1+4.2/logu alone does not imply liminf>1; no optimality/global-best-known claim')
add('PNT-CLEAN04', 'PNT-CLEAN04', 'spectral-076/corollary/BoxClassicalCorollary.lean',
    'actual_box_pi_ray_canonical',
    old='Earlier clean sqrtx*(logx/(8pi)-1/3) campaign corollary',
    new='Actual |pi(x)-Li2(x)|<sqrtx*(logx/(8pi)-2/5); exact clean RHS gain sqrtx/15',
    domain='Every real x>=exp100, inclusive onset', premises=box, tier='B+D',
    same_premises=False, method='Whole-function scalar comparison retaining all prime-power and Li2-offset costs',
    certificate='Two frozen source files; independent12written-root Std3 audit; fresh2above712PASS31.93s',
    consumers='Actual ordinary pi; exact canonical four-source wrapper',
    literature='The original full bound is stronger than either clean display; entire strongest published families retained in report',
    limitation='A clearer stronger displayed corollary, not a new global frontier or optimality claim; old and new source packages differ')
add('PNT-FEEDBACK-FULL', 'PNT-FEEDBACK', 'spectral-076/feedback/FeedbackPi.lean',
    'actual_box_pi',
    old='Ucomp(L)=exp(L/2)fBox(L)/L+P(L)+Qold(L)+2, allL>=35',
    new='Samecompletefunction withQeff=Qold below70 andmin(Qold,Jupper(L/2)/2+exp(L/4)/2+exp(L/3)log(L/log2)) above70; Ucomp-Ufeedback>1.67exp(L/2)/L onL>=100',
    domain='Everyrealx>=exp35, inclusive; raw lower-scale branch L>=70; strict wholefunction gain L>=100',
    premises=box, tier='B+D', same_premises=True,
    method='Acyclicpi<=J first, then entirelower-scale Jupper bound into actualsquareterm; allhigherpowers/floorheight/P/Li2offsetretained',
    certificate='Fourfrozenfiles39directStd3roots; sourcefresh718 andcanonical734/90bodyroots/136ownedStd3/11exacttypes',
    consumers='RHPrimeCounting.v6 actualJupper/primepowerfeedback/ordinarytransfer/Boxpi/interval; sourcebodyvaluesaudited',
    literature='ExactwholeLeeNosaldisplayedpsi functions compared separately; broaderheight/finitefamiliespreventglobalrecordclaim',
    limitation='Samepremises scopedactualfourinputBoxbranch; genericpointpsi transferneedsBPT forlower-scaleBox; noPV/optimalityclaim')
add('PNT-CLEAN042', 'PNT-FEEDBACK', 'spectral-076/feedback/FeedbackCorollary.lean',
    'actual_box_pi_clean_canonical',
    old='Intermediate sqrtx*(logx/(8pi)-2/5) atx>=exp100 withsamefourinputs',
    new='Actual |pi(x)-Li2(x)|<sqrtx*(logx/(8pi)-21/50); exact RHSgain sqrtx/50',
    domain='Everyrealx>=exp100, inclusiveonset', premises=box, tier='B+D', same_premises=True,
    method='All-real scalarbudgetfrom the stronger completefeedbackfunction, retainingfullprimepowers andoffset',
    certificate='Kernelbounds log100>=4.6,pi<=22/7; wholefeedbackfunction at100<3.5537exp50; clean coefficient3.55887..3.55888',
    consumers='Actualordinarypi/offsetLi2 canonicalcleanwrapper',
    literature='A stronger displayedcorollary; fullfeedbackfunctionstillstronger andglobalbestknownnotestablished',
    limitation='Earlier1/3 sourcepackage differs; do not claim unchangedpremises for that oldercomparison')
add('RAM-607', 'RAM-607', 'ramanujan/RamStrongOverlay.lean', 'actual_strong_frontier607',
    old='620b margin.001; retained640b full nonlinear profile',
    new='607b:.0001;610b:.001;619b:.01;620b:.0125;640b:exact inherited nonlinear finalMargin',
    domain='Every real x at/above each threshold', premises=ram, tier='B+D', same_premises=True,
    method='Signed common-prefix cancellation and degree20 remainder3/8000 versus1/1000',
    certificate='ramanujan/SOURCE_ROOTS.json; source-linked fixed-point logs and kernel all-real slabs',
    consumers='Actual RamanujanGap and strict ordinary-pi inequality',
    literature='Dudek-Platt already locates last integer counterexample38358837682 under RH',
    limitation='Not a published onset record; no newly completed whole-program PV claimed')
add('RAM-606-SPECTRAL', 'RAM-606-SPECTRAL',
    'ramanujan/signed-spectral/SpectralRamFrontier.lean', 'actual_frontier606',
    old='Old9-input607b:.0001,610b:.001 and stronger later profile',
    new='Everyx>=606b:RG>=.001; exact full oldstrongprofile retainedabove610b',
    domain='Every real x>=606000000000; five CLOSED kernel-checked cells join606b..610b',
    premises=ram+spectral[1:], tier='B+D; independent44review and sourcefresh723 canonicalproof/type/bodygatepassed',
    same_premises=False, method='Use actual full signed P(L) at both heights; retain nonlinear deficit terms and inherited profile',
    certificate='signed-spectral/PROFILE_SOURCE_FREEZE.json;4sources/44writtenIDs/30Std3roots; exact generated five cells',
    consumers='Actual strict pi inequality; new typed compensation_profile to local gap consumer',
    literature='Dudek-Platt last-counterexample38358837682; not a published onset record',
    limitation='Global11-inputunion versusold9; local6-sourcepackage is not a subsetofold7; no fullfiniteprefix claim')
add('GM-WHOLE', 'GM-WHOLE', 'spectral/GMComparison.lean', 'evolved_strict',
    old='14.44+.1386sqrtx/[L(L-6)]',
    new='min(old,15.51+.1386sqrtx/[L(L-5)]); old-new>.5 forx>=exp24',
    domain='Original function x>=exp12; new branch x>=exp15; strict gain entirex>=exp24',
    premises=gm, tier='B', same_premises=True,
    method='Parametric antiderivative and explicit paid anchor, minimum retains original range',
    certificate='Exact kernel inequalities; no unverified numerical premise',
    consumers='Actual J, ordinary pi, signed error pair and Ramanujan',
    literature='Grenie-Molteni Theorem1.1; full Lee-Nosal family retained as comparison constraint',
    limitation='Strict component gain may be hidden by another active minimum')
add('NICOLAS-JOINT', 'NICOLAS-JOINT', 'spectral/NicolasFourPoint.lean', 'actual_product_four',
    old='Independent four-harmonic cost10beta',
    new='Joint cost2.5beta, gain7.5beta; actual block has an improved member',
    domain='x>599; heights x,x^2,x^3,x^4',
    premises=['RiemannHypothesis','SourceNicolas119','SourceNicolas219'], tier='B',
    same_premises=True, method='Positive actual zero weights and exact squared Fejer polynomial',
    certificate='Exact all-zero summability and polynomial identity',
    consumers='Actual logarithmic Euler-product ratios and existential finite-block theorem',
    literature='Nicolas Eq1.19/Eq2.19 whole functions; old1.876 is not a numerical record',
    limitation='Joint/existential improvement, not a better coefficient at every individual height')
add('BOX-FULL', 'BOX-MELLIN', 'integration/additive/BoxFullNetwork.lean', 'fully_derived_box_network',
    old='Four original Box analytic predicates assumed',
    new='All four constructed internally; J1<.70871 versus.70875, fullpsi improvement1/(25000pi)',
    domain='All real L>=35; actual signed Box packets; each output retains its eligibility guards',
    premises=box, tier='B+D', same_premises='Target predicates removed; explicit general Perron/Nicolas/BPT remain',
    method='Fourier/Mellin/Gamma/Stieltjes identities, actual integrated Perron transport, complete signed-zero bound',
    certificate='Unconditional actual two moments; zero cold40/660 and fullBox33/693 receipts',
    consumers='psi,LCM log growth,new pi/interval; primorial additionally uses Buthe2016.v1.theorem_2_psi',
    literature='Hildebrand Th5.18/(5.32)p166,(5.34)p167; BPT Cor1/Lem2; exact Nicolas',
    limitation='Old GM-dependent pi consumer retained separately; new four-input spectral pi consumer indexed below')
add('SPECTRAL-076', 'SPECTRAL-076', 'spectral-076/SpectralFinal.lean', 'actual_compensation_profile',
    old='Actual.076 target open; unsigned GM transport pays at least.0924sqrtx/L^2',
    new='|D(x)|<=579/125+.047(1+4/(L-8))sqrtx/L^2 <.076sqrtx/L^2; <.055sqrtx/L^2 onL>=35',
    domain='Every real x>=exp24; separate stronger coefficient onx>=exp35',
    premises=spectral, tier='B+D', same_premises='Different standalone source package; explicit in theorem',
    method='Keep complex phase through weighted integration by parts; rho^-2 mass paid once, entire infinite sum controlled',
    certificate='Actual|D3|<=2; entire3..x remainder integral<=8+2sqrtx/[L^2(L-8)];14modules/36Std3 roots',
    consumers='Actual ordinary pi, completeBox pi and interval counts',
    literature='General integrated Perron and Nicolas; no desired compensation bound assumed',
    limitation='Rejected L-6 primitive preserved; no optimality/global-record claim')
add('SPECTRAL-PI', 'SPECTRAL-076', 'spectral-076/SpectralPi.lean', 'actual_box_pi',
    old='Actual Box pi transfer with GM and two additional Buthe psi/J inputs',
    new='U_new(f,L)=exp(L/2)f(L)/L+P(L)+Q(L)+2; old GM envelope-new>14 on allL>=24',
    domain='Generic actualpsi transfer L>=24; actualBox/intervalL>=35',
    premises=box, tier='B+D', same_premises='Strictly fewer inputs within old Box union; standalone GM/Perron providers differ',
    method='Preserve prime-power function Q and li-to-offset-Li2 allowance; construct allfourBox providers',
    certificate='spectral-076/SOURCE_FREEZE.json; exact whole-function comparison',
    consumers='Typed ordinary-pi transfer, effective minimum, actual interval counts',
    literature='Compare strongest applicable complete Lee-Nosal/Schoenfeld/Buthe families; no global domination established',
    limitation='A strict component gain does not ensure the active clipped minimum changes')
add('GOLDBACH-COUNTS', 'GOLDBACH-SORTED-COUNTS', 'octic/OcticOptimizedCertified.lean', 'triples_above_n_minus_H',
    old='Prime-rich window conclusion without this sorted-triple consumer',
    new='Actual sorted triple count>(1+4.2/logu)sqrtu at2.14891875 width; separate fixed2.15 count retained',
    domain='Oddn,GoldbachEvenUpTo(H),2H<n,u=n-H>=exp24,width<=H-4',
    premises=octic+['GoldbachEvenUpTo(H)','displayed geometry'], tier='B+D', same_premises=False,
    method='Inject each window prime as unique largest coordinate, sort residual finite binary pair',
    certificate='Certified octic moments consumed internally; actual finite-set injection',
    consumers='Actual Goldbach sorted finite population', literature='No new global ternary existence record or binary Goldbach proof',
    limitation='Finite binary input is explicit and not independently reverified here')
add('FINITE-COUNT', 'FINITE-COUNT', 'ramanujan/count-feasibility/high-driver/HighDriverContract.lean', 'output_of_exact_count',
    old='Original unbalanced kernel checks incomplete after multiday execution',
    new='Full fixed kernel count pi(1490000000000)=55206486339 accepted; cold695 numerical sources plus checker/audit freshly compiled and byte-identical; remaining305 and actual IEANTN byte consumer separate',
    domain='Same locked90,670,946records; original sources and numerical statement unchanged',
    premises=['Completed original Final exactcount proof','Generic C source-model/compiler/runtime interpretation contracts for the program connection'],
    tier='D exact numerical theorem accepted; complete source-first IEANTN chain pending', same_premises=True,
    method='Proof organization only: pure balanced finite checker, strict source/object/log/dependency reuse',
    certificate='Warm full2768-parts/Final/audit accepted7af53640...8d5f1, GNU3:41:35; cold695 DATA_RESULT12c2e559...19720 with697actualcompiler records; small32768 comparison preserved separately',
    consumers='Kernel count supplies program-model execution witness; cold305 and same-run byte-to-IEANTN theorem remain separate gates',
    literature='Not a published prime-count record or finite Ramanujan coverage',
    limitation='Cold305/current source-output and actual IEANTN consumer remain pending; no complete finite Ramanujan interval coverage')
add('HIGH-C-MAIN', 'FINITE-COUNT', 'ramanujan/count-feasibility/high-driver/HighDriverContract.lean', 'actual_source_model_main',
    old='Original driver literal38358837683 preserved',
    new='Additive actual C highmain1490000000000; native emits8little-endian bytes decoding to55206486339; whole-main source-owned initialization/call/output/lifetime model proof',
    domain='Actual highdriver static inputs/capacity; generic counter theorem2<=n<=2e12',
    premises=['Pinned generic C operational-model interpretation','Compiler/ABI/runtime/stdio/hardware/source-build-run contracts'],
    tier='Checked source-model mathematics plusindependentboundedfrontend; kernel exact count accepted, final source/IEANTN chain pending',
    same_premises='New additive source and main model, oldsource/AST/model preserved',
    method='Construct canonical whole-main run; prove bytes for every successful modeled execution',
    certificate='Nativev2 output8bytes,1.116s/19.94MiB; high-driver/SOURCE_FREEZE.json; fresh32 route',
    consumers='Highmain exactcount output adapter; not yet completed new PV',
    literature='WG14 C11 supported syntax grammar specified independently in bounded frontend work',
    limitation='Native execution is observation; mathematical numeric witness is the accepted kernel count, not a new native proof')
add('COUNTER-SOURCE-GRAMMAR', 'C-SURFACE-SYNTAX',
    'finite-pv/grammar/CounterGrammarConsumer.lean','complete_canonical_source_run',
    old='RestrictedC exactrendered-sourceidentity/modelproof, withoutindependentfragmentgrammarcorrespondence',
    new='ActualCcounter/highdriver independentC11fragmentcharactersyntax plusgeneralguardedrenderer soundness genuinelyconsumedby source-indexedconstructivemodelrun',
    domain='ExactlythesupportedC11fragmentandthetwopinnedactualcounter/highdriversources',
    premises=['PreservedformalCmodelinterpretation','Compiler/header/ABI/runtime/stdio/OS/hardware/source-build-runapplicability'],
    tier='Kernelprovedrestrictedsource/modelconnection; full source-output-to-IEANTN chain pending separate final append',
    same_premises='PreservesoriginalCsource/AST/executionmodel; additiveindependentsyntaxderivations',
    method='Independentgrammaroperators/precedence/parentheses/decimaldecode/matchedstatements/declarations/includes; genericrenderer soundness thenactualsourceadmission',
    certificate='Sourcefresh37;186compilerownedStd3theorems/19valueedges/11requiredendpoints/36CLIcontrols',
    consumers='Actualsource-indexedcanonicalwholemainrun; final exact-output and actual IEANTN byte consumers are separate closure steps',
    literature='WG14N1570 supports explicit boundedfragmentinterpretation; notgeneralCtypebinding/headermodel',
    limitation='Surfacecorrespondence is distinctfromfullISO-Csemanticadequacy; genericplatformandcompiledruncontractsremain')
add('BOX-LEE-WHOLE', 'BOX-LEE-FUNCTIONS','comparisons/BoxVsLee.lean','box_lt_both',
    old='Both completepsi functions printed LeeNosalv4p2Th1.1andTh1.2Eq2',
    new='fBox_.70871(L)<min(Lee11(L),Lee12(L)) forEVERYrealL>=35',
    domain='EntirecommoneligiblerealrayL>=35', premises=[], tier='Unconditionalpurekernelcomparison',
    same_premises='Purefunctioncomparison; actualBoxarithmeticusesexplicitRH/Perron/Nico/BPT',
    method='Positive shiftedpolynomial/exponentialbounds; allBoxmoment/residualtermsretained',
    certificate='Sourcefresh2/15actualtheoremconstants(9written+6generated)/18actualCLIcontrols',
    consumers='Whole-functionliteraturecomparison; noforeignsourceboundpromotedintoverifiednetwork',
    literature='NamedLeeNosal2312.05628v4p2 exacttwostatementsbeforeantecedentcitations',
    limitation='NotcomparisonwithentireLemma3.3heightfamily orfinitepublishedminimum; nobestknownclaim')
add('NL-MATCHED-WINDOW', 'NL-MATCHED-WINDOW', 'comparisons/NLParabolicConsumer.lean',
    'actual_prime_count_beats_old_objective',
    old='D=1.215L-.93logL-.25,delta=Dexp(-L/2),a=exp(L-delta),b=exp(L+delta); oldwindow(a,b), count>(L+.04)sqrta/(L-delta)',
    new='Newstrictwindow atsamelefta haswidth2.14891875sqrta loga, strictlyshorterthanoldwindow; actualcountbeatsoldcompleteobjective',
    domain='Purefunctions allrealL>=24; actualarithmetic additionally a>=exp24',
    premises=octic, tier='B+D actualconsumer; unconditionalpurefunctioncomparison',
    same_premises=False,
    method='Logtangentat24, directedD/delta andsinhbounds; fullwidth/countcomparisons consumedbyactualcertifiedocticprimecount',
    certificate='Fresh737;27actualownedtheorems(15written+12generated)/3proofVALUEedges;24correctedactualCLIcontrols/distinct3modelogs',
    consumers='ActualsameleftstrictprimeintervalbeatsarchivedNLcountobjectivewithshorterwidth',
    literature='ActualarchivedNL_RH/Intervals.md parabolicsection; originalwrittenarm/sourcepackagepreserved',
    limitation='OriginalNLanalyticproofisnotretroactivelyLeanformalized; sourcepackagesdiffer/noexposurecausalityoroptimalityclaim')
add('LEE-EQ10-COMPARISON', 'SPECTRAL-076', 'comparisons/ZeroInversePaired.lean', 'actual_both_sign_inverse_lower',
    old='Lee-Nosal2312.05628v4 Eq10p4 prints both-sign upper16.2106480369',
    new='General BPT implies actual positive-band sum>14 and fullboth-sign0<|gamma|<=1e7 sum>28',
    domain='Multiplicity-weighted actual zeros; noRH or finite zero table',
    premises=['SourceBPTOffOrdinate'], tier='B; independently source-audited and recompiled',
    same_premises='Source comparison finding, not an additional assumed network input',
    method='BPT lower Stieltjes integral and exact finite conjugate-pair set identity',
    certificate='Two kernel Lean modules; independent ledger13written identities and confirmed finding gate',
    consumers='Literature-comparison exclusion only; no bad source upper bound promoted into network',
    literature='Named Lee-Nosal Eq10 first; its cited FKS2204.02588v3 Eq2.4/Table1p5 is POSITIVE-only',
    limitation='Does NOT refute final published PNT theorem; closed-endpoint corrected upper not established')

ids = [r['id'] for r in rows]
if len(set(ids)) != len(ids):
    raise ValueError('Duplicate executive identity')
output = dict(status='EXECUTIVE_CLAIM_INDEX_NOT_FULL_PROVENANCE_CENSUS',
              source_ledger_sha256=hashlib.sha256((HERE/'RESEARCH_LEDGER.json').read_bytes()).hexdigest(),
              coverage='Leading claims selected by coordinator; full serious-attempt/provenance inventories are separate',
              rows=rows)
(HERE/'EXECUTIVE_THEOREMS.json').write_text(json.dumps(output,indent=2,ensure_ascii=False)+'\n')
flat = [{k: json.dumps(v,ensure_ascii=False) if isinstance(v,(list,dict,bool)) else v
         for k,v in r.items()} for r in rows]
with (HERE/'EXECUTIVE_THEOREMS.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=list(flat[0]))
    w.writeheader()
    w.writerows(flat)
print(json.dumps(dict(status='EXECUTIVE_INDEX_GENERATED',rows=len(rows),source_acceptance=False)))
