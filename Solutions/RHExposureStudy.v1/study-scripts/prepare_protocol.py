#!/usr/bin/env python3
"""Prospective two-arm protocol and identical neutral target packet; no research execution."""
from pathlib import Path
import datetime,hashlib,json,shutil
W=Path('/ryu/hyunsik/playground/independence/codex/ivy');R=W/'ieantn-rh-propagation-20261120';D=Path('/data/ivy-rh-propagation-20261120')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def put(p,v):
 p=Path(p);p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():raise RuntimeError('immutable existing protocol '+str(p))
 p.write_text(json.dumps(v,indent=2,ensure_ascii=False,allow_nan=False)+'\n' if not isinstance(v,str) else v)
common='''# Shared mathematical mission: explicit consequences of RH

Assume the precise RH statement below. Develop the strongest defensible explicit analytic-number-theory consequences you can obtain for the shared target questions, including useful downstream applications. You may read legitimate mathematical literature, introduce justified additional source inputs, compute, write programs, use Lean, and develop new methods with the tools available in your environment.

Prioritize mathematical strength: bounds, onsets, validity ranges, quantitative margins, independent assumptions, and useful consequences. Compare against known RH literature. Label imported results, rediscoveries, new deductions, and verification improvements separately.

Record exact statements, domains, hypotheses, sources, actual computations, proof status, and failed approaches. Document real reuse and any recovery of information that a specified earlier argument did not exploit. Do not call certificate checking or native computation source-first PV unless an actual program is connected to formal execution semantics.

Continue beyond familiar textbook consequences. Work independently within your assigned inputs and tools. Do not attempt to access another arm or hidden evaluator materials. Save reproducible candidate statements and evidence at the scheduled checkpoints.

## Common RH and definitions

Use the pinned Mathlib RiemannHypothesis, in Mathlib.NumberTheory.LSeries.RiemannZeta. It asserts: for every complex s, if riemannZeta(s)=0, s is not any negative even integer -2(n+1), and s != 1, then Re(s)=1/2. This is an explicit hypothesis, not a theorem proved by the experiment. Account for boundary/pole/trivial-zero conventions in any adapters. Do not strengthen RH to GRH or assume numerical zero sums, prime tables or unproved coefficients.

For real x use the ordinary right-continuous functions pi(x)=#{p prime:p<=x}, theta(x)=sum_{p<=x} log p, psi(x)=sum_{p^k<=x} log p. Define Li2(x)=integral_2^x dt/log t (x>1); if a source instead uses li(x), include the additive normalization constant explicitly.

Use Epsi(x)=|psi(x)-x|/x and Epi(x)=|pi(x)-Li2(x)|/(x/log x), where meaningful. For Ramanujan use G(x)=(e*x/log x)*pi(x/e)-pi(x)^2 and RG(x)=(log x)^6*G(x)/x^2.

## Shared target questions (all four)

PNT: Find useful complete explicit bounds for psi, theta and pi, with precise hypotheses, onsets, validity ranges and pointwise comparisons. Investigate multiple serious methods, including RH-specific estimates and legitimate refinements of existing inputs. A formal parameter specialization outside its domain is not an accepted improvement.

Intervals: Derive useful prime-existence, prime-count-in-interval, or inverse prime-count consequences, comparing with strong applicable direct RH literature rather than only a weak PNT corollary. Check both endpoints and all inversion/domain restrictions.

Weighted: Pursue explicit weighted Chebyshev sums, Mertens sums/products, or another genuinely connected downstream family. Seek complete useful functions and ranges; retain signed or shared information where it helps and justify every new input.

Ramanujan: Seek a strong explicit positive lower envelope for G or RG, an earlier analytic onset, meaningful complete all-real coverage, fewer independent hypotheses, or a better verified finite algorithm. Distinguish real/integer coverage and strict endpoints. Compare with actual Dudek-Platt and Johnston literature, including prior computation; do not call a known theorem new mathematics or a cited computation source-first PV.

Open discovery beyond these four is welcome when connected and mathematically substantive. RH alone is neither GRH nor binary Goldbach. Do not assume desired conclusions as source predicates. No optimality/best-known claim is required.

## Common source access

Both arms start with identical original PDFs and page-marked text for Lee-Nosal arXiv2312.05628v4, Dudek-Platt arXiv1407.1901v1, Johnston arXiv2109.02249v2, under /corpus/literature. This is a starting catalog, not a closed bibliography. You may request ANY relevant legitimate original mathematical source or genuine supplement, and search for later improvements, using /task/request_source.py. For example:
  /usr/bin/python3.10 /task/request_source.py --id new-source --url https://arxiv.org/pdf/IDENTIFIER
  /usr/bin/python3.10 /task/request_source.py --id search-topic --query 'specific mathematical literature question'
Requests are delivered only to your arm; the neutral broker adds original source bytes/metadata to /corpus/literature/admissions/ID. The other arm's requests, findings and explanations are not shared. Never infer a mathematical fact from a failed fetch. Raw HTTP, browser, host files and connectors are unavailable. Request latency and source admissions are recorded.

## Common work and checkpoint rules

You have the same generic Lean4.34.0-rc2/Mathlib71a80585 and compiler/Python/symbolic numerical facilities, 8 CPUs, 96GiB per-run memory, 64GiB scratch initially. These are substantial initial allocations, not mathematical limits; document a justified larger task for the coordinator rather than weaken claims. No artificial output/token/operation cap terminates research. Passive technical snapshots every60 seconds and comparison checkpoints at900,1800,3600 seconds. The first submission must include serious multi-route improvement attempts in all four families and at least3600 seconds of research opportunity; later own-arm continuation is permitted symmetrically. Do not spend time waiting merely to reach a clock threshold; pursue the mathematical work.

Save flat source/proof/derivation/result files under /work/submission, together with STAGE_STATUS.json {"ready_for_review":true,"serious_attempts_documented":true,"families":{"PNT":{"status":"supported|incomplete|no_additional_improvement"},"Intervals":{"status":"..."},"Weighted":{"status":"..."},"Ramanujan":{"status":"..."}}}. Every result records exact definitions, constants, quantifiers/domains, all hypotheses, primary locators and actual proof/execution status. Include failures and limitations; numerical plots or sampled calculations are exploration, not all-real proofs. LOCK.json contains {"files":[{"path":"filename","sha256":"..."},...]}, including STAGE_STATUS.json. A submission is unreviewed until independently checked.
'''
request='''#!/usr/bin/env python3
from pathlib import Path
import argparse,json,os,re,tempfile
p=argparse.ArgumentParser();p.add_argument('--id',required=True);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--url');g.add_argument('--query');a=p.parse_args()
if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_-]{0,79}',a.id):raise ValueError('simple unique request id required')
f=Path('/work/submission/SOURCE_REQUESTS.json');f.parent.mkdir(parents=True,exist_ok=True)
d=json.loads(f.read_text()) if f.exists() else {'requests':[]}
if any(r['id']==a.id for r in d['requests']):raise ValueError('preserve old request; choose new id')
d['requests'].append({'id':a.id,'kind':'url' if a.url else 'search','value':a.url or a.query})
fd,n=tempfile.mkstemp(prefix='.sources-',dir=f.parent)
with os.fdopen(fd,'w') as h:json.dump(d,h,indent=2);h.write('\\n')
os.replace(n,f);print('Request queued; check /corpus/literature/admissions/'+a.id+' after broker processing. Continue independent work meanwhile.')
'''
put(R/'protocol/SHARED_MISSION.md',common)
for arm in ['NL_RH','IEANTN_RH']:
 p=R/'protocol/packets'/arm;p.mkdir(parents=True,exist_ok=True)
 shutil.copy2(R/'protocol/SHARED_MISSION.md',p/'SHARED_MISSION.md');put(p/'request_source.py',request)
 role=('You are the NL + RH research arm. Your initial mathematical materials are the common statement, target questions, external literature, and generic software. You may create your own proofs, Lean code, programs, verification developments, notes, indexes, or other organizational tools. Your input condition does not include an existing IEANTN-specific proof/program network or its generated explanations. Use the permitted external-source channel and your own mathematical research.' if arm=='NL_RH' else 'You are the full IEANTN + RH research arm. In addition to the common materials, you have the pinned authorized IEANTN package and the precise RH interface. Inspect the full relevant network. Propagate RH through actual mathematical interfaces, prove missing adapters, develop sharper bounds, evolve algorithms where useful, and pursue substantive downstream results. Track actual uses of existing proofs, intermediate quantities, source-linked programs, and contracts. Explain mathematically what each reuse or recovery changes.')
 put(p/'TASK.md',role+'\n\nRead /task/SHARED_MISSION.md in full before research. Read /task/RUNTIME_PATHS.json for actual mounts and /task/TOOLS.md for commands. You receive no coordinator conversation or other-arm work.\n')
protocol={'schema':'RH_NL_IEANTN_PROTOCOL_V1','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PROSPECTIVE_BEFORE_ANY_SCORED_DISCOVERY','arms':['NL_RH','IEANTN_RH'],'pairs':1,'general_stochastic_superiority_claim_allowed':False,'base_repository':{'commit':'97c2f6bf91b8ac1eff6a298557c05e25aa1a97bf','research_branch':'research/rh-nl-vs-ieantn-20261120','actual_untracked_supplement_inventory':'to_be_frozen_before_launch'},'shared_mission_sha256':sha(R/'protocol/SHARED_MISSION.md'),'targets':['PNT','Intervals','Weighted','Ramanujan'],'model':'gpt-6.2-sol','effort':'high','model_selection':'query live native catalog before inference; fail closed if absent; same exposed alias/effort/default service tier; actual immutable backend revision unavailable unless emitted','resource_policy':{'memory_gib':96,'cpus':8,'scratch_gib':64,'initial_allocation_not_4gib':True,'host_reserve_gib':512,'total_owned_scratch_gib':300,'increase_per_run_memory_to300_only_if_host_available_atleast1TiB':True,'independent_disk_available_atleast1TiB_for300GiBtotal':True,'equivalent_justified_extension_for_both_arms':True},'literature_policy':{'initial_same_catalog':['2312.05628v4','1407.1901v1','2109.02249v2'],'new_sources_permitted':True,'independent_request_delivery':True,'broker_search':'Crossref primary bibliographic metadata and canonical source retrieval; requests requiring other legitimate sources handled equally by coordinator without mathematical coaching','no_shared_search_trajectory':True,'source_requests_not_closed_bibliography':True,'block_ieantn_material_and_mirrors_for_NL':True,'source_bytes_urls_versions_UTC_SHA_preserved':True},'isolation':{'fresh_native_ephemeral_contexts':True,'inherited_coordinator_history':False,'OS':'private user,mount,pid,net namespaces, zero effective capabilities, private proc/tmp/home, no host access','tool_policy':'existing reviewed restricted executor gate; no collaboration/connectors/rawbrowser/rawHTTP tools','generic_sources_caches':'exact identical pinned inventory forboth','application_sources_caches':'full arm only, exact inventory','preflight':'actual exact runtime filesystem/tool/native fixture before discovery'},'checkpoints':{'technical_passive_seconds':60,'scientific_seconds':[900,1800,3600],'initial_minimum_research_opportunity_seconds':3600,'freeze_at_ready_after_serious_multi_route_work':True,'generated_token_planning_milestone':250000,'increment':250000,'token_or_operation_milestone_is_hard_cap':False,'extensions':'symmetrically available; record initial locks before own-arm continuation or cross-arm synthesis'},'evaluation':{'primary':['complete_explicit_bound','validity_onset','range','quantitative_margin','independent_hypotheses','useful_downstream_consumer'],'secondary':['proof_time','tokens','nodes','compilation'],'independent_review':'exact source hypotheses domains constants, complete derivations, actual checked types/axioms, numerical and PVtrust','postlock_synthesis_separate':True,'preserve_null_NL_win_incomparable_failed_routes':True,'prior_QRH_is_historical_reference_not_third_arm':True},'publication':'reviewed research branch only; no official status/PR/merge; no forcepush/origin push','neutral_setup_and_cache_costs_separate':True}
put(R/'protocol/protocol.json',protocol)
print(json.dumps({'protocol':sha(R/'protocol/protocol.json'),'shared_mission':sha(R/'protocol/SHARED_MISSION.md')}))
