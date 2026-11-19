#!/usr/bin/env python3
"""Build source-isolated follow-up research packets, without model calls.

Fresh packets contain only the common task/input and the relevant frozen runtime
exposure. The separate legacy inventory does not enter fresh packets.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re

S=Path(__file__).resolve().parents[1]
OLD=S.parent/'ieantn-deep-tertiary-exposure-a-20261117'
CAMPAIGN='D01_D02_REPAIR_RERUN_20261118_V1'
ARMS=('IEANTN','PNT','NL')
RUNTIMES={'IEANTN':'IEANTN_GENERIC_COMPLETE_V2','PNT':'PNT','NL':'NL'}
PINS={'IEANTN':'ef21db9ba5dceffd976da71e24f8497b3a13f798','PNT':'a4fb6989b07e9c76b511807ae93e33e25b820e9b'}

TASK='''# Research task

Begin with one innocuous tool command: confirm the current directory and read the names of INPUT_CONTRACT.json and RUNTIME_PATHS.json under /task. Then read the permitted files and conduct the actual mathematical research. If these files or ordinary commands are inaccessible, record the exact interruption; do not pretend execution.

Use the exact additional assumption in INPUT_CONTRACT.json and the permitted original papers to obtain the strongest defensible explicit arithmetic conclusions in BOTH requested application families. This is mathematical research: develop new proofs and justified computations, repair your own incomplete derivations, and actively improve the final conclusions rather than stopping at an intermediate estimate.

For the Ramanujan prime-counting gap, improve quantitative lower-bound profiles, real onsets and connected domains. Compare margins at fixed onsets and onsets at fixed margins; retain stronger higher-order profiles and justified tradeoffs. For Mertens products and related prime sums, improve constants, powers, logarithmic factors, onsets and the whole-domain pointwise envelope of every valid branch.

All common original-paper results, including the original QRH paper, remain available. The new hypothetical input adds knowledge; it does not replace or revoke old inputs. Show exactly where the additional assumption changes each claimed result. Compare your result with the strongest lawful original-source envelope on matched domains. If the added assumption does not help a branch, state its actual bottleneck and serious improvement attempts; preserve valuable input-independent discoveries as separate secondary results. A within-method reconstruction of the original-input baseline is not an independent blind baseline run.

No argument route is prescribed. You may develop new self-contained lemmas, shorter analytic arguments, finite computations or new algorithms from the permitted material. Every final whole-ray claim needs a justified entire-domain proof, including its finite joins and analytic tail. Keep strict/non-strict and real/integer endpoint conventions explicit. Do not claim a theorem from exploratory floating-point samples or infer global optimality or best-known status without proof.

Read COMMON_FOUNDATION.md, BASELINES.md, EVALUATION_RULES.md, BUDGET.json, CHECKPOINTS.md and OPERATING_NOTICES.md. SOURCE_INDEX.json names the exact originals. Use only sources actually bound by RUNTIME_PATHS.json. Do not search outside the isolated environment, use other sessions or create subagents. Keep work and outputs in /work.

Research and independent mathematical review are separate stages. Improve both requested families until your portfolio is complete and evaluated, or a concrete mathematical bottleneck remains after serious attempts. Do not stop merely because you reach a planning milestone or finish the first good bound. You need not consume unused resources once the mathematical stage is actually complete.
'''

FOUNDATION='''# Common mathematical permissions and conventions

The only external analytic-number-theory literature premises are the exact seven original papers named by SOURCE_INDEX.json, at their original hypotheses, domains and trust tier. All these sources remain available cumulatively. An optional project environment can supply source, proofs and valid consequences of the permitted premises, but an imported proposition, stub, numerical table or outside citation is not automatically a new external mathematical premise. Justify a project result from the permitted sources or give a self-contained proof.

Common foundational mathematics includes classical logic and elementary arithmetic/algebra; finite sums/products and unique factorization; elementary prime and valuation facts; ordinary real and complex analysis, limits, derivatives, integrals, series, justified convergence/interchange and contour/residue arguments with their hypotheses. New self-contained mathematical lemmas and computational algorithms are allowed equally.

Conventions: pi(x) counts primes p<=x; theta(x)=sum log p over p<=x; psi(x)=sum log p over prime powers p^m<=x. All logarithms are natural. Unless explicitly restricted, a real-ray statement includes nonintegers. Preserve each original source's logarithmic-integral normalization and endpoint conventions.

Lean is optional. Mathematical validity is distinct from formal verification. Kernel-only rational checks, native_decide, ordinary certificate checking and executable numerical replay are not source-first PV. A source-first PV claim needs actual C/C++/CUDA source correspondence to formal execution semantics, program correctness and linkage of its verified outputs to the endpoint theorem. Do not label unfinished analytic Lean implications as full formalization.

Use the same generic offline computation tools as the other treatments. Treat published finite computations as inherited literature trust unless independently reverified. Do not add new numerical outputs as an unproved mathematical hypothesis. No external web/search, host tools, other workspaces, prior sessions, personal memory, connectors or worker-created subagents are authorized. Submit reproducible mathematical artifacts and factual work notes, not private reasoning transcripts.
'''

BASELINES='''# Requested families and original-source comparison

## Ramanujan gap

For real x>1 write L=log x and define
R(x)=(exp(1)*x/L)*pi(x/exp(1))-pi(x)^2.
Seek stronger justified lower profiles R(x)>M(x), earlier sufficient onsets and fully connected domains. State the complete assumptions, real/integer meaning, strictness and every interval boundary.

Relevant original starting references include Platt--Trudgian arXiv:1809.03134v2 Theorem2 (PDF page3) and Dudek--Platt arXiv:1407.1901v1 Theorem1.2 (PDF page2). Inspect their exact source statements and verify the conventions needed by your conclusion. These are starting references, not a restriction to a selected weak bound.

## Mertens products and prime sums

Define raw P_raw(x)=product over p<=x of(1-1/p) and Q_raw(x)=1/P_raw(x). Seek smaller whole-domain relative-error envelopes for |exp(gamma)*L*P_raw(x)-1| and |exp(-gamma)*Q_raw(x)/L-1|, stronger domains and justified tradeoffs. gamma is Euler's constant. Related sums sum 1/p and sum log(p)/p are also requested; specify the source's normalizing constants exactly.

Dusart2018 Theorems5.6--5.9 (PDF pages17--20) supply original prime-sum/product baselines. Theorem5.9 gives the two relative product errors at most0.2/L^3 for x>=2278382. Retain every stronger applicable estimate in the supplied corpus or a valid independently derived consequence. The two reciprocal products and other consequences of one derivation are correlated outputs, not independent trials.

Compare B0 (the original common assumptions only) and B0 plus the exact supplied hypothetical direct-psi assumption. Report whole-domain dominance or a proved crossover for different functional shapes; a sample grid is not an all-ray comparison. Smaller coefficients with later onsets are tradeoffs. Ties and incomparable frontiers are valid outcomes.
'''

EVAL='''# Submission and evaluation

Submit exact statements, full hypotheses/domains, source locators, derivations, explicit numerical obligations, reproducible scripts/certificates/proofs and remaining gaps. Report the strongest supported whole-domain portfolio for BOTH families; keep nondominated threshold/strength/premise tradeoffs and valid old minima. Distinguish original-source reuse, new derivation, conditional computation, unproved conjecture and secondary input-independent results. A result called new is not thereby globally novel or best known.

Mathematical statuses are supported at its stated trust tier, false with a concrete counterexample, incomplete with a concrete missing step, unassessed, or review interrupted. Formal Lean and source-first PV are separately reported. A written proof can be mathematically supported without full Lean; a successful numerical executable does not prove the surrounding mathematics.

Save regular flat payload files under /work/submission, preferably at most2MiB each so snapshots remain portable. Use concise filenames without directories or symlinks. Preserve large regenerable computations through deterministic scripts/parameters/hash receipts instead of huge raw dumps; explain any essential nonregenerable evidence. Include a factual completed/remaining/next-step restart note.

Write LOCK.json in EXACTLY this minimal format:
{"files":[{"path":"candidate.md","sha256":"<64 lowercase hexadecimal SHA256 of exact bytes>"}]}
List every payload exactly once. LOCK.json is the manifest and is not listed in itself. Do not add extra top-level fields. Update it after editing payloads. Save it early and at checkpoints. Harmless formatting defects can be mechanically corrected with the original snapshot retained; they do not discard assessable mathematics.

When the research stage is ready for independent review, write STAGE_STATUS.json as a regular payload and include it in LOCK.json. Use the following structure, filling each status with supported, incomplete, or no_additional_improvement and listing your actual claim files:
{"ready_for_review":true,"families":{"Ramanujan":{"status":"supported","claim_files":["candidate.md"]},"Mertens":{"status":"incomplete","claim_files":["candidate.md"]}},"serious_attempts_documented":true}
Both families need an explicit status and their actual evidence. Incomplete can be an honest completed research submission only after serious attempts and a concrete mathematical bottleneck are documented; it is not an accepted theorem. Independent mathematical review still follows. Do not copy the example statuses unless they describe your actual work.

There is no over-cap invalidation or mandatory termination at the stated planning milestones. Checkpoint, continue automatically and use the same extension policy in every treatment. Platform/provider interruption is an execution interruption, not a mathematical failure. Full mathematical review and opportunity for your own repair/re-review follow submission; that feedback contains only your own work.
'''

CHECKPOINTS='''# Checkpoints and continuation

Save mathematical source/code and update submission/LOCK.json regularly, before any context handoff, and at planning checkpoints (initial125000,250000,500000 aggregate generated tokens; further250000-token planning increments). These are recording milestones, not hard caps. Record actual generated tokens, tool use, elapsed time, current best supported results and their trust tier where available. The controller's measured usage is authoritative; do not fabricate counters.

When context becomes long, save a concise factual restart note with the exact files, definitions, current proofs, certificates, failed approaches, unfinished obligations and next concrete step. Continuation sessions may use only this trajectory's own state and permitted sources. They retain cumulative effort accounting. An interrupt never deletes a previously valid theorem. A milestone never disqualifies an output or requires new user approval.

Do not save private reasoning transcripts as public artifacts. Preserve reproducible mathematics, code and factual work/usage notes. A mathematical checkpoint is not external evaluation feedback. Stop research only after complete portfolio/substantive improvement attempts or an explicitly recorded serious bottleneck, not because a weaker result appeared first.
'''

NOTICES='''# Operational notices

The research planning allowance begins at500000 aggregate generated tokens, with automatic250000-token increments when meaningful work remains. These figures are not hard caps. The old80000 discovery/24000 review policies do not apply. The controller can preserve state and start same-trajectory continuation sessions within actual platform capabilities; it must not silently truncate legitimate research through old operation/response/wall admission limits.

The runtime's read-only mounts are the complete source authority. No outside corpus or prior research answer is permitted in a fresh stage. Keep all work in /work; save submission/LOCK.json and a factual restart note before handoff. Do not claim ordinary execution, native_decide or rational certificate checks as source-first PV. Report any actual tool/provider interruption distinctly.
'''


def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def enc(v):return (json.dumps(v,indent=2,ensure_ascii=False,allow_nan=False)+'\n').encode()
def load(p):return json.loads(Path(p).read_text())
def pin(p):return {'path':str(Path(p).resolve()),'sha256':sha(p)}
def runtime(arm):
 p=OLD/'protocol/runtimes'/RUNTIMES[arm]/'runtime.json';j=load(p)
 need(j['arm']==arm and j['external_network'] is False and j['host_tools'] is False,'runtime authority mismatch')
 if arm in PINS:need(j.get('pin',j.get('source_pin'))==PINS[arm],'native source pin changed')
 need(arm!='NL' or all(x['role']!='native' for x in j['mounts']),'NL exposed to project')
 for row in j['mounts']:
  need(Path(row['source']).is_dir(),'runtime source missing: '+row['source'])
  need(sha(row['manifest']['path'])==row['manifest']['sha256'],'runtime manifest changed')
 return p,j

def common_contract(stage):
 j=load(OLD/f'protocol/main-packets/MAIN-A-{stage}-NL/INPUT_CONTRACT.json')
 j['input_id']='FOLLOWUP-'+stage
 j['source_policy']='Cumulative: all seven supplied originals, including their common QRH conclusions, remain available at exact original hypotheses/trust. This supplied hypothetical direct-psi input adds knowledge; it does not revoke any valid original result.'
 return j

def build(collection):
 need(not collection.exists(),'preserve existing packet collection')
 collection.mkdir(parents=True)
 srcindex=load(OLD/'protocol/main-packets/MAIN-A-D01-NL/SOURCE_INDEX.json');need(len(srcindex['sources'])==7,'exact seven sources required')
 for item in srcindex['sources']:
  for kind in ['pdf','text']:
   p=OLD/'sources/primary-papers'/item[kind];need(p.is_file() and sha(p)==item[kind+'_sha256'],'corpus bytes changed')
 rows=[]
 for arm in ARMS:
  rp,rj=runtime(arm);run='FRESH-R1-D01-'+arm;folder=collection/run;folder.mkdir()
  paths={'schema':'BOUND_WORKER_RUNTIME_PATHS_V1','status':'BOUND','paper_root':'/corpus/originals','read_only_roots':[{'path':x['target'],'role':x['role']} for x in rj['mounts']],'lean_path':rj.get('lean_path',[]),'generic_tools':{'python':'/usr/bin/python3.10','mpmath':'1.3.0','sympy':'1.12','C_and_Cpp':True},'private_writable_roots':['/work','/tmp','/home/worker'],'other_sources_authorized':False}
  budget={'schema':'FOLLOWUP_RESEARCH_PLANNING_RESOURCES_V1','model':'gpt-6.2-sol','effort':'high','initial_generated_token_milestone':500000,'automatic_increment_generated_tokens':250000,'milestone_is_hard_cap':False,'overrun_invalidates_result':False,'operation_response_wall_admission_caps':None,'memory_gib_per_active_allocation':64,'private_work_gib':24,'private_tmp_gib':1,'CPUs_per_active_allocation':8,'checkpoint_generated_tokens':[125000,250000,500000],'provider_seed':'NOT_EXPOSED','service_tier':'default','completion':'Complete evaluated portfolio and substantive improvement attempts, or specific mathematical bottleneck after serious attempts. Platform interruptions retain state and resume; no forced wasteful resource consumption.'}
  files={'TASK.md':TASK.encode(),'COMMON_FOUNDATION.md':FOUNDATION.encode(),'BASELINES.md':BASELINES.encode(),'EVALUATION_RULES.md':EVAL.encode(),'CHECKPOINTS.md':CHECKPOINTS.encode(),'OPERATING_NOTICES.md':NOTICES.encode(),'INPUT_CONTRACT.json':enc(common_contract('D01')),'SOURCE_INDEX.json':enc(srcindex),'RUNTIME_PATHS.json':enc(paths),'BUDGET.json':enc(budget)}
  for name,raw in files.items():
   for banned in ['CAND-','FINAL_REPORT','0.011','2840','coordinator/', 'D01_D02_REPAIR_AND_RERUN_PROMPT','48 <=','6301136165','1/50000']:
    need(banned not in raw.decode(),'coordinator result/diagnosis in fresh packet '+name)
   p=folder/name;p.write_bytes(raw);p.chmod(0o444)
  manifest={'schema':'DEEP_TERTIARY_TREE_V1','root':str(folder.resolve()),'files':[{'path':n,'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()} for n,raw in sorted(files.items())]}
  mp=collection/(run+'.manifest.json');mp.write_bytes(enc(manifest));mp.chmod(0o444);folder.chmod(0o555)
  rows.append({'run_id':run,'campaign':CAMPAIGN,'track':'FRESH_MATCHED_TRAJECTORY','replicate':1,'stage':'D01','arm':arm,'packet_manifest':pin(mp),'runtime_manifest':pin(rp),'native_source_commit':PINS.get(arm),'runtime_toolchain':rj.get('toolchain'),'prior_research_artifacts_supplied':False,'source_corpus':'Same seven exact PDF/text originals; common assumptions cumulative','isolation_status':'ACTUAL_PREFLIGHT_PENDING','inference_started':False})
 for name in files:
  if name!='RUNTIME_PATHS.json':need(len({(collection/r['run_id']/name).read_bytes() for r in rows})==1,'matched common packet bytes differ')
 result={'schema':'FOLLOWUP_FIRST_FRESH_D01_PACKET_COLLECTION_V1','campaign':CAMPAIGN,'status':'PREPARED_ONLY_NOT_STARTED','UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'builder':pin(__file__),'worker_packet_count':3,'common_files_byte_identical_except_runtime_paths':True,'historical_campaign_modified':False,'no_master_combined_report_old_candidates_or_coordinator_results_in_fresh_packets':True,'rows':rows}
 p=collection/'COLLECTION.json';p.write_bytes(enc(result));p.chmod(0o444)
 print(json.dumps({'status':result['status'],'packet_collection':pin(p),'packets':3,'model_calls':0}))

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--out',type=Path,default=S/'protocol/packets-first-fresh-D01-v1');args=p.parse_args();build(args.out.resolve())
if __name__=='__main__':main()
