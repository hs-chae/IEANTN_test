#!/usr/bin/env python3
"""Freeze all16 new packets and exact matched runtimes; no inference."""
from pathlib import Path
import argparse,importlib.util,json,shutil,hashlib
R=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parent

def need(ok,message):
 if not ok:raise RuntimeError(message)
def module(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
helper=module('rh080_runtime_helpers',R/'Solutions/RH080Study.v1/ablation/prepare_runtime_locks.py');sha,pin,save,tree=helper.sha,helper.pin,helper.save,helper.tree
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--support-work',type=Path,required=True);p.add_argument('--controller',type=Path,required=True);p.add_argument('--packets',type=Path,required=True);a=p.parse_args();need(not a.controller.exists()and not a.packets.exists(),'Fresh controlled roots required');a.controller.mkdir();a.packets.mkdir()
prepared=json.loads((a.support_work/'PREPARATION_RESULT.json').read_text());need(prepared['status']=='PASS_EXACT_ACCEPTED_SUPPORT_PREPARATION_NO_INFERENCE','Unaccepted support preparation')
protocol=json.loads((HERE/'PROTOCOL.json').read_text());order=json.loads((HERE/'TRIAL_ORDER.json').read_text());need(protocol['planned_unique_trials']==len(order['trials'])==16,'Frozen population changed');old=R/'Solutions/RH080Study.v1/ablation';corpus=json.loads((old/'CORPUS_MANIFEST.json').read_text());shutil.copyfile(old/'CORPUS_MANIFEST.json',HERE/'CORPUS_MANIFEST.json');corpus_pin=tree(Path(corpus['root']),a.controller/'trees/corpus.json');base=json.loads((R/'Solutions/RHExposureStudy.v1/protocol/runtime-NL_RH.json').read_text());mounts=[dict(x)for x in base['mounts']if x['role']in ['generic','toolchain']]
common='''# Identical mathematical facts in every arm

Full compiled statement types and ordinary definition bodies for the169 selected application modules are supplied identically in /source_pv/FLAT_FACTS.txt (readable display), FLAT_FACTS.json (exact expression trees). These include all statement types supplied by any arm; theorem/proof bodies are omitted. The exact expression trees are authoritative. This mechanical application-closure selection is not a complete source-attribution audit. Ordinary data definitions can contain proof subterms, identically supplied to every arm. See /source_pv/SHARED_FACTS.json for exact hashes and selection.

Use ordinary RH for the Riemann zeta function. Keep all named general analytic
inputs explicit: CMSFunctionalInput.v1.population_reduction (CMS Theorem3,
(1.13), after its admissible-class/functional definitions),
BRFourierInput.v1.norm_identity (the arbitrary rational support-five affine
norm identity), and BRFourierInput.v1.uniform_population_q1 (the general affine
population estimate with a vanishing logarithmic remainder). These are
literature-backed inputs, not theorems from RH alone in Mathlib. The primary
CMS/Blanquer papers are the same frozen bytes in /corpus/literature.

Definitions: piReal(x)=Nat.primeCounting(floor_nonnegative(x)).
N(c,x)=piReal(x+c*sqrt(x)*log(x))-piReal(x), counting (x,x+h].
GoodCoefficient(alpha,c) means c>0 and there exists delta>0 such that,
for every sufficiently large real x, alpha+delta <= N(c,x)/sqrt(x).
Each parameter has its own eventual threshold. This does not give an explicit
onset. An upper endpoint prime may require an additional count/order argument
when passing to a strict-open interval.

The following existing results are supplied identically to every arm. They
are completed coordinator results, not literal newly published paper theorems:

(1) Under RH+CMS population_reduction, for every alpha>=0 and epsilon>0,
GoodCoefficient(alpha,q*(1+2*alpha)+epsilon),
q=20582561296/24680948495. The actual Gaussian Fourier transform, eligibility,
whole-line norms/tails and this consumer are Lean-kernel verified. This is
kernel-only verification, not source-first PV. Do not erase epsilon.

(2) Under RH+the two named BR inputs, for every alpha>=0,
GoodCoefficient(alpha,944247/1000000+(1163388/1000000)*alpha).

(3) Under exactly the same RH+BR inputs, for every alpha>=0,
GoodCoefficient(alpha,9/8+(16/15)*alpha).

Both (2) and (3) have completed ordinary kernel-only numerical proof routes
and completed actual C-source/AST/execution/numerical-to-ANT routes. Every arm
receives the same numerical values and actual executable C source bytes.
Only the assigned proof/representation exposure differs. The C port/semantics
scope and compiler/runtime/OS/hardware boundaries must be kept explicit.
The separate original large FFT migration is incomplete and not supplied as PV.

Original comparison: under its separate named RH+Green+Nicolas+BPT package,
for real x>=exp(24) and1.03<=C<=16 the strict-open count is greater than
((8/9)*C-18203/20000+(21/5)/log(x))*sqrt(x). Its limiting inverted leading
width is (9/8)*(alpha+18203/20000), only when the parameter range applies.
It also proves leading count1 at width343827/160000=2.14891875 with that
explicit onset. A new eventual theorem does not inherit this onset. Treat
this as the preserved coordinator baseline, not a universal literature record.

Primes are indexed from p_0=2 (p_n=Nat.nth Nat.Prime n). At a prime p_n,
piReal(p_n)=n+1. Derive every additional rank/count/order or endpoint step;
do not assume the desired prime-index conclusion. No new axioms, sorry,
or unverified numerical premises in accepted claims. Do not work on Ramanujan.
'''
supports={};representations={}
for row in protocol['conditions']:
 arm=row['id'];support=a.support_work/'supports'/arm;supports[arm]=tree(support,a.controller/'trees'/('support-'+arm+'.json'));representation=a.support_work/'representations'/arm;representation.mkdir(parents=True);(representation/'README.md').write_text('This is the '+arm+' exposure. Identical mathematical facts are in /task/COMMON_FACTS.md. Assigned proof assets are at /source_pv; that historical path name does not label ordinary kernel proofs as PV.\n');representations[arm]=(representation,tree(representation,a.controller/'trees'/('representation-'+arm+'.json')))
rows=[]
for trial in order['trials']:
 arm=trial['condition'];directory=a.controller/'trials'/trial['id'];packet=a.packets/trial['id'];packet.mkdir();(packet/'COMMON_FACTS.md').write_text(common);goal=next(x['goal']for x in protocol['tasks']if x['id']==trial['task']);(packet/'TASK.md').write_text('# Fresh matched mathematical transfer assignment\n\n'+goal+'\n\nUse only the identical common facts, frozen primary corpus and assigned exposure. The input curves were discovered before this study; derive new consequences. Distinguish written validity, complete Lean proofs, source-first PV and open work. Do not infer an advantage from being assigned an exposure.\n\nBudget:1200seconds,18000outputtokens,180executoroperations,96responses,4CPUs,64GiB RAM,12GiB scratch. No adaptive extensions or outside sources. Preserve negative results and exact statements, hypotheses and verification commands.\n')
 (packet/'TOOLS_AND_CHECKPOINTS.md').write_text('''# Tools and early saved work

Use /usr/bin/python3.10 for ordinary file/directory/hash/clock operations;
ls/cat/date need not be present. Use /bin/lean (the bounded wrapper). Generic
Mathlib sources are at /generic/source/mathlib. Assigned source and object
assets, if present, are at /source_pv/source and /source_pv/objects. C and D
also have /source_pv/GRAPH.json. B has compiled named estimates, without an
authored graph or readable solution-source tree. A has flat common facts.
B/C/D can import RH080EstimatePack. The named theorem roots are
RH080Exposure.Estimates.gaussian, .sparse and .flat; source-first alternatives
exist only in D's PopulationActualConsumers. All arms have the same C files.

Save a useful flat /work/submission early. LOCK.json MUST be an object
{"files":[{"path":"candidate.md","sha256":"actual SHA256"}]}, listing every
other payload; at most15 payloads, each at most2MiB. Update hashes before
relocking. Partial valid timed work remains evidence if the budget ends.
Statements/proofs/code/source locators/failed attempts are useful; a proposal
or a self-reported success flag is not a mathematical proof. Do not copy
private reasoning. No delegation, outside network or other-arm material.
''')
 packet_pin_path=a.controller/'packets'/(trial['id']+'.json');save(packet_pin_path,{'root':str(packet),'files':{x.name:sha(x)for x in sorted(packet.iterdir())}})
 repr_root,repr_pin=representations[arm];runtime={'schema':'RH080_ASSIGNED_RUNTIME_V1','condition':arm,'task':trial['task'],'replicate':trial['replicate'],'mounts':mounts+[{'role':'literature','target':'/corpus/literature','source':corpus['root'],'manifest':corpus_pin},{'role':'representation','target':'/representation','source':str(repr_root),'manifest':repr_pin},{'role':'source_pv','target':'/source_pv','source':str(a.support_work/'supports'/arm),'manifest':supports[arm]}],'lean_path':['/source_pv/objects']+base['lean_path'],'external_network':False,'host_tools':False};runtime_path=directory/'runtime.json';save(runtime_path,runtime);lock={'schema':'RH080_TRIAL_LOCK_V1','reviewed_by':'/root','fixture':True,'condition':arm,'task':trial['task'],'replicate':trial['replicate'],'protocol':pin(HERE/'PROTOCOL.json'),'runtime':pin(runtime_path),'packet_manifest':pin(packet_pin_path),'out':str(directory/'fixture-v1')};lock_path=directory/'FIXTURE_LOCK.json';save(lock_path,lock);rows.append({'trial':trial['id'],'condition':arm,'task':trial['task'],'replicate':trial['replicate'],'block':trial['block'],'directory':str(directory),'fixture_lock':str(lock_path)})
save(HERE/'PREPARED_RUNTIMES_v2.json',{'status':'FROZEN16_MATCHED_RUNTIMES_PREPARED_NO_INFERENCE','trials':rows,'protocol_sha256':sha(HERE/'PROTOCOL.json'),'support_preparation_sha256':sha(a.support_work/'PREPARATION_RESULT.json'),'model_calls':0});print('PREPARED16_NO_INFERENCE')
