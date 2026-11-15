"""Recheck sealed outcomes, exact independent Lean evidence and the final source ledger.

This summarizer never launches workers, repairs submissions or changes original scores.
"""
from pathlib import Path
import argparse,csv,hashlib,json,os,re
R=Path(__file__).resolve().parents[2]
STD3={'propext','Classical.choice','Quot.sound'}
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def strict(p):
 def pairs(xs):
  d={}
  for k,v in xs:
   need(k not in d,'duplicate JSON key '+k);d[k]=v
  return d
 def bad(s):raise ValueError('nonfinite JSON '+s)
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_constant=bad)
def timing(p):
 s=p.read_text();m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',s)
 need(m is not None,'GNU time RSS missing '+str(p));return int(m.group(1))*1024

def owned_view(p):
 seen=set();size=0;files=0
 for f in p.rglob('*'):
  if f.is_file()and not f.is_symlink():
   z=f.stat();key=z.st_dev,z.st_ino
   if key not in seen:seen.add(key);size+=z.st_size;files+=1
 return dict(distinct_inode_logical_bytes=size,files=files,qualification='Logical retained view of this exact experiment-owned directory, counting each inode once within this view; not physical-exclusive disk allocation or a peak disk measurement.')
def final():
 sealed_path=R/'exposure/heldout-study-v1/STUDY_SEALED.json';sealed=strict(sealed_path)
 need(sealed['completed']==6 and sealed['original_outcomes_unchanged']and sealed['no_candidate_content_read_until_all_sealed'],'sealed six-session design')
 lock=R/'exposure/design/HELDOUT_LOCK_V1.json';need(sha(lock)==sealed['lock_sha256'],'original prelaunch lock')
 verification=R/'exposure/heldout-independent-v1/namespace/data/verification';compiled=strict(verification/'RECEIPT.json');cases={x['case']:x for x in compiled['cases']}
 need(set(cases)=={x['case']for x in sealed['rows']},'same exact six original cases')
 audit=R/'exposure/heldout-audit-v1';scope=list(csv.DictReader((audit/'ALL_WRITTEN_SCOPE.csv').open()));ledger=list(csv.DictReader((audit/'ALL_WRITTEN_LEDGER_V1.csv').open()))
 key=lambda x:(x['file'],x['decl_line'],x['lean_name'])
 need(len(scope)==172 and len({key(x)for x in scope})==172 and {key(x)for x in scope}=={key(x)for x in ledger}and len(ledger)==172,'exact172written-identity population')
 need(all(x['proposed_verification_status']in{'internal_verified','external_verified'}for x in ledger),'all final source ledger gates')
 for row in scope:need(sha(R/row['file'])==row['source_sha256'],'unchanged audited written source '+row['file'])
 full={'H01-PROSE','H02-PROSE','H02-STRUCTURED','H03-PROSE','H03-STRUCTURED'}
 notes={
 'H01-STRUCTURED':'Finite Abel identity and boundary bound compile; improper-tail integrability, limiting constant and complete all-ray tail were not formalized in this original submission. Provided constant changed only to noncomputable; the archived original TaskDefinitionsInput intentionally fails to compile.',
 'H01-PROSE':'Complete actual-prime Abel identity, genuine improper-tail integrability, limiting constant, convergence and nine-C all-ray error compile. Provided definitions receive a noncomputable section only; mathematical objects and constant are unchanged.',
 'H02-PROSE':'Standalone original Main compiles and gives actual psi-to-theta transfer with additive coefficient 1e-13, hence the requested 1e-9. The unused provided stub is outside its imports; the standalone real definitions are noncomputable and definitionally match canonical IEANTN errors.',
 'H02-STRUCTURED':'Standalone original Main compiles and gives the stronger two-term theta remainder, exact additive 16/exp75 coefficient and requested 1e-9 target. It does not apply the psi hypothesis below exp300. Canonical IEANTN errors match definitionally.',
 'H03-STRUCTURED':'Known-target reconstruction: complete parameter-dependent envelope and existing PNT transfer compile with epsilon=1/1048576. Correct but weaker than the coordinator incumbent epsilon=1e-8; not an original improvement. Only noncomputable was added to the supplied finiteCap.',
 'H03-PROSE':'Known-target reconstruction: standalone Envelope compiles with epsilon=1/1000000. Correct but weaker than the coordinator incumbent. The retained unused original TaskDefinitions is an intentional diagnostic failure; standalone definitions are noncomputable.'}
 results=[]
 for row in sealed['rows']:
  name=row['case'];v=cases[name];raw=R/row['result'];need(sha(raw)==row['result_sha256']and row['exit_code']==0 and row['mechanical_gate'],'exact mechanically admitted original result '+name)
  per=strict(verification/name/'RECEIPT.json');need(not per['nonstandard_axiom_roots'],'all submitted theorem closures standard '+name)
  for c in per['commands']:
   for suffix,k in[('.stdout','stdout_sha256'),('.stderr','stderr_sha256'),('.time','time_sha256')]:need(sha(verification/name/'logs'/(c['module']+suffix))==c[k],'independent log '+name+'/'+c['module'])
   if c['module']not in{'audit','census'}:
    original=R/'exposure/heldout-study-v1/cases'/name/'submission'/(c['module']+'.lean');need(sha(original)==c['source_sha256'],'unmodified original candidate '+name+'/'+c['module'])
   if c.get('object_sha256'):
    need(sha(verification/name/'objects'/(c['module']+'.olean'))==c['object_sha256'],'actual independently compiled object '+name+'/'+c['module'])
  sp=R/'exposure/heldout-study-v1/scopes'/name/'scope.json';s=strict(sp);need(s['exit_code']==0,'resource scope completed '+name)
  samples=s.get('samples',[]);charged=max([int(x.get('memory.current','0'))for x in samples]or[0]);events=[x.get('memory.events','')for x in samples]
  oom=max([int(m.group(1))for e in events for m in re.finditer(r'^oom_kill\s+(\d+)$',e,re.M)]or[0])
  independent_rss=max(timing(verification/name/'logs'/(c['module']+'.time'))for c in per['commands'])
  results.append(dict(case=name,task=row['task'],representation=row['arm'],known_target=row['task']=='H03',original_full_formal_target=name in full,mathematical_contract='VALID_SCOPED_FIRST_PASS',source_first_PV_by_worker=False,generated_tokens=row['generated_tokens'],operations=row['operation_count'],session_scope_seconds=row['elapsed_seconds'],independent_check_seconds=v['seconds'],independent_max_single_child_RSS_bytes=independent_rss,research_scope_sampled_charged_RAM_lower_bound_bytes=charged,exact_aggregate_peak_RAM_bytes=None,observed_OOM_kills=oom,submitted_Lean_files=v['submitted_Lean_files'],compiled_submitted_files=len(v['successfully_compiled_modules']),failed_submitted_modules=v['failed_modules'],complete_native_free_theorem_closures=True,interpretation=notes[name],sealed_result_sha256=row['result_sha256'],independent_receipt_sha256=sha(verification/name/'RECEIPT.json'),resource_scope_sha256=sha(sp),retained_view=owned_view(R/'exposure/heldout-study-v1/cases'/name)))
 result=dict(schema='SEALED_HELDOUT_DESCRIPTIVE_RESULTS_V1',status='PASS_SIX_ORIGINAL_OUTCOMES_INDEPENDENTLY_COMPILED_AND_SCOPED_CONTRACTS_REVIEWED',rows=results,total_sessions=6,formal_targets_completed=5,formal_partial=1,mechanically_admitted=6,source_first_PV_by_workers=0,original_outcomes_unchanged=True,shared_packet_defect='Provided exact-real constants C/finiteCap lacked noncomputable. Confirmed only after all six sessions sealed. Equal corresponding broken stubs were supplied; each actual standalone/import/repair handling was reviewed. No hint, retry, budget adjustment, packet repair or rescoring occurred. This defect may affect effort and limits representation comparisons.',scope=dict(tasks=3,representations=2,replications_per_task_arm=1,source_contract_identities=172,external_formal_library_support_identities=sum(x['proposed_verification_status']=='external_verified'for x in ledger),internal_identities=sum(x['proposed_verification_status']=='internal_verified'for x in ledger),independent_second_pass_selected_H02_identities=10,primary_source_claim='Pinned Mathlib theorem/formal-source support was checked; not an exhaustive audit of original number-theory papers, not full-network coverage.'),design_limits=['Descriptive six-session study with one run per cell; no confirmatory causal-effect or significance claim.','Three classical mechanisms; H03 explicitly known-target reconstruction. No global mathematical novelty or priority claim.','No program evolution or source-first proof was supplied by these workers. Two actual C-source consumers are separate poststudy parent integrations.','Original eight pilots and historical67/192 primary scores remain unchanged.','Scheduling/paired-task seeds are recorded; provider generation RNG was not controlled.'],evidence=dict(lock_sha256=sha(lock),sealed_sha256=sha(sealed_path),verification_receipt_sha256=sha(verification/'RECEIPT.json'),source_scope_sha256=sha(audit/'ALL_WRITTEN_SCOPE.csv'),source_ledger_sha256=sha(audit/'ALL_WRITTEN_LEDGER_V1.csv'),second_pass_receipt_sha256=sha(audit/'H02_SELECTED_CONTRACT_SECOND_PASS_ROOT_V1.json')),resource_interpretation='Exact cgroup memory.peak was unavailable. Sampled charged RAM is a lower bound, not a peak; GNU-time RSS is the largest individual compiler process, not concurrent aggregate RAM. Disk values are retained owned-directory logical views, not peak allocation. No unobserved period is certified OOM-free.')
 return result

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();need(not a.out.exists(),'fresh output');result=final();a.out.parent.mkdir(parents=True,exist_ok=True);tmp=a.out.with_suffix('.pending');tmp.write_text(json.dumps(result,indent=2)+'\n');os.replace(tmp,a.out);print(result['status'])
if __name__=='__main__':main()
