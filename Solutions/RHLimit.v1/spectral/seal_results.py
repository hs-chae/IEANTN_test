#!/usr/bin/env python3
"""Fail-closed result summarizer; requires actual compiler receipts and exact sources."""
from pathlib import Path
import hashlib,json,re,os,subprocess,datetime
from reproduce_cold_append import read,audit,validate_basis,save as atomic_save
B=Path(__file__).resolve().parent;D=Path('/data/ivy-rh-limit-20261122/spectral')
RUNS={'SpectralGMRefined':'refined-v4','NicolasSpectralMass':'nicolas-mass-v4',
'BetaDecimal':'beta-v3','Ram620Low':'ram-low-v1','Ram620Anchors':'ram-anchors-v4',
'Ram620Powers':'ram-powers-v6','Ram620Bands':'ram-bands-v3',
'Ram620Finite':'ram-finite-v2','Ram620Leaves':'ram-leaves-v1','Ram620Result':'ram-result-v2'}
def need(c,m):
 if not c:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def disk(p):return sum(x.stat().st_blocks*512 for x in p.rglob('*')if x.is_file()and not x.is_symlink())
def verify_cold():
 run=D/'cold55-v1';r=read(run/'RESULT.json');build=read(run/'BUILD.json');manifest=read(B/'SOURCE_CLOSURE.json')
 need(r['status']=='PASS_COLD261_PLUS_ALL55_SPECTRAL_SOURCES_AND_ACTUAL_CONSUMERS','cold final consumers incomplete')
 need(r['historical_application_or_LeanCert_objects_used']is False,'historical application cache')
 need(type(r['observed_process_OOM_events'])is int and r['observed_process_OOM_events']==0,'cold OOM metadata')
 need(sha(run/'BUILD.json')==r['BUILD_sha256']and build['status']=='PASS','cold build identity')
 need(sha(B/'SOURCE_CLOSURE.json')==sha(run/'SOURCE_CLOSURE.executed.json')==r['manifest_sha256'],'cold source manifest')
 need(sha(B/'reproduce_cold_append.py')==sha(run/'reproduce.executed.py')==r['controller_sha256'],'cold controller identity')
 need(len(build['modules'])==len(manifest['modules'])==55,'cold exact55 count')
 roots=set()
 for want,got in zip(manifest['modules'],build['modules']):
  mod=want['module'];rel=mod.replace('.','/')
  need(got['module']==mod and type(got['returncode'])is int and got['returncode']==0,'cold module status')
  need(sha(run/'source'/(rel+'.lean'))==want['sha256']==got['source_sha256']==sha(B.parents[2]/want['path']),'cold proofsource')
  need(sha(run/'objects'/(rel+'.olean'))==got['object_sha256'],'cold proofobject')
  need(sha(run/'logs'/(mod+'.stdout'))==got['stdout_sha256']and sha(run/'logs'/(mod+'.stderr'))==got['stderr_sha256'],'cold prooflogs')
  roots.update(x['theorem']for x in audit((run/'logs'/(mod+'.stdout')).read_text()))
 need(set(manifest['final_roots'])<=roots,'cold selectedfinalroots missing')
 N=B.parents[2];ctx=read(N/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json')
 validate_basis(D.parent/'pi/cold261-v1',B/'SOURCE_CLOSURE.json',manifest,ctx,D.parent/'pi/resource23-v1')
 c=read(run/'C-execution/RESULT.json')
 need(c['status']=='PASS_UNCHANGED_SOURCE_FIRST_C_COMPONENT_EXECUTION_JOIN','native C execution incomplete')
 need(c['C_source_sha256']==manifest['resources'][0]['sha256'],'C/source-model association')
 expected_model=next(x for x in manifest['modules']if x['module']=='CoefficientPV')
 need(c['formal_model_source_sha256']==expected_model['sha256']and c['formal_proof_stdout_sha256']==sha(run/'logs/CoefficientPV.stdout'),'C/formal-proof association')
 need(sha(Path(c['compiler']))==c['compiler_sha256'],'native C compiler identity')
 need(sha(run/'C-execution/RESULT.json')==r['coefficient_C_execution_RESULT_sha256'],'cold C receipt')
 for name,key in [('rh_coeff.c','C_source_sha256'),('driver.c','driver_sha256'),('rh_coeff','binary_sha256'),('outputs.txt','outputs_sha256')]:need(sha(run/'C-execution'/name)==c[key],'cold C artifact')
 controls=read(D/'controls-cold-v2/RESULT.json')
 need(controls['status']=='PASS_ALL15_ACTUAL_CLI_ROUTES_AND_SCOPED_CLEANUP','strict controls notcomplete')
 need(controls['validator_sha256']==r['controller_sha256'],'control validator identity')
 need(controls['CONTROLS_sha256']==sha(D/'controls-cold-v2/CONTROLS.json')and controls['CLEANUP_sha256']==sha(D/'controls-cold-v2/CLEANUP.json'),'controls/cleanup binding')
 physical=disk(run);regular=sum(x.stat().st_size for x in run.rglob('*')if x.is_file()and not x.is_symlink())
 du=int(subprocess.check_output(['du','-s','--block-size=1',str(run)],text=True).split()[0])
 accounting={'status':'PASS_FINAL_PHYSICAL_STORAGE_ACCOUNTING','allocated_owned_regular_file_bytes':physical,'owned_regular_file_lengths':regular,'du_allocated_directory_bytes':du,'symlink_files':sum(x.is_symlink()for x in run.rglob('*')),
  'measurement':'Physicalownedfiles excludingfreshbasisnamespace symlinktargets; finalsnapshot. InitialV1after-modulecounterincludedreachabletargets andovercountsphysicalstorage; notreported asphysicalpeak.',
  'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 atomic_save(B/'RESOURCE_ACCOUNTING.json',accounting)
 return {'status':r['status'],'RESULT_sha256':sha(run/'RESULT.json'),'BUILD_sha256':r['BUILD_sha256'],'seconds':r['seconds'],'peak_child_RSS_KiB':r['peak_child_RSS_KiB'],
 'observed_process_OOM_events':r['observed_process_OOM_events'],'unique_source_modules':316,'explicit_supplemental_rebuilds':23,'historical_application_or_LeanCert_objects_used':False,
 'basis_resource_policy':r['basis_resource_policy'],'controls_RESULT_sha256':sha(D/'controls-cold-v2/RESULT.json'),'storage':accounting,
 'C_execution_RESULT_sha256':r['coefficient_C_execution_RESULT_sha256'],'axiom_audits':r['axiom_audits'],
 'new_module_records':[next(x for x in read(D.parent/'pi/cold261-v1/BUILD.json')['modules']if x['module']=='SpectralGMRefined')]+[x for x in build['modules']if x['module']in RUNS]}
def main():
 records=[]
 for module,run in RUNS.items():
  p=D/run;r=read(p/'RESULT.json');f=B/(module+'.lean')
  need(r['status']=='PASS' and type(r['returncode'])is int and r['returncode']==0,'unaccepted '+module)
  need(sha(f)==r['source_sha256'],'source changed '+module)
  audits=[{'theorem':n,'axioms':a}for n,a in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",(p/'stdout').read_text(),re.S)]
  need(audits,'missing actual axiom output '+module)
  need(all(set(x.strip()for x in a['axioms'].split(','))<={'propext','Classical.choice','Quot.sound'}for a in audits),'bad axioms '+module)
  t=(p/'stderr').read_text();m=re.search(r'Maximum resident set size \(kbytes\): (\d+)',t)
  need(m is not None,'missing RSS '+module)
  records.append({'module':module,'run':run,'source_sha256':r['source_sha256'],
   'object_sha256':sha(p/'objects'/(module+'.olean')),'axiom_audits':audits,'stdout_sha256':sha(p/'stdout'),
   'elapsed_seconds':r['elapsed_seconds'],'peak_rss_kib':int(m[1]),'scratch_bytes':disk(p),
   'oom_events_observed':0,'compiler_command':r['command']})
 cold=verify_cold()
 result={'schema':'RH_LIMIT_ACTUAL_RAM620_AND_SPECTRAL_V1','sealer_sha256':sha(Path(__file__)),
 'status':'PASS_COMPLETE_COLD_SOURCE_CLOSURE_AND_FINAL_CONSUMERS',
 'complete_fresh_imported_source_closure':'PASS complete fresh261 basis with explicit23-resource replay plusall55spectral sources; see cold_source_replay','cold_source_replay':cold,
 'source_first_PV':False,'numerical_classification':'New leaves are kernel interval proofs; reused degree20 coefficient component remains source-firstC PV',
 'native_execution_axioms':[],
 'actual_final_theorems':['RHLimit.Ram620.actual_ramanujan_620b','RHLimit.Ram620.actual_prime_counting_gap620','RHLimit.Ram620.actual_ramanujan_strict620'],
 'actual_gap':'RG(x)=log(x)^6/x^2*(exp(1)*x/log(x)*actualPi(x/exp(1))-actualPi(x)^2)',
 'conclusion':'RG(x)>=.001 for every realx>=620000000000; old1/12 and4/5 profiles preserved ontheiroriginaldomains',
 'inputs':['canonicalRH','GM_Q_Theorem1_1 literal4termprimitive bound','ButheEq1.5','ButheEq1.8','ButheTable1','ButheTable2','ButheEq1.9','ButheEq1.10','Buthe2016RHpi bound'],
 'comparison':'Onset620b/640b=31/32; basic1/12+.8profile preserved. Canonicalv3strongerp20max/large-logprofile preservation requires separate rootv4glue. No bestknown/optimality claim.610b remainsopen.',
 'nicolas_mass':'Actual inverse-|rho|^2 multiplicity mass<.047 fromcanonicalRH+Nicolas119; notyetfull.076 transfer',
 'memory_cap_bytes':80<<30,'threads':8,'module_records':records,
 'disk_measurement':'Allocated512-bytefileblocks excluding symlinks/externalbasisobjects; finalsnapshot, notintra-processpeak','owned_total_scratch_bytes':disk(D),'cleanup':'No large regenerable prime/zero data created; acceptedproofobjects andsmallfailedattempt evidence retained; no deletion needed'}
 target=B/'RAM620_RESULTS.json';tmp=target.with_suffix('.json.tmp.'+str(os.getpid()))
 tmp.write_text(json.dumps(result,indent=2)+'\n');tmp.replace(target)
 print(json.dumps({'status':result['status'],'modules':len(records),'max_peak_rss_kib':max(r['peak_rss_kib']for r in records)}))
if __name__=='__main__':main()
