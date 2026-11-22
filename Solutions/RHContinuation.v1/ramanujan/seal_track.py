#!/usr/bin/env python3
"""Seal exact accepted local research evidence; never an official Comparator receipt."""
from pathlib import Path
import argparse,json,hashlib,re,subprocess,datetime,tarfile
S=Path(__file__).resolve().parent;N=S.parents[2]
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--data-root',type=Path,required=True);a=p.parse_args();D=a.data_root.resolve()
def need(c,m):
 if not c:raise ValueError(m)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def read(p):return json.loads(Path(p).read_text())
r=read(S/'RESULTS.json');rows=[]
for name in ['fresh-base-v1','final-source-v1','source-component-v1','strong-source-v2','node-publication-v9']:
 j=read(D/name/'RESULT.json');need(j['status'].startswith('PASS'),'incomplete stage:'+name);peaks=[]
 for row in j.get('modules',[]):
  need(row['returncode']==0,'module failed');raw=row.get('resources',row.get('resource',row.get('resource_receipt_text','')));v=raw.split()
  if len(v)==2:peaks.append(int(v[1])*1024)
  if name=='node-publication-v9':
   src=D/name/'source'/Path(*row['module'].split('.')).with_suffix('.lean');need(sha(src)==row['source_sha256']and sha(row['original_source'])==row['source_sha256'],'final exact source changed');need(sha((D/name/'objects'/Path(*row['module'].split('.'))).with_suffix('.olean'))==row['object_sha256'],'final proof object changed');t=(D/name/'logs'/(row['module']+'.stdout')).read_text();need('sorryAx'not in t and 'Lean.ofReduce'not in t,'unaccepted axiom')
 rows.append({'stage':name,'status':j['status'],'modules':len(j.get('modules',[])),'elapsed_seconds':j.get('elapsed_seconds',j.get('seconds',sum(x.get('elapsed_seconds',0)for x in j.get('modules',[])))),'actual_max_single_compiler_worker_peak_RSS_bytes':max(peaks)if peaks else None,'receipt_sha256':sha(D/name/'RESULT.json'),'OOM':'No OOM kill/process failure observed; proof-stage cgroup event counters were not sampled.','evidence':str(D/name/'RESULT.json')})
r.update(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),stages=rows,actual_disk_bytes_at_seal=int(subprocess.check_output(['du','-sb',str(D)],text=True).split()[0]));r['completed']+=['actualJ=finiteMangoldt identity for everypositive realx','exact independent lower-height prime-power series andQ>=0','actualGMprimitive=integral and right-derivative jump handling','literal full4termGMsource→actualJ bound14+.2772sqrtx/log²x','canonicalRHPrimeCounting generic/boxed/B5 signed andabsoluteLi consumer, sameQcorrection strictgain']
r['completed']=list(dict.fromkeys(r['completed']));r['per_family_inputs']={'RamanujanGap.v3':r['mathematical_inputs'],'RHPrimeCounting.generic_transfer':['RH.v1.hypothesis','RHPrimeCounting.v1.gm_source','Buthe.v1.theorem_2_psi','Buthe.v1.theorem_2_li_minus_riemann_pi'],'RHPrimeCounting.boxed':['generic_transfer inputs','RHSmoothing.v1.box_psi'],'RHPrimeCounting.strict_gain':['RHSmoothing.v1.box_improves_B5'],'prime_power_series_and_nonnegative':[]};r['remaining']=[x for x in r['remaining']if x!='Actual GM weighted spectral-transfer proof and full610b optimizedTable1consumer'];r['remaining'].append('Stronger.076 spectral-correlation transfer and full610b optimizedTable1consumer; robust.2772GMprimitive relay is completed');r['remaining']=list(dict.fromkeys(r['remaining']));r['pure_scalar_pi_bound_claimed']=False
for q in [S/'RESULTS.json',D/'RESULTS.json']:q.write_text(json.dumps(r,indent=2)+'\n')
selected={}
for stage in ['final-source-v1','strong-source-v2','node-publication-v9']:
 for pth in (D/stage/'source').rglob('*.lean'):selected[str(pth.relative_to(D/stage/'source'))]=pth
for pth in (D/'source-component-v1/source').rglob('*.lean'):selected['source_component/'+str(pth.relative_to(D/'source-component-v1/source'))]=pth
proof_inventory=[]
for filename,src in sorted(selected.items()):
 for i,line in enumerate(src.read_text().splitlines(),1):
  m=re.match(r'\s*(?:theorem|lemma)\s+([A-Za-z0-9_]+)',line)
  if m:proof_inventory.append({'module_source_path':filename,'file':str(src),'declaration':m.group(1),'line':i,'source_sha256':sha(src),'scope':'fresh selected source module; final theorem closures audited separately'})
keys=[(x['file'],x['declaration'],x['line'])for x in proof_inventory]
need(len(keys)==len(set(keys)),'duplicate written-source declaration identity')
(S/'SELECTED_DECLARATION_INVENTORY.json').write_text(json.dumps({'scope':'Theorem/lemma declarations in selected fresh10foundation+7strong+14appended source modules and8reused C-component modules, deduplicated by canonical module path. Excludes146historical baseline and genericMathlib declarations. This is not a source-claim census or an all-network audit.','modules':sorted(selected),'declarations':proof_inventory,'duplicate_written_source_keys_rejected':True},indent=2)+'\n')
claim=[{'file':'LiPVDefinition.lean','declaration':'actual_li_hasDerivAt','status':'COMPLETE_NO_ANALYTIC_IDENTITY_PREMISE','domain':'x>1'},{'file':'ActualSourceResult.lean','declaration':'source_ramanujan_640b','status':'COMPLETE_SIX_ORIGINAL_ANALYTIC_INPUTS','claim':'actualRG>=1/12 forallrealx>=640b'},{'file':'ActualDynamicTail.lean','declaration':'actual_tail_144','status':'COMPLETE_RH_AND_BUTHE2016','claim':'actualRG(expL)>=1+14/L+144/L² forallL>=70'},{'file':'ActualFinalProfile.lean','declaration':'final_gap_profile','status':'COMPLETE_ACTUAL_NONLINEAR_CONSUMER'},{'file':'source_component/CoefficientPV.lean','declaration':'source_runs','status':'COMPLETE_REUSED_SOURCE_FIRST_COMPONENT','claim':'actual restricted C AST source correspondence and all21 typed uint64 executions; consumed in actual bound'},{'file':'ActualJIdentity.lean','declaration':'actual_J_eq_riemann','status':'COMPLETE_UNCONDITIONAL','domain':'allx>0'},{'file':'ActualJIdentity.lean','declaration':'actual_prime_power_series','status':'COMPLETE_UNCONDITIONAL','claim':'Q is exact summable lower-height prime-count series'},{'file':'ActualGMPrimitive.lean','declaration':'gmPrimitive_eq_integral','status':'COMPLETE_UNCONDITIONAL','domain':'allx>=0'},{'file':'ActualGMTransfer.lean','declaration':'GM_Q_Theorem1_1','status':'EXACT_PUBLISHED_LITERATURE_INPUT_NOT_A_PROOF','source':'1312.4465v4 Thm1.1 PDFp3; allfourterms'},{'file':'ActualGMClosed.lean','declaration':'actual_J_closed_GM','status':'COMPLETE_FROM_EXACT_GM_RH_BUTHE_INPUTS','claim':'actualJcorrection14+.2772sqrtx/log²x forallx>=exp8'},{'file':'IEANTN/Nodes/RHPrimeCounting/v1/Conclusions.lean','declaration':'boxed_absolute','status':'COMPLETE_TYPED_SOLUTION_CONDITIONAL_ON_DECLARED_NETWORK_INPUTS','claim':'actualpi-Li bound with actualQ andli2 offset; notpure scalarPNTpi'},{'file':'historical610b branch','declaration':'Table1_plus_spectral_transfer','status':'INCOMPLETE_PRESERVED','claim':'written/exact-rational only; stronger.076 notformalized'},{'file':'finite_scout','declaration':'full_missing_prefix','status':'NATIVE_SCOUT_COMPLETE_SOURCE_FIRST_PV_INCOMPLETE','claim':'twofull deterministicruns;2,480,042distinct countqueries; never promoted'}]
for row in claim:
 q=N/row['file'] if row['file'].startswith('IEANTN/') else S/row['file']
 if q.is_file():
  row['file']=str(q);row['source_sha256']=sha(q)
  lines=[i for i,line in enumerate(q.read_text().splitlines(),1)if re.match(r'\s*(?:theorem|lemma|def)\s+'+re.escape(row['declaration'])+r'\b',line)]
  row['line']=lines[0]if lines else None
 else:row['record_type']='explicit research gap, not a Lean declaration audit row'
(S/'CLAIM_LEDGER.json').write_text(json.dumps(claim,indent=2)+'\n')
source_paths=[q for q in S.rglob('*')if q.is_file()and '__pycache__'not in q.parts and q.suffix in ['.lean','.py','.c','.cpp','.md','.json','.html']and q.name not in ['FILE_MANIFEST.json']]
for rel in ['IEANTN/Nodes/RamanujanGap/v3','IEANTN/Nodes/RHPrimeCounting/v1','Solutions/RamanujanGap.v3','Solutions/RHPrimeCounting.v1']:
 source_paths.extend(q for q in (N/rel).rglob('*')if q.is_file()and q.name not in ['Challenge.lean','fingerprints.json'])
manifest=[{'path':str(q.relative_to(N)),'sha256':sha(q),'bytes':q.stat().st_size}for q in sorted(set(source_paths))];(S/'FILE_MANIFEST.json').write_text(json.dumps({'status':'EXACT_SOURCE_AND_REPORT_HASH_INVENTORY_NOT_COMPARATOR','files':manifest},indent=2)+'\n')
print(json.dumps({'status':'SEALED_ACCEPTED_LOCAL_MATHEMATICAL_TRACK','proof_stages':len(rows),'selected_declarations':len(proof_inventory),'source_report_files':len(manifest),'remaining_full_finite_PV':True,'official_comparator_receipt':False}))
