"""Inventory only. No copy/archive/publication or scientific execution."""
from pathlib import Path,PurePosixPath
import argparse,ast,hashlib,io,json,math,re,tarfile,zipfile
A=Path(__file__).resolve().parent;R=A.parents[1];W=R.parent
def need(x,m):
 if not x:raise ValueError(m)
def pairs(xs):
 d={}
 for k,v in xs:need(k not in d,'duplicate JSON key');d[k]=v
 return d
def finite(s):
 v=float(s);need(math.isfinite(v),'nonfinite or overflow JSON float');return v
def reject_constant(s):raise ValueError('nonfinite JSON constant '+s)
def load(p):return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_float=finite,parse_constant=reject_constant)
def sha(b):return hashlib.sha256(b).hexdigest()
def readpin(z):
 p=Path(z['path']);need(p.is_file() and sha(p.read_bytes())==z['sha256'],'exact selected input pin');return p
def safe_name(s):
 need(isinstance(s,str) and '\\' not in s and '\x00' not in s,'canonical POSIX member text');p=PurePosixPath(s);need(not p.is_absolute() and '..' not in p.parts and s not in ('','.') and str(p)==s,'safe canonical relative archive member');return s
def inspect_bytes(name,b,depth=0):
 """Inspect actual JSON schemas and every nested archive member, not filenames alone."""
 flags=[];schemas=[];members=[];need(depth<=8,'bounded nested archive depth')
 low=name.lower();parts=PurePosixPath(low).parts
 forbidden={'memory','.codex','.cache','__pycache__','site-packages','node_modules','negative-fixtures','synthetic-fixtures'}
 if forbidden.intersection(parts) or re.search(r'(?:^|/)(?:auth|credentials|private_context|native[._-]events?|transcript)(?:[./_-]|$)',low):
  flags.append('FORBIDDEN_OR_REQUIRES_EXPLICIT_PRIVATE_CONTEXT_REVIEW')
 if re.search(rb'(?:(?<![A-Za-z0-9_])sk-[A-Za-z0-9_-]{24,}|-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----|mfa\.[A-Za-z0-9_-]{40,})',b):flags.append('POTENTIAL_CREDENTIAL_BYTES')
 if low.endswith(('.json','.jsonl')):
  z=[json.loads(line,object_pairs_hook=pairs) for line in b.split(b'\n') if line.strip()] if low.endswith('.jsonl') else json.loads(b,object_pairs_hook=pairs);keys=set();bad=[]
  def walk(v,where=''):
   if isinstance(v,dict):
    if isinstance(v.get('role'),str) and v['role'] in {'analysis','assistant','developer','system','user'} and v.get('content') not in (None,'',[],{}):bad.append(where+'/ROLE_CONTENT_PRIVATE_CONTEXT_REVIEW')
    if v.get('type')=='reasoning' and (v.get('text') or v.get('summary')):bad.append(where+'/NATIVE_REASONING_REVIEW')
    for k,t in v.items():
     keys.add(k);q=where+'/'+k
     if k.lower() in {'messages','system_prompt','developer_prompt','user_prompt','prompt','private_reasoning','access_token','refresh_token','id_token','api_key','credentials'} and t not in (None,False,'',[],{}):bad.append(q)
     if k=='private_reasoning_collected' and t is not False:bad.append(q)
     walk(t,q)
   elif isinstance(v,list):
    for i,t in enumerate(v):walk(t,where+'/'+str(i))
  walk(z);schemas.append({'member':name,'top_level_type':type(z).__name__,'all_distinct_field_names':sorted(keys),'prohibited_nonempty_fields':bad})
  if bad:flags.append('JSON_SCHEMA_PRIVATE_CONTENT_REVIEW_REQUIRED')
 stream=io.BytesIO(b)
 iszip=zipfile.is_zipfile(stream);stream.seek(0)
 istar=False
 if not iszip and (low.endswith(('.tar.gz','.tgz','.tar'))):
  try:
   with tarfile.open(fileobj=stream,mode='r:*') as t:istar=True
  except tarfile.TarError:flags.append('DECLARED_ARCHIVE_UNREADABLE')
  stream.seek(0)
 if iszip:
  with zipfile.ZipFile(stream) as z:
   seen=set()
   for f in z.infolist():
    safe_name(f.filename[:-1] if f.is_dir() and f.filename.endswith('/') else f.filename);need(f.filename not in seen,'duplicate nested zip member');seen.add(f.filename)
    if f.is_dir():continue
    need((f.external_attr>>16)&0o170000!=0o120000,'no nested symlink')
    c=z.read(f);sub=inspect_bytes(f.filename,c,depth+1);members.append({'name':f.filename,'sha256':sha(c),'size':len(c),'inspection':sub});flags.extend('NESTED:'+x for x in sub['flags'])
 elif istar:
  with tarfile.open(fileobj=stream,mode='r:*') as t:
   seen=set()
   for f in t:
    safe_name(f.name[:-1] if f.isdir() and f.name.endswith('/') else f.name);need(f.name not in seen,'duplicate nested tar member');seen.add(f.name)
    if f.isdir():continue
    need(f.isfile(),'no nested special/hard/symbolic links');c=t.extractfile(f).read();sub=inspect_bytes(f.name,c,depth+1);members.append({'name':f.name,'sha256':sha(c),'size':len(c),'inspection':sub});flags.extend('NESTED:'+x for x in sub['flags'])
 return {'flags':sorted(set(flags)),'JSON_schema_readbacks':schemas,'nested_members':members,'actual_bytes_inspected':len(b)}
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--snapshot',type=Path,required=True);ap.add_argument('--human-html',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--frontier-selection',type=Path);ap.add_argument('--source-map',type=Path);ap.add_argument('--browser-receipt',type=Path);ap.add_argument('--additional-selection',type=Path,action='append',default=[]);q=ap.parse_args();need(not q.out.exists(),'fresh inventory output');snapshot=load(q.snapshot);need(snapshot['currently_Root_finalized_case_count']==24,'all24 current Root mathematical seals')
 rows={};pending=[];private=load(q.snapshot.parent/'INPUT_HASH_MANIFEST_PRIVATE.json');by_hash={}
 for z in private['inputs']:by_hash.setdefault(z['sha256'],[]).append(Path(z['path']))
 def add(p,dest,category,gzip_json=True):
  p=Path(p).resolve();need(p.is_file() and not p.is_symlink(),'selected ordinary source file');safe_name(dest);b=p.read_bytes();h=sha(b)
  if dest in rows:need(rows[dest]['sha256']==h,'public destination collision');return
  rows[dest]={'source_path':str(p),'archive_path':dest,'sha256':h,'size':len(b),'category':category,'gzip_json':bool(gzip_json and p.suffix=='.json' and len(b)>=65536),'privacy':inspect_bytes(p.name,b)}
 def original(p,category):
  p=Path(p).resolve()
  dest='evidence/study/'+str(p.relative_to(R)) if p.is_relative_to(R) else 'evidence/external/'+sha(p.read_bytes())[:20]+'/'+p.name
  add(p,dest,category,category not in {'ROOT_MATHEMATICAL_FINALIZATION','ROOT_COMPLETE_MATHEMATICAL_ASSESSMENT','ORIGINAL_AND_LATER_ROOT_MATHEMATICAL_ASSESSMENT'})
 def resolve_public(v):
  if v is None:return None
  if 'study_relative_path' in v:p=R/v['study_relative_path']
  elif 'workspace_relative_path' in v:p=W/v['workspace_relative_path']
  else:
   ps=[p for p in by_hash.get(v['sha256'],[]) if p.is_file() and p.name==v['basename']];need(ps,'every external public pin resolves to exact private original evidence');p=ps[0]
  need(sha(p.read_bytes())==v['sha256'],'actual public-to-original evidence hash');return p
 add(R/'reports/SOURCE_LIBRARY_MANIFEST.json','SOURCE_LIBRARY_MANIFEST.json','EXACT_FROZEN_CORPUS_AND_PRIMARY_SOURCE_URLS',False)
 add(R/'reports/README_REPRODUCTION_AND_RESULTS.md','README.md','FIRST_USE_COMPLETE_STUDY_README',False)
 add(q.human_html,'report.html','COMPLETE_STANDALONE_HUMAN_REPORT',False);add(q.human_html.with_suffix('.md'),'report.md','COMPLETE_SAME_HUMAN_MARKDOWN',False);add(q.snapshot,'ALL24_PUBLIC_SCIENTIFIC_STATUS.json','PUBLIC_MODEL_RESOURCE_AND_24_48_TABLES',False)
 add(q.human_html.with_suffix('.md'),q.human_html.with_suffix('.md').name,'BYTE_IDENTICAL_HUMAN_MARKDOWN_LINK_ALIAS',False)
 for p in sorted((q.snapshot.parent/'accepted-floors').glob('*.json')):add(p,'accepted-floors/'+p.name,'LATEST_ACCEPTED_QUALIFIED_FLOOR',False)
 for name in ['ANALYTIC_ENGINE_EXPOSITION.md','ANALYTIC_ENGINE_EXPOSITION_24CASE_REVIEW_DRAFT_V2.html','PUBLIC_EVIDENCE_SELECTION_PLAN.md']:
  add(R/'reports'/name,'paper/'+name,'CURRENT_PAPER_OR_PUBLICATION_PLAN',False)
 add(R/'reports/FINAL_ANALYTIC_ENGINE_EXPOSITION.html','paper/ANALYTIC_ENGINE_EXPOSITION.html','CANONICAL_ACCEPTED_PAPER_BYTE_IDENTICAL_ALIAS',False)
 old=W/'ieantn-deep-tertiary-exposure-a-20261117'
 for p in sorted((old/'sources/primary-papers').iterdir()):
  if p.is_file():add(p,'original-papers/'+p.name,'ORIGINAL_SEVEN_PAPER_PAIRS',False)
 for name in ['STIXGeneral.ttf','LICENSE_STIX']:add(old/'reports/fonts'/name,'fonts/'+name,'LICENSED_OFFLINE_MATH_FONT',False)
 wheelplan=R/'coordinator-private/twenty-normalized-frontiers-v1/PLOT_EXECUTION_PLAN_UNSIGNED_V4.json'
 original(wheelplan,'EXACT_OFFLINE_PLOT_DEPENDENCY_PLAN')
 wheels=sorted(wheelplan.parent.glob('plot-wheels/*.whl'));need(len(wheels)==11,'all11 pinned offline figure wheels')
 wp=wheelplan.parent/'PLOT_WHEEL_SOURCE_RECEIPT.json';wr=load(wp);original(wp,'EXACT_ELEVEN_OFFLINE_WHEEL_VERSIONS_AND_HASHES');wb={z['wheel']:z for z in wr['wheels']};need(len(wb)==11,'whole original wheel receipt')
 for p in wheels:
  need(p.name in wb and sha(p.read_bytes())==wb[p.name]['sha256'] and p.stat().st_size==wb[p.name]['bytes'],'each exact originally pinned plotting wheel')
  add(p,'reproduction/plot-wheels/'+p.name,'OFFLINE_FIGURE_WHEEL_WITH_EMBEDDED_LICENSES',False)
 for name in ['prepare_inventory.py','prepare_inventory_v11.py','prepare_current_public_source_map.py','package_evidence.py','verify_and_reconstruct.py','README.md']:
  p=A/name
  if p.is_file():add(p,'reproduction/package-tools/'+name,'PUBLIC_REPRODUCTION_AND_PACKAGE_TOOLS',False)
 for p in sorted((R/'reproduction').iterdir()):
  if p.is_file() and p.suffix in {'.md','.py','.json'}:add(p,'reproduction/'+p.name,'EXACT_OFFLINE_ALL24_REPRODUCTION_COMPANION',False)
 for p in sorted((R/'reproduction/paper-wheels').glob('*.whl')):add(p,'reproduction/paper-wheels/'+p.name,'EXACT_EXISTING_STATIC_PAPER_PRODUCER_DEPENDENCY_WHEEL',False)
 paper_controls=R/'coordinator-private/offline-paper-reproduction-controls-v1/RESULT_V2_STRICT_CURRENT.json'
 if paper_controls.is_file():
  original(paper_controls,'ACTUAL_CLEAN_OFFLINE_PAPER_REGENERATION_AND_ALL_PROCESS_OPEN_TRACE_RECEIPT')
  pc=load(paper_controls)
  for z in pc['normal_O_OO']:original(readpin(z['receipt']),'ACTUAL_PAPER_REGENERATION_OPTIMIZATION_MODE_RECEIPT')
  for key in ['external_source_plan','external_actual_receipt','all_process_open_trace','strict_metadata_rejection_receipt','historical_pre_strict_receipt','historical_pre_strict_source']:original(readpin(pc[key]),'ACTUAL_EXTERNAL_SOURCE_ONLY_PAPER_REGENERATION_EVIDENCE')
 else:pending.append({'category':'CLEAN_OFFLINE_PAPER_REGENERATION_REQUIRED'})
 report_tools=A.parent/'final-report-assembly-preparation-v1'
 for name in ['render_main_report_complete_v3.py','render_main_report_complete_v4.py','readable_markdown_from_static_html_v3.py','readable_markdown_from_static_html_v4.py','verify_complete_renderer_v4.py','finalize_report_data.py','ALL48_QUANTITATIVE_EXCERPTS_V2.json']:
  add(report_tools/name,'reproduction/report-tools/'+name,'EXACT_OFFLINE_REPORT_REGENERATION_SOURCE',False)
 for name in ['build_final_report.py','embed_offline_math_font.py','final_report.css']:
  add(old/'scripts'/name,'reproduction/paper-tools/'+name,'ORIGINAL_UNCHANGED_STATIC_PAPER_RENDERER',False)
 for rel in ['protocol/FOLLOWUP_DESIGN.json','protocol/ROOT_ALL24_CANONICAL_REVIEW_ROUTER_V1.json','protocol/CUMULATIVE_RESOURCE_ANALYSIS_AMENDMENT_V1.json']:
  original(R/rel,'EXACT_PUBLIC_EXPERIMENT_DESIGN_IDENTITY_AND_RESOURCE_POLICY')
 design=load(R/'protocol/FOLLOWUP_DESIGN.json');corpus=design['corpus'];cp=Path(corpus['source_manifest']);need(sha(cp.read_bytes())==corpus['source_manifest_sha256'],'exact frozen common paper corpus manifest');original(cp,'EXACT_FROZEN_COMMON_CORPUS_MANIFEST')
 ledger=R/'evidence/final24-actual-resource-ledger-v1/FINAL24_ACTUAL_NUMERICAL_RESOURCE_LEDGER.json'
 if ledger.is_file():
  original(ledger,'ALL24_ACTUAL_UNIQUE_NUMERICAL_RESOURCE_LEDGER');ld=load(ledger);need(ld['completed_unique_cases']==24 and ld['total_required_routes']==595,'actual complete24 and595routeledger')
  for ref in ld['input_references_checked']:original(readpin(ref),'ALL24_ACTUAL_RESOURCE_LEDGER_EXACT_INPUT_REFERENCE')
  for lp in sorted(ledger.parent.iterdir()):
   if lp.is_file() and lp.suffix in {'.json','.tsv','.md'}:original(lp,'ALL24_ACTUAL_RESOURCE_LEDGER_REGENERATION_RECEIPT')
 else:pending.append({'category':'ALL24_ACTUAL_RESOURCE_LEDGER_REQUIRED'})
 if q.source_map is not None:add(q.source_map,'PUBLIC_SOURCE_MAP.json','EXACT_ORIGINAL_TO_PUBLIC_SOURCE_RESOLUTION_MAP',False)
 else:pending.append({'category':'FINAL_PUBLIC_SOURCE_MAP_REQUIRED'})
 if q.frontier_selection is not None:
  fs=load(q.frontier_selection);need(isinstance(fs.get('assets'),list) and fs['assets'],'exact pinned final comparison assets')
  for z in fs['assets']:
   p=readpin(z);need(p.stat().st_size==z['bytes'],'exact final comparison asset length');add(p,z['archive_path'],'FINAL24_SOURCE_COMPLETE_QUANTITATIVE_COMPARISON_OR_FIGURE',z.get('gzip_json',True))
  original(q.frontier_selection,'EXACT_FINAL24_COMPARISON_ASSET_SELECTION')
 else:pending.append({'category':'FINAL24_QUANTITATIVE_COMPARISON_AND_FIGURES_PENDING_EXACT_FINAL_PINS'})
 for selection in q.additional_selection:
  selected=load(selection);need(isinstance(selected.get('assets'),list),'explicit supplementary asset list')
  for z in selected['assets']:
   p=readpin(z);need(p.stat().st_size==z['bytes'],'supplementary source exact length');need(type(z.get('gzip_json',True)) is bool,'supplementary compression flag explicit boolean');add(p,z['archive_path'],z.get('category','EXPLICIT_CURRENT_REPRODUCTION_OR_SOURCE_ACCEPTANCE_ASSET'),z.get('gzip_json',True))
  original(selection,'EXACT_SUPPLEMENTARY_SOURCE_AND_ACCEPTANCE_ASSET_SELECTION')
 if q.browser_receipt is not None:original(q.browser_receipt,'ACTUAL_FINAL_PUBLICATION_DESKTOP_MOBILE_MATH_AND_KEYBOARD_RECEIPT')
 else:pending.append({'category':'FINAL_ACTUAL_BROWSER_VISUAL_RECEIPT_REQUIRED'})
 processing=R/'evidence/FINAL_PUBLICATION_PROCESSING_RUNTIME.json';need(processing.is_file(),'exact generic publication processing runtime');original(processing,'EXACT_GENERIC_PUBLICATION_RUNTIME_DISTINCT_FROM_SCIENTIFIC_TOOLS')
 compatibility=R/'evidence/ROOT_C022_FINAL_STATUS_ENUM_COMPATIBILITY_CORRIGENDUM.json'
 if compatibility.is_file():original(compatibility,'METADATA_ENUM_COMPATIBILITY_ONLY_NO_MATHEMATICAL_CHANGE')
 for key in ['original_snapshot_before_completion_labels','final_comparison_acceptance']:
  if key in snapshot:original(readpin(snapshot[key]),'ADDITIVE_FINAL_COMPLETION_METADATA_PROVENANCE_OR_ROOT_COMPARISON_ACCEPTANCE')
 sr=q.snapshot.with_suffix('.FINALIZATION_RECEIPT.json')
 if sr.is_file():original(sr,'RECURSIVE_ALLOWLIST_FINAL_DATA_COMPLETION_LABEL_RECEIPT')
 selected_audit_pins=set()
 for stage in snapshot['stages']:
  cid=stage['candidate_id'];fin=stage['latest_Root_finalization'];fp=R/fin['study_relative_path'];need(sha(fp.read_bytes())==fin['sha256'],'latest final public pin');original(fp,'ROOT_MATHEMATICAL_FINALIZATION');f=load(fp)
  for old in sorted(fp.parent.glob('FINAL_*_PORTFOLIO_ROOT*.json')):
   if old!=fp:original(old,'HISTORICAL_SUPERSEDED_ROOT_FINALIZATION_NOT_CURRENT_VERDICT')
  ar=[v for v in f.values() if isinstance(v,dict) and {'path','sha256'}<=v.keys() and 'ASSOCIATION' in Path(v['path']).name];need(len(ar)==1,'one exact current Root assessment');assocpath=readpin(ar[0]);original(assocpath,'ROOT_COMPLETE_MATHEMATICAL_ASSESSMENT');assoc=load(assocpath)
  for k,v in assoc.items():
   if isinstance(v,dict) and {'path','sha256'}<=v.keys() and any(t in k.lower() for t in ['audit','census','correction','corrigendum','retention','qualified','truth_object','validated','source_drain','root_actual']):
    p=readpin(v);original(p,'ROOT_SOURCE_PROOF_DOMAIN_AUDIT_OR_CORRECTION');selected_audit_pins.add(str(p))
  for k in ['candidate_manifest','reviewed_source_view_manifest','review_manifest']:
   if k not in assoc:continue
   lp=readpin(assoc[k]);original(lp,'EXACT_LOCKED_SCIENTIFIC_SOURCE_MANIFEST');lock=load(lp)
   for z in lock['files']:
    p=lp.parent/z['path'];need(sha(p.read_bytes())==z['sha256'],'every selected locked payload');original(p,'LOCKED_CANDIDATE_OR_PUBLIC_MATHEMATICAL_REVIEW')
    if k=='candidate_manifest' and p.suffix.lower() in {'.md','.py','.c','.cc','.cpp','.h','.hpp'}:add(p,'source-code/'+cid+'/'+p.name,'CURRENT_WRITTEN_PROOF_AND_CODE_LINK_TARGET',False)
  for h in stage.get('historical_Root_assessments',[]):
   hp=resolve_public(h['assessment_source']);original(hp,'ORIGINAL_AND_LATER_ROOT_MATHEMATICAL_ASSESSMENT')
  for typ in ['research_physical_results','review_physical_results']:
   for metadata in stage[typ]:
    p=resolve_public(metadata['source']);result=load(p);need(result.get('private_reasoning_collected') is False and result.get('credentials_mounted_in_worker') is False,'actual source-associated model-result privacy indicators');original(p,'SCHEMA_INSPECTED_PUBLIC_MODEL_AND_EFFORT_SOURCE_METADATA')
  for z in stage['actual_numerical_reproductions']:
   for key in ['actual_full_readback','actual_final_receipt','actual_numerical_receipt','actual_resource_receipt','actual_executed_job','actual_job_Root_finalization','durable_copy_manifest','GNU_time_source']:
    p=resolve_public(z[key])
    if p is not None:original(p,'ACTUAL_NUMERICAL_READBACK_JOB_OUTPUT_OR_RESOURCE')
   raw=load(resolve_public(z['actual_full_readback']))
   if 'archive' in raw:original(readpin(raw['archive']),'ACTUALLY_EXECUTED_PORTABLE_SOURCE_ARCHIVE')
   final=load(resolve_public(z['actual_final_receipt']));original(readpin(final['Root_authority']),'ACTUAL_NUMERICAL_ROOT_EXECUTION_AUTHORITY')
   # Every durable member is rehashed and included, not only its manifest.
   v=z['durable_copy_manifest']
   if v is not None:
    dm=load(resolve_public(v));need(isinstance(dm['files'],list) and dm['files'],'complete actual durable census')
    for member in dm['files']:
     p=readpin(member['durable']);need(member['original']['sha256']==member['durable']['sha256'] and p.stat().st_size==member['bytes'],'whole actual original-to-durable identity');original(p,'ACTUAL_COMPLETE_DURABLE_NUMERICAL_OUTPUT')
 missing=[s['candidate_id'] for s in snapshot['stages'] if not s['clean_relocated_full_reproduction_completed']]
 examples=A.parent/'final-report-assembly-preparation-v1/ALL48_QUANTITATIVE_EXCERPTS_V2.json'
 add(examples,'ALL48_QUANTITATIVE_EXCERPTS.json','REPRESENTATIVE_SOURCE_BOUND_EXCERPTS_NOT_COVERAGE_SELECTION',False)
 for ex in load(examples)['rows']:
  for z in ex['exact_accepted_objects']:
   p=Path(z['source']['file']);need(sha(p.read_bytes())==z['source']['sha256'],'exact source excerpt file');add(p,'source-code/'+ex['candidate_id']+'/'+p.name,'EXACT_HUMAN_QUANTITATIVE_EXCERPT_SOURCE',False)
 finalprep=R/'coordinator-private/portable-v2-C022-final24-actual-preparation-v4/PREPARATION_RECEIPT.json';finalapproval=finalprep.parent/'ROOT_APPROVED_C022_FINAL24_PORTABLE_EXECUTION.json'
 if finalprep.is_file() and finalapproval.is_file():
  approved=load(finalapproval);need(sha(finalapproval.read_bytes())=='397aabf6fca3593807a4e23274f668e042b77c5cf4c936bc14825ff5929f5db1' and approved['status']=='ROOT_SIGNED_EXACT_C022_CURRENT_FULL_PORTABLE_EXECUTION_NOT_DISPATCHED','exact Root aggregate final24 authority');sap=readpin(approved['source_approval']);need(load(sap)['reviewed_by']=='/root','actual pinned Root source approval');pr=load(finalprep)
  need(pr['archive']['sha256']=='1da943a15aaebeb949a5ef472e82e97bb0d349d1914f2f0c01fbfe6f08a1de3a','exact Root-reviewed7303-member final24 archive')
  companion=R/'reproduction/verify_extract_final24.py';constants={}
  for node in ast.parse(companion.read_text()).body:
   if isinstance(node,ast.Assign) and isinstance(node.value,ast.Constant):
    for target in node.targets:
     if isinstance(target,ast.Name):constants[target.id]=node.value.value
  if constants.get('ARCHIVE_SHA')!=pr['archive']['sha256'] or constants.get('RECEIPT_SHA')!=pr['archive_receipt']['sha256']:
   pending.append({'category':'REPRODUCTION_COMPANION_HARDCODED_PINS_NEED_CURRENT_V4_SOURCE_REFRESH','actual_constants':{k:constants.get(k) for k in ['ARCHIVE_SHA','RECEIPT_SHA']},'current_archive':pr['archive'],'current_receipt':pr['archive_receipt']})
  original(finalprep,'ROOT_REVIEWED_ALL24_SOURCE_PREPARATION_NOT_ALL24_EXECUTION');original(finalapproval,'ROOT_FINAL24_SOURCE_AND_ONE_C022_EXECUTION_APPROVAL');original(sap,'EXACT_ROOT_ALL24_PORTABLE_SOURCE_APPROVAL')
  for key in ['archive','archive_receipt','source_manifest','config']:original(readpin(pr[key]),'CURRENT_ALL24_PORTABLE_SOURCE_AND_EXACT_MANIFESTS')
  failure=R/'evidence/C022_FIRST_ACTUAL_PORTABLE_FRAMING_FAILURE_FULL_DRAIN_AND_DURABLE_READBACK.json'
  if failure.is_file():
   fail=load(failure);need(fail['execution_drained'] and fail['reservation_released'] and fail['no_FINAL_REPRODUCTION_RECEIPT_exists'],'actual failed whole replay retained as failure');original(failure,'ACTUAL_FAILED_FULL_REPLAY_READBACK_NOT_SUCCESS')
   for key in ['actual_resource','actual_partial_outcomes','exact_recovered_public_source_provenance','durable_copy_manifest']:original(readpin(fail[key]),'ACTUAL_FAILED_FULL_REPLAY_SOURCE_AND_PARTIAL_EVIDENCE')
   dm=load(readpin(fail['durable_copy_manifest']))
   for member in dm['files']:
    p=readpin(member['durable']);need(p.stat().st_size==member['bytes'] and member['original']['sha256']==member['durable']['sha256'],'exact failed-attempt durable bytes');original(p,'ACTUAL_FAILED_FULL_REPLAY_DURABLE_OUTPUT')
   oldprep=load(R/'coordinator-private/portable-v2-C022-final24-actual-preparation-v2/PREPARATION_RECEIPT.json')
   for key in ['archive','archive_receipt']:original(readpin(oldprep[key]),'ACTUALLY_USED_FAILED_C022_SOURCE_ARCHIVE_PRESERVED_NOT_CURRENT_PIPELINE')
 else:pending.append({'category':'FINAL_ALL24_NUMERICAL_SOURCE_ARCHIVE_PENDING_ROOT_PIN','do_not_substitute_old21_archive':True})
 if missing:pending.append({'category':'MISSING_ACTUAL_FULL_CLEAN_NUMERICAL_READBACKS','candidate_ids':missing})
 links=[];materialized=set(rows)|{name+'.gz' for name,z in rows.items() if z['gzip_json']}
 for name in ['report.html','paper/ANALYTIC_ENGINE_EXPOSITION_24CASE_REVIEW_DRAFT_V2.html']:
  z=rows[name];text=Path(z['source_path']).read_text()
  for href in re.findall(r'href=[\"\']([^\"\']+)',text):
   if href.startswith(('#','https://','http://','mailto:','data:')):continue
   target=str(PurePosixPath(name).parent/PurePosixPath(href.split('#')[0]));m=safe_name(target)
   links.append({'from':name,'href':href,'public_target':target,'materialized':target in materialized})
 pending.extend({'category':'RELATIVE_HUMAN_REPORT_LINK_TARGET_NOT_MATERIALIZED','link':z} for z in links if not z['materialized'])
 flagged=[{'archive_path':z['archive_path'],'flags':z['privacy']['flags']} for z in rows.values() if z['privacy']['flags']]
 result={'schema':'PUBLIC_EVIDENCE_SOURCE_INVENTORY_DRAFT_V1','status':'ROOT_REVIEW_REQUIRED_NO_PACKAGE_BUILD_AUTHORITY','selection_plan':{'path':str(R/'reports/PUBLIC_EVIDENCE_SELECTION_PLAN.md'),'sha256':sha((R/'reports/PUBLIC_EVIDENCE_SELECTION_PLAN.md').read_bytes())},'snapshot':{'path':str(q.snapshot.resolve()),'sha256':sha(q.snapshot.read_bytes())},'assets':sorted(rows.values(),key=lambda z:z['archive_path']),'selected_asset_count':len(rows),'original_total_bytes':sum(z['size'] for z in rows.values()),'privacy_flagged_assets':flagged,'static_relative_human_link_target_census':links,'pending_required_assets_and_joins':pending,'source_only_no_copy_or_package_build':True,'new_scientific_model_scope_compiler_numerics':0}
 with q.out.open('x') as f:json.dump(result,f,indent=2,ensure_ascii=False);f.write('\n')
 print(json.dumps({'status':result['status'],'assets':len(rows),'privacy_flagged':len(flagged),'pending':len(pending),'inventory_sha256':sha(q.out.read_bytes())},sort_keys=True))
if __name__=='__main__':main()
