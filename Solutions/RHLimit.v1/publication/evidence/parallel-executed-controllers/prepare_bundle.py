#!/usr/bin/env python3
"""Plan the exact RHLimit source package; freeze only after ROOT_FINAL_READY.

Archive mechanics are reused from the independently tested previous publication.
Planning reads mutable study sources but never freezes or archives them.
"""
from pathlib import Path, PurePosixPath
import argparse,hashlib,io,json,os,re,shutil,subprocess,sys,tarfile
sys.dont_write_bytecode=True
from archive_tools import need,sha,safe,save,verify,manifest,pack,extract,regular_files
PRIOR_SHA='4788c7dda3939a0c1dc5f7d7dbeddc87eb68d95036aa0d13d7027c5371734140'
PRIVATE={'.git','.lake','__pycache__','memory','human_input','prompts','transcripts','sessions'}
OMIT={'.pyc','.pyo','.olean','.ilean','.o','.a','.so','.ir','.pdf','.part','.tar','.gz'}
PREFIX='Solutions/RHLimit.v1/'

def decode(raw):
 def pairs(rows):
  d={}
  for k,v in rows:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 def number(s):
  x=float(s);need(abs(x)!=float('inf'),'overflowing JSON number');return x
 return json.loads(raw,object_pairs_hook=pairs,parse_float=number,
  parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def strict(p):return decode(Path(p).read_bytes())
def digest(raw):return hashlib.sha256(raw).hexdigest()
def excluded(path):
 p=safe(path)
 return (any(x.lower()in PRIVATE for x in p.parts)or p.suffix.lower()in OMIT
  or any(z in p.name for z in ['.olean.','.ilean.','.ir.'])or p.name.endswith('.pending'))

def prior(path):
 need(path.is_file()and not path.is_symlink()and sha(path)==PRIOR_SHA,'exact prior source archive required')
 tf=tarfile.open(path,'r:gz');members={}
 for m in tf.getmembers():
  safe(m.name);need(m.isfile()and m.name not in members,'prior archive duplicate/nonfile');members[m.name]=m
 need('BUNDLE_MANIFEST.json'in members,'prior manifest missing')
 bm=decode(tf.extractfile(members['BUNDLE_MANIFEST.json']).read());need(bm['schema']=='STRICT_RELATIVE_FILE_HASH_MANIFEST_V1','prior schema')
 rows={r['path']:r for r in bm['files']};need(len(rows)==len(bm['files'])and set(rows)==set(members)-{'BUNDLE_MANIFEST.json'},'prior exact membership')
 for name,row in rows.items():
  need(type(row['bytes'])is int and members[name].size==row['bytes'],'prior size')
 def take(name):
  safe(name);need(name in rows,'missing selected prerequisite:'+name)
  raw=tf.extractfile(members[name]).read();need(digest(raw)==rows[name]['sha256'],'prior selected source hash:'+name);return raw
 return tf,rows,take

def baseline(path):
 tf,rows,take=prior(path);selected={}
 def add(name,why):
  need(name in rows,'missing baseline prerequisite:'+name)
  if name in selected:selected[name]['reasons'].append(why)
  else:selected[name]={**rows[name],'origin':'prior_archive','source_path':name,'reasons':[why]}
 for name in ['BOOTSTRAP_GENERIC.py','bootstrap_missing_generic.py','generic_transport.py',
  'fetch_generic_cache.py','run_bounded.py','GENERIC_CACHE_ARCHIVES.json','GENERIC_DEPENDENCY_PINS.json']:
  add(name,'Unchanged pinned generic bootstrap prerequisite')
 for name in rows:
  if name.startswith(('generic-source-recipe/','generic-transport/')):add(name,'Exact generic source recipe or nonsemantic legacy metadata transport')
 for name in rows:
  if name.startswith('network/Solutions/RHContinuation.v1/reports/render-support/latex2mathml/')or name in {'network/Solutions/RHContinuation.v1/reports/fonts/STIXGeneral.ttf','network/Solutions/RHContinuation.v1/reports/fonts/LICENSE_STIX'}:add(name,'Exact offline static-MathML and embedded-font report renderer prerequisite')
 for name in rows:
  if name.startswith('network/IEANTN/'):add(name,'Pinned baseline canonical core; reviewed new canonical files override explicitly')
 for name in ['IEANTN.lean','lean-toolchain','lakefile.toml','lake-manifest.json','LICENSE']:
  add('network/'+name,'Pinned baseline build/license metadata')
 leg='network/Solutions/RHExposureStudy.v1/Ramanujan640/'
 lm=decode(take(leg+'SOURCE_MANIFEST.json'));add(leg+'SOURCE_MANIFEST.json','Unchanged full generic inventory gate')
 add(leg+'REPRODUCE.py','Unchanged legacy generic gate entry')
 for row in lm['files']:add(leg+safe(row['path']).as_posix(),'Input required by unchanged legacy --check gate')
 for row in lm['generic_libraries']:add(leg+safe(row['inventory']).as_posix(),'Exact generic full-file identity inventory')
 old='network/Solutions/RHContinuation.v1/'
 add(old+'scripts/GENERIC_CONTEXT.json','Exact reference compiler/dependency identities')
 add(old+'integration/SOURCE_CLOSURE.json','Original111-source manifest used by analytic/octic replayers')
 cm=decode(take(old+'integration/SOURCE_CLOSURE.json'))
 need(len(cm['modules'])==111,'original111 source scope')
 for row in cm['modules']:add(old+'integration/'+safe(row['frozen']).as_posix(),'Original frozen111-source proof prerequisite')
 inventory=decode(take('SOURCE_SELECTION.json'))
 need(len(inventory['actual_C_application_modules'])==46,'original46 C-log closure scope')
 for row in inventory['actual_C_application_modules']:add('network/'+safe(row['path']).as_posix(),'Exact46 actual-C log-to-mathematics source closure')
 add('network/Solutions/RamanujanSourcePV.v1/c/verified_finite_log.c','Actual source payload and executable numerical workload')
 for name in ['reproduce_clog.py','native_log_workload.py','box_mellin_trapezoid.py','box_mellin_series.py','rational.py']:
  add(old+'parabolic/'+name,'Deterministic actual-C/numerical regeneration controller')
 for name in rows:
  if name.startswith(old+'parabolic/')and name.count('/')==4 and name.endswith('.md'):add(name,'Written mathematical provenance for reused analytic contracts')
 tf.close();return selected

def live_files(network):
 root=network/'Solutions/RHLimit.v1';need(root.is_dir(),'study source tree absent');files=[];omitted=[]
 for p in sorted(root.rglob('*')):
  need(not p.is_symlink(),'linked entry in new study source tree')
  if p.is_file():
   rel=p.relative_to(network).as_posix()
   if excluded(rel):omitted.append(rel)
   else:files.append(rel)
 return files,omitted

def canonical_rows(path):
 if path is None:return []
 d=strict(path);need(d['schema']=='RH_LIMIT_REVIEWED_CANONICAL_FILES_V1'and isinstance(d['files'],list),'canonical whitelist schema')
 names=[]
 for row in d['files']:
  rel=safe(row['path']).as_posix();need(not excluded(rel)and not rel.startswith(PREFIX),'canonical path scope')
  need(rel.startswith(('IEANTN/','Solutions/'))or rel=='IEANTN.lean','canonical file outside requested research scope')
  need(re.fullmatch('[0-9a-f]{64}',row['sha256'])is not None,'canonical source identity');names.append(rel)
 need(len(names)==len(set(names)),'duplicate canonical file');return sorted(d['files'],key=lambda r:r['path'])

def make_plan(network,archive,canonical):
 network=network.resolve();archive=archive.resolve();selected=baseline(archive);files,omitted=live_files(network);can=canonical_rows(canonical)
 def add(rel,why,expected=None):
  p=network/safe(rel);need(p.is_file()and not p.is_symlink(),'missing regular live source:'+rel)
  h=sha(p);need(expected is None or h==expected,'canonical file changed:'+rel)
  target='network/'+rel
  if target in selected and selected[target]['sha256']!=h:
   need(why=='Reviewed canonical override','unexpected baseline/source collision:'+rel)
   old=selected[target]['sha256']
  else:old=None
  selected[target]={'path':target,'origin':'network','source_path':rel,'sha256':h,'bytes':p.stat().st_size,'reasons':[why]}
  if old:selected[target]['prior_sha256']=old
 for rel in files:add(rel,'Complete new RHLimit scientific source/evidence')
 for row in can:add(row['path'],'Reviewed canonical override',row['sha256'])
 pub=Path(__file__).resolve().parent
 for name,target in [('prepare_bundle.py','prepare_bundle.py'),('archive_tools.py','archive_tools.py'),('join_bundle.py','join_bundle.py'),('REPRODUCE_RH_LIMIT.py','REPRODUCE_RH_LIMIT.py'),('FETCH_GENERIC_SOURCES.py','FETCH_GENERIC_SOURCES.py'),('run_replay_bounded.py','run_replay_bounded.py'),('BUNDLE_README.md','README.md')]:
  p=pub/name;need(p.is_file(),'publication controller not ready:'+name)
  rel=p.relative_to(network).as_posix();selected[target]={'path':target,'origin':'network','source_path':rel,'sha256':sha(p),'bytes':p.stat().st_size,'reasons':['Top-level verified restore/bootstrap/replay helper']}
 # Check frozen theorem modules/resources without assuming the source archive is a proof.
 gates=[];pending_canonical=[]
 prior_tf,prior_rows,_=prior(archive)
 for rel,count in [('pi/SOURCE_CLOSURE.json',261),('spectral/SOURCE_CLOSURE.json',55),('integration/SOURCE_CLOSURE.json',24)]:
  m=strict(network/'Solutions/RHLimit.v1'/rel);need(len(m['modules'])==count,'source scope changed:'+rel)
  for row in m['modules']:
   p=network/safe(row['path']);need(sha(p)==row['sha256'],'frozen module source changed:'+row['module'])
   if rel.startswith('integration/')and 'original_path'in row:
    original=safe(row['original_path']).as_posix();target='network/'+original
    need(sha(network/original)==row['sha256'],'actual canonical source drift:'+original)
    if target not in selected:
     if target in prior_rows and prior_rows[target]['sha256']==row['sha256']:
      selected[target]={**prior_rows[target],'origin':'prior_archive','source_path':target,'reasons':['Exact original source required by final canonical association gate']}
     else:pending_canonical.append(original)
    elif selected[target]['sha256']!=row['sha256']:pending_canonical.append(original)
   for payload in re.findall(r'include_str\s+"([^"\n]+)"',p.read_text()):
    q=(p.parent/payload).resolve();need(q.is_relative_to(network)and q.is_file(),'missing frozen include_str resource:'+str(q))
    target='network/'+q.relative_to(network).as_posix();need(target in selected and selected[target]['sha256']==sha(q),'unselected source payload:'+str(q))
  resource_rows=m.get('resources',[])
  if rel.startswith('pi/'):
   resource_manifest=network/'Solutions/RHLimit.v1/pi/RESOURCES.json';resource_rows+=strict(resource_manifest)['resources']
  for resource_row in resource_rows:
   q=network/safe(resource_row['path']);need(q.is_file()and sha(q)==resource_row['sha256'],'frozen C/resource identity')
  gates.append({'manifest':rel,'sha256':sha(network/'Solutions/RHLimit.v1'/rel),'modules':count,'resources':len(resource_rows)})
 prior_tf.close()
 for target,row in selected.items():safe(target);need(target==row['path'],'plan file identity')
 return {'schema':'RH_LIMIT_SOURCE_BUNDLE_PLAN_V1','status':'DRAFT_SOURCE_PLAN_NOT_FROZEN','network_root':str(network),'network_HEAD':subprocess.check_output(['git','rev-parse','HEAD'],cwd=network,text=True).strip(),'prior_archive':str(archive),'prior_archive_sha256':PRIOR_SHA,'selection_rule_author':'Root-directed RHLimit publication helper','selection_rule':'All new RHLimit source/evidence minus explicit private/runtime/paper exclusions; exact reviewed canonical whitelist; selected pinned baseline prerequisites for all active proof and generic-bootstrap routes.','excluded_new_paths':omitted,'study_paths':files,'canonical_files':can,'source_gates':gates,'files':sorted(selected.values(),key=lambda r:r['path']),'uncompressed_selected_bytes':sum(r['bytes']for r in selected.values()),'canonical_whitelist_complete':canonical is not None,'pending_canonical_paths':sorted(set(pending_canonical))}

def freeze(plan_path,ready_path,out):
 p=strict(plan_path);r=strict(ready_path)
 need(p['schema']=='RH_LIMIT_SOURCE_BUNDLE_PLAN_V1'and p['status']=='DRAFT_SOURCE_PLAN_NOT_FROZEN','source plan schema')
 need(p['prior_archive_sha256']==PRIOR_SHA,'prior prerequisite pin')
 targets=[]
 for row in p['files']:
  targets.append(safe(row['path']).as_posix());safe(row['source_path'])
  need(type(row['bytes'])is int and row['bytes']>=0 and re.fullmatch('[0-9a-f]{64}',row['sha256'])is not None,'planned source identity')
  need(row['origin']in {'network','prior_archive'},'planned source origin')
 need(len(targets)==len(set(targets))and targets==sorted(targets),'duplicate/nonordered planned file')
 need(r['status']=='ROOT_FINAL_READY'and r['schema']=='RH_LIMIT_ROOT_FINAL_READY_V1','ROOT_FINAL_READY required')
 need(r['approved_plan_sha256']==sha(plan_path),'ready receipt does not approve exact current plan')
 need(r['canonical_files']==p['canonical_files']and p['canonical_whitelist_complete']and not p['pending_canonical_paths'],'reviewed canonical whitelist not approved')
 need(r['network_HEAD']==p['network_HEAD'],'baseline HEAD approval mismatch')
 need(isinstance(r['canonical_replay'],dict)and r['canonical_replay'].get('script'),'final canonical replay route required')
 can=r['canonical_replay'];script=safe(can['script']).as_posix();need(script in {x['path']for x in p['files']},'canonical replay script not selected')
 need(isinstance(can.get('argv'),list)and all(isinstance(x,str)for x in can['argv']),'canonical replay structured arguments')
 need(isinstance(can.get('expected_status'),str)and can['expected_status'],'canonical expected status');safe(can['receipt'])
 network=Path(p['network_root']);need(subprocess.check_output(['git','rev-parse','HEAD'],cwd=network,text=True).strip()==p['network_HEAD'],'HEAD changed after approval')
 need(live_files(network)[0]==p['study_paths'],'study membership changed after final approval')
 need(not out.exists()and not out.resolve().is_relative_to(network),'fresh external staging output required')
 required=baseline(Path(p['prior_archive']));need(set(required)<=set(targets),'baseline prerequisite omitted')
 old_tf,old_rows,_=prior(Path(p['prior_archive']));old_tf.close()
 for row in p['files']:
  if row['origin']=='prior_archive':need(row['path']==row['source_path']and row['path']in old_rows and row['sha256']==old_rows[row['path']]['sha256'],'unapproved prior prerequisite')
 tf,_,take=prior(Path(p['prior_archive']));out.mkdir(parents=True)
 try:
  for row in p['files']:
   rel=safe(row['path']);dst=out/rel;dst.parent.mkdir(parents=True,exist_ok=True)
   if row['origin']=='prior_archive':raw=take(row['source_path'])
   else:
    need(row['origin']=='network','unknown plan origin');src=network/safe(row['source_path']);need(src.is_file()and not src.is_symlink(),'live source absent');raw=src.read_bytes()
   need(len(raw)==row['bytes']and digest(raw)==row['sha256'],'source changed since approved plan:'+row['path']);dst.write_bytes(raw)
  shutil.copyfile(plan_path,out/'SOURCE_PLAN.json');shutil.copyfile(ready_path,out/'ROOT_FINAL_READY.json')
  save(out/'REPLAY_ROUTES.json',{'schema':'RH_LIMIT_FINAL_CANONICAL_REPLAY_ROUTE_V1','canonical':r['canonical_replay']})
  manifest(out);count=verify(out)
  save(out.parent/(out.name+'.STAGE_RECEIPT.json'),{'status':'PASS_ROOT_APPROVED_FINAL_SOURCE_TREE','files':count,'plan_sha256':sha(plan_path),'ready_sha256':sha(ready_path),'bundle_manifest_sha256':sha(out/'BUNDLE_MANIFEST.json')})
  print(json.dumps({'status':'PASS_ROOT_APPROVED_FINAL_SOURCE_TREE','files':count}))
 finally:tf.close()

def approved_archive(tree,out):
 verify(tree);r=strict(tree/'ROOT_FINAL_READY.json');p=strict(tree/'SOURCE_PLAN.json')
 need(r['schema']=='RH_LIMIT_ROOT_FINAL_READY_V1'and r['status']=='ROOT_FINAL_READY','unapproved final tree')
 need(r['approved_plan_sha256']==sha(tree/'SOURCE_PLAN.json')and r['canonical_files']==p['canonical_files'],'tree differs from exact root approval')
 need(p['canonical_whitelist_complete']and not p['pending_canonical_paths'],'unfinished canonical selection')
 pack(tree,out)
 expected=strict(tree/'BUNDLE_MANIFEST.json');rows={r['path']:r for r in expected['files']};seen=set()
 with tarfile.open(out,'r:gz')as tf:
  for m in tf.getmembers():
   safe(m.name);need(m.isfile()and m.name not in seen,'archive member identity');seen.add(m.name);h=hashlib.sha256();size=0
   with tf.extractfile(m)as stream:
    for block in iter(lambda:stream.read(1048576),b''):h.update(block);size+=len(block)
   if m.name=='BUNDLE_MANIFEST.json':need(h.hexdigest()==sha(tree/'BUNDLE_MANIFEST.json'),'archived manifest bytes differ')
   else:need(m.name in rows and size==rows[m.name]['bytes']and h.hexdigest()==rows[m.name]['sha256'],'archived source bytes differ:'+m.name)
 need(seen==set(rows)|{'BUNDLE_MANIFEST.json'},'archive file membership differs');verify(tree)
 save(out.with_name(out.name+'.VERIFIED.json'),{'status':'PASS_ROOT_APPROVED_ARCHIVE_ALL_MEMBER_SOURCE_HASHES','archive_sha256':sha(out),'archive_bytes':out.stat().st_size,'manifest_sha256':sha(tree/'BUNDLE_MANIFEST.json'),'files':len(rows),'root_ready_sha256':sha(tree/'ROOT_FINAL_READY.json')})
 print('PASS_ROOT_APPROVED_ARCHIVE_ALL_MEMBER_SOURCE_HASHES')

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);sp=p.add_subparsers(dest='action',required=True)
 q=sp.add_parser('plan',allow_abbrev=False);q.add_argument('--network',type=Path,required=True);q.add_argument('--prior-archive',type=Path,required=True);q.add_argument('--canonical',type=Path);q.add_argument('--out',type=Path,required=True)
 q=sp.add_parser('freeze',allow_abbrev=False);q.add_argument('--plan',type=Path,required=True);q.add_argument('--ready',type=Path,required=True);q.add_argument('--out',type=Path,required=True)
 q=sp.add_parser('verify',allow_abbrev=False);q.add_argument('--tree',type=Path,required=True)
 q=sp.add_parser('pack',allow_abbrev=False);q.add_argument('--tree',type=Path,required=True);q.add_argument('--out',type=Path,required=True)
 q=sp.add_parser('extract',allow_abbrev=False);q.add_argument('--archive',type=Path,required=True);q.add_argument('--out',type=Path,required=True)
 a=p.parse_args()
 if a.action=='plan':need(not a.out.exists(),'fresh plan required');j=make_plan(a.network,a.prior_archive,a.canonical);save(a.out,j);print(json.dumps({'status':j['status'],'files':len(j['files']),'bytes':j['uncompressed_selected_bytes'],'plan_sha256':sha(a.out)}))
 elif a.action=='freeze':freeze(a.plan,a.ready,a.out)
 elif a.action=='verify':print(json.dumps({'status':'PASS_ALL_SOURCE_BYTES_AND_MEMBERS','files':verify(a.tree)}))
 elif a.action=='pack':approved_archive(a.tree,a.out)
 else:extract(a.archive,a.out)
if __name__=='__main__':main()
