#!/usr/bin/env python3
"""Read-only candidate-to-final source/validator gate; writes only a fresh D receipt."""
from pathlib import Path
import argparse,collections,datetime,difflib,hashlib,json,math,os,subprocess,tarfile
P=Path('/data/ivy-rh-limit-20261122/publication')
N=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-rh-continuation-20261122/network')
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--network',type=Path,default=N);p.add_argument('--candidate',type=Path,default=P/'restored-candidate');p.add_argument('--out',type=Path,required=True);a=p.parse_args();N=a.network.resolve();C=a.candidate.resolve();out=a.out.resolve();S=N/'Solutions/RHLimit.v1';stem='Solutions/RHLimit.v1/'
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(f):
 need(f.is_file()and not f.is_symlink(),'regular file required:'+str(f));h=hashlib.sha256()
 with f.open('rb')as stream:
  for block in iter(lambda:stream.read(1048576),b''):h.update(block)
 return h.hexdigest()
def read(f):
 def pairs(items):
  d={}
  for k,v in items:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 def fl(raw):
  v=float(raw);need(math.isfinite(v),'nonfinite JSON');return v
 return json.loads(f.read_bytes(),object_pairs_hook=pairs,parse_float=fl,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
need(not out.exists(),'fresh output required')
need(sha(C/'BUNDLE_MANIFEST.json')=='7685c69ec1d036839a69508e4c09e43b31c21633c9202ce23643d42b38ca0675','frozen candidate identity')
m=read(C/'BUNDLE_MANIFEST.json');rows=m['files'];need(len({x['path']for x in rows})==len(rows),'unique candidate identities')
for r in rows:need(sha(C/r['path'])==r['sha256']and(C/r['path']).stat().st_size==r['bytes'],'candidate source bytes:'+r['path'])
network={x['path'][8:]:x for x in rows if x['path'].startswith('network/')};mathrows={k:v for k,v in network.items()if Path(k).suffix in {'.lean','.c','.h'}};need(len(mathrows)==970,'exact970application source scope')
proofs=[]
for rel,r in sorted(mathrows.items()):
 need(sha(N/rel)==r['sha256'],'changed mathematical/C source:'+rel);proofs.append({'path':rel,'sha256':r['sha256']})
allowed_reporting={stem+x for x in ['README.md','ledgers/MATH_ACCEPTANCE.json','publication/BUNDLE_README.md','publication/README.md','reports/FACTS.json','reports/render.py','reports/RH_LIMIT_REPORT_EN.html']};guard=stem+'scripts/reproduce_integration.py';changed=[]
for rel,r in sorted(network.items()):
 now=sha(N/rel)
 if now!=r['sha256']:
  need(rel in allowed_reporting or rel==guard,'unapproved candidate delta:'+rel);changed.append({'path':rel,'before':r['sha256'],'after':now,'classification':'optional historical replay validation only'if rel==guard else'reporting/evidence metadata'})
old=(C/'network'/guard).read_text();new=(N/guard).read_text();before=sha(C/'network'/guard);after=sha(N/guard)
need(before=='9b630a9fec993749d6fefdf81dd7893cac2b4f674392be21eb385c1fecd106e6'and after=='857ba8bf9f670e5df415dba16c84cf72c3168c6aa49df0cf1649bdd7f1d404cf','exact reviewed combined guard patch identity')
start='def main():\n';end=" m=read(S/'integration/SOURCE_CLOSURE.json');"
need(old.split(start)[0]==new.split(start)[0]and old.split(end)[1]==new.split(end)[1],'outside-main/consumer execution suffix changed')
need(old.split(start)[1].split(" if br.get('resource_complete_default_recipe')is not True:")[0]==new.split(start)[1].split(" need(not(br.get('resource_complete_default_recipe')is True")[0],'argument parsing changed')
fixed=['pi/SOURCE_CLOSURE.json','pi/RESOURCES.json','pi/RESOURCE_CLOSURE.json','spectral/SOURCE_CLOSURE.json','spectral/MATCHED_TRANSFER_PARAMETERS.json','integration/SOURCE_CLOSURE.json','analytic/ABSOLUTE_MANIFEST.json','analytic/ANALYTIC_MANIFEST.json','analytic/SOURCE_MANIFEST.json','octic/OCTIC_MANIFEST.json','octic/STRICT_MANIFEST.json','WORKPLAN.json']
fixedrows=[]
for rel in fixed:
 r=network[stem+rel];need(sha(S/rel)==r['sha256'],'fixed source/parameter manifest changed:'+rel);fixedrows.append({'path':stem+rel,'sha256':r['sha256']})
active=['scripts/reproduce_pi_complete.py','analytic/reproduce_absolute.py','octic/reproduce.py','analytic/reproduce.py','spectral/reproduce_cold_append.py'];controllers=[]
for rel in active:
 r=network[stem+rel];need(sha(S/rel)==r['sha256'],'other active proof controller changed:'+rel);controllers.append({'path':stem+rel,'sha256':r['sha256']})
plan=read(C/'SOURCE_PLAN.json');prior=P/'prior-source.tar.gz';need(sha(prior)==plan['prior_archive_sha256']=='4788c7dda3939a0c1dc5f7d7dbeddc87eb68d95036aa0d13d7027c5371734140','same immutable baseline source archive')
helpers=[]
for r in plan['files']:
 if '/'not in r['path']and r['path'].endswith('.py'):
  if r['origin']=='network':need(sha(N/r['source_path'])==r['sha256'],'top-level helper changed:'+r['path'])
  else:
   with tarfile.open(prior,'r:gz')as tf:
    members=[x for x in tf.getmembers()if x.name==r['source_path']];need(len(members)==1 and members[0].isfile(),'baseline helper membership');f=tf.extractfile(members[0]);need(f is not None and hashlib.sha256(f.read()).hexdigest()==r['sha256'],'baseline bootstrap helper changed')
  helpers.append({'path':r['path'],'origin':r['origin'],'sha256':r['sha256']})
knownsha={x['sha256']for x in mathrows.values()};added=[]
for f in sorted(S.rglob('*')):
 if not f.is_file()or '__pycache__'in f.parts:continue
 rel=str(f.relative_to(N))
 if rel in network:continue
 short=str(f.relative_to(S));need(short.split('/')[0]in {'evidence','ledgers','reviews','reports'},'new non-reporting source path:'+rel)
 h=sha(f)
 if f.suffix in {'.lean','.c','.h'}:need(short.startswith('evidence/')and h in knownsha,'new mathematical source beyond frozen candidate:'+rel)
 added.append({'path':rel,'bytes':f.stat().st_size,'sha256':h,'classification':'exact frozen source evidence copy'if f.suffix in {'.lean','.c','.h'}else'new reporting/evidence artifact'})
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='candidate/'+guard,tofile='final/'+guard))
result={'status':'PASS_STRICT_CANDIDATE_TO_FINAL_SOURCE_AND_SINGLE_ACTIVE_VALIDATOR_DELTA','final_freeze_authorized':False,'scope_author':'Root requested exact frozen candidate application source universe, all candidate network file identities, exact six active controllers, top-level/bootstrap helpers and explicitly added reporting/evidence paths. Unrelated current network workspaces are excluded.','candidate_manifest_sha256':sha(C/'BUNDLE_MANIFEST.json'),'candidate_network_files':len(network),'unchanged_mathematical_C_sources':proofs,'generic_recipe_sources_excluded_from970_but_immutable_in_same_baseline_archive':38,'fixed_source_parameter_manifests':fixedrows,'other_five_active_controllers':controllers,'top_level_and_bootstrap_helpers':helpers,'changed_candidate_paths':changed,'new_reporting_evidence_files':added,'combined_guard':{'before':before,'after':after,'scope':'Disallow unused legacy flag on clean basis; exact stored23 module/source/objects/logs/controller/C payload associations on historical basis. Mathematical source, statements, parameters, old proof execution loop and remaining function suffix byte-identical.','independent_review':'Actual source diff read by octic/publication child; all check additions occur before unchanged canonical source execution. Exact Root-reviewed857 hash enforced.'},'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'network_HEAD':subprocess.check_output(['git','rev-parse','HEAD'],cwd=N,text=True).strip(),'boundary':'Candidate620 replay used9b guard. Final857 clean24/legacy24 replays and controls are separate; this gate is read-only identity verification, not another complete620 run.','checker_sha256':sha(Path(__file__))}
out.mkdir(parents=True);(out/'FINAL_GUARD_EXACT.patch').write_text(patch);result['combined_guard']['patch_sha256']=sha(out/'FINAL_GUARD_EXACT.patch');tmp=out/'RESULT.json.tmp';tmp.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n');os.replace(tmp,out/'RESULT.json');print(json.dumps({'status':result['status'],'math_C_sources':len(proofs),'fixed_manifests':len(fixedrows),'other_active_controllers':len(controllers),'top_helpers':len(helpers),'changed_candidate_paths':len(changed),'added_evidence_paths':len(added),'receipt_sha256':sha(out/'RESULT.json')}))
