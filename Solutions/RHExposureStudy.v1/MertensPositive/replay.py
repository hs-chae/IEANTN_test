#!/usr/bin/env python3
"""Fresh source-only ordinary Lean replay; no official receipt or source-first PV claim."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,re,time
B=Path(__file__).resolve().parent
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--optimize',choices=['normal','O','OO'],default='normal');p.add_argument('--context',type=Path,default=B/'BUILD_CONTEXT.json');a=p.parse_args()
def need(ok,why):
 if not ok:raise RuntimeError(why)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
level={'normal':0,'O':1,'OO':2}[a.optimize];need(sys.flags.optimize==level,'actual Python optimization matches label');o=a.out.resolve();need(not o.exists(),'fresh output only');manifest=json.loads((B/'SOURCE_MANIFEST.json').read_text());c=json.loads(a.context.read_text());need(sha(c['compiler'])==c['compiler_sha256']=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550','exact compiler');need(c['pinned_mathlib_revision']=='71a80585ee495fc24472fd0eaffc89d94e4fd8d6','Mathlib pin');o.mkdir(parents=True);started=time.monotonic()
for row in manifest['modules']:
 src=B/row['path'];need(sha(src)==row['sha256'],'source pin '+row['module']);dst=o/row['path'];dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
for n in ['compile.py','SOURCE_MANIFEST.json','THEOREM_CENSUS.json']:shutil.copyfile(B/n,o/n)
c['source_root']=str(o);c['new_application_object_root']=str(o/'objects');(o/'BUILD_CONTEXT.json').write_text(json.dumps(c,indent=2)+'\n');prefix=[sys.executable,*([]if level==0 else['-'+a.optimize])]
commands=[]
for row in manifest['modules']:
 cmd=[*prefix,str(o/'compile.py'),row['module'],'--attempt',row['module']];r=subprocess.run(cmd,capture_output=True,text=True);commands.append({'command':cmd,'exit_code':r.returncode});(o/(row['module']+'.driver.stdout')).write_text(r.stdout);(o/(row['module']+'.driver.stderr')).write_text(r.stderr);need(r.returncode==0,'module compile '+row['module']+': '+r.stdout[:2000]);need(sha(o/row['path'])==row['sha256'],'source stable '+row['module'])
log=(o/'compile-observations/Audit/stdout').read_text();pairs=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S);census=json.loads((B/'THEOREM_CENSUS.json').read_text());expected={r['declaration']for r in census};need(len(pairs)==len({x[0]for x in pairs})==len(census)==manifest['new_theorem_count']==27,'exact distinct physical theorem census');need({x[0]for x in pairs}==expected,'all written theorem declarations audited');allowed={'propext','Classical.choice','Quot.sound'}
for n,ax in pairs:need(set(x.strip()for x in ax.split(',')if x.strip())<=allowed,'axiom policy '+n)
d={'status':'PASS_FRESH_12_MODULE_27_THEOREM_REPLAY','optimization_mode':a.optimize,'source_manifest_sha256':sha(B/'SOURCE_MANIFEST.json'),'elapsed_seconds':time.monotonic()-started,'commands':commands,'all_axioms_subset':sorted(allowed),'actual_source_stable':True,'no_old_application_objects':True,'only_pinned_generic_libraries_reused':True,'not_source_first_PV':True,'not_Comparator_receipt':True};tmp=o/'REPLAY_RESULT.json.tmp';tmp.write_text(json.dumps(d,indent=2)+'\n');tmp.replace(o/'REPLAY_RESULT.json');print(d['status'],a.optimize,round(d['elapsed_seconds'],2))
