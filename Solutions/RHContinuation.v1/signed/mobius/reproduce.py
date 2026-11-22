#!/usr/bin/env python3
"""Fresh full source replay; named literature predicates remain theorem parameters."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,sys,time
B=Path(__file__).resolve().parent
COMPILER='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
MATHLIB='71a80585ee495fc24472fd0eaffc89d94e4fd8d6'
def need(ok,msg):
 if not ok:raise ValueError(msg)
def read(p):
 def pairs(rows):
  obj={}
  for k,v in rows:need(k not in obj,'duplicate JSON key');obj[k]=v
  return obj
 return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_constant=lambda x:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
 return h.hexdigest()
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path);p.add_argument('--context',type=Path,default=B/'BUILD_CONTEXT.json');p.add_argument('--optimize',choices=['normal','O','OO'],default='normal');p.add_argument('--check',action='store_true');a=p.parse_args();level={'normal':0,'O':1,'OO':2}[a.optimize];need(sys.flags.optimize==level,'actual optimization differs from label');m=read(B/'SOURCE_MANIFEST.json');c=read(a.context);census=read(B/'THEOREM_CENSUS.json');need(m['schema']=='MOBIUS_ANALYTIC_COMPONENT_SOURCE_V1','source schema');need(m['compiler_sha256']==COMPILER==c['compiler_sha256']==sha(c['compiler']),'compiler identity');need(m['mathlib_revision']==MATHLIB==c['pinned_mathlib_revision'],'Mathlib identity');need(len(m['modules'])==7 and len({r['module']for r in m['modules']})==7,'complete7moduleinventory');need(len(census)==m['new_theorem_count']==25 and len({(r['file'],r['line'],r['declaration'])for r in census})==25,'exact25declarationidentityinventory');need(len(c['generic_dependencies'])==9 and len(c['generic_libraries'])==8,'ninepinnedsourcesandeightusedlibraries');need([x['library']for x in c['generic_dependencies']if x['library']in c['generic_libraries']]==c['generic_libraries'],'librarymapping')
for dep in c['generic_dependencies']:
 root=Path(dep['path']);revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip();need(revision==dep['revision'],'generic revision:'+dep['name']);need(dep['library']not in c['generic_libraries']or Path(dep['library']).is_dir(),'missing generic library:'+dep['name']);dirty=subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=root,text=True);need(not dirty.strip(),'generic tracked-source changes:'+dep['name'])
for row in m['modules']:
 need(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*',row['module'])is not None,'moduleidentifier');need(row['path']=='source/'+row['module'].replace('.','/')+'.lean','modulepath');f=(B/row['path']).resolve();need(f.is_relative_to((B/'source').resolve())and f.is_file(),'sourcepath');need(type(row['bytes'])is int and f.stat().st_size==row['bytes']and sha(f)==row['sha256'],'sourceidentity:'+row['module'])
for row in census:
 text=(B/row['file']).read_text().split('\n');need(0<row['line']<=len(text)and re.match(r'(theorem|lemma)\s+'+re.escape(row['declaration'].split('.')[-1])+r'\b',text[row['line']-1])is not None,'writtendeclarationidentity')
print('PASS_ALL7_SOURCE_AND_COMPILER_GENERIC_SOURCE_PINS',flush=True)
if a.check:raise SystemExit(0)
need(a.out is not None,'--out required');o=a.out.resolve();need(not o.exists(),'fresh output required');o.mkdir(parents=True);(o/'source').mkdir();(o/'objects').mkdir();(o/'logs').mkdir();started=time.monotonic();commands=[]
for row in m['modules']:
 f=o/row['path'];f.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(B/row['path'],f)
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(o/'objects'),*c['generic_libraries']])
for row in m['modules']:
 mod=row['module'];obj=o/'objects'/(mod.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);log=o/'logs'/mod;cmd=[c['compiler'],'-R',str(o/'source'),'-o',str(obj),str(o/row['path'])];st=time.monotonic();r=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=o/'source',env=env,text=True,capture_output=True);log.with_suffix('.stdout').write_text(r.stdout);log.with_suffix('.stderr').write_text(r.stderr);need(r.returncode==0,'compile failed:'+mod+':'+r.stdout[:1600]);need(sha(o/row['path'])==row['sha256'],'copiedsourcechanged');commands.append({'module':mod,'command':cmd,'returncode':r.returncode,'elapsed_seconds':time.monotonic()-st,'source_sha256':row['sha256'],'object_sha256':sha(obj)});print('PASS',mod,round(commands[-1]['elapsed_seconds'],3),flush=True)
log=(o/'logs/MobiusAudit.stdout').read_text();pairs=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S);expected={r['declaration']for r in census};need(len(pairs)==len({x[0]for x in pairs})==25,'exactauditcount');need({x[0]for x in pairs}==expected,'completeauditidentitycoverage');allowed={'propext','Classical.choice','Quot.sound'}
for name,axioms in pairs:need({x.strip()for x in axioms.split(',')if x.strip()}<=allowed,'nonstandardaxiom:'+name)
for row in m['modules']:need(sha(B/row['path'])==row['sha256'],'originalsourcechanged')
receipt={'schema':'MOBIUS_ANALYTIC_COMPONENT_REPLAY_V1','status':'PASS_7_MODULE_25_KERNEL_COMPONENTS_WITH_EXPLICIT_ANALYTIC_GAPS','python_optimization':level,'compiler_sha256':COMPILER,'source_manifest_sha256':sha(B/'SOURCE_MANIFEST.json'),'commands':commands,'all_axioms_subset':sorted(allowed),'elapsed_seconds':time.monotonic()-started,'native_execution_axioms':False,'old_application_objects_used':False,'only_pinned_generic_libraries_used':True,'source_first_PV':False,'official_Comparator_receipt':False,'mathematical_premises':'Not a closed RH-to-M theorem: actual Perron identity, three actual integral enclosures, SourceDLMF513 and actual Abel remain explicit as applicable; see full theorem types'}
tmp=o/'REPLAY_RESULT.json.tmp';tmp.write_text(json.dumps(receipt,indent=2)+'\n');tmp.replace(o/'REPLAY_RESULT.json');print(receipt['status'],flush=True)
