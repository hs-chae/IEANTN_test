#!/usr/bin/env python3
"""Replay the selected source package with pinned generic libraries only."""
from pathlib import Path
import argparse, datetime, hashlib, json, os, shutil, subprocess, sys, time, types

B=Path(__file__).resolve().parent
def need(ok,msg):
    if not ok:raise ValueError(msg)
def read(p):
    def pairs(rows):
        d={}
        for k,v in rows:need(k not in d,'duplicate JSON key');d[k]=v
        return d
    return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,
        parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb')as f:
        for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
    return h.hexdigest()
p=argparse.ArgumentParser(allow_abbrev=False)
p.add_argument('--out',type=Path)
p.add_argument('--compiler',type=Path)
p.add_argument('--generic-root',action='append',default=[],metavar='NAME=PATH')
p.add_argument('--check',action='store_true')
a=p.parse_args();manifest=read(B/'SOURCE_MANIFEST.json')
compiler=(a.compiler or Path(manifest['default_compiler'])).resolve()
need(compiler.is_file()and sha(compiler)==manifest['compiler_sha256'],'compiler identity differs')
roots={row['name']:Path(row['default_root'])for row in manifest['generic_libraries']}
for raw in a.generic_root:
    name,sep,value=raw.partition('=');need(sep and name in roots and value,'invalid generic root mapping')
    roots[name]=Path(value).resolve()
for row in manifest['files']:
    path=(B/row['path']).resolve();need(path.is_relative_to(B)and path.is_file()and sha(path)==row['sha256'],'package input changed:'+row['path'])
for row in manifest['generic_libraries']:
    index=B/row['inventory'];need(sha(index)==row['inventory_sha256'],'generic inventory changed')
    tree=read(index);root=roots[row['name']]
    for item in tree['files']:
        f=(root/item['path']).resolve()
        need(f.is_relative_to(root.resolve())and f.is_file(),'generic input missing/escaping:'+str(f))
        need(f.stat().st_size==item['bytes']and sha(f)==item['sha256'],'generic library differs:'+str(f))
print('PASS_ALL_SOURCE_AND_FULL_PINNED_GENERIC_INVENTORIES',flush=True)
if a.check:raise SystemExit(0)
need(a.out is not None,'--out required for build')
O=a.out.resolve();need(not O.exists(),'fresh output required')
for d in ['source','objects','logs','resources']:(O/d).mkdir(parents=True,exist_ok=True)
shutil.copytree(B/'source',O/'source',dirs_exist_ok=True)
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(O/'objects')]+[str(roots[r['name']])for r in manifest['generic_libraries']])
core=compiler.parent.parent/'lib/lean'
result={'schema':'RAMANUJAN640_PORTABLE_SOURCE_REPLAY_V2','status':'RUNNING',
    'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'source_manifest_sha256':sha(B/'SOURCE_MANIFEST.json'),'compiler':str(compiler),
    'compiler_sha256':sha(compiler),'generic_roots':{n:str(v)for n,v in roots.items()},
    'application_cached_objects_used':False,'leancert_cached_objects_used':False,
    'new_proof_cached_objects_used':False,'model_calls':0,'source_first_PV':False,'modules':[]}
try:
    # Exact original program, with only its readonly absolute table path remapped.
    original=B/'numerical/ram_cert.py';table=B/'numerical/Tables.lean'
    m=types.ModuleType('frozen_900s');code=original.read_text().replace('/ieantn/IEANTN/Nodes/Buthe/v1/Tables.lean',str(table))
    exec(compile(code,str(original),'exec'),m.__dict__)
    m.setup();tested,skipped,leaves=m.bisect_cover();e0,e1=m.expi(m.Q(1));rows=m.tables();data=[]
    for l,u,lower in leaves:
        r=m.cell(rows,m.Q(640000000000),l,u,e0,e1)
        data.append({'l':str(l),'u':str(u),'lower':str(lower),'c':str(r[2]),'d':str(r[3])})
    raw=read(B/'numerical/RAW_EIGHT_LEAVES.json')
    need((tested,skipped,len(data))==(19,2,8)and data==raw['leaves'],'frozen numerical witnesses changed')
    need(sha(original)==raw['source_sha256']and sha(table)==raw['source_table_sha256'],'frozen numerical source identity differs')
    result['raw_input_sha256']=sha(B/'numerical/RAW_EIGHT_LEAVES.json')
    built=set();allnames={r['module']for r in manifest['modules']}
    need(len(allnames)==len(manifest['modules']),'duplicate source module identity')
    for spec in manifest['modules']:
        name=spec['module'];rel=Path(*name.split('.')).with_suffix('.lean');src=O/'source'/rel
        need(sha(src)==spec['source_sha256'],'selected source differs:'+name)
        need(all(d in built for d in spec['direct_source_imports']if d in allnames),'module order/dependency gap:'+name)
        obj=O/'objects'/rel.with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
        cmd=[str(compiler),'--root='+str(O/'source'),'-j8','-o',str(obj),str(src)]
        resource=O/'resources'/(name+'.txt');started=time.monotonic();print('BUILD',name,flush=True)
        run=subprocess.run(['/usr/bin/time','-f','%e %M','-o',str(resource)]+cmd,cwd=O/'source',env=env,capture_output=True,text=True)
        row={'module':name,'source':str(src),'source_sha256':sha(src),'command':cmd,
            'returncode':run.returncode,'elapsed_seconds':time.monotonic()-started,
            'resource_receipt_text':resource.read_text(),'stdout':run.stdout,'stderr':run.stderr}
        result['modules'].append(row);(O/'logs'/(name+'.json')).write_text(json.dumps(row,indent=2)+'\n')
        need(run.returncode==0,'compiler child failed:'+name)
        need(not any(s in run.stdout for s in ['sorryAx','Lean.ofReduceBool','Lean.trustCompiler']),'forbidden printed proof trust:'+name)
        probe=subprocess.run([str(compiler),'--deps',str(src)],cwd=O/'source',env=env,capture_output=True,text=True)
        row['compiler_dependency_probe']={'returncode':probe.returncode,'stdout':probe.stdout,'stderr':probe.stderr}
        need(probe.returncode==0,'compiler dependency probe failed:'+name)
        for line in probe.stdout.split('\n'):
            if line:need(any(Path(line).is_relative_to(root)for root in [O/'objects',core]+list(roots.values())),'unexpected cached dependency:'+line)
        (O/'logs'/(name+'.json')).write_text(json.dumps(row,indent=2)+'\n');built.add(name);print('PASS',name,flush=True)
    need(built==allnames and manifest['modules'][-1]['module']=='FinalResult','incomplete selected source closure')
    result['final_source_sha256']=sha(O/'source/FinalResult.lean')
    result['final_object_sha256']=sha(O/'objects/FinalResult.olean')
    final=result['modules'][-1]
    import re
    for theorem in ['ramanujan_640b','actual_gap_640b']:
        hits=re.findall(r"'Ramanujan640\."+theorem+r"' depends on axioms: \[([^\]]*)\]",final['stdout'])
        need(len(hits)==1 and set(s.strip()for s in hits[0].split(','))=={'propext','Classical.choice','Quot.sound'},'final exact axiom gate failed')
    result['status']='PASS_PORTABLE_ALL_APPLICATION_AND_LEANCERT_SOURCE_GENERIC_CACHE_ONLY'
except Exception as error:
    result['status']='FAILED_OR_PARTIAL_NO_PORTABLE_SOURCE_ACCEPTANCE';result['error']=str(error)
finally:
    result['completed_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    tmp=O/'RESULT.pending';tmp.write_text(json.dumps(result,indent=2)+'\n');os.link(tmp,O/'RESULT.json');tmp.unlink()
    print(result['status'],O/'RESULT.json',flush=True)
if not result['status'].startswith('PASS_'):raise SystemExit(1)
