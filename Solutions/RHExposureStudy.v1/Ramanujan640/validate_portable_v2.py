#!/usr/bin/env python3
"""Validate every actual standalone source-replay child; effective under -O/-OO."""
from pathlib import Path
import argparse, hashlib, json, re, sys
def need(ok,msg):
    if not ok:raise ValueError(msg)
def read(p):
    def pairs(rows):
        d={}
        for k,v in rows:need(k not in d,'duplicate JSON key');d[k]=v
        return d
    return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--package',type=Path,required=True);p.add_argument('--replay',type=Path,required=True);a=p.parse_args();B=a.package.resolve()
m=read(B/'SOURCE_MANIFEST.json');v=read(a.replay)
need(v.get('schema')=='RAMANUJAN640_PORTABLE_SOURCE_REPLAY_V2','wrong replay schema')
need(v.get('status')=='PASS_PORTABLE_ALL_APPLICATION_AND_LEANCERT_SOURCE_GENERIC_CACHE_ONLY','portable replay not accepted')
need(sha(B/'SOURCE_MANIFEST.json')==v.get('source_manifest_sha256'),'source manifest changed')
for flag in['application_cached_objects_used','leancert_cached_objects_used','new_proof_cached_objects_used','source_first_PV']:need(v.get(flag)is False,'unpermitted trust flag:'+flag)
need(type(v.get('model_calls'))is int and v['model_calls']==0,'unexpected model call')
for row in m['files']:
    f=(B/row['path']).resolve();need(f.is_relative_to(B)and f.is_file()and sha(f)==row['sha256'],'package input changed:'+row['path'])
expected={r['module']:r for r in m['modules']};need(len(expected)==len(m['modules']),'duplicate selected module')
rows=v.get('modules');need(isinstance(rows,list)and rows,'empty active source closure');seen={}
names=[r.get('module')for r in rows]
need(all(isinstance(n,str)for n in names)and len(set(names))==len(names)and set(names)==set(expected),'active source module population differs')
# Reject every failed child before expensive object/source hashing. Positive
# receipts still undergo every hash/dependency check below.
for row in rows:
    need(type(row.get('returncode'))is int and row['returncode']==0,'active compiler route failed:'+row['module'])
    dep=row.get('compiler_dependency_probe')
    need(isinstance(dep,dict)and type(dep.get('returncode'))is int and dep['returncode']==0,'dependency child failed:'+row['module'])
    need(not any(s in row.get('stdout','')for s in['sorryAx','Lean.ofReduceBool','Lean.trustCompiler']),'forbidden printed proof trust:'+row['module'])
O=Path(rows[-1]['source']).parents[1];roots=[Path(s)for s in v['generic_roots'].values()];core=Path(v['compiler']).parent.parent/'lib/lean'
need(sha(v['compiler'])==v.get('compiler_sha256')==m['compiler_sha256'],'compiler identity differs')
probed=set();objects={}
for row in rows:
    name=row.get('module');need(isinstance(name,str)and name in expected and name not in seen,'invalid/duplicate/extra module');seen[name]=row
    need(type(row.get('returncode'))is int and row['returncode']==0,'active compiler route failed:'+name)
    rel=Path(*name.split('.')).with_suffix('.lean');src=O/'source'/rel
    need(str(src)==row.get('source')and src.is_file()and sha(src)==row.get('source_sha256')==expected[name]['source_sha256'],'source identity differs:'+name)
    obj=O/'objects'/rel.with_suffix('.olean');need(obj.is_file()and not obj.is_symlink(),'compiled source object absent/symlink:'+name);objects[name]=sha(obj)
    need(not any(s in row.get('stdout','')for s in['sorryAx','Lean.ofReduceBool','Lean.trustCompiler']),'forbidden printed proof trust:'+name)
    dep=row.get('compiler_dependency_probe');need(isinstance(dep,dict)and type(dep.get('returncode'))is int and dep['returncode']==0,'dependency child failed:'+name)
    for raw in dep['stdout'].split('\n'):
        if raw:
            f=Path(raw);need(any(f.is_relative_to(r)for r in[O/'objects',core]+roots),'unexpected cached dependency:'+raw)
            if f.is_relative_to(O/'objects'):probed.add('.'.join(f.relative_to(O/'objects').with_suffix('').parts))
need(set(seen)==set(expected)and probed.issubset(seen),'active source closure incomplete')
need('FullRH'in seen and 'RHTailActual640'in seen and 'RamAlgebra'in seen and 'LeanCert.Tactic.IntervalAuto'in seen,'required source/checker/provider route missing')
final=seen['FinalResult']
for name in['ramanujan_640b','actual_gap_640b']:
    matches=re.findall(r"'Ramanujan640\."+name+r"' depends on axioms: \[([^\]]*)\]",final['stdout'])
    need(len(matches)==1 and set(s.strip()for s in matches[0].split(','))=={'propext','Classical.choice','Quot.sound'},'final exact axiom gate failed:'+name)
need(sha(B/'numerical/RAW_EIGHT_LEAVES.json')==v.get('raw_input_sha256'),'frozen numerical inputs changed')
need(sha(O/'objects/FinalResult.olean')==v.get('final_object_sha256'),'final object changed')
need(sha(O/'source/FinalResult.lean')==v.get('final_source_sha256'),'final source changed')
print(json.dumps({'status':'PASS_ALL_PORTABLE_SOURCE_CHILDREN_DEPENDENCIES_STANDARD_AXIOMS_AND_RAW_INPUTS','module_count':len(rows),'checker_module_count':sum(n.startswith('LeanCert.')for n in seen),'python_optimization':sys.flags.optimize,'replay_sha256':sha(a.replay),'source_manifest_sha256':sha(B/'SOURCE_MANIFEST.json'),'object_sha256':objects}))
