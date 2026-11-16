"""Existing sandbox executor; source-only adapter and one validated4486 RO parent."""
from pathlib import Path
import argparse,os,sys,subprocess,time,importlib.util,json
B=Path(__file__).resolve().parent
P=B.parent
spec=importlib.util.spec_from_file_location('public_reproduce',P/'reproduce.py');proof=importlib.util.module_from_spec(spec);spec.loader.exec_module(proof)
need,read,sha,save=proof.need,proof.read,proof.sha,proof.save

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--environment',type=Path,required=True)
 ap.add_argument('--moment-parent',type=Path,required=True);ap.add_argument('--out',type=Path,required=True)
 a=ap.parse_args();out=a.out.resolve();prior=a.moment_parent.resolve()
 need(not out.exists()and not out.is_relative_to(P)and not out.is_relative_to(prior),'Fresh disjoint output')
 proof.inputs();association=proof.parent_exact(prior)
 cap=proof.load(P/'Dependencies/moment/reproduce.py','validated_source_recipe')
 _,_,base,runner=cap.inputs()
 strict_environment=read(a.environment.resolve())
 env=runner.environment_inputs(a.environment.resolve(),base);need(env==strict_environment,'Strict environment parsing')
 tool=Path(env['compiler']).resolve().parent.parent
 generic=[tool]
 for d in env['generic_dependencies']:
  root=Path(d['source']).resolve();need(Path(d['objects']).resolve().is_relative_to(root),'Generic object/source association')
  generic.append(root)
 generic=[p for p in sorted(set(generic))if not any(p!=q and p.is_relative_to(q)for q in generic)]
 need(not any(P.is_relative_to(g)or prior.is_relative_to(g)for g in generic),'No application hidden in generic mount')
 inputs=[{'path':str(p.relative_to(P)),'sha256':sha(p)}for p in sorted(P.rglob('*'))if p.is_file()and '__pycache__'not in p.parts]
 need(not any(p.is_symlink()for p in P.rglob('*')),'No source symlinks')
 out.mkdir();(out/'root').mkdir();(out/'data').mkdir()
 canary=out/'HOST_CANARY';canary.write_text('Owned namespace canary, excluded from mounts.\n')
 pins=[{'path':str(p),'sha256':sha(p)}for p in [Path(env['compiler']),tool/'lib/lean/libleanshared.so',tool/'lib/lean/Init.olean',tool/'lib/lean/Std.olean']]
 command=['/usr/bin/python3.10','-I','-B','/task/reproduce.py','--environment','/environment.json','--moment-parent','/prior4486','--out','/out/run']
 save(out/'REQUEST.json',{'command':command,'parent_namespaces':{n:os.readlink('/proc/self/ns/'+n)for n in ['pid','mnt','net']},'host_canary':str(canary),'compiler_pins':pins})
 entries=[{'kind':'ro','path':'/task','source':str(P)}, {'kind':'rw','path':'/out','source':str(out/'data')},
  {'kind':'ro','path':'/prior4486','source':str(prior)}, {'kind':'ro','path':'/entry.py','source':str(B/'entry.py')},
  {'kind':'ro','path':'/request.json','source':str(out/'REQUEST.json')}, {'kind':'dir','path':'/home/worker'},
  {'kind':'ro','path':'/environment.json','source':str(a.environment.resolve())}]
 for path in ['/usr/lib/python3.10','/usr/lib/x86_64-linux-gnu','/lib/x86_64-linux-gnu','/lib64/ld-linux-x86-64.so.2']:
  need(Path(path).exists(),'Generic system libraries');entries.append({'kind':'ro','path':path,'source':path})
 for dest,src in {'/usr/bin/python3.10':'/usr/bin/python3.10','/usr/bin/time':'/usr/bin/time','/usr/bin/git':'/usr/bin/git','/bin/sh':'/usr/bin/dash'}.items():entries.append({'kind':'ro','path':dest,'source':str(Path(src).resolve())})
 entries +=[{'kind':'ro','path':str(p),'source':str(p)}for p in generic]
 task={'version':1,'root':str(out/'root'),'cwd':'/out','uid':os.getuid(),'gid':os.getgid(),
  'command':['/usr/bin/python3.10','-I','-B','/entry.py'],'network':'offline','tmpfsSize':'128m','tmpSize':'1g',
  'entries':entries,'env':{'HOME':'/home/worker','PATH':str(tool/'bin')+':/usr/bin:/bin','LANG':'C.UTF-8','LEAN_NUM_THREADS':'1','MALLOC_ARENA_MAX':'2'}}
 save(out/'SPEC.json',task);save(out/'INPUTS.json',inputs)
 commandHost=['unshare','--user','--map-root-user','--mount','--propagation','private','--','/usr/bin/python3.10','-I','-B',str(B/'sandbox.py'),str(out/'SPEC.json')]
 start=time.monotonic()
 with(out/'stdout').open('wb')as f,(out/'stderr').open('wb')as g:q=subprocess.run(commandHost,stdout=f,stderr=g)
 need(q.returncode==0,'Isolated append failed; inspect preserved stderr')
 probe=read(out/'data/NAMESPACE_PROBE.json');result=read(out/'data/COMMAND_RESULT.json');mathematics=read(out/'data/run/RECEIPT.json')
 need(probe['status']=='PASS_DISTINCT_NAMESPACES_VALIDATED_RO_SOURCE_PARENT'and result['exit_code']==0,'Actual namespace/command acceptance')
 need(mathematics['status']=='PASS_PUBLIC_SOLUTION_SIX_EXACT_TYPES_STD3','Actual mathematical acceptance')
 need(all(sha(P/x['path'])==x['sha256']for x in inputs),'All source inputs unchanged')
 need(proof.parent_exact(prior)==association,'RO parent unchanged')
 save(out/'RECEIPT.json',{'status':'PASS_ISOLATED_PUBLIC_SOLUTION_SIX_EXACT_TYPES_STD3',
  'seconds':time.monotonic()-start,'source_manifest_sha256':sha(out/'INPUTS.json'),
  'mathematical_receipt_sha256':sha(out/'data/run/RECEIPT.json'),'namespace_probe_sha256':sha(out/'data/NAMESPACE_PROBE.json'),
  'prior_classification':'Validated isolated4486 RO parent plus fresh vector3/coretypes/helper/Solution; not empty-bank',
  'solution_imports_admitted_challenge':False,'exact_type_environments_separate':True,
  'official_comparator_receipt':False,'resource_scope':'Separate outer admission/metrics receipt required'})
 print(out/'RECEIPT.json')
if __name__=='__main__':main()
