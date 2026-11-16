"""Same namespace evidence gate as prior runs; no host-wide application bank."""
from pathlib import Path
import os,json,subprocess,sys,hashlib
sys.path.insert(0,'/task')
from reproduce import read,need,sha,save,parent_exact
q=read(Path('/request.json'))
ns={n:os.readlink('/proc/self/ns/'+n)for n in ['pid','mnt','net']}
need(all(ns[n]!=q['parent_namespaces'][n]for n in ns),'Distinct namespaces')
need(not Path(q['host_canary']).exists()and not Path('/task/.git').exists(),'Host workspace/history absent')
for x in q['compiler_pins']:need(sha(Path(x['path']))==x['sha256'],'Pinned compiler/kernel inside namespace')
parent_exact(Path('/prior4486'))
save(Path('/out/NAMESPACE_PROBE.json'),{'status':'PASS_DISTINCT_NAMESPACES_VALIDATED_RO_SOURCE_PARENT',
 'namespaces':ns,'host_workspace_absent':True,'research_git_history_absent':True,
 'application_object_inputs':'Exact previously isolated4486 same-pipeline source-built RO parent only',
 'empty_application_bank':False,'compiler_pins':q['compiler_pins']})
result=subprocess.run(q['command'])
save(Path('/out/COMMAND_RESULT.json'),{'command':q['command'],'exit_code':result.returncode})
raise SystemExit(result.returncode)
