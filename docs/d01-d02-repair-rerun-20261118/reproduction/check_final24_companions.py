"""Check source/command documentation tools only. No numerical children or deletion."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parent;S=R.parent;W=S.parent;D=S/'coordinator-private/final24-reproduction-companion-controls-v1';D.mkdir();P='/usr/bin/python3';root=Path('/data/ivy-d01-d02-portable-20261118-c022-1224mjs2/source-tree-24-v2');archive=S/'coordinator-private/portable-relocation-v2/portable-final24-source-review-v2.tar.gz';bad=D/'DELIBERATE_INVALID_RECEIPT.json';bad.write_text('{}\n');rows=[]
def need(v,m):
 if not v:raise ValueError(m)
def pin(p):return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
for mode,flags in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
 verify=[str(R/'verify_extract_final24.py'),'--archive',str(archive),'--receipt',str(archive)+'.RECEIPT.json'];inventory=[str(R/'final24_command_inventory.py'),'--source-root',str(root),'--registry',str(W/'EXPOSURE_LONGCHAIN_20261117_V1_RESOURCES'),'--controller-python',P,'--new-authority-directory',str(root.parent/'NEW_HOST_AUTHORITIES_NOT_ISSUED')]
 for name,args,code in [('archive-positive',verify,0),('inventory-positive',inventory,0),('archive-reject-invalid-receipt',verify[:-1]+[str(bad)],1),('inventory-reject-original-incompatible-source',inventory[:2]+[str(root.parent/'source-tree-24')]+inventory[3:],1)]:
  argv=[P,'-I','-B']+flags+args;q=subprocess.run(argv,capture_output=True);out=D/(name+'.'+mode+'.stdout');err=D/(name+'.'+mode+'.stderr');out.write_bytes(q.stdout);err.write_bytes(q.stderr);need(q.returncode==code,'exact companion CLI rejection/acceptance')
  if code==0:
   v=json.loads(q.stdout)
   if name=='archive-positive':need(v['regular_members']==7296 and v['source_compiler_model_or_scope_calls']==0,'all exact source identities')
   else:need(len(v['cases'])==24 and sum(x['complete_route_count']for x in v['cases'])==595 and v['scopes_compilers_numerical_or_model_calls']==0,'all24 whole command census')
  rows.append({'name':name,'mode':mode,'argv':argv,'returncode':q.returncode,'stdout':pin(out),'stderr':pin(err)})
receipt={'status':'PASS_TWELVE_ACTUAL_FINAL24_COMPANION_METADATA_CLIS_NORMAL_O_OO','sources':[pin(R/'verify_extract_final24.py'),pin(R/'final24_command_inventory.py'),pin(R/'README_PORTABLE_FINAL24.md')],'checks':rows,'scientific_model_compiler_or_scope_calls':0,'actual_extraction_run_in_this_control':False,'acceptance_uses_explicit_errors_under_all_optimization_modes':True};f=D/'RESULT.json';tmp=D/'RESULT.pending';tmp.write_text(json.dumps(receipt,indent=2)+'\n');tmp.replace(f);print(json.dumps(pin(f)))
