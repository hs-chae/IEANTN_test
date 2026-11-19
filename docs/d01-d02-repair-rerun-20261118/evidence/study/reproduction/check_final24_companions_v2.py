"""Check current final24 companion CLIs; no numerical work, compiler or deletion.
Unlike historical V1 this accepts the actual source/archive/registry as arguments.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys
sys.dont_write_bytecode=True

def need(value,message):
    if not value:raise ValueError(message)
def pin(path):return {'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--archive',type=Path,required=True);p.add_argument('--receipt',type=Path,required=True);p.add_argument('--source-root',type=Path,required=True);p.add_argument('--registry',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();need(not a.out.exists()and a.out.parent.is_dir(),'fresh metadata output');a.out.mkdir();comp=Path(__file__).resolve().parent;invalid=a.out/'DELIBERATE_INVALID_RECEIPT.json';invalid.write_text('{}\n');rows=[]
    def call(name,flags,arguments,expected):
        argv=[sys.executable,'-I','-S','-B']+flags+arguments;q=subprocess.run(argv,capture_output=True);out=a.out/(name+'.'+(''.join(flags)or'normal')+'.stdout');err=out.with_suffix('.stderr');out.write_bytes(q.stdout);err.write_bytes(q.stderr);need(q.returncode==expected,'intended acceptance/rejection '+name)
        rows.append({'name':name,'flags':flags,'argv':argv,'returncode':q.returncode,'stdout':pin(out),'stderr':pin(err)})
        return json.loads(q.stdout)if expected==0 else None
    for flags in [[],['-O'],['-OO']]:
        v=call('archive-positive',flags,[str(comp/'verify_extract_final24.py'),'--archive',str(a.archive),'--receipt',str(a.receipt)],0);need(v['regular_members']==7303 and v['source_compiler_model_or_scope_calls']==0,'complete exact7303 archive')
        v=call('all24-command-inventory',flags,[str(comp/'final24_command_inventory.py'),'--source-root',str(a.source_root),'--registry',str(a.registry),'--controller-python','/usr/bin/python3','--new-authority-directory',str(a.out/'NEVER_CREATED_AUTHORITIES')],0);need(len(v['cases'])==24 and sum(x['complete_route_count']for x in v['cases'])==595 and v['scopes_compilers_numerical_or_model_calls']==0,'all24 exact595 command routes')
        v=call('all24-coordinator',flags,[str(comp/'reproduce_final24.py'),'--source-root',str(a.source_root),'--registry',str(a.registry),'--authority-dir',str(a.out/'NEVER_CREATED_AUTHORITIES'),'--cases','all','--check'],0);need(v['status']=='PASS_FINAL24_LOCAL_COORDINATOR_METADATA_ONLY'and len(v['cases'])==24 and v['actual_scopes_compilers_models']==0,'complete source-only coordinator')
        call('reject-invalid-receipt',flags,[str(comp/'verify_extract_final24.py'),'--archive',str(a.archive),'--receipt',str(invalid)],1)
    result={'status':'PASS_TWELVE_ACTUAL_CURRENT_FINAL24_COMPANION_METADATA_CLIS_NORMAL_O_OO_STDLIB_ONLY','checks':rows,'sources':[pin(comp/x)for x in ['verify_extract_final24.py','final24_command_inventory.py','reproduce_final24.py','check_final24_companions_v2.py']],'new_scientific_scope_compiler_numerical_model_or_deletion_calls':0,'source_members':7303,'full_cases':24,'required_routes':595,'acceptance_explicit_under_optimization':True};file=a.out/'RESULT.json';temporary=file.with_suffix('.pending');temporary.write_text(json.dumps(result,indent=2)+'\n');temporary.replace(file);print(json.dumps(pin(file)))
if __name__=='__main__':main()
