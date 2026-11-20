#!/usr/bin/env python3
"""Fresh actual positive/rejection CLIs under normal/-O/-OO; explicit errors."""
from pathlib import Path
import argparse,json,hashlib,subprocess,sys
from verify_scalar_source_receipts import need,sha,read,S

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--kind',choices=['log','cell','domain'],required=True);p.add_argument('--proposal',type=Path,required=True);p.add_argument('--original-log-proposal',type=Path);p.add_argument('--context',type=Path,default=S/'BUILD_CONTEXT.json');p.add_argument('--out',type=Path,required=True);p.add_argument('--cpus',default='16');a=p.parse_args();context=read(a.context);out=a.out.resolve();need(out.is_relative_to(Path(context['new_application_object_root']).resolve().parent)and not out.exists(),'fresh context-owned control output');need(a.kind!='domain'or a.original_log_proposal is not None,'domain control requires originallogproposal');out.mkdir(parents=True);validator=S/'scripts'/('verify_scalar_domains.py'if a.kind=='domain'else'verify_scalar_source_receipts.py');pin=sha(validator);records=[]
 for mode,flags in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
  for good in [True,False]:
   label=mode+('-good'if good else'-bad-lock');target=out/label;proposal=a.proposal
   if not good:
    j=read(a.proposal);j['rows_sha256']='0'*64;proposal=out/(label+'.json');proposal.write_text(json.dumps(j,indent=2)+'\n')
   command=[sys.executable,*flags,str(validator),'--proposal',str(proposal),'--context',str(a.context),'--out',str(target),'--cpus',a.cpus]
   if a.kind=='domain':command+=['--original-log-proposal',str(a.original_log_proposal)]
   else:command+=['--kind',a.kind]
   r=subprocess.run(command,capture_output=True,text=True);(out/(label+'.stdout')).write_text(r.stdout);(out/(label+'.stderr')).write_text(r.stderr)
   if good:
    need(r.returncode==0 and(target/'RESULT.json').is_file(),'actual positiveCLI rejected '+label);result=read(target/'RESULT.json');need(result['controller_sha256']==pin,'current validator identity inpositive result');record=dict(mode=mode,positive=True,command=command,returncode=r.returncode,result=str(target/'RESULT.json'),result_sha256=sha(target/'RESULT.json'))
   else:
    need(r.returncode!=0 and not(target/'RESULT.json').exists(),'negativeCLI accepted '+label);record=dict(mode=mode,positive=False,command=command,returncode=r.returncode,stderr_sha256=sha(out/(label+'.stderr')))
   records.append(record)
 need(sha(validator)==pin,'validatorchanged during controls');result=dict(status='PASS_SIX_ACTUAL_SCALAR_VERIFIER_ROUTES_ALL_OPTIMIZATIONS',kind=a.kind,controller_sha256=pin,test_driver_sha256=sha(__file__),routes=records);(out/'RESULT.json.pending').write_text(json.dumps(result,indent=2)+'\n');(out/'RESULT.json.pending').replace(out/'RESULT.json');print(json.dumps({'status':result['status'],'result':str(out/'RESULT.json')}))
if __name__=='__main__':main()
