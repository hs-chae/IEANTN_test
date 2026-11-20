#!/usr/bin/env python3
"""Regenerate EXACT source bytes under a relocated context in allPythonmodes."""
from pathlib import Path
import argparse,json,subprocess,sys,hashlib
from verify_scalar_source_receipts import need,read,sha,S,LOCK

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--original-log-proposal',type=Path,required=True);p.add_argument('--original-cell-proposal',type=Path,required=True);p.add_argument('--original-domain-proposal',type=Path,required=True);a=p.parse_args();out=a.out.resolve();need(not out.exists(),'fresh explicitlyownedrelocationroot');out.mkdir(parents=True);context=read(S/'BUILD_CONTEXT.json');context['new_application_object_root']=str(out/'lean');context['fresh_new_application_modules']=True;cp=out/'CONTEXT.json';cp.write_text(json.dumps(context,indent=2)+'\n');base=read(a.original_log_proposal);need(base['rows_sha256']==LOCK and sha(base['rows_source'])==LOCK,'originalrowsidentity');old={'log':base,'cell':read(a.original_cell_proposal),'domain':read(a.original_domain_proposal)};commands=[];records=[]
 def run(name,argv,flags):
  cmd=[sys.executable,*flags,str(S/'scripts'/name),*argv];r=subprocess.run(cmd,capture_output=True,text=True);log=out/(f'command-{len(commands):03d}');log.with_suffix('.stdout').write_text(r.stdout);log.with_suffix('.stderr').write_text(r.stderr);commands.append(dict(command=cmd,returncode=r.returncode,stdout_sha256=sha(log.with_suffix('.stdout')),stderr_sha256=sha(log.with_suffix('.stderr'))));need(r.returncode==0,'actualrelocationCLI failed '+name);return r
 for mode,flags in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
  root=out/mode;root.mkdir();log=root/'log';cell=root/'cell';domain=root/'domain'
  run('generate_scalar_pv_rows.py',['--out',str(log),'--rows-source',base['rows_source'],'--rows-sha256',LOCK,'--context',str(cp)],flags)
  run('generate_scalar_pv_final.py',['--proposal',str(log/'PROPOSAL.json'),'--context',str(cp)],flags)
  run('generate_cell_source_rows.py',['--out',str(cell),'--original-log-proposal',str(log/'PROPOSAL.json'),'--context',str(cp)],flags)
  run('generate_cell_domains.py',['--out',str(domain),'--original-log-proposal',str(log/'PROPOSAL.json'),'--context',str(cp)],flags)
  n=0
  for kind,folder in [('log',log),('cell',cell),('domain',domain)]:
   fresh=read(folder/'PROPOSAL.json');need(fresh['row_count']==285,'samewholepopulation');pairs=list(zip(old[kind]['modules'],fresh['modules']));need(len(pairs)==9,'samechunks')
   for before,after in pairs:
    need(before['module']==after['module']and before['sha256']==after['sha256']==sha(after['source']),'exactscientificproofbytes');n+=1
   prior=read(a.original_log_proposal.parent/'LOG_FINAL_PROPOSAL.json')if kind=='log'else old[kind]['final'];final=read(folder/'LOG_FINAL_PROPOSAL.json')if kind=='log'else fresh['final'];need(prior['sha256']==final['sha256']==sha(final['source']),'exactfinalproofbytes');n+=1
  native=root/'native';run('observe_finite_scalars_native.py',['--out',str(native),'--rows-source',base['rows_source'],'--rows-sha256',LOCK,'--context',str(cp)],flags);result=read(native/'RESULT.json');need(result['rows']==285 and result['outputs_sha256']=='5694b33a262a2010d5192759085b487d86752d70ea61315f323299535da1743d','unchangedactualnativeoutputs')
  bad=root/'native-bad';cmd=[sys.executable,*flags,str(S/'scripts/observe_finite_scalars_native.py'),'--out',str(bad),'--rows-source',base['rows_source'],'--rows-sha256','0'*64,'--context',str(cp)];r=subprocess.run(cmd,capture_output=True,text=True);need(r.returncode!=0 and not(bad/'RESULT.json').exists(),'nativebadlockaccepted');commands.append(dict(command=cmd,returncode=r.returncode,expected_rejection=True));records.append(dict(mode=mode,exact_proof_source_modules=n,native_receipt=str(native/'RESULT.json'),native_receipt_sha256=sha(native/'RESULT.json')))
 scripts=['generate_scalar_pv_rows.py','generate_scalar_pv_final.py','generate_cell_source_rows.py','generate_cell_domains.py','observe_finite_scalars_native.py'];result=dict(status='PASS_CONTEXT_RELOCATION_EXACT_GENERATORS_AND_NATIVE_OBSERVER_ALL_OPTIMIZATIONS',context=str(cp),context_sha256=sha(cp),scratch_root_outside_original_fixed_root=str(out),scripts={name:sha(S/'scripts'/name)for name in scripts},test_driver_sha256=sha(__file__),routes=records,commands=commands,not_claimed='No Lean compilation or cleanfullpipelineclosure is inferred from this source-regeneration/nativeobservercontrol.')
 (out/'RESULT.json.pending').write_text(json.dumps(result,indent=2)+'\n');(out/'RESULT.json.pending').replace(out/'RESULT.json');print(json.dumps({'status':result['status'],'result':str(out/'RESULT.json')}))
if __name__=='__main__':main()
