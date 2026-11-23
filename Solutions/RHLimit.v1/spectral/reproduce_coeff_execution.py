#!/usr/bin/env python3
"""Reproduce the unchanged historical C coefficient application after its cold proof.
The CSV comparison is an additional execution receipt, not the source-first proof.
"""
from pathlib import Path
import argparse,math,shutil,subprocess,time
from reproduce_cold_append import need,read,sha,save,audit
B=Path(__file__).resolve().parent

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--proof-run',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();pr=a.proof_run.resolve();out=a.out.resolve()
 need(not out.exists(),'fresh C execution output');m=read(B/'SOURCE_CLOSURE.json')
 c=next(x for x in m['resources']if x['path'].endswith('/rh_coeff.c'))
 source=B.parent.parents[1]/c['path'];need(sha(source)==c['sha256'],'actual C resource pin')
 rows=audit((pr/'logs/CoefficientPV.stdout').read_text());need({'CoefficientPV.source','CoefficientPV.numerical'}<={x['theorem']for x in rows},'actual source/AST/model proof audit absent')
 model=next(x for x in m['modules']if x['module']=='CoefficientPV');need(sha(pr/'source/CoefficientPV.lean')==model['sha256'],'cold coefficient proofsource changed')
 need(sha(pr/'source/rh_coeff.c')==c['sha256'],'cold source/model execution resource changed')
 out.mkdir(parents=True);(out/'rh_coeff.c').write_bytes(source.read_bytes())
 driver=out/'driver.c';driver.write_text('#include <stdio.h>\n#include <inttypes.h>\n#include "rh_coeff.c"\nint main(void){for(uint64_t j=0;j<=20;j++)printf("%" PRIu64 " %" PRIu64 "\\n",j,rh_coeff(j));return 0;}\n')
 compiler=Path(shutil.which('cc')).resolve();binary=out/'rh_coeff';cmd=[str(compiler),'-std=c11','-Wall','-Wextra','-Werror','-O2',str(driver),'-o',str(binary)]
 t=time.monotonic();cp=subprocess.run(['/usr/bin/time','-v',*cmd],capture_output=True,text=True);(out/'compile.stdout').write_text(cp.stdout);(out/'compile.stderr').write_text(cp.stderr);need(cp.returncode==0,'actual C compilation')
 cp=subprocess.run(['/usr/bin/time','-v',str(binary)],capture_output=True,text=True);(out/'outputs.txt').write_text(cp.stdout);(out/'run.stderr').write_text(cp.stderr);need(cp.returncode==0,'actual C execution')
 expected=''.join(str(k)+' '+str(sum(math.factorial(i)*math.comb(k,i)for i in range(k+1))-sum(math.factorial(i)*math.factorial(k-i)for i in range(k+1)))+'\n'for k in range(21))
 need(cp.stdout==expected,'compiled source outputs differ from verified coefficient model')
 save(out/'RESULT.json',{'status':'PASS_UNCHANGED_SOURCE_FIRST_C_COMPONENT_EXECUTION_JOIN',
  'controller_sha256':sha(__file__),'C_source_sha256':sha(out/'rh_coeff.c'),'formal_model_source_sha256':model['sha256'],
  'formal_proof_stdout_sha256':sha(pr/'logs/CoefficientPV.stdout'),'formal_proof_axioms':rows,
  'compiler':str(compiler),'compiler_sha256':sha(compiler),'compiler_version':subprocess.run([str(compiler),'--version'],capture_output=True,text=True,check=True).stdout,
  'command':cmd,'driver_sha256':sha(driver),'binary_sha256':sha(binary),'outputs_sha256':sha(out/'outputs.txt'),'seconds':time.monotonic()-t,
  'remaining_trust':'Existing restrictedC source-to-AST/typeduint64 semantics and numerical outputs kernelproved in completed source replay; nativecompiledexecution additionally assumes genericCcompiler/runtime/OS/hardware contracts. Harness/CSVcomparison is additional execution evidence, not the source proof. Whole620 numerical pipeline is notPV.'})
 print('PASS_UNCHANGED_SOURCE_FIRST_C_COMPONENT_EXECUTION_JOIN')
if __name__=='__main__':main()
