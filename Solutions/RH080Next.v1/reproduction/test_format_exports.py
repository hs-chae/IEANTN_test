#!/usr/bin/env python3
"""Actual all-mode positive and mutation controls for format-only bank exports."""
import argparse,json,os,shutil,subprocess,sys
from pathlib import Path
from bootstrap_context import atomic,need,read_json,sha
HERE=Path(__file__).resolve().parent
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for name in ['context','population','run']:ap.add_argument('--'+name,required=True,type=Path)
    ap.add_argument('--analytic',required=True,action='append',type=Path)
    a=ap.parse_args();need(len(a.analytic)==3,'Supply three accepted analytic formats')
    need(not os.path.lexists(a.run),'Fresh control directory required');a.run.mkdir(parents=True)
    scripts={'analytic':HERE/'export_simple_analytic_bank.py','population':HERE/'export_population_bank.py'}
    hashes={k:sha(v)for k,v in scripts.items()};cases=[]
    def invoke(mode,label,kind,base,success):
        target=a.run/(mode+'-'+label+'-bank');cmd=[sys.executable]+{'normal':[],'O':['-O'],'OO':['-OO']}[mode]
        cmd += [str(scripts[kind]),'--context',str(a.context),'--base',str(base),'--run',str(target)]
        out=a.run/(mode+'-'+label+'.stdout');err=a.run/(mode+'-'+label+'.stderr')
        with out.open('xb')as o,err.open('xb')as e:r=subprocess.run(cmd,stdout=o,stderr=e,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
        need((r.returncode==0)is success,'Unexpected format export outcome: '+mode+'/'+label)
        need((target/'RESULT.json').is_file()is success,'Fresh format acceptance state differs')
        if success:
            expected='PASS_FORMAT_ONLY_ANALYTIC_BANK_EXPORT'if kind=='analytic'else'PASS_FORMAT_ONLY_POPULATION91_BANK_EXPORT'
            need(read_json(target/'RESULT.json')['status']==expected,'Wrong format-only result')
        cases.append(dict(mode=mode,case=label,expected_success=success,returncode=r.returncode,
            command=cmd,stdout_sha256=sha(out),stderr_sha256=sha(err)))
    fixtures={}
    for kind,base,exitkey in [('analytic',a.analytic[0],'exitcode'),('population',a.population,'returncode')]:
        for mutation in ['wrong-status','false-exitcode','object-hash']:
            target=a.run/(kind+'-'+mutation+'-fixture')
            shutil.copytree(base,target,copy_function=os.link)
            path=target/'RESULT.json';value=read_json(path);path.unlink()
            if mutation=='wrong-status':value['status']='UNACCEPTED'
            elif mutation=='false-exitcode':value['commands'][0][exitkey]=False
            else:value['commands'][0]['object_sha256']='0'*64
            atomic(path,value);fixtures[(kind,mutation)]=target
    for mode in ['normal','O','OO']:
        for i,base in enumerate(a.analytic):invoke(mode,'analytic-'+str(i),'analytic',base,True)
        invoke(mode,'population','population',a.population,True)
        for (kind,mutation),base in fixtures.items():invoke(mode,kind+'-'+mutation,kind,base,False)
    need({k:sha(v)for k,v in scripts.items()}==hashes,'Format validator source changed during controls')
    atomic(a.run/'RESULT.json',dict(status='PASS_FORMAT_ONLY_EXPORT_ALL_MODES_AND_MUTATION_CONTROLS',
        scripts=hashes,controller_sha256=sha(Path(__file__)),cases=cases,positive=12,negative=18,
        context_sha256=sha(a.context),new_compilation=False,new_mathematical_proof=False))
    print('PASS format exports:12 positive/18 negative actual CLIs, normal/-O/-OO')
if __name__=='__main__':main()
