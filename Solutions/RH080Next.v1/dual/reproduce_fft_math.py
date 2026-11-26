#!/usr/bin/env python3
# Copyright (c) 2026 IEANTN contributors. All rights reserved.
# Released under Apache 2.0 license as described in LICENSE.
# Authors: OpenAI (Codex)
"""Cold-build the mathematical FFT identities and both fixed-point budgets.

This checks mathematics only. It does NOT certify execution of either C FFT.
Compiler and eight generic dependencies are checked by reproduce_dual.context.
No prior application objects, native execution axioms or proof admissions.
"""
import argparse,json,os,re,subprocess,sys,time
from pathlib import Path
from reproduce_dual import context,need,publish,sha

MODULES = ["FFTButterfly","FFTRoundoff","FFTSeedBounds","FFTTwiddleBounds",
           "FFT24Bridge","FFTPolynomial","FFT17SeedBounds","FFT17Bridge"]
REQUIRED = {
 "recursiveFFT_eq_dft","roundedFFT_dft_error","rootSeed_error",
 "fft24_twiddle_bound","fft24_dft_error","mirrored_dft_re",
 "rootSeed17_error","fft17_twiddle_bound","fft17_dft_error"
}
STANDARD = {"propext","Classical.choice","Quot.sound"}

def main():
    a=argparse.ArgumentParser(allow_abbrev=False)
    a.add_argument('--repository',type=Path,required=True)
    a.add_argument('--context',type=Path,required=True)
    a.add_argument('--run',type=Path,required=True)
    o=a.parse_args()
    need(not os.path.lexists(o.run),'Fresh run directory required')
    root=o.repository.resolve(strict=True)
    source=root/'Solutions/RH080Next.v1/dual'
    need(source.resolve()==Path(__file__).resolve().parent,'Wrong repository/controller association')
    c=context(o.context,root)
    rows=[]; expected=[]
    for name in MODULES:
        p=source/(name+'.lean');raw=p.read_text()
        need(not re.search(r'^\s*(?:axiom|opaque)\b|\bsorry\b|\bnative_decide\b',raw,re.M),
             'Unapproved execution or admission leaf in '+name)
        printed=re.findall(r'^#print axioms ([\w.]+)\s*$',raw,re.M)
        need(printed,'No audited roots in '+name)
        expected.extend(printed)
        imports=re.findall(r'^import ([\w.]+)\s*$',raw,re.M)
        for dep in imports:
            need(dep.startswith('Mathlib.')or dep in MODULES[:len(rows)],
                 'Unpinned or incorrectly ordered dependency '+dep)
        rows.append({'module':name,'source':str(p.relative_to(root)),
                     'sha256':sha(p),'audited_roots':printed})
    need(len(expected)==len(set(expected))and REQUIRED<=set(expected),'Missing/duplicate required roots')
    o.run.mkdir(parents=True)
    bank=o.run/'objects';bank.mkdir()
    plan={'status':'FROZEN_MATHEMATICAL_FFT_BUILD_NOT_C_PV',
          'sources':rows,'context_sha256':sha(o.context),
          'controller_sha256':sha(Path(__file__)),
          'context_helper_sha256':sha(source/'reproduce_dual.py'),
          'compiler_sha256':c['compiler_sha256'],
          'optimization':sys.flags.optimize,'command':[sys.executable,*sys.argv],
          'remaining_source_obligations':['C helper/caller refinement','source-linked full FFT output'],
          'permitted_axioms':sorted(STANDARD)}
    publish(o.run/'PLAN.json',plan)
    env=dict(os.environ,LEAN_PATH=str(bank)+':'+c['generic_lean_path'])
    start=time.monotonic(); compiled=[]; audits={}
    for row in rows:
        name=row['module'];p=root/row['source']
        cmd=[c['compiler'],'-j1','-R',str(source),'-o',str(bank/(name+'.olean')),str(p)]
        out=o.run/(name+'.stdout');err=o.run/(name+'.stderr');tm=o.run/(name+'.time')
        t=time.monotonic()
        with out.open('x')as f,err.open('x')as g:
            result=subprocess.run(['/usr/bin/time','-v','-o',str(tm),*cmd],env=env,stdout=f,stderr=g)
        peak=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',tm.read_text())
        receipt={'module':name,'command':cmd,'returncode':result.returncode,
                 'seconds':time.monotonic()-t,'peak_RSS_KiB':int(peak[1])if peak else None,
                 'source_sha256':sha(p),'stdout_sha256':sha(out),'stderr_sha256':sha(err)}
        publish(o.run/(name+'.COMPILED.json'),receipt)
        need(result.returncode==0,'Compilation failed: '+name)
        need(receipt['source_sha256']==row['sha256'],'Source changed while compiling '+name)
        facts=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",out.read_text())
        need([n for n,_ in facts]==['RH080Next.FFT.'+n for n in row['audited_roots']],
             'Missing or changed axiom output '+name)
        for n,raw in facts:
            ax=[s.strip()for s in raw.split(',')if s.strip()]
            need(set(ax)<=STANDARD,'Unapproved axiom '+n)
            audits[n]=ax
        compiled.append(receipt)
        print('checked',name,flush=True)
    for row in rows:need(sha(root/row['source'])==row['sha256'],'Final source changed')
    need(sha(Path(__file__))==plan['controller_sha256'],'Controller changed')
    need(sha(source/'reproduce_dual.py')==plan['context_helper_sha256'],'Context helper changed')
    publish(o.run/'RESULT.json',{
        'status':'PASS_SOURCE_COLD_FFT_MATHEMATICS_STANDARD_AXIOMS_ONLY_NOT_C_PV',
        'modules':len(rows),'audited_theorems':len(audits),'axioms':audits,
        'seconds':time.monotonic()-start,
        'max_individual_RSS_KiB':max(v['peak_RSS_KiB']or 0 for v in compiled),
        'disk_bytes':sum(p.stat().st_size for p in o.run.rglob('*')if p.is_file()),
        'plan_sha256':sha(o.run/'PLAN.json'),'source_first_whole_fft_PV':False})
    print('PASS: mathematical FFT closure; C execution refinement remains separate.')

if __name__=='__main__':main()
