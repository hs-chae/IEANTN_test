#!/usr/bin/env python3
"""Bounded actual normal/-O/-OO guards and deterministic figure checks."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--context',type=Path,required=True)
    ap.add_argument('--render-package',type=Path,required=True)
    ap.add_argument('--run',type=Path,required=True)
    a=ap.parse_args()
    need(not os.path.lexists(a.run),'Fresh control run required');a.run.mkdir(parents=True)
    here=Path(__file__).resolve().parent
    context=json.loads(a.context.read_text())
    rows=[]
    def call(name,mode,script,flags,success):
        cmd=[sys.executable,*mode,str(here/script),*map(str,flags)]
        p=subprocess.run(cmd,capture_output=True)
        (a.run/(name+'.stdout')).write_bytes(p.stdout);(a.run/(name+'.stderr')).write_bytes(p.stderr)
        need((p.returncode==0)==success,'Unexpected child status: '+name)
        rows.append(dict(name=name,command=cmd,exit_code=p.returncode,expected_success=success,
            stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stderr_sha256=hashlib.sha256(p.stderr).hexdigest()))
    for mode,label in [([], 'normal'),(['-O'],'O'),(['-OO'],'OO')]:
        positive=a.run/('scalar-'+label)
        call('scalar-'+label,mode,'reproduce_competition_scalar.py',['--context',a.context,'--run',positive],True)
        for kind in ['compiler','revision','generic']:
            changed=dict(context)
            if kind=='compiler':changed['compiler_sha256']='0'*64
            if kind=='revision':changed['generic_dependencies']=[dict(x)for x in context['generic_dependencies']];changed['generic_dependencies'][0]['revision']='0'*40
            if kind=='generic':changed['generic_lean_path']=[]
            bad=a.run/(label+'-'+kind+'.json');bad.write_text(json.dumps(changed))
            rejected=a.run/(label+'-'+kind)
            call(label+'-'+kind,mode,'reproduce_competition_scalar.py',['--context',bad,'--run',rejected],False)
            need(not (rejected/'RESULT.json').exists(),'Rejected scalar emitted acceptance')
        call(label+'-reuse',mode,'reproduce_competition_scalar.py',['--context',a.context,'--run',positive],False)
        figure=a.run/('figure-'+label)
        call('figure-'+label,mode,'plot_population_competition.py',['--render-package',a.render_package,'--out',figure],True)
        receipt=json.loads((figure/'COMPETITION_FRONTIER.json').read_text())
        need(receipt['old_G_O_crossing_order']['paper_is_strictly_lower'] is True,'Plot ordering reversed')
        need(receipt['rows']==2008,'Wrong exact figure grid')
        call('figure-'+label+'-reuse',mode,'plot_population_competition.py',['--render-package',a.render_package,'--out',figure],False)
    for suffix in ['svg','pdf','csv','json']:
        identities={sha(a.run/('figure-'+label)/('COMPETITION_FRONTIER.'+suffix))for label in ['normal','O','OO']}
        need(len(identities)==1,'Figure differs across modes: '+suffix)
    result=dict(status='PASS_ACTUAL_COMPETITION_CONTROLS_ALL_PYTHON_MODES',children=len(rows),
        actual_scalar_kernel_runs=3,negative_controls=15,actual_plot_runs=3,all_mode_figure_bytes_equal=True,
        scope='Auxiliary scalar proof and figure only; not source-first PV or a new ANT theorem.',rows=rows)
    temp=a.run/'RESULT.json.tmp';temp.write_text(json.dumps(result,indent=2)+'\n');os.link(temp,a.run/'RESULT.json');temp.unlink()
    print(json.dumps({k:result[k]for k in ['status','children','actual_scalar_kernel_runs','negative_controls','actual_plot_runs']}))


if __name__=='__main__':main()
