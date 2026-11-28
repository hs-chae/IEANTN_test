#!/usr/bin/env python3
"""Regenerate the fixed old dual frontend and observe its exact C output.

These source/run associations supplement the separate49-module kernel proof.
Physical execution and an untrusted parser are not mathematical acceptance.
"""
import argparse,os,re,shutil,subprocess,sys
from pathlib import Path
from bootstrap_context import PROJECT,REPOSITORY,atomic,need,sha

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--run',required=True,type=Path);ap.add_argument('--cc',type=Path)
    a=ap.parse_args();need(not os.path.lexists(a.run),'Fresh fixed-dual fixture directory required')
    cc=(a.cc or Path(shutil.which('cc')or'')).resolve(strict=True);need(cc.is_file(),'C compiler required')
    old=REPOSITORY/'Solutions/RH080Study.v1/pv';a.run.mkdir(parents=True)
    generator=a.run/'source-generator';generator.mkdir();(generator/'lean').mkdir();logs=a.run/'logs';logs.mkdir()
    inputs=[];commands=[]
    for name in ['dual_grid.c','PARAMETERS.json','parse_source.py']:
        source=old/name;target=generator/name;shutil.copyfile(source,target)
        inputs.append(dict(origin=str(source),snapshot=str(target),sha256=sha(source)))
    def invoke(tag,cmd):
        out=logs/(tag+'.stdout');err=logs/(tag+'.stderr')
        with out.open('xb')as o,err.open('xb')as e:r=subprocess.run(list(map(str,cmd)),stdout=o,stderr=e,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
        commands.append(dict(command=list(map(str,cmd)),returncode=r.returncode,
            stdout_sha256=sha(out),stderr_sha256=sha(err)))
        need(r.returncode==0,'Fixed-dual input command failed: '+tag);return out,err
    invoke('frontend',[sys.executable,generator/'parse_source.py'])
    outputs=[]
    for name in ['DualAST.lean','DualSource.lean']:
        generated=generator/'lean'/name;expected=old/'lean'/name
        need(sha(generated)==sha(expected),'Original dual frontend byte identity differs: '+name)
        outputs.append(dict(file=name,sha256=sha(generated),formal_source=str(expected)))
    source_text=(generator/'lean/DualSource.lean').read_text()
    chars=source_text.split('def sourceChars : List Char := [',1)[1].split(']',1)[0]
    need(bytes(int(x)for x in re.findall(r'Char.ofNat ([0-9]+)',chars))==(generator/'dual_grid.c').read_bytes(),
        'Fixed C bytes differ from formal source character fixture')
    executable=a.run/'dual_grid'
    invoke('compile',[cc,'-std=c11','-O2','-Wall','-Wextra','-Werror','-pedantic',generator/'dual_grid.c','-o',executable])
    stdout,stderr=invoke('observe',[executable])
    need(stdout.read_bytes()==b'1221161\n'and stderr.stat().st_size==0,'C output differs from the separate kernel-proved serialization')
    for item in inputs:need(sha(Path(item['origin']))==sha(Path(item['snapshot']))==item['sha256'],'Fixed dual input changed')
    version=subprocess.run([str(cc),'--version'],check=True,capture_output=True,text=True).stdout
    atomic(a.run/'RESULT.json',dict(status='PASS_REGENERATED_DUAL_FRONTEND_AND_FIXED_C_OBSERVATION',
        controller_sha256=sha(Path(__file__)),source_inputs=inputs,regenerated_formal_inputs=outputs,
        compiler=str(cc),compiler_sha256=sha(cc),compiler_version=version,
        executable_sha256=sha(executable),stdout='1221161\n',commands=commands,
        source_bytes_checked=True,mathematical_proof=False,compiler_correctness_proved=False))
    print('PASS original fixed dual source/AST regeneration and actual C observation1221161')
if __name__=='__main__':main()
