#!/usr/bin/env python3
"""Actual all-mode no-overwrite and complete-input guards after cell bootstrap.

The supplied extraction must already have passed the real missing49 bootstrap.
No numerical regeneration/heavy Lean proof is repeated by these light controls.
"""
import argparse,hashlib,json,os,subprocess,sys,tempfile
from pathlib import Path


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--repository',type=Path,required=True);ap.add_argument('--run',type=Path,required=True);a=ap.parse_args()
    R=a.repository.resolve(strict=True);S=R/'Solutions/RH080Study.v1';need(not a.run.exists(),'Fresh bootstrap controls required');a.run.mkdir(parents=True);out=a.run.resolve();rows=[]
    target=R/json.loads((S/'GENERATED_CELL_SOURCES.json').read_text())['files'][0]['path'];original=target.read_bytes()
    def execute(name,args,good,marker):
        x=subprocess.run(list(map(str,args)),capture_output=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
        (out/(name+'.stdout')).write_bytes(x.stdout);(out/(name+'.stderr')).write_bytes(x.stderr)
        need((x.returncode==0)==good,'Wrong bootstrap CLI disposition '+name);need(marker.encode() in (x.stdout if good else x.stderr),'Wrong intended bootstrap guard '+name)
        rows.append(dict(name=name,command=list(map(str,args)),returncode=x.returncode,expected_success=good,intended_guard=marker,
                         stdout_sha256=sha(out/(name+'.stdout')),stderr_sha256=sha(out/(name+'.stderr'))))
    for label,flags in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
        prefix=[sys.executable]+flags;script=S/'materialize_generated.py'
        execute(label+'-complete-byte-guard',prefix+[script,'--repository',R,'--check-only'],True,'CHECKED_EXACT_GENERATED_SOURCE_BOOTSTRAP_POPULATION_NOT_PROOF')
        scratch=out/(label+'-already-present')
        execute(label+'-already-complete-no-write',prefix+[script,'--repository',R,'--scratch',scratch],True,'PASS_EXACT_PINNED_GENERATED_SOURCE_MATERIALIZATION_ALL_278_INPUTS_NOT_A_LEAN_PROOF')
        receipt=json.loads((scratch/'RESULT.json').read_text());need(receipt['restored_count']==0 and target.read_bytes()==original,'Existing correct source was modified')
        changed=original+b'\n-- INTENTIONALLY ALTERED OWN EXTRACTION CONTROL\n';target.write_bytes(changed)
        try:
            bad=out/(label+'-wrong-existing-file')
            execute(label+'-refuse-different-source',prefix+[script,'--repository',R,'--scratch',bad],False,'Existing reproduction input differs; never overwrite:')
            need(target.read_bytes()==changed and not bad.exists(),'Different existing source overwritten or generation started')
        finally:target.write_bytes(original)
        non_generated=S/'pv/dual_grid.c';saved=non_generated.read_bytes();non_generated.unlink()
        try:
            bad=out/(label+'-missing-input')
            execute(label+'-missing-nongenerated',prefix+[script,'--repository',R,'--scratch',bad],False,'Missing non-generated reproduction input:')
            need(not bad.exists(),'Missing-input guard started generation')
        finally:non_generated.write_bytes(saved)
    receipt=dict(status='PASS_12_ACTUAL_BOOTSTRAP_COMPLETE_INPUT_AND_NO_OVERWRITE_CLI_CONTROLS_ALL_PYTHON_MODES',rows=rows,
                 controller_sha256=sha(Path(__file__)),materializer_sha256=sha(S/'materialize_generated.py'),
                 source_repository=str(R),source_byte_guard_rechecked=True,heavy_proofs_or_generator_rerun=False)
    fd,name=tempfile.mkstemp(prefix='.receipt-',dir=out);p=Path(name)
    try:
        with os.fdopen(fd,'w') as f:json.dump(receipt,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
        os.link(p,out/'RESULT.json')
    finally:p.unlink()
    print(json.dumps(dict(status=receipt['status'],cases=len(rows))))


if __name__=='__main__':main()
