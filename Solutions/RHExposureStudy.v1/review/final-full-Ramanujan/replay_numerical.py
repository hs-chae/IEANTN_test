#!/usr/bin/env python3
"""Replay exact frozen final numerical programs; execution is not a proof."""
from pathlib import Path
import datetime, hashlib, json, subprocess, sys, time

B = Path(__file__).resolve().parent
O = B / 'numerical-v2'
if O.exists(): raise ValueError('fresh output required')
O.mkdir()
study = Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-rh-propagation-20261120')
F = study / 'evaluator-private/final-locks/IEANTN_RH/files'
sha = lambda f: hashlib.sha256(Path(f).read_bytes()).hexdigest()
launcher = O / 'launch.py'
launcher.write_text('''import pathlib,runpy,sys,types
F=pathlib.Path(sys.argv[1]);N=pathlib.Path(sys.argv[2]);name=sys.argv[3]
m=types.ModuleType("ram_cert");m.__file__=str(F/"ram_cert.py")
s=(F/"ram_cert.py").read_text().replace("/ieantn/IEANTN/Nodes/Buthe/v1/Tables.lean",str(N/"IEANTN/Nodes/Buthe/v1/Tables.lean"))
exec(compile(s,m.__file__,"exec"),m.__dict__);sys.modules["ram_cert"]=m
sys.argv=[str(F/(name+".py"))]
s=(F/(name+".py")).read_text().replace("/ieantn/IEANTN/Nodes/Buthe/v1/Tables.lean",str(N/"IEANTN/Nodes/Buthe/v1/Tables.lean"))
exec(compile(s,sys.argv[0],"exec"),{"__name__":"__main__","__file__":sys.argv[0]})
''')
result = {'schema': 'FINAL_RAMANUJAN_NUMERICAL_READONLY_REPLAY_V1',
    'status': 'RUNNING', 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'mathematical_status': 'Identical numerical execution evidence only; no proof inferred from running programs.',
    'adapter': 'Only readonly absolute Buthe table path remapped in imported ram_cert and final program; all other program bytes and mathematical parameters unchanged.',
    'source_pins': {n: sha(F / n) for n in ['ram_cert.py','refined_ram.py','crossing_cert.py','johnston_tail.py']},
    'table_source_sha256': sha(study / 'network/IEANTN/Nodes/Buthe/v1/Tables.lean'), 'runs': []}
try:
    names = [('refined_ram','RefinedRamRun.txt'), ('crossing_cert','CrossingRun.txt'), ('johnston_tail','JohnstonTailRun.txt')]
    for name, historical in names:
        outputs = []
        for mode in [0,1,2]:
            cmd=[sys.executable]+(['-O'] if mode==1 else ['-OO'] if mode==2 else [])+[str(launcher),str(F),str(study/'network'),name]
            started=time.monotonic();run=subprocess.run(cmd,capture_output=True)
            (O/f'{name}-O{mode}.stdout').write_bytes(run.stdout)
            (O/f'{name}-O{mode}.stderr').write_bytes(run.stderr)
            row={'program':name,'optimization':mode,'command':cmd,'returncode':run.returncode,
                'elapsed_seconds':time.monotonic()-started,'stdout_sha256':hashlib.sha256(run.stdout).hexdigest(),
                'matches_frozen_stdout':run.stdout==(F/historical).read_bytes()}
            result['runs'].append(row);outputs.append(run.stdout)
            if run.returncode or not row['matches_frozen_stdout']:raise ValueError('exact numerical replay mismatch:'+name)
        if len(set(outputs))!=1:raise ValueError('optimization changed exact numerical stdout:'+name)
    if any(sha(F/n)!=v for n,v in result['source_pins'].items()):raise ValueError('frozen source changed')
    result['status']='PASS_IDENTICAL_FROZEN_OUTPUTS_NORMAL_O_OO_NO_PROOF_INFERRED'
except Exception as error:
    result['status']='FAILED_OR_PARTIAL_NUMERICAL_REPLAY';result['error']=str(error)
(O/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'],flush=True)
if not result['status'].startswith('PASS_'):raise SystemExit(1)
