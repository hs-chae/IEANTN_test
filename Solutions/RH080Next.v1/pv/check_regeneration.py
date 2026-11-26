#!/usr/bin/env python3
"""Regenerate source/AST fixtures in a private temporary directory and compare.
The candidate parser is untrusted; Lean independently checks its generated AST.
"""
import contextlib,hashlib,importlib.util,io,json,shutil,tempfile
from pathlib import Path
import sys
sys.dont_write_bytecode = True
HERE=Path(__file__).resolve().parent
def need(x,m):
    if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(name):
    spec=importlib.util.spec_from_file_location(name,HERE/(name+'.py'));module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module

def main():
    rows=[]
    with tempfile.TemporaryDirectory(prefix='rh080-source-regeneration-')as td:
        work=Path(td);(work/'lean').mkdir()
        for n in ['window_scalars.c','w4.json','population_m8_r2.json']:shutil.copyfile(HERE/n,work/n)
        for n in ['WindowSource.lean','WindowExecution.lean']:shutil.copyfile(HERE/'lean'/n,work/'lean'/n)
        module=load('generate_frontend');module.HERE=work
        with contextlib.redirect_stdout(io.StringIO()):module.main()
        names=['WindowAST.lean','WindowSource.lean','WindowData.lean','WindowExecution.lean']
        for n in names:
            a=work/'lean'/n;b=HERE/'lean'/n
            need(a.read_bytes()==b.read_bytes(),'Window regeneration mismatch: '+n)
            rows.append(dict(file='lean/'+n,sha256=sha(a)))
        module=load('generate_population');module.HERE=work
        with contextlib.redirect_stdout(io.StringIO()):module.main()
        for n in ['population_norm.c','lean/PopulationAST.lean','lean/PopulationSource.lean','lean/PopulationExecution.lean']:
            a=work/n;b=HERE/n;need(a.read_bytes()==b.read_bytes(),'Population regeneration mismatch: '+n);rows.append(dict(file=n,sha256=sha(a)))
    print(json.dumps(dict(status='PASS_DETERMINISTIC_SOURCE_AST_REGENERATION',artifacts=rows),indent=2))
if __name__=='__main__':main()
