#!/usr/bin/env python3
"""Regenerate source/AST fixtures privately, then compare every selected byte.
The candidate parser is untrusted; Lean independently checks its generated AST.
"""
import contextlib,hashlib,importlib.util,io,json,shutil,subprocess,sys,tempfile
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
def need(x,m):
    if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(name):
    spec=importlib.util.spec_from_file_location(name,HERE/(name+'.py'))
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

def main():
    rows=[]
    with tempfile.TemporaryDirectory(prefix='rh080-source-regeneration-')as td:
        work=Path(td)/"private"/"numerical"/"pv"
        work.mkdir(parents=True)
        old=HERE.parents[2]/"Solutions/RH080Study.v1/pv"
        for name in ["dual_grid.c","parse_source.py","lean/DualExecution.lean"]:
            dest=Path(td)/"Solutions/RH080Study.v1/pv"/name
            dest.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(old/name,dest)
        for p in HERE.glob('*.py'):shutil.copyfile(p,work/p.name)
        for p in HERE.glob('*.json'):shutil.copyfile(p,work/p.name)
        for p in HERE.glob('*.c'):shutil.copyfile(p,work/p.name)
        shutil.copytree(HERE/'lean',work/'lean',ignore=shutil.ignore_patterns('__pycache__','*.olean','*.ilean'))
        shutil.copytree(HERE/'fft',work/'fft',ignore=shutil.ignore_patterns('__pycache__','*.olean','*.ilean'))
        def compare(names):
            for name in names:
                a=work/name;b=HERE/name
                need(a.is_file()and b.is_file(),'Missing regenerated artifact '+name)
                need(a.read_bytes()==b.read_bytes(),'Regeneration mismatch: '+name)
                rows.append(dict(file=name,sha256=sha(a)))
        def generate(name):
            module=load(name);module.HERE=work
            with contextlib.redirect_stdout(io.StringIO()):module.main()
        generate('generate_scalars')
        compare(['window_scalars.c','w4.json'])
        generate('generate_frontend')
        compare(['lean/Window'+n+'.lean'for n in ['AST','Source','Data','Execution']])
        generate('generate_population')
        compare(['population_norm.c']+['lean/Population'+n+'.lean'for n in ['AST','Source','Execution']])
        generate('generate_flat')
        compare(['flat_m8_r2.json','flat_population_norm.c']+
                ['lean/FlatPopulation'+n+'.lean'for n in ['AST','Source','Execution','Actual','Main','Model','Bounds','Samples','Norm','Control','SourceFinal','Nodes']])
        generate('generate_fap')
        compare(['fap_original.json','fap_scaled.json','fap_scalars.c']+
                ['lean/Fap'+n+'.lean'for n in ['AST','Source','Execution','Data','AffineData','Model','RationalBridge','Main','SourceFinal','TrustAudit','ActualF0','ActualArea','ActualHeight','ActualV0','ActualV1','ActualMu2','ActualMaximum']]+
                ['fft/fap_fft.c','fft/fap_fft_recursive.c'])
        for flags,prefix in [([], 'FFT'),(['--recursive'],'FFTRecursive'),(['--fap'],'FapFFT'),(['--fap','--recursive'],'FapFFTRecursive')]:
            command=[sys.executable,str(work/'fft/generate_fft_ast.py'),*flags]
            p=subprocess.run(command,capture_output=True,text=True)
            need(p.returncode==0,'FFT candidate regeneration failed: '+p.stderr)
            compare(['lean/'+prefix+n+'.lean'for n in ['AST','Source']])
    print(json.dumps(dict(status='PASS_DETERMINISTIC_SOURCE_AST_REGENERATION',python_optimize=sys.flags.optimize,controller_sha256=sha(Path(__file__)),artifacts=rows),indent=2))
if __name__=='__main__':main()
