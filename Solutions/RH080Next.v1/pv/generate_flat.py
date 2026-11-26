#!/usr/bin/env python3
"""Separate same-algorithm PV profile; never rewrites the original packet."""
import contextlib,importlib.util,io,json,subprocess,tempfile
from pathlib import Path
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
def need(x,m):
    if not x:raise ValueError(m)
def main():
    packet=dict(m=8,scale=10**18,coefficients=[533333333333333333]*8+[0]*8)
    (HERE/'flat_m8_r2.json').write_text(json.dumps(packet,indent=2)+'\n')
    with tempfile.TemporaryDirectory(prefix='rh080-flat-candidate-')as td:
        work=Path(td);(work/'lean').mkdir();(work/'population_m8_r2.json').write_text(json.dumps(packet)+'\n')
        for n in ['WindowSource.lean','WindowExecution.lean']:(work/'lean'/n).write_bytes((HERE/'lean'/n).read_bytes())
        spec=importlib.util.spec_from_file_location('candidate_population_generator',HERE/'generate_population.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);module.HERE=work
        with contextlib.redirect_stdout(io.StringIO()):module.main()
        (HERE/'flat_population_norm.c').write_bytes((work/'population_norm.c').read_bytes())
        binary=work/'native';p=subprocess.run(['gcc','-std=c11','-O2','-Wall','-Wextra','-Werror',str(work/'population_norm.c'),'-o',str(binary)],capture_output=True);need(p.returncode==0,'C candidate compile failed')
        output=subprocess.check_output([str(binary)],text=True);need(output.endswith('\n')and output[:-1].isascii()and output[:-1].isdecimal(),'Unexpected native candidate output');value=int(output)
        for base in ['AST','Source','Execution']:
            text=(work/'lean'/('Population'+base+'.lean')).read_text().replace('PopulationAST','FlatPopulationAST').replace('RH080Next.PopulationPV','RH080Next.FlatPopulationPV')
            (HERE/'lean'/('FlatPopulation'+base+'.lean')).write_text(text)
        modules=['Actual','Main','Model','Bounds','Samples','Norm','Control','SourceFinal','Nodes']
        for base in modules:
            text=(HERE/'lean'/('Population'+base+'.lean')).read_text()
            for name in ['AST','Source','Execution',*modules]:text=text.replace('import Population'+name+'\n','import FlatPopulation'+name+'\n')
            text=text.replace('RH080Next.PopulationPV','RH080Next.FlatPopulationPV').replace('887721072633027910',str(value))
            if base=='Model':
                a=text.index('def coefficients : List Nat :=');b=text.index('def coefficient (',a)
                text=text[:a]+'def coefficients : List Nat := '+str(packet['coefficients'])+'\n'+text[b:]
            if base=='Nodes':text=text.replace('nodalF0 nodes 8 = 1','nodalF0 nodes 8 = (15*533333333333333333 : ℝ)/(8*1000000000000000000)')
            (HERE/'lean'/('FlatPopulation'+base+'.lean')).write_text(text)
    print(json.dumps(dict(status='GENERATED_UNTRUSTED_PROFILE_NOT_PROOF',native_candidate=value,scale=10**18)))
if __name__=='__main__':main()
