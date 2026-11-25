#!/usr/bin/env python3
"""Restore only the exact49 omitted pinned Gaussian cell proof-source files.

Uses the unchanged exact-rational generator and fixed candidates/partitions.
Never overwrites an existing different file, never downloads a result, and never
claims that source generation is Lean proof acceptance. Original Git/accepted
sources and proof banks are not deleted by this bootstrap.
"""
import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time


def need(ok,message):
    if not ok:raise ValueError(message)


def read(p):
    def pairs(items):
        out={}
        for key,value in items:
            need(key not in out,'Duplicate JSON key');out[key]=value
        return out
    return json.loads(p.read_bytes(),object_pairs_hook=pairs,
        parse_constant=lambda x:(_ for _ in ()).throw(ValueError('Non-finite JSON constant: '+x)))


def sha(p):
    need(p.is_file() and not p.is_symlink(),'Expected regular pinned file: '+str(p))
    h=hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(2**20),b''):h.update(block)
    return h.hexdigest()


def publish(p,value):
    need(not os.path.lexists(p),'Fresh bootstrap receipt required')
    fd,name=tempfile.mkstemp(prefix='.materialize-',dir=p.parent);q=Path(name)
    try:
        with os.fdopen(fd,'w') as f:json.dump(value,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
        os.link(q,p)
    finally:q.unlink()


def header(p):
    rows=[]
    for node in ast.parse(p.read_text()).body:
        if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='HEADER' for t in node.targets):
            rows.append(ast.literal_eval(node.value))
    need(len(rows)==1 and isinstance(rows[0],str),'Expected actual generator HEADER constant')
    return rows[0]


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--repository',type=Path,default=Path(__file__).resolve().parents[2])
    ap.add_argument('--scratch',type=Path)
    ap.add_argument('--check-only',action='store_true')
    ap.add_argument('--keep-scratch',action='store_true')
    a=ap.parse_args();R=a.repository.resolve(strict=True);S=R/'Solutions/RH080Study.v1'
    source_manifest=read(S/'REPRODUCTION_INPUTS.json');generated=read(S/'GENERATED_CELL_SOURCES.json')
    rows=generated['files'];need(len(rows)==49 and len({row['path'] for row in rows})==49,'Exact49 distinct generated identities required')
    by_path={row['path']:row for row in rows};all_rows=source_manifest['files']
    need(len(all_rows)==278 and len({row['path'] for row in all_rows})==278,'Expected exact278 reproduction input population')
    need({row['family'] for row in rows}=={'primal40','primal28'} and sum(row['family']=='primal40'for row in rows)==25 and sum(row['family']=='primal28'for row in rows)==24,'Generated family population differs')
    pinned={row['path']:row for row in all_rows}
    need(set(by_path)<=set(pinned),'Generated source outside frozen input universe')
    for family in ['primal40','primal28']:
        cell_manifest=read(S/'functional'/family/'CELL_SOURCE_MANIFEST.json')
        expected={row['module']:row['sha256'] for row in cell_manifest['chunks']}
        supplied={row['module']:row['sha256'] for row in rows if row['family']==family}
        need(expected==supplied and len(expected)==len(cell_manifest['chunks']),
             'Generated population differs from actual cell source manifest')
        for row in rows:
            if row['family']==family:
                need(row['path']=='Solutions/RH080Study.v1/functional/'+family+'/'+row['module']+'.lean',
                     'Generated module/path identity differs')
    for row in rows:
        need(row['sha256']==pinned[row['path']]['sha256'] and row['bytes']==pinned[row['path']]['bytes'],'Generated source/input identity differs')
    missing=[]
    for row in all_rows:
        relative=Path(row['path']);need(not relative.is_absolute() and '..'not in relative.parts,'Invalid pinned source path')
        p=R/relative;need(p.resolve().is_relative_to(R),'Pinned source leaves supplied repository')
        if not p.exists():
            need(row['path'] in by_path,'Missing non-generated reproduction input: '+row['path']);missing.append(row['path'])
        else:
            need(sha(p)==row['sha256'],'Existing reproduction input differs; never overwrite: '+row['path'])
    if a.check_only:
        print(json.dumps(dict(status='CHECKED_EXACT_GENERATED_SOURCE_BOOTSTRAP_POPULATION_NOT_PROOF',missing=missing,
                              missing_count=len(missing),complete_input_count=278)));return
    need(a.scratch is not None and not a.scratch.exists(),'Fresh --scratch required')
    scratch=a.scratch.resolve();need(not scratch.is_relative_to(R),'Bootstrap scratch must be outside repository');scratch.mkdir(parents=True)
    began=time.monotonic();controller_sha=sha(Path(__file__));(scratch/'materialize_generated.executed.py').write_bytes(Path(__file__).read_bytes())
    publish(scratch/'PLAN.json',dict(status='FROZEN_GENERATED_SOURCE_BOOTSTRAP_PLAN_NOT_PROOF',repository=str(R),missing_before=missing,
        exact_generated_population=rows,source_manifest_sha256=sha(S/'REPRODUCTION_INPUTS.json'),generated_manifest_sha256=sha(S/'GENERATED_CELL_SOURCES.json'),
        controller_sha256=controller_sha,no_overwrite=True,random_seed=None))
    commands=[];staged={};raw_dirs=[]
    flags=[] if not sys.flags.optimize else ['-O'if sys.flags.optimize==1 else'-OO']
    if missing:
        for family,degree in [('primal40','40'),('primal28','28')]:
            base=S/'functional'/family;raw=scratch/('raw-'+degree);raw_dirs.append(raw)
            candidate=base/('CANDIDATE_LAGUERRE'+degree+'.json')
            command=[sys.executable]+flags+[str(S/'functional/primal40/generate_kernel_cells.py'),'--candidate',str(candidate),
                '--partition',str(base/'PARTITION.json'),'--output',str(raw),'--chunk-size','48']
            start=time.monotonic()
            with (scratch/(family+'.stdout')).open('wb') as out,(scratch/(family+'.stderr')).open('wb') as err:
                completed=subprocess.run(command,stdout=out,stderr=err,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
            commands.append(dict(family=family,command=command,returncode=completed.returncode,seconds=time.monotonic()-start,
                stdout_sha256=sha(scratch/(family+'.stdout')),stderr_sha256=sha(scratch/(family+'.stderr'))))
            need(completed.returncode==0,'Exact-rational cell generator failed; original sources untouched')
            actual_header=header(base/'regenerate.py')
            for row in rows:
                if row['family']!=family:continue
                old=row['module'].replace('G40Cells'if family=='primal40'else'G28Cells','GaussianCells')
                text=(raw/(old+'.lean')).read_text()
                if family=='primal40':
                    text=text.replace('import GaussianSources\n','import G40Sources\nset_option autoImplicit false\n').replace('RHOnePrime.GaussianKernel','RH080.Gaussian40')
                else:
                    text=text.replace('import GaussianSources\n','import G28Sources\nset_option autoImplicit false\n').replace('namespace RHOnePrime.GaussianKernel','namespace RH080.Gaussian28\nopen RH080.Gaussian40').replace('end RHOnePrime.GaussianKernel','end RH080.Gaussian28')
                data=(actual_header+text).encode()
                need(hashlib.sha256(data).hexdigest()==row['sha256'] and len(data)==row['bytes'],'Generated source differs from exact pinned file: '+row['path'])
                staged[row['path']]=data
        need(set(staged)==set(by_path),'Not every exact generated source was checked')
        # Verify every staged source BEFORE installing any. Existing paths are
        # never overwritten: link publishes a fresh file atomically.
        for name in missing:
            target=R/name;need(target.parent.resolve().is_relative_to(R),'Generated target parent leaves repository')
            fd,tempname=tempfile.mkstemp(prefix='.pinned-cell-',dir=target.parent);temporary=Path(tempname)
            try:
                with os.fdopen(fd,'wb') as out:out.write(staged[name]);out.flush();os.fsync(out.fileno())
                try:os.link(temporary,target)
                except FileExistsError:need(sha(target)==by_path[name]['sha256'],'Concurrent existing source differs; never overwrite')
            finally:temporary.unlink()
    for row in all_rows:need(sha(R/row['path'])==row['sha256'],'Full278 input guard failed after materialization: '+row['path'])
    artifacts=[dict(path=str(p.relative_to(scratch)),sha256=sha(p),bytes=p.stat().st_size)
               for raw in raw_dirs for p in sorted(raw.rglob('*')) if p.is_file()]
    publish(scratch/'GENERATED_ARTIFACT_HASHES.json',dict(status='GENERATED_BOOTSTRAP_INTERMEDIATE_HASHES_NOT_PROOF',files=artifacts))
    removed=0
    if not a.keep_scratch:
        for raw in raw_dirs:
            need(raw.parent==scratch and not raw.is_symlink(),'Wrong bootstrap cleanup target')
            removed+=sum(row['bytes'] for row in artifacts if row['path'].startswith(raw.name+'/'))
            shutil.rmtree(raw)
    need(sha(Path(__file__))==controller_sha,'Bootstrap controller changed during generation')
    result=dict(status='PASS_EXACT_PINNED_GENERATED_SOURCE_MATERIALIZATION_ALL_278_INPUTS_NOT_A_LEAN_PROOF',
        restored_files=missing,restored_count=len(missing),exact_generated_population=49,complete_input_count=278,
        seconds=time.monotonic()-began,commands=commands,controller_sha256=controller_sha,
        plan_sha256=sha(scratch/'PLAN.json'),artifact_inventory_sha256=sha(scratch/'GENERATED_ARTIFACT_HASHES.json'),
        source_first_PV=False,mathematical_proofs_executed=False,intermediate_logical_bytes_removed=removed,
        no_existing_file_overwritten=True,original_Git_sources_and_accepted_proof_banks_unchanged=True,
        scope='Byte-identical source materialization only. Run reproduce_study.py afterward for actual Lean/source-first C proof execution.')
    publish(scratch/'RESULT.json',result);print(json.dumps(dict(status=result['status'],restored=len(missing),seconds=result['seconds'])))


if __name__=='__main__':main()
