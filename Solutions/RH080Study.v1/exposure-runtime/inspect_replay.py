#!/usr/bin/env python3
"""Inspect additive clean-root exposure replay prerequisites, without inference.

Never rewrites a historical lock/protocol, reads credentials, relaxes a runtime
check, starts a worker, or calls a model. A source receipt is not trial readiness.
"""
import argparse
import ast
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):
    need(p.is_file() and not p.is_symlink(),'Regular pinned file required')
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(2**20),b''):h.update(b)
    return h.hexdigest()


def read(p):
    def pairs(items):
        x={}
        for k,v in items:
            need(k not in x,'Duplicate JSON key');x[k]=v
        return x
    return json.loads(p.read_bytes(),object_pairs_hook=pairs,
                      parse_constant=lambda x:(_ for _ in ()).throw(ValueError(x)))


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--repository',type=Path,default=Path(__file__).resolve().parents[3])
    ap.add_argument('--corpus',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();R=a.repository.resolve(strict=True);here=R/'Solutions/RH080Study.v1/exposure-runtime'
    need(not os.path.lexists(a.output),'Fresh output required')
    components=read(here/'SOURCE_COMPONENTS.json');sources=[]
    for row in components['sources']:
        source=R/row['path'];need(sha(source)==row['sha256'],'Reviewed runtime component differs: '+row['path'])
        if source.suffix=='.py':ast.parse(source.read_text())
        sources.append(dict(path=row['path'],sha256=row['sha256'],bytes=source.stat().st_size))
    corpus=read(here/'CORPUS_RECIPE.json');checked=[];missing=[]
    if a.corpus is not None:
        root=a.corpus.resolve(strict=True)
        for row in corpus['frozen_files']:
            p=root/row['path']
            if not p.is_file():missing.append(row['path']);continue
            need(p.resolve().is_relative_to(root) and not p.is_symlink(),'Corpus input escapes fresh root')
            need(p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],'Frozen corpus bytes differ: '+row['path'])
            checked.append(row['path'])
    else:
        missing=[row['path'] for row in corpus['frozen_files']]
    tools={name:shutil.which(name) for name in ['codex','unshare','python3.10','git','gcc','g++']}
    versions={}
    for name in ['websockets','PyMuPDF','mpmath','sympy']:
        try:versions[name]=importlib.metadata.version(name)
        except importlib.metadata.PackageNotFoundError:versions[name]=None
    blockers=[
        'No new reviewed packet/runtime/fixture/execution lock has been generated or accepted for the relocated root.',
        'Exact source assignment and generic compiler/package/certificate mount trees must be regenerated and independently checked; historical absolute lock paths are provenance, not portable launch authority.',
        'Pinned mpmath/sympy source trees and their per-file manifests must be recreated under the new runtime root; a version string alone is insufficient.',
        'Linux namespace executor and cgroup CPU/RAM/scratch applicability require a fresh successful no-model fixture using the identical intended mounts; no fallback that weakens isolation is permitted.',
        'A configured native Codex account and the accepted Codex executable/runtime are external requirements; this inspector does not read or package account credentials.',
        'Historical model alias has no exposed immutable service revision or replay sampling seed; future outputs cannot be claimed byte-identical.']
    if missing:blockers.insert(0,'Frozen corpus is not fully reconstructed; missing '+str(len(missing))+' files. Exact recovered source bytes may be unavailable from the currently served primary URL.')
    result=dict(status='PASS_ADDITIVE_EXPOSURE_RUNTIME_SOURCE_AUDIT_NO_INFERENCE_NOT_TRIAL_READINESS',
                sources=sources,corpus_checked=checked,corpus_missing=missing,tools=tools,installed_versions=versions,
                source_manifest_sha256=sha(here/'SOURCE_COMPONENTS.json'),corpus_recipe_sha256=sha(here/'CORPUS_RECIPE.json'),
                model_calls=0,worker_launches=0,credentials_read=False,historical_locks_modified=False,
                ready_for_research_trials=False,remaining_prerequisites=blockers,
                disclosure='Generic source/config bytes and syntax checked only. This is not a source-first mathematical proof, an actual isolation fixture or a completed exposure rerun.')
    a.output.parent.mkdir(parents=True,exist_ok=True)
    fd,name=tempfile.mkstemp(prefix='.runtime-',dir=a.output.parent);p=Path(name)
    try:
        with os.fdopen(fd,'w') as f:json.dump(result,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
        os.link(p,a.output)
    finally:p.unlink()
    print(json.dumps(dict(status=result['status'],components=len(sources),corpus_missing=len(missing),model_calls=0)))


if __name__=='__main__':main()
