#!/usr/bin/env python3
"""Restore optional generic-runtime inventories; not a mathematical verifier."""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import tempfile
import urllib.request


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--repository', type=Path, required=True)
    ap.add_argument('--receipt', type=Path, required=True)
    a = ap.parse_args()
    need(not a.receipt.exists(), 'Fresh receipt required')
    manifest = Path(__file__).with_name('OPTIONAL_RUNTIME_REFERENCES.json')
    def unique(items):
        result = {}
        for key,value in items:
            need(key not in result, 'Duplicate manifest key')
            result[key]=value
        return result
    def finite(value):
        result=float(value)
        need(math.isfinite(result),'Nonfinite manifest number')
        return result
    j = json.loads(manifest.read_bytes(),object_pairs_hook=unique,parse_float=finite,
                   parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))
    need(j['schema']=='RH080_OPTIONAL_GENERIC_RUNTIME_INVENTORIES_V1', 'Wrong schema')
    commit = j['source_commit']
    need(isinstance(commit,str) and len(commit)==40 and all(c in '0123456789abcdef' for c in commit), 'Unpinned source')
    result = []
    root = a.repository.resolve(strict=True)
    rows = j['files']
    need(len(rows)==3 and len({x['path'] for x in rows})==3, 'Wrong optional population')
    for row in rows:
        rel = PurePosixPath(row['path'])
        need(not rel.is_absolute() and str(rel)==row['path'] and '..'not in rel.parts,
             'Invalid source-relative path')
        need(str(rel).startswith('Solutions/RH080Study.v1/exposure-runtime/references/trees/')
             and rel.suffix=='.json','Unexpected optional source')
        need(type(row['bytes']) is int and 0<row['bytes']<30_000_000, 'Unexpected source size')
        h = row['sha256']
        need(isinstance(h,str) and len(h)==64 and all(c in '0123456789abcdef' for c in h), 'Invalid source hash')
        target = root.joinpath(*rel.parts)
        need(target.parent.resolve().is_relative_to(root), 'Destination outside repository')
        fetched = not os.path.lexists(target)
        if fetched:
            url = 'https://raw.githubusercontent.com/hs-chae/IEANTN_test/'+commit+'/'+str(rel)
            request = urllib.request.Request(url,headers={'User-Agent':'IvyMathematicsReproduction/1.0'})
            with urllib.request.urlopen(request,timeout=60) as response:
                raw=response.read(row['bytes']+1)
            need(len(raw)==row['bytes'] and sha(raw)==h, 'Downloaded source differs')
            target.parent.mkdir(parents=True,exist_ok=True)
            fd,name=tempfile.mkstemp(prefix='.inventory-',dir=target.parent)
            temporary=Path(name)
            try:
                with os.fdopen(fd,'wb')as out:out.write(raw)
                os.link(temporary,target)
            finally:temporary.unlink(missing_ok=True)
        need(target.is_file() and not target.is_symlink(),'Nonregular inventory')
        raw=target.read_bytes()
        need(len(raw)==row['bytes'] and sha(raw)==h,'Existing inventory differs; never overwritten')
        result.append(dict(path=str(rel),sha256=h,bytes=len(raw),downloaded=fetched))
    receipt=dict(status='PASS_OPTIONAL_GENERIC_INVENTORY_BYTES_NOT_A_PROOF_OR_RESEARCH_EXECUTION',
                 source_commit=commit,files=result,manifest_sha256=sha(manifest.read_bytes()),
                 script_sha256=sha(Path(__file__).read_bytes()),required_for_mathematical_replay=False)
    a.receipt.parent.mkdir(parents=True,exist_ok=True)
    fd,name=tempfile.mkstemp(prefix='.runtime-reference-',dir=a.receipt.parent)
    temporary=Path(name)
    try:
        with os.fdopen(fd,'w')as out:json.dump(receipt,out,indent=2,allow_nan=False);out.write('\n')
        os.link(temporary,a.receipt)
    finally:temporary.unlink(missing_ok=True)
    print(json.dumps({'status':receipt['status'],'downloaded':sum(x['downloaded']for x in result),'files':len(result)}))


if __name__=='__main__':
    main()
