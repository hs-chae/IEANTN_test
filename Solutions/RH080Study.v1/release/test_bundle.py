#!/usr/bin/env python3
"""Exercise actual creator/verifier CLIs and malformed archives in all modes."""
import argparse
import hashlib
import json
import os
import tempfile
from pathlib import Path
import subprocess
import sys
import zipfile

HERE = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--run', type=Path, required=True)
    a = ap.parse_args()
    need(not a.run.exists(), 'Fresh control directory required')
    a.run.mkdir(parents=True)
    source = a.run / 'sources'
    source.mkdir()
    raw = b'int main(void){return 0;}\n'
    (source / 'program.c').write_bytes(raw)
    omitted = [dict(path=f'generated/Cell{i:02d}.lean', bytes=12, sha256='1'*64)
               for i in range(49)]
    selection = dict(schema='RH080_REVIEWED_COMPACT_BUNDLE_SELECTION_V1',
                     reviewed_by='/root', source_commit='2'*40,
                     files=[dict(path='program.c', bytes=len(raw), sha256=sha(raw), role='fixture')],
                     readme='Fixture, not a proof.\n', omitted_regenerable_sources=omitted)
    sp = a.run / 'selection.json'
    sp.write_text(json.dumps(selection))
    cases = []
    for mode in [[], ['-O'], ['-OO']]:
        label = mode[0][1:] if mode else 'normal'
        output = a.run / (label+'.zip')
        command = [sys.executable]+mode+[str(HERE/'create_bundle.py'), '--repository', str(source),
                                        '--selection', str(sp), '--output', str(output)]
        c = subprocess.run(command, capture_output=True, text=True)
        need(c.returncode == 0 and output.is_file(), 'Creator positive failed: '+c.stderr)
        cases.append(dict(mode=label, case='create_positive', exit_code=c.returncode))
        def check(path, name, expected, extract=False):
            receipt = a.run/(label+'-'+name+'.json')
            cmd = [sys.executable]+mode+[str(HERE/'verify_bundle.py'), '--archive', str(path),
                                       '--expected-sha256', sha(path.read_bytes()), '--receipt', str(receipt)]
            if extract:
                cmd += ['--extract', str(a.run/(label+'-extracted'))]
            result = subprocess.run(cmd, capture_output=True, text=True)
            need((result.returncode == 0) == expected, 'Wrong verifier result: '+name)
            need(receipt.exists() == expected, 'Invalid receipt publication: '+name)
            cases.append(dict(mode=label, case=name, exit_code=result.returncode,
                              receipt_published=receipt.exists()))
        check(output, 'positive', True, True)
        with zipfile.ZipFile(output) as z:
            blobs = {n:z.read(n) for n in z.namelist()}
        manifest = json.loads(blobs['BUNDLE_MANIFEST.json'])
        variants = {}
        variants['changed_source'] = dict(blobs, **{'program.c':raw+b'// mutation\n'})
        variants['changed_readme'] = dict(blobs, **{'README_REPRODUCE.txt':b'changed\n'})
        m = json.loads(json.dumps(manifest));m['source_commit']='unfixed'
        variants['unpinned_commit'] = dict(blobs, **{'BUNDLE_MANIFEST.json':json.dumps(m).encode()})
        m = json.loads(json.dumps(manifest));m['omitted_regenerable_sources'][0]['path']='../escape'
        variants['omitted_path_escape'] = dict(blobs, **{'BUNDLE_MANIFEST.json':json.dumps(m).encode()})
        text = blobs['BUNDLE_MANIFEST.json'].decode()
        variants['duplicate_key'] = dict(blobs, **{'BUNDLE_MANIFEST.json':text.replace('{','{"schema":"duplicate",',1).encode()})
        variants['nonfinite'] = dict(blobs, **{'BUNDLE_MANIFEST.json':text.replace('"source_commit":','"ignored":1e9999,"source_commit":',1).encode()})
        variants['extra_payload'] = dict(blobs, **{'unlisted.txt':b'unlisted'})
        for name, payload in variants.items():
            path = a.run/(label+'-'+name+'.zip')
            with zipfile.ZipFile(path, 'x') as z:
                for n,b in payload.items():z.writestr(n,b)
            check(path, name, False)
        reserved = dict(selection)
        reserved['files'] = [dict(path='README_REPRODUCE.txt',bytes=len(raw),sha256=sha(raw),role='fixture')]
        rp = a.run/(label+'-reserved-selection.json');rp.write_text(json.dumps(reserved))
        c = subprocess.run([sys.executable]+mode+[str(HERE/'create_bundle.py'),'--repository',str(source),
                        '--selection',str(rp),'--output',str(a.run/(label+'-reserved.zip'))],capture_output=True,text=True)
        need(c.returncode != 0 and not (a.run/(label+'-reserved.zip')).exists(), 'Reserved member accepted')
        cases.append(dict(mode=label,case='reserved_creator',exit_code=c.returncode))
    need((a.run/'normal.zip').read_bytes()==(a.run/'O.zip').read_bytes()==(a.run/'OO.zip').read_bytes(),
         'Deterministic creator bytes differ by optimization mode')
    receipt = dict(status='PASS_ACTUAL_CLI_BUNDLE_CONTROLS_NOT_A_LEAN_PROOF', cases=cases,
                   count=len(cases), deterministic_modes=True,
                   creator_sha256=sha((HERE/'create_bundle.py').read_bytes()),
                   verifier_sha256=sha((HERE/'verify_bundle.py').read_bytes()))
    fd,name=tempfile.mkstemp(prefix='.controls-',dir=a.run)
    temporary=Path(name)
    try:
        with os.fdopen(fd,'w')as out:
            json.dump(receipt,out,indent=2,allow_nan=False);out.write('\n')
        os.link(temporary,a.run/'RESULT.json')
    finally:
        temporary.unlink(missing_ok=True)
    print(json.dumps({k:v for k,v in receipt.items() if k!='cases'}))


if __name__ == '__main__':
    main()
