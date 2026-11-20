#!/usr/bin/env python3
"""Export exact analytic sources and small receipts; never copy old proof objects."""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import math
import shutil
import tarfile

S = Path(__file__).resolve().parents[1]
NETWORK = S.parents[1]
WORKSPACE = NETWORK.parent
PACKETS = ['coupled-analytic-1250-v1', 'coupled-final-independent-v2',
           'coupled-large-margin-independent-v1', 'guarded-coupled-cold-controls-v2']
SCRIPTS = ['export_coupled_analytic_evidence.py', 'reproduce_coupled_analytic.py',
           'reproduce_guarded_coupled_closure.py', 'reproduce_profiled_closure.py',
           'rebuild_qrh_closure.py', 'execute_demand_high_resource.py',
           'execute_demand_manifest_parallel.py', 'bootstrap_context.py']


def need(ok, text):
    if not ok:
        raise ValueError(text)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    def finite(text):
        value = float(text)
        need(math.isfinite(value), 'finite JSON number')
        return value
    def invalid(text):
        raise ValueError('nonfinite JSON constant ' + text)
    return json.loads(path.read_text(), object_pairs_hook=pairs,
                      parse_float=finite, parse_constant=invalid)


def inventory(root):
    return [{'path': str(p.relative_to(root)), 'bytes': p.stat().st_size,
             'sha256': sha(p)} for p in sorted(root.rglob('*'))
            if p.is_file() and p.name != 'EXPORT_MANIFEST.json'
            and '__pycache__' not in p.relative_to(root).parts]


def verify(root):
    manifest = read(root / 'EXPORT_MANIFEST.json')
    need(manifest['files'] == inventory(root), 'every exact exported byte')
    lock = read(root / 'reproduction/network/Solutions/RamanujanSourcePV.v1/'
                'evidence/coupled-analytic-1250-v1/SOURCE_LOCK.json')
    need(len(lock['modules']) == lock['module_count'] == 673, 'entire selected closure')
    for row in lock['modules']:
        need(sha(root / 'reproduction/network' / row['network_relative_source']) ==
             row['source_sha256'], 'pinned source ' + row['module'])
    return manifest


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--check', type=Path)
    args = parser.parse_args()
    if args.check:
        result = verify(args.check.resolve())
        print(json.dumps({'status': 'PASS_EXACT_EXPORTED_SOURCE_AND_EVIDENCE_BYTES',
                          'files': len(result['files'])}))
        return
    need(args.out is not None, '--out required')
    out = args.out.resolve()
    need(not out.exists(), 'fresh export directory required')
    need(out.is_relative_to(WORKSPACE / 'artifacts'), 'owned artifacts destination')
    out.mkdir(parents=True)
    repro = out / 'reproduction/network'
    solution = repro / 'Solutions/RamanujanSourcePV.v1'

    def copy(source, target):
        need(source.is_file(), 'source file with pinned bytes')
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)

    lock = read(S / 'evidence/coupled-analytic-1250-v1/SOURCE_LOCK.json')
    for row in lock['modules']:
        source = NETWORK / row['network_relative_source']
        need(sha(source) == row['source_sha256'], 'current pinned scientific source')
        copy(source, repro / row['network_relative_source'])
    for name in ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain']:
        copy(NETWORK / name, repro / name)
    for name in SCRIPTS:
        copy(S / 'scripts' / name, solution / 'scripts' / name)
    copy(S / 'BUILD_CONTEXT.json', solution / 'BUILD_CONTEXT.json')
    copy(S / 'REPRODUCE_COUPLED_ANALYTIC.md', solution / 'REPRODUCE_COUPLED_ANALYTIC.md')
    copy(S / 'REPRODUCE_COUPLED_ANALYTIC.md', out / 'README.md')
    for packet in PACKETS:
        source = S / 'evidence' / packet
        for path in sorted(source.rglob('*')):
            if path.is_file():
                need(path.suffix not in ['.olean', '.ilean', '.c', '.o'],
                     'compact evidence excludes compiled or generated C objects')
                copy(path, out / 'evidence' / packet / path.relative_to(source))
    copy(S / 'evidence/coupled-analytic-1250-v1/SOURCE_LOCK.json',
         solution / 'evidence/coupled-analytic-1250-v1/SOURCE_LOCK.json')
    for name in ['Buthe1511.02032v2.pdf', 'Buthe1511.02032v2.txt',
                 'Axler2016IntegersA22.pdf', 'Axler2016IntegersA22.txt',
                 'Axler2016IntegersA22Corrigendum.pdf',
                 'Axler2016IntegersA22Corrigendum.txt']:
        copy(WORKSPACE / 'sources' / name, out / 'primary_sources' / name)
    manifest = {'schema': 'ieantn.coupled-analytic-portable-evidence.v1',
                'claim': 'actual Ramanujan gap > 6000000000000 for all real x >= 1250000000000 under exactly 25 explicit analytic/source contracts',
                'finite_counts_completed': False,
                'old_application_objects_included': False,
                'clean_replay_status': 'separate actual final receipt required; checkpoint is not acceptance',
                'application_source_modules': 673, 'files': inventory(out)}
    (out / 'EXPORT_MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
    verify(out)
    archive = out.with_suffix('.tar.gz')
    need(not archive.exists(), 'fresh archive required')
    with archive.open('wb') as raw:
        with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as compressed:
            with tarfile.open(fileobj=compressed, mode='w') as tar:
                for path in sorted(out.rglob('*')):
                    if path.is_file():
                        info = tar.gettarinfo(str(path), arcname=str(path.relative_to(out)))
                        info.uid = info.gid = info.mtime = 0
                        info.uname = info.gname = ''
                        with path.open('rb') as stream:
                            tar.addfile(info, stream)
    with tarfile.open(archive, 'r:gz') as tar:
        members = tar.getmembers()
        need(len(members) == len(manifest['files']) + 1, 'exact archive membership')
        expected = {r['path']: r['sha256'] for r in manifest['files']}
        expected['EXPORT_MANIFEST.json'] = sha(out / 'EXPORT_MANIFEST.json')
        for member in members:
            stream = tar.extractfile(member)
            need(member.isfile() and stream is not None and
                 hashlib.sha256(stream.read()).hexdigest() == expected.pop(member.name),
                 'exact archived member')
        need(not expected, 'no omitted file')
    print(json.dumps({'status': 'PASS_PORTABLE_ANALYTIC_EVIDENCE_EXPORT',
                      'files': len(manifest['files']) + 1, 'archive': str(archive),
                      'bytes': archive.stat().st_size, 'sha256': sha(archive)}))


if __name__ == '__main__':
    main()
