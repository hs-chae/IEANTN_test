#!/usr/bin/env python3
"""Preserve compact exact scientific evidence; no proof/object cache promotion."""
from pathlib import Path
import argparse, datetime, hashlib, json, os, shutil

S = Path(__file__).resolve().parent
p = argparse.ArgumentParser(allow_abbrev=False)
p.add_argument('--data-root', type=Path, required=True)
p.add_argument('--out', type=Path, required=True)
a = p.parse_args()
D = a.data_root.resolve()
O = a.out.resolve()

def need(c, message):
    if not c:
        raise ValueError(message)

def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda: f.read(1048576), b''):
            h.update(b)
    return h.hexdigest()

need(not O.exists(), 'fresh evidence output directory required')
O.mkdir(parents=True)
rows = []

def copy(src, rel):
    need(src.is_file() and not src.is_symlink(), 'plain evidence file required: ' + str(src))
    dst = O / rel
    need(not dst.exists(), 'evidence collision: ' + str(rel))
    dst.parent.mkdir(parents=True, exist_ok=True)
    before = sha(src)
    shutil.copyfile(src, dst)
    need(sha(dst) == before and sha(src) == before, 'evidence copy hash mismatch')
    rows.append({'path': str(rel), 'original_path': str(src), 'bytes': dst.stat().st_size,
                 'sha256': before})

stages = ['fresh-base-v1', 'final-source-v1', 'source-component-v1',
          'strong-source-v2', 'node-publication-v9']
for stage in stages:
    root = D / stage
    status = json.loads((root / 'RESULT.json').read_text())['status']
    need(status.startswith('PASS'), 'nonpassing selected stage: ' + stage)
    copy(root / 'RESULT.json', Path(stage) / 'RESULT.json')
    for name in ['source', 'logs', 'resources']:
        srcroot = root / name
        if srcroot.is_dir():
            for src in sorted(srcroot.rglob('*')):
                if src.is_file():
                    copy(src, Path(stage) / name / src.relative_to(srcroot))
    for name in ['driver.c', 'outputs.txt', 'foundation-validation.json',
                 'strong-validation.json', 'strong-validation.foundation.json']:
        src = root / name
        if src.is_file():
            copy(src, Path(stage) / name)

for stage in ['acceptance-controls-v1', 'strong-controls-v1']:
    for src in sorted((D / stage).rglob('*.json')):
        copy(src, Path(stage) / src.relative_to(D / stage))

for stage in ['node-publication-v1', 'node-publication-v2', 'node-publication-v3',
              'node-publication-v4', 'node-publication-v5', 'node-publication-v6',
              'node-publication-v7', 'node-publication-v8']:
    src = D / stage / 'RESULT.json'
    if src.is_file():
        copy(src, Path('historical-append-receipts') / (stage + '.json'))

for src in sorted((D / 'finite-full-scout-v1').iterdir()):
    if src.is_file() and (src.suffix in ['.json', '.stdout', '.stderr', '.resources']):
        copy(src, Path('finite-full-scout-v1') / src.name)
for name in ['configured-context-v1.json', 'PORTABILITY_CHECK.stdout',
             'PORTABILITY_CHECK.stderr']:
    copy(D / name, Path('relocation') / name)
copy(D / 'sources/GM_1312.4465v4.pdf', Path('literature/GM_1312.4465v4.pdf'))

readme = '''# Compact scientific evidence: Ramanujan and actual prime-counting continuation

This folder preserves exact source snapshots, measured compiler/resource logs, passing
receipts, negative controls, corrected resource evidence and the full native-prefix
scout's two-run/hash/cleanup evidence. MANIFEST.json records every copied byte by
SHA256 and the original measured location. No compiled Lean application object bank
is included. Accepted original proof objects remain retained on the host; a clean
recipient regenerates them using the source reproduction scripts in the parent folder.

Selected passing sequence: fresh-base-v1 (146 original application/checker sources),
final-source-v1 (10 new actual-li/foundation/consumer modules), source-component-v1
(8 reused C-model modules and the actual C outputs), strong-source-v2 (7 new
source-linked/full-tail modules), node-publication-v9 (14 final append sources;
all four Ramanujan and seven derived prime-counting adapters audited standard3).
Earlier append receipts are historical attempts, not substitutes for final v9.

The derived results retain explicit original RH/literature assumptions. The coefficient
application is source-first PV; finite interval numerical leaves are kernel-only and
the full native finite scout remains UNVERIFIED. No official Comparator receipt is
claimed. The GM primary PDF is preserved with its literal four-term Theorem1.1 bound
on PDF page3. The actual integration relay is proved separately; it does not prove GM.

The finite scout's original CGROUP_RESOURCES.json called its sampled maximum a peak;
CGROUP_RESOURCES_CORRECTED.json explicitly records a largest 1Hz observed current
sample, because this kernel exposes no exact memory.peak. Preserve both historical
and corrected receipts, and use the corrected interpretation. The native generator
receipt also explains that the historical primesieve_commit field resolves the
containing primecount repository rather than a separate primesieve revision.

Absolute paths in historical receipts describe the original measured run. They are
provenance, not portable path requirements. configure_context.py and the current
reproduction scripts support a clean relocated environment. The relocated generic
context and complete generic-inventory preflight passed; this prerequisite check is
separate from the fresh application proof replay. See ../README.md and
../finite_scout/README.md for clean commands, versions, claims, trust and open gaps.
'''
(O / 'README.md').write_text(readme)
rows.append({'path': 'README.md', 'original_path': None,
             'bytes': (O / 'README.md').stat().st_size, 'sha256': sha(O / 'README.md')})
manifest = {'schema': 'RAMANUJAN_COMPACT_SCIENTIFIC_EVIDENCE_V1',
            'status': 'BYTE_CHECKED_SCIENTIFIC_EVIDENCE_NOT_NEW_PROOF_RECEIPT',
            'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'contains_compiled_Lean_object_banks': False,
            'native_finite_outputs_promoted': False,
            'files': rows, 'total_bytes': sum(r['bytes'] for r in rows)}
tmp = O / 'MANIFEST.pending'
tmp.write_text(json.dumps(manifest, indent=2) + '\n')
os.replace(tmp, O / 'MANIFEST.json')
for row in rows:
    need(sha(O / row['path']) == row['sha256'], 'final evidence readback failure')
print(json.dumps({'status': manifest['status'], 'files': len(rows),
                  'bytes': manifest['total_bytes'], 'manifest_sha256': sha(O / 'MANIFEST.json')}))
