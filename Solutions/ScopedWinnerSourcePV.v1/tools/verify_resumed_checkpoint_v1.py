"""Check published bytes and the exact accepted54-helper source/receipt chain.

This verifies evidence association, not Lean proofs or aggregate replay status.
Use each completed capsule's separate reproduction command for proof replay.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import math
import re
import zipfile


def need(ok, message):
    if not ok:
        raise ValueError(message)


def decode(text):
    def pairs(rows):
        d = {}
        for k, v in rows:
            need(k not in d, 'duplicate JSON key')
            d[k] = v
        return d

    def floating(text):
        v = float(text)
        need(math.isfinite(v), 'nonfinite number')
        return v

    def constant(text):
        raise ValueError('nonfinite JSON constant: '+text)
    return json.loads(text, object_pairs_hook=pairs, parse_float=floating,
                      parse_constant=constant)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--receipt', type=Path, required=True)
    args = ap.parse_args()
    root = args.root.resolve()
    need(root.is_dir() and not args.receipt.exists(), 'input and fresh receipt')
    hashes = decode((root/'HASHES.json').read_text())['files']
    seen = set()
    for row in hashes:
        p = root/row['path']
        need(row['path'] not in seen and p.is_file() and
             p.resolve().is_relative_to(root), 'unique owned manifest member')
        seen.add(row['path'])
        data = p.read_bytes()
        need(len(data)==row['bytes'] and digest(data)==row['sha256'], 'published file identity')
    artifacts = decode((root/'evidence/resumed-20261115/ARTIFACTS.json').read_text())['files']
    for row in artifacts:
        p = root/row['path']
        need(p.stat().st_size==row['bytes'] and digest(p.read_bytes())==row['sha256'],
             'component archive identity')
        with zipfile.ZipFile(p) as z:
            names = z.namelist()
            need(len(names)==len(set(names)) and all(not PurePosixPath(n).is_absolute()
                 and '..' not in PurePosixPath(n).parts for n in names), 'archive member paths')
            need(z.testzip() is None, 'archive CRC')
    base = root/'SOURCE_INTEGRATION_RESUMED_20261115.zip'
    delta = root/'SOURCE54_MAIN_MODEL_EVIDENCE_DELTA_V1.zip'
    merged = {}
    for p, manifest_name in [(base,'SOURCE_CHECKPOINT_MANIFEST.json'),
                             (delta,'SOURCE54_MAIN_DELTA_MANIFEST.json')]:
        with zipfile.ZipFile(p) as z:
            m = decode(z.read(manifest_name).decode())
            if p==delta:
                need(m['base_sha256']==digest(base.read_bytes()), 'overlay parent identity')
            for row in m['files']:
                data = z.read(row['path'])
                need(len(data)==row['bytes'] and digest(data)==row['sha256'], 'source payload identity')
                merged[row['path']] = data
    index = decode(merged['scoped/frontend/proof/SOURCE_HELPER_SUPPORT_INDEX_V31.json'].decode())
    need(len(index['concrete_functions'])==28 and len(index['files'])==265,
         'exact numerical-helper population; controls26 separate')
    for row in index['files']:
        for key, pin in [('source','source_sha256'),('receipt','receipt_sha256')]:
            name = row[key]
            # Historical receipts preserve original absolute workspace paths.
            if '/ieantn-qrh-pv-synergy-20261114/' in name:
                name = name.split('/ieantn-qrh-pv-synergy-20261114/',1)[1]
            need(name in merged and digest(merged[name])==row[pin], 'accepted helper source/receipt')
    status = decode((root/'STATUS.json').read_text())
    need(status['resumed_current']['original_bodies_closed']==54 and
         status['resumed_current']['whole_original_program_source_first_PV_complete'] is False,
         'partial acceptance boundary')
    report = root/'RESUMED_SOURCE_PROGRESS_V6.html'
    html = report.read_text()
    for href in re.findall(r'href="([^"]+)"', html):
        if '://' not in href and not href.startswith('#'):
            p = (report.parent/href.split('#',1)[0]).resolve()
            need(p.is_relative_to(root) and p.is_file(), 'report link: '+href)
    receipt = dict(status='PASS_PUBLISHED_BYTES_AND_ACCEPTED_SOURCE_RECEIPT_ASSOCIATION',
                   qualification='NOT_A_LEAN_REPLAY_OR_SOURCE_FIRST_PV_COMPLETION_RECEIPT',
                   published_files=len(hashes), artifacts=len(artifacts),
                   overlay_payloads=len(merged), accepted_numerics_helper_modules=265,
                   hashes_sha256=digest((root/'HASHES.json').read_bytes()),
                   validator_sha256=digest(Path(__file__).read_bytes()),
                   python_optimization=__import__('sys').flags.optimize)
    args.receipt.parent.mkdir(parents=True, exist_ok=True)
    pending = args.receipt.with_name(args.receipt.name+'.pending')
    need(not pending.exists(), 'fresh atomic staging receipt')
    pending.write_text(json.dumps(receipt, indent=2, allow_nan=False)+'\n')
    pending.replace(args.receipt)
    print(json.dumps(receipt))


if __name__=='__main__':
    main()
