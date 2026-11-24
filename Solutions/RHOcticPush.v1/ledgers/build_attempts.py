#!/usr/bin/env python3
"""Reproduce the explicit research-route inventory, not a proof acceptance gate.

The coordinator-authored catalog is evidence about attempted mathematics. It is
not inferred from file names, a sorry scan, or the number of compiler modules.
Actual proof and numerical acceptance remain in their independent receipts.
"""
import argparse
import csv
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]


def unique(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('Duplicate catalog key: '+key)
        result[key] = value
    return result


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    if args.out.exists():
        raise ValueError('Use a fresh output directory')
    path = HERE/'SERIOUS_ATTEMPT_CATALOG.json'
    raw = path.read_bytes()
    catalog = json.loads(raw, object_pairs_hook=unique,
                         parse_constant=lambda s: (_ for _ in ()).throw(ValueError(s)))
    rows = catalog['routes']
    identities = [row['id'] for row in rows]
    if len(identities) != len(set(identities)):
        raise ValueError('Duplicate route identity')
    for row in rows:
        for pin in row['source_evidence']:
            source = Path(pin['file'])
            if source.is_absolute() or '..' in source.parts:
                raise ValueError('Non-repository source path')
            if hashlib.sha256((REPO/source).read_bytes()).hexdigest() != pin['sha256']:
                raise ValueError('Frozen route source changed: '+str(source))
    args.out.mkdir(parents=True)
    (args.out/'SERIOUS_ATTEMPTS.json').write_bytes(raw)
    flat = [{key: json.dumps(value, ensure_ascii=False)
             if isinstance(value, (list, dict, bool)) else value
             for key, value in row.items()} for row in rows]
    with (args.out/'SERIOUS_ATTEMPTS.csv').open('w', newline='') as handle:
        writer = csv.DictWriter(handle, fieldnames=list(flat[0]))
        writer.writeheader()
        writer.writerows(flat)
    receipt = dict(status='CATALOG_SOURCE_PINS_AND_DETERMINISTIC_EXPORT_REPRODUCED',
                   catalog_sha256=hashlib.sha256(raw).hexdigest(), routes=len(rows),
                   mathematical_proof_acceptance=False)
    (args.out/'CATALOG_READBACK.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt))


if __name__ == '__main__':
    main()
