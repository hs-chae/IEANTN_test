#!/usr/bin/env python3
"""Split one explicitly pinned release archive into 6,000,000-byte parts."""
import argparse
import re
from pathlib import Path
from common import identity, need, save, sha

PART_BYTES = 6000000


def split(archive, expected_sha256, out):
    need(re.fullmatch('[0-9a-f]{64}', expected_sha256) and sha(archive) == expected_sha256,
         'actual explicitly pinned complete archive identity')
    need(not out.exists() and out.parent.is_dir(), 'fresh parts output directory')
    out.mkdir()
    rows = []
    with archive.open('rb') as stream:
        while block := stream.read(PART_BYTES):
            path = out/('RH_EVIDENCE_PART_'+str(len(rows)+1).zfill(3)+'.bin')
            path.write_bytes(block)
            rows.append(dict(path=path.name, **identity(path)))
    need(rows and sum(row['bytes'] for row in rows) == archive.stat().st_size and
         sha(archive) == expected_sha256, 'complete archive unchanged through splitting')
    manifest = dict(schema='RH_LIMIT_BREAKTHROUGH_EVIDENCE_PARTS_V1',
                    archive=dict(path=archive.name, **identity(archive)), parts=rows)
    save(out/'EVIDENCE_PARTS.json', manifest)
    return manifest


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False, description=__doc__)
    parser.add_argument('--archive', type=Path, required=True)
    parser.add_argument('--sha256', required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    result = split(args.archive, args.sha256, args.out)
    print('PASS exact 6000000-byte maximum parts:', len(result['parts']))


if __name__ == '__main__':
    main()
