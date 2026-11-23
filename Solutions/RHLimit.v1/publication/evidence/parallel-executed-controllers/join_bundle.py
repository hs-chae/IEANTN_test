#!/usr/bin/env python3
"""Split a checked source archive into <=6MiB parts or join/check exact parts.

Usage after downloading every attachment into one folder:
  python3 join_bundle.py --parts-dir . --out RH_LIMIT_SOURCE.tar.gz
  python3 join_bundle.py --parts-dir . --check
"""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, sys
sys.dont_write_bytecode = True

MAX_PART = 6 * 1024 * 1024

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def read(path):
    def pairs(rows):
        result = {}
        for key, value in rows:
            need(key not in result, 'duplicate manifest key')
            result[key] = value
        return result
    def number(raw):
        value = float(raw); need(abs(value) != float('inf'), 'overflowing manifest number'); return value
    return json.loads(path.read_bytes(), object_pairs_hook=pairs, parse_float=number,
        parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite manifest number')))

def save(path, data):
    pending = path.with_name(path.name + '.pending'); need(not pending.exists(), 'preexisting pending metadata')
    pending.write_text(json.dumps(data, indent=2, allow_nan=False) + '\n'); os.replace(pending, path)

def split(archive, out, part_bytes):
    need(archive.is_file() and not archive.is_symlink() and not out.exists(), 'regular archive and fresh parts directory required')
    need(1 <= part_bytes <= MAX_PART and re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9._-]{0,127}', archive.name), 'invalid archive name/part bound')
    size = archive.stat().st_size; need(size > 0, 'nonempty archive required')
    before = sha(archive); out.mkdir(parents=True); rows = []
    with archive.open('rb') as stream:
        index = 0
        while block := stream.read(part_bytes):
            index += 1; name = 'RH_LIMIT_SOURCE.part' + str(index).zfill(3); target = out / name
            target.write_bytes(block)
            rows.append({'path': name, 'bytes': len(block), 'sha256': hashlib.sha256(block).hexdigest()})
    need(sha(archive) == before and sum(row['bytes'] for row in rows) == size, 'archive changed during split')
    helper = out / 'join_bundle.py'; shutil.copyfile(Path(__file__).resolve(), helper)
    extractor = out / 'archive_tools.py'; shutil.copyfile(Path(__file__).resolve().parent / 'archive_tools.py', extractor)
    manifest = {'schema': 'DETERMINISTIC_SIX_MIB_SOURCE_ARCHIVE_PARTS_V1',
        'archive': archive.name, 'archive_bytes': size, 'archive_sha256': before,
        'part_bytes': part_bytes, 'maximum_part_bytes': MAX_PART, 'parts': rows,
        'join_helper_sha256': sha(helper), 'extract_helper_sha256': sha(extractor)}
    save(out / 'PARTS_MANIFEST.json', manifest)
    print(json.dumps({'status': 'PASS_SPLIT_EXACT_ARCHIVE_INTO_BOUNDED_PARTS', 'parts': len(rows),
                      'maximum_part_bytes': max(row['bytes'] for row in rows), 'archive_sha256': before}))

def join(parts, out, check):
    need(parts.is_dir(), 'parts directory missing')
    m = read(parts / 'PARTS_MANIFEST.json')
    need(m['schema'] == 'DETERMINISTIC_SIX_MIB_SOURCE_ARCHIVE_PARTS_V1', 'parts schema')
    need(type(m['part_bytes']) is int and 1 <= m['part_bytes'] <= MAX_PART and m['maximum_part_bytes'] == MAX_PART,
         'part size limit')
    need(type(m['archive_bytes']) is int and m['archive_bytes'] > 0 and
         re.fullmatch('[0-9a-f]{64}', m['archive_sha256']), 'archive identity')
    need(re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9._-]{0,127}', m['archive']), 'archive basename')
    rows = m['parts']; need(isinstance(rows, list) and len(rows) == (m['archive_bytes'] + m['part_bytes'] - 1) // m['part_bytes'], 'complete part count')
    need(sha(Path(__file__).resolve()) == m['join_helper_sha256'], 'join helper identity differs from delivered helper')
    need(sha(parts / 'archive_tools.py') == m['extract_helper_sha256'], 'extract helper identity differs')
    need({p.name for p in parts.glob('RH_LIMIT_SOURCE.part*')} == {row['path'] for row in rows}, 'unexpected or missing part membership')
    aggregate = hashlib.sha256(); total = 0
    for index, row in enumerate(rows, 1):
        expected_name = 'RH_LIMIT_SOURCE.part' + str(index).zfill(3)
        need(row['path'] == expected_name and type(row['bytes']) is int and
             0 < row['bytes'] <= m['part_bytes'] and re.fullmatch('[0-9a-f]{64}', row['sha256']), 'part name/size/hash identity')
        if index < len(rows):
            need(row['bytes'] == m['part_bytes'], 'short nonfinal part')
        file = parts / row['path']; need(file.is_file() and not file.is_symlink() and file.stat().st_size == row['bytes'], 'missing/linked/wrong-size part: ' + row['path'])
        local = hashlib.sha256()
        with file.open('rb') as stream:
            for block in iter(lambda: stream.read(1024 * 1024), b''):
                local.update(block); aggregate.update(block); total += len(block)
        need(local.hexdigest() == row['sha256'], 'part hash mismatch: ' + row['path'])
    need(total == m['archive_bytes'] and aggregate.hexdigest() == m['archive_sha256'], 'joined archive byte identity')
    if check:
        need(out is None, '--check does not take --out')
        print(json.dumps({'status': 'PASS_ALL_PARTS_AND_WHOLE_ARCHIVE_SHA256', 'bytes': total,
                          'sha256': aggregate.hexdigest()})); return
    need(out is not None and not out.exists() and not out.is_symlink(), 'fresh --out archive required')
    pending = out.with_name(out.name + '.pending'); need(not pending.exists(), 'fresh pending output required')
    with pending.open('xb') as target:
        for row in rows:
            with (parts / row['path']).open('rb') as stream:
                shutil.copyfileobj(stream, target)
    need(pending.stat().st_size == total and sha(pending) == m['archive_sha256'], 'parts changed during join')
    os.replace(pending, out)
    print(json.dumps({'status': 'PASS_RECONSTRUCTED_EXACT_ARCHIVE', 'bytes': total, 'sha256': sha(out)}))

def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--parts-dir', type=Path)
    p.add_argument('--out', type=Path)
    p.add_argument('--check', action='store_true')
    p.add_argument('--split', type=Path)
    p.add_argument('--part-bytes', type=int, default=MAX_PART)
    a = p.parse_args()
    if a.split is not None:
        need(a.out is not None and a.parts_dir is None and not a.check, '--split needs fresh --out directory only')
        split(a.split.resolve(), a.out.resolve(), a.part_bytes)
    else:
        need(a.parts_dir is not None, '--parts-dir required')
        join(a.parts_dir.resolve(), a.out.resolve() if a.out is not None else None, a.check)

if __name__ == '__main__':
    main()
