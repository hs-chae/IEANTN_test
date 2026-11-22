#!/usr/bin/env python3
"""Download exact generic cache archives from the official read-only endpoint.

The archive manifest fixes bytes and SHA256. This supplies no application proof
objects and performs no cache extraction, source change or generic installation.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse, hashlib, json, os, re, sys, time, urllib.request
sys.dont_write_bytecode = True
from prepare_bundle import need, safe, sha, strict, save

def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--check', action='store_true')
    p.add_argument('--jobs', type=int, default=12)
    a = p.parse_args(); need(1 <= a.jobs <= 16, 'download concurrency1..16')
    m = strict(a.manifest); rows = m['archives']
    need(m['schema'] == 'OFFICIAL_PINNED_GENERIC_CACHE_ARCHIVE_HASHES_V1' and len(rows) == 8865, 'exact archive inventory')
    need(len({r['path'] for r in rows}) == len(rows), 'duplicate cache archive')
    for r in rows:
        safe(r['path']); need(re.fullmatch(r'[0-9a-f]{16}\.ltar', r['path']), 'cache archive filename')
        need(type(r['bytes']) is int and r['bytes'] >= 0 and re.fullmatch('[0-9a-f]{64}', r['sha256']), 'cache archive identity')
        need(r['url'] == 'https://cache.mathlib.org/mathlib4-master/f/' + r['path'], 'unapproved cache endpoint')
    if a.check:
        for r in rows:
            file = a.out / r['path']
            need(file.is_file() and not file.is_symlink() and file.stat().st_size == r['bytes'] and sha(file) == r['sha256'], 'cache archive differs: ' + r['path'])
        print(json.dumps({'status': 'PASS_ALL8865_OFFICIAL_ARCHIVE_SHA256', 'files': len(rows)})); return
    need(not a.out.exists(), 'fresh download output required'); a.out.mkdir(parents=True)
    start = time.monotonic(); results = []
    def one(row):
        request = urllib.request.Request(row['url'], headers={'User-Agent': 'IEANTN-pinned-scientific-reproducer/1'})
        h = hashlib.sha256(); size = 0; target = a.out / row['path']; temp = target.with_suffix('.pending')
        with urllib.request.urlopen(request, timeout=90) as response, temp.open('xb') as stream:
            while block := response.read(1024 * 1024):
                size += len(block); need(size <= row['bytes'], 'oversized cache archive')
                h.update(block); stream.write(block)
        need(size == row['bytes'] and h.hexdigest() == row['sha256'], 'cache archive hash differs: ' + row['path'])
        os.replace(temp, target)
        return {'path': row['path'], 'bytes': size, 'sha256': h.hexdigest()}
    result = {'schema': 'FRESH_OFFICIAL_GENERIC_CACHE_DOWNLOAD_V1', 'status': 'RUNNING',
              'manifest_sha256': sha(a.manifest), 'validator_sha256': sha(__file__),
              'generic_libraries_vendored_in_source_bundle': False, 'download_jobs': a.jobs}
    save(a.out / 'RESULT.json', result)
    try:
        with ThreadPoolExecutor(max_workers=a.jobs) as pool:
            for row in pool.map(one, rows):
                results.append(row)
        result.update(status='PASS_FRESH_DOWNLOAD_ALL8865_PINNED_OFFICIAL_GENERIC_ARCHIVES',
                      archives=len(results), bytes=sum(r['bytes'] for r in results), elapsed_seconds=time.monotonic() - start)
        save(a.out / 'RESULT.json', result); print(json.dumps(result))
    except BaseException as error:
        result.update(status='FAILED_OR_PARTIAL_OFFICIAL_GENERIC_DOWNLOAD', complete_results_observed=len(results),
                      error=str(error), elapsed_seconds=time.monotonic() - start)
        save(a.out / 'RESULT.json', result); raise

if __name__ == '__main__':
    main()
