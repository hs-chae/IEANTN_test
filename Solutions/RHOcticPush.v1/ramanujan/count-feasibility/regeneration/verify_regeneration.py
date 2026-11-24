#!/usr/bin/env python3
"""Read back regenerated locked data and every original and pure source identity.

This verifies reproducibility, not mathematical correctness of the untrusted
proposal. The separate complete Lean campaign must still finish.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, os, re, time

HERE = Path(__file__).resolve().parent
COUNT = HERE.parent
NS = 'RamanujanPV.HighTransitionCount'

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as handle:
        for block in iter(lambda: handle.read(8 << 20), b''):
            h.update(block)
    return h.hexdigest()

def read(path):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite JSON')))

def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--regenerated', type=Path, required=True)
    p.add_argument('--recovery', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args()
    need(not a.out.exists(), 'fresh verification receipt')
    start = time.monotonic()
    lock_path = HERE/'HIGH_ORIGINAL_REPRODUCTION_IDENTITIES.json'
    locked, proposal = read(lock_path), read(a.regenerated/'PROPOSAL.json')
    need(proposal['namespace'] == locked['namespace'] == NS, 'exact namespace')
    for key in ['queries', 'records', 'packed_bits', 'data_chunk', 'proof_chunk']:
        need(proposal[key] == locked[key], 'locked parameter: '+key)
    need(proposal['results'] == locked['original_candidates_unverified'], 'same proposed roots')
    packed = a.regenerated/'records.324bit.le'
    need(Path(proposal['packed_file']).resolve() == packed.resolve(), 'owned regenerated packed file')
    need(packed.stat().st_size == 3717508786 == proposal['packed_bytes'], 'exact packed bytes')
    need(sha(packed) == locked['packed_sha256'] == proposal['packed_sha256'], 'independent packed hash')
    need(len(proposal['modules']) == len(locked['modules']) == 3464, 'exact original source census')
    generated, source_bytes = {}, 0
    for row in proposal['modules']:
        mod = row['module']
        need(mod not in generated, 'duplicate original module')
        source = a.regenerated/'source'/Path(*mod.split('.')).with_suffix('.lean')
        need(Path(row['source']).resolve() == source.resolve(), 'regenerated source association')
        need(source.is_file() and not source.is_symlink(), 'owned regular source')
        digest = sha(source)
        need(digest == row['sha256'] == locked['modules'].get(mod), 'original source mismatch: '+mod)
        source_bytes += source.stat().st_size
        generated[mod] = digest
    need(set(generated) == set(locked['modules']), 'all and only original modules')
    controller = COUNT/'recover_count.py'
    manifest = read(a.recovery/'MANIFEST.json')
    need(sha(controller) == manifest['controller_sha256'] ==
         'a58fe8105587ea9b94beace2d5c6ab29b3225e9b9bea023d65e0cf78f29b61b1',
         'exact frozen pure source generator')
    spec = importlib.util.spec_from_file_location('frozen_count_recipes', controller)
    recovery = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(recovery)
    pure = {}
    for row in manifest['modules']:
        if row['kind'] != 'arithmetic':
            continue
        mod = row['module']
        index = mod.rsplit('Check', 1)[1]
        need(re.fullmatch(r'\d{4}', index) is not None, 'exact arithmetic index')
        first, size = row['range']
        text = recovery.leaf_text(index, first, size)
        digest = hashlib.sha256(text.encode()).hexdigest()
        path = a.recovery/'source'/Path(*mod.split('.')).with_suffix('.lean')
        need(digest == row['source_sha256'] == sha(path), 'pure source recipe: '+mod)
        old = row['original']
        need(old['sha256'] == generated[mod], 'original/pure source association')
        pure[mod] = digest
    need(len(pure) == 2469 == manifest['remaining_arithmetic'], 'exact remaining pure source census')
    receipt = dict(status='PASS_DETERMINISTIC_LOCKED_REGENERATION_AND_PURE_SOURCE_RECIPES',
        original_modules=3464, regenerated_pure_remaining_modules=2469,
        records=90670946, packed_bytes=packed.stat().st_size,
        packed_sha256=locked['packed_sha256'], original_source_bytes=source_bytes,
        original_source_hash_inventory=generated, pure_source_hash_inventory=pure,
        original_identity_lock_sha256=sha(lock_path),
        regenerated_proposal_sha256=sha(a.regenerated/'PROPOSAL.json'),
        pure_manifest_sha256=sha(a.recovery/'MANIFEST.json'),
        verification_script_sha256=sha(__file__),
        resource_variant_generator_sha256=sha(HERE/'generate_demand_certificate_safe.py'),
        original_generator_sha256=sha(HERE/'generate_demand_certificate_resources.py'),
        numerical_proof_complete=False, source_first_PV_complete=False,
        semantics='Hash identity and deterministic regeneration only; original and pure complete Lean gates remain separate.',
        seconds=time.monotonic()-start)
    temp = a.out.with_suffix(a.out.suffix+'.pending')
    temp.write_text(json.dumps(receipt, indent=2, allow_nan=False)+'\n')
    os.replace(temp, a.out)
    print(json.dumps({k: receipt[k] for k in ['status', 'records', 'original_modules',
                                             'regenerated_pure_remaining_modules', 'seconds']}))

if __name__ == '__main__':
    main()
