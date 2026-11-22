#!/usr/bin/env python3
"""Retain exact legacy generic build metadata without vendoring generic libraries.

Restore checks every semantic/tooling artifact against the legacy full inventory,
then creates a fresh owned library view. It never changes a generic source/cache.
"""
from pathlib import Path
import argparse, copy, hashlib, json, os, shutil, subprocess, sys, tarfile
sys.dont_write_bytecode = True
from prepare_bundle import need, safe, sha, strict, save

HERE = Path(__file__).resolve().parent

def libraries(bundle):
    base = bundle / 'network/Solutions/RHExposureStudy.v1/Ramanujan640'
    manifest = strict(base / 'SOURCE_MANIFEST.json')
    rows = []
    for lib in manifest['generic_libraries']:
        index = base / lib['inventory']
        need(sha(index) == lib['inventory_sha256'], 'legacy generic inventory hash changed')
        for entry in strict(index)['files']:
            safe(entry['path'])
            need(type(entry['bytes']) is int and entry['bytes'] >= 0, 'invalid inventory size')
            rows.append((lib['name'], entry))
    names = [(name, row['path']) for name, row in rows]
    need(len(names) == len(set(names)), 'duplicate legacy generic file')
    return rows

def checked_context(bundle, path):
    ctx = strict(path)
    pinned = strict(bundle / 'network/Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json')
    need(ctx['compiler_sha256'] == pinned['compiler_sha256'] == sha(ctx['compiler']), 'exact compiler identity')
    need([(d['name'], d['revision']) for d in ctx['generic_dependencies']] ==
         [(d['name'], d['revision']) for d in pinned['generic_dependencies']], 'exact generic source pins')
    need(len(ctx['generic_dependencies']) == 9 and len(ctx['generic_libraries']) == 8, 'exact generic context shape')
    for dep in ctx['generic_dependencies']:
        revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=dep['path'], text=True).strip()
        dirty = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=dep['path'], text=True)
        need(revision == dep['revision'] and not dirty.strip(), 'dirty or different pinned generic source: ' + dep['name'])
    return ctx

def metadata(row):
    suffix = Path(row['path']).suffix
    archival_ide_reference = (row['path'] == 'Mathlib/Tactic/NormNum/Ineq.ilean'
        and row['bytes'] == 47449
        and row['sha256'] == 'f3005c6577c288024aeab935aea9d881fe541b68310d35bf38a57bdbaa5375d0')
    return suffix in {'.trace', '.hash'} or (row['bytes'] == 0 and suffix == '.3056269') or archival_ide_reference

def capture(bundle, context, out):
    need(not out.exists(), 'fresh metadata capture directory required')
    ctx = checked_context(bundle, context); rows = libraries(bundle)
    mapped = {r['name']: Path(r['library']) for r in ctx['generic_dependencies']}
    out.mkdir(parents=True)
    archive = out / 'GENERIC_BUILD_METADATA.tar.gz'
    captured = []; semantic_count = 0; semantic_bytes = 0
    with tarfile.open(archive, 'w:gz', format=tarfile.PAX_FORMAT, compresslevel=9) as tf:
        for name, row in rows:
            if not metadata(row):
                semantic_count += 1; semantic_bytes += row['bytes']; continue
            src = mapped[name] / row['path']
            need(src.is_file() and src.stat().st_size == row['bytes'] and sha(src) == row['sha256'],
                 'legacy metadata differs: ' + name + '/' + row['path'])
            path = name + '/' + row['path']; safe(path)
            info = tf.gettarinfo(str(src), arcname=path)
            info.uid = info.gid = info.mtime = 0; info.uname = info.gname = ''; info.mode = 0o644
            with src.open('rb') as stream:
                tf.addfile(info, stream)
            captured.append({'path': path, 'bytes': row['bytes'], 'sha256': row['sha256']})
    result = {'schema': 'LEGACY_GENERIC_NONSEMANTIC_METADATA_TRANSPORT_V1',
              'status': 'CAPTURED_METADATA_ONLY_NO_GENERIC_LIBRARIES',
              'archive': archive.name, 'archive_sha256': sha(archive), 'archive_bytes': archive.stat().st_size,
              'metadata_files': captured, 'metadata_bytes': sum(r['bytes'] for r in captured),
              'external_semantic_files': semantic_count, 'external_semantic_bytes': semantic_bytes,
              'semantic_identity_rule': 'Every external file must exactly match its unchanged legacy per-library SHA256/size inventory before an owned view is accepted.',
              'independent_generic_bootstrap_tested': False}
    result['archival_IDE_metadata_exception'] = {
        'path': 'mathlib/Mathlib/Tactic/NormNum/Ineq.ilean', 'bytes': 47449,
        'sha256': 'f3005c6577c288024aeab935aea9d881fe541b68310d35bf38a57bdbaa5375d0',
        'reason': 'Root-approved archival IDE reference-usage metadata: declarations/imports/module/version equal the fresh official cache; four reference-usage dictionaries differ. All corresponding kernel/IR object files match exact legacy hashes.',
        'comparison_receipt': 'generic-bootstrap-evidence/INEQ_ILEAN_DIFFERENCE.json',
        'unchanged_legacy_full_validator': True}
    save(out / 'METADATA_MANIFEST.json', result)
    print(json.dumps({k: result[k] for k in ['status', 'archive_bytes', 'metadata_bytes', 'external_semantic_files', 'external_semantic_bytes']}))

def restore(bundle, context, transport, out):
    need(not out.exists(), 'fresh owned generic view required')
    rows = libraries(bundle); ctx = checked_context(bundle, context)
    manifest = strict(transport / 'METADATA_MANIFEST.json')
    need(manifest['schema'] == 'LEGACY_GENERIC_NONSEMANTIC_METADATA_TRANSPORT_V1', 'metadata schema')
    archive = transport / manifest['archive']; safe(manifest['archive'])
    need(sha(archive) == manifest['archive_sha256'], 'metadata archive hash')
    expected = {name + '/' + row['path']: row for name, row in rows if metadata(row)}
    listed = {row['path']: row for row in manifest['metadata_files']}
    need(len(listed) == len(manifest['metadata_files']) and listed.keys() == expected.keys(), 'complete metadata membership')
    for name, row in listed.items():
        safe(name)
        need(row['bytes'] == expected[name]['bytes'] and row['sha256'] == expected[name]['sha256'], 'metadata identity')
    mapped = {row['name']: Path(row['library']) for row in ctx['generic_dependencies']}
    # Complete every semantic hash check before materializing the view.
    count = 0; total = 0
    for name, row in rows:
        if metadata(row):
            continue
        src = mapped[name] / row['path']
        need(src.is_file() and src.stat().st_size == row['bytes'] and sha(src) == row['sha256'],
             'external semantic/tooling artifact differs: ' + name + '/' + row['path'])
        count += 1; total += row['bytes']
    with tarfile.open(archive, 'r:gz') as tf:
        members = tf.getmembers(); actual = set()
        for member in members:
            safe(member.name)
            need(member.isfile() and member.name not in actual and member.name in expected,
                 'unexpected/duplicate/linked metadata archive member')
            need(member.size == expected[member.name]['bytes'], 'metadata archive member size')
            actual.add(member.name)
        need(actual == expected.keys(), 'incomplete metadata archive')
        out.mkdir(parents=True); libs = out / 'libraries'; libs.mkdir()
        for member in members:
            dst = libs / member.name; dst.parent.mkdir(parents=True, exist_ok=True)
            with tf.extractfile(member) as src, dst.open('xb') as stream:
                while block := src.read(1024 * 1024):
                    stream.write(block)
            need(sha(dst) == expected[member.name]['sha256'], 'restored metadata hash')
    for name, row in rows:
        if metadata(row):
            continue
        dst = libs / name / row['path']; dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile((mapped[name] / row['path']).resolve(), dst)
        need(dst.stat().st_size == row['bytes'] and sha(dst) == row['sha256'], 'owned semantic copy changed')
    fresh = copy.deepcopy(ctx); replacements = {}
    for dep in fresh['generic_dependencies']:
        if dep['library'] in fresh['generic_libraries']:
            lib = str(libs / dep['name']); replacements[dep['library']] = lib
            dep['library'] = lib
    fresh['generic_libraries'] = [replacements[p] for p in fresh['generic_libraries']]
    fresh.update(generic_metadata_transport_manifest_sha256=sha(transport / 'METADATA_MANIFEST.json'),
                 generic_identity_policy='Unchanged legacy full cache byte identity; metadata restored into owned transport view, semantic files externally supplied and individually hash checked',
                 independent_generic_bootstrap_tested=False)
    save(out / 'GENERIC_CONTEXT.json', fresh)
    result = {'schema': 'EXACT_GENERIC_OWNED_TRANSPORT_VIEW_V1', 'status': 'PASS_ALL_LEGACY_GENERIC_SEMANTIC_HASHES_AND_METADATA_VIEW',
              'external_semantic_files_checked': count, 'external_semantic_bytes_checked': total,
              'metadata_files': len(expected), 'metadata_manifest_sha256': sha(transport / 'METADATA_MANIFEST.json'),
              'semantic_transport': 'Independent regular file copies, so unchanged legacy realpath containment gates remain effective',
              'context_sha256': sha(out / 'GENERIC_CONTEXT.json'), 'original_generic_caches_modified': False,
              'independent_bootstrap_claim': 'This receipt only establishes exact input/view identities. Independent bootstrap requires separately documenting how external semantic files were obtained.'}
    save(out / 'RESULT.json', result); print(json.dumps(result))

def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('action', choices=['capture', 'restore'])
    p.add_argument('--bundle', type=Path, default=HERE)
    p.add_argument('--context', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--transport', type=Path)
    a = p.parse_args()
    if a.action == 'capture':
        capture(a.bundle.resolve(), a.context.resolve(), a.out.resolve())
    else:
        need(a.transport is not None, '--transport required for restore')
        restore(a.bundle.resolve(), a.context.resolve(), a.transport.resolve(), a.out.resolve())

if __name__ == '__main__':
    main()
