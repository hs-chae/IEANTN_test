#!/usr/bin/env python3
"""Add the checked fresh QRH objects without overwriting root proof objects.

A different existing object is retained only with an accepted current-source
receipt for the identical module/source bytes/compiler. Such choices are
explicitly listed and must be followed by the selected theorem axiom audit in
the merged context. This is object integration, not a numerical acceptance.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import tempfile

S = Path(__file__).resolve().parents[1]


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--fresh', type=Path, required=True)
    parser.add_argument('--receipt', type=Path, required=True)
    args = parser.parse_args()
    context = json.loads((S / 'BUILD_CONTEXT.json').read_text())
    destination = Path(context['new_application_object_root'])
    fresh = args.fresh.resolve()
    output = args.receipt.resolve()
    need(not output.exists(), 'fresh integration receipt required')
    result = json.loads((fresh / 'RESULT.json').read_text())
    need(result['status'] == 'FRESH_QRH_CLOSURE_BUILD_PASS', 'fresh build incomplete')
    need(result['old_application_objects_used'] is False, 'old application object policy')
    rows = []
    for source in result['records']:
        module = source['module']
        relative = Path(*module.split('.')).with_suffix('.olean')
        original = fresh / 'lean' / relative
        target = destination / relative
        need(source['exit_code'] == 0, 'unsuccessful source module')
        need(sha(source['source']) == source['source_sha256'], 'source changed ' + module)
        need(sha(original) == source['object_sha256'], 'fresh object changed ' + module)
        record = {'module': module, 'source': source['source'],
                  'source_sha256': source['source_sha256'],
                  'fresh_build_object_sha256': source['object_sha256'],
                  'destination': str(target)}
        if not target.exists():
            target.parent.mkdir(parents=True, exist_ok=True)
            descriptor, temporary_name = tempfile.mkstemp(prefix='.' + target.name + '.qrhmerge-', dir=target.parent)
            temporary = Path(temporary_name)
            try:
                with os.fdopen(descriptor, 'wb') as stream:
                    stream.write(original.read_bytes())
                need(sha(temporary) == source['object_sha256'], 'copy identity')
                os.link(temporary, target)  # Atomic create; never replace.
            finally:
                temporary.unlink(missing_ok=True)
            record['selection'] = 'ADDED_LOCKED_FRESH_BUILD_OBJECT'
        else:
            current_hash = sha(target)
            if current_hash == source['object_sha256']:
                record['selection'] = 'EXISTING_IDENTICAL_OBJECT'
            else:
                candidates = []
                for receipt in (S / 'audit' / module).glob('*/RUN.json'):
                    proof = json.loads(receipt.read_text())
                    if (proof.get('returncode') == 0 and proof.get('object_sha256') == current_hash
                            and proof.get('source') == source['source']
                            and proof.get('source_sha256') == source['source_sha256']
                            and proof.get('compiler_sha256') == context['compiler_sha256']
                            and proof.get('generic_dependency_context_sha256') == sha(S / 'BUILD_CONTEXT.json')):
                        candidates.append(receipt)
                need(len(candidates) > 0, 'unverified divergent existing object ' + module)
                chosen = max(candidates, key=lambda p: p.stat().st_mtime_ns)
                record.update(selection='RETAINED_ROOT_OBJECT_IDENTICAL_CHECKED_SOURCE',
                              root_receipt=str(chosen), root_receipt_sha256=sha(chosen))
        record['selected_object_sha256'] = sha(target)
        rows.append(record)
    manifest = {'status': 'MERGED_FRESH_QRH_OBJECTS_NO_ROOT_OVERWRITES',
                'application_object_root': str(destination), 'fresh_closure': str(fresh),
                'fresh_result_sha256': sha(fresh / 'RESULT.json'), 'rows': rows,
                'module_count': len(rows), 'existing_root_objects_overwritten': False,
                'script_sha256': sha(Path(__file__)),
                'remaining_gate': 'Compile full adapter and actual four-theorem axiom audit against this merged prefix.'}
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_suffix(output.suffix + '.tmp')
    need(not temporary.exists(), 'fresh atomic receipt temporary')
    temporary.write_text(json.dumps(manifest, indent=2) + '\n')
    os.link(temporary, output)
    temporary.unlink()
    print(json.dumps({'status': manifest['status'], 'module_count': len(rows),
                      'retained_source_equivalent_objects': [r['module'] for r in rows
                      if r['selection'] == 'RETAINED_ROOT_OBJECT_IDENTICAL_CHECKED_SOURCE']}))


if __name__ == '__main__':
    main()
