#!/usr/bin/env python3
"""Check exact public-source origins and excluded private-context paths/markers."""
from pathlib import Path
import argparse, hashlib, json, sys, tarfile
sys.dont_write_bytecode = True

DENY_PARTS = {'.git', '.lake', '__pycache__', 'memory', 'human_input', 'source-freeze', 'canaries'}
MARKERS = [b'Message Type: NEW_TASK', b'Message Type: FINAL_ANSWER', b'User [hschae]:',
           b'# AGENTS.md instructions for /ryu/', b'OWNER_CURRENT_PROMPT', b'current_owner_prompt',
           b'BEGIN PRIVATE CONTEXT']

def need(ok, text):
    if not ok:
        raise ValueError(text)

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--tree', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args(); root = a.tree.resolve(); need(not a.out.exists(), 'fresh gate receipt required')
    inventory = json.loads((root / 'SOURCE_SELECTION.json').read_text())
    expected = {r['path']: r for r in inventory['files']}
    actual = {p.relative_to(root / 'network').as_posix(): p for p in (root / 'network').rglob('*') if p.is_file()}
    need(actual.keys() == expected.keys(), 'complete public network source-origin membership')
    for rel, file in actual.items():
        need(sha(file) == expected[rel]['sha256'], 'selected public source changed: ' + rel)
    files = 0; metadata_members = 0
    for file in root.rglob('*'):
        need(not file.is_symlink(), 'linked file in deliverable')
        if not file.is_file():
            continue
        rel = file.relative_to(root)
        need(not any(part in DENY_PARTS for part in rel.parts), 'private/runtime source path: ' + str(rel))
        files += 1
        if file.name == 'check_private_context.py':
            need(sha(file) == sha(Path(__file__).resolve()), 'private-context checker source identity')
            continue  # Its literal forbidden-marker list is validator code.
        raw = file.read_bytes()
        for marker in MARKERS:
            need(marker not in raw, 'private transcript/prompt marker: ' + str(rel))
    transport = root / 'generic-transport/GENERIC_BUILD_METADATA.tar.gz'
    with tarfile.open(transport, 'r:gz') as tf:
        for member in tf:
            need(member.isfile() and not any(part in DENY_PARTS for part in Path(member.name).parts), 'private generic metadata path')
            raw = tf.extractfile(member).read()
            for marker in MARKERS:
                need(marker not in raw, 'private context marker in generic build metadata')
            metadata_members += 1
    result = {'schema': 'PUBLIC_SOURCE_ORIGIN_AND_PRIVATE_CONTEXT_MARKER_GATE_V1',
        'status': 'PASS_EXACT_PUBLIC_SOURCE_ORIGINS_AND_NO_EXCLUDED_PRIVATE_CONTEXT_MARKERS',
        'python_optimization': sys.flags.optimize, 'network_source_files': len(actual),
        'delivered_files_scanned': files, 'generic_metadata_members_scanned': metadata_members,
        'forbidden_path_components': sorted(DENY_PARTS), 'marker_classes': len(MARKERS),
        'scope': 'Complete source-selection/hash membership plus exact private transcript/prompt markers across all regular payload files and compressed generic metadata. Public scientific reviews and reproducibility diagnostics are included; no memory, owner input packets, sessions or private canary trees are selected.'}
    a.out.write_text(json.dumps(result, indent=2) + '\n'); print(result['status'])

if __name__ == '__main__':
    main()
