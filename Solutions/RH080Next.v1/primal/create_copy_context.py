#!/usr/bin/env python3
"""Create a public, generic-only pinned context for the copy helper replay."""
import argparse, hashlib, json, subprocess
from pathlib import Path
PINS = {
    'mathlib': '71a80585ee495fc24472fd0eaffc89d94e4fd8d6',
    'plausible': 'd9598f07b1bc701f1e3aae163d2681c1fd978793',
    'LeanSearchClient': 'ba67e212be1197b84c1f1f6299488a10a3002713',
    'importGraph': '1681d78dd6e65e38b143f9740d829c826673807c',
    'proofwidgets': 'a8acbfd87375ff4abe14ce09db5b7664d383bc7f',
    'aesop': '18889deb9e83ea7420ef51c160d6f88552e744e3',
    'Qq': '507746ab8f4b643ccdacb2ec4cdb5853fa9f8ab3',
    'batteries': '4cac2177c37f5530c4da76aa8e4307f3fc9e4dcb',
}
COMPILER_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'

def need(ok, message):
    if not ok:
        raise ValueError(message)

def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--compiler', type=Path, required=True)
    ap.add_argument('--mathlib', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    compiler, mathlib = a.compiler.resolve(), a.mathlib.resolve()
    need(not a.output.exists(), 'Refusing to overwrite an existing context')
    need(compiler.is_file(), 'Missing Lean compiler')
    compiler_sha = hashlib.sha256(compiler.read_bytes()).hexdigest()
    need(compiler_sha == COMPILER_SHA, 'Expected the pinned Linux Lean 4.34.0-rc2 compiler bytes')
    paths = []
    for name, revision in PINS.items():
        candidates = [mathlib] if name == 'mathlib' else [mathlib.parent / name, mathlib / '.lake/packages' / name]
        root = next((p for p in candidates if (p / '.git').exists()), None)
        need(root is not None, 'Missing generic dependency checkout: ' + name)
        actual = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()
        need(actual == revision, 'Generic revision mismatch: ' + name)
        library = root / '.lake/build/lib/lean'
        need(library.is_dir(), 'Missing generic compiled library: ' + name)
        paths.append(str(library))
    result = dict(status='PINNED_GENERIC_ONLY', compiler=str(compiler), compiler_sha256=compiler_sha,
                  compiler_version=subprocess.check_output([str(compiler), '--version'], text=True).strip(),
                  generic_lean_path=':'.join(paths),
                  generic_dependencies=[dict(name=n, revision=r) for n, r in PINS.items()])
    with a.output.open('x') as f:
        json.dump(result, f, indent=2)
        f.write('\n')
    print(a.output)

if __name__ == '__main__':
    main()
