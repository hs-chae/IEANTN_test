#!/usr/bin/env python3
"""Bounded incremental Lean development; final acceptance requires clean replay."""
from pathlib import Path
import argparse, hashlib, json, os, resource, shutil, subprocess, time

S = Path(__file__).resolve().parents[1]
BASE = S.parent / 'RHContinuation.v1'
DATA = Path('/data/ivy-rh-limit-20261122/pi')


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    def pairs(rows):
        result = {}
        for key, value in rows:
            need(key not in result, 'duplicate JSON key')
            result[key] = value
        return result

    def number(raw):
        value = float(raw)
        need(abs(value) != float('inf'), 'nonfinite JSON')
        return value

    return json.loads(Path(path).read_bytes(), object_pairs_hook=pairs, parse_float=number,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite JSON')))


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--module', required=True)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--profile', choices=['ram', 'pnt'], default='ram')
    args = parser.parse_args()
    ctx = read(BASE / 'scripts/GENERIC_CONTEXT.json')
    need(sha(ctx['compiler']) == ctx['compiler_sha256'], 'compiler identity')
    source = args.source.resolve()
    legacy = S.parents[1] / 'Solutions/RHExposureStudy.v1/Ramanujan640/source'
    extra = [S.parents[1] / x for x in read(S / 'integration/DEVELOPMENT_ALLOWED.json')]
    need(any(source.is_relative_to(root.resolve()) for root in [S, BASE, legacy, *extra]),
         'declared application source roots required')
    out = DATA / args.tag
    need(not out.exists() and out.parent == DATA, 'fresh bounded output required')
    available = next(int(x.split()[1]) * 1024 for x in Path('/proc/meminfo').read_text().splitlines()
                     if x.startswith('MemAvailable:'))
    need(available >= (512 + 48) * 1024**3, 'host RAM reserve')
    bank = DATA / ('work-objects' if args.profile == 'ram' else 'work-pnt-objects')
    original = DATA / ('baseline-objects' if args.profile == 'ram' else 'baseline-pnt-objects')
    manifest = DATA / ('BASELINE_PROOF_BANK.json' if args.profile == 'ram'
                       else 'BASELINE_PNT_PROOF_BANK.json')
    if not bank.exists():
        shutil.copytree(original, bank)
    for row in read(manifest)['objects']:
        name = row['module'].replace('.', '/') + '.olean'
        need(sha(bank / name) == row['sha256'], 'baseline object changed')
    out.mkdir()
    snapshot = out / 'source' / (args.module.replace('.', '/') + '.lean')
    snapshot.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, snapshot)
    obj = bank / (args.module.replace('.', '/') + '.olean')
    obj.parent.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join([str(bank), *ctx['generic_libraries']])
    command = [ctx['compiler'], '--root=' + str(out / 'source'), '-j8',
               '-o', str(obj), str(snapshot)]

    def cap():
        resource.setrlimit(resource.RLIMIT_AS, (48 * 1024**3, 48 * 1024**3))

    started = time.monotonic()
    process = subprocess.run(['/usr/bin/time', '-v', *command], cwd=out, env=env,
                             capture_output=True, text=True, preexec_fn=cap)
    (out / 'stdout').write_text(process.stdout)
    (out / 'stderr').write_text(process.stderr)
    need(sha(source) == sha(snapshot), 'source changed during build')
    result = dict(status='PASS_INCREMENTAL_ONLY' if process.returncode == 0 else 'FAIL',
                  returncode=process.returncode, command=command,
                  seconds=time.monotonic()-started, source_sha256=sha(source),
                  compiler_sha256=ctx['compiler_sha256'], controller_sha256=sha(__file__),
                  object_sha256=sha(obj) if process.returncode == 0 else None,
                  final_clean_source_replay_required=True, source_first_PV=False)
    if process.returncode == 0:
        shutil.copyfile(obj, out / (args.module + '.olean'))
    (out / 'RESULT.json').write_text(json.dumps(result, indent=2) + '\n')
    print(process.stdout)
    print(json.dumps(result))
    raise SystemExit(process.returncode)


if __name__ == '__main__':
    main()
