#!/usr/bin/env python3
"""Freshly rebuild the Fourier proof from frozen sources and pinned providers.

The existing Gaussian numerical providers are explicit inputs. Their full fresh
rebuild belongs to the combined Gaussian numerical/Fourier/gap reproduction.
No previous Fourier proof object is imported by this script.
"""
import argparse, hashlib, json, os, pathlib, re, subprocess, time

HERE = pathlib.Path(__file__).resolve().parent
DEFAULT_CONTEXT = HERE.parents[1] / 'RHContinuation.v1/scripts/GENERIC_CONTEXT.json'
MODULES = ['GaussianFourierCore', 'GaussianFourierPolynomial', 'GaussianFourierEven',
           'GaussianRationalTransform', 'GaussianActualTransform', 'GaussianActualFourier',
           'GaussianFourierAudit']

def digest(path):
    data = path.read_bytes()
    return {'file': str(path), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def atomic(path, data):
    temp = path.with_suffix(path.suffix + '.tmp')
    temp.write_text(json.dumps(data, indent=2) + '\n')
    temp.replace(path)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=pathlib.Path, required=True)
    parser.add_argument('--context', type=pathlib.Path, default=DEFAULT_CONTEXT)
    parser.add_argument('--gaussian-providers', type=pathlib.Path,
                        default=pathlib.Path('/data/ivy-rh-one-prime-20261124/gaussian-kernel/objects'))
    parser.add_argument('--lean-cert-providers', type=pathlib.Path,
                        default=pathlib.Path('/data/ivy-rh-octic-20261123/integration/public739-runtime-appends-v1/feedback734/union'))
    args = parser.parse_args()
    context = json.loads(args.context.read_text())
    compiler = pathlib.Path(context['compiler'])
    if digest(compiler)['sha256'] != context['compiler_sha256']:
        raise RuntimeError('Pinned compiler bytes differ')
    for name in ['GaussianSources', 'GaussianCoeffs', 'GaussianCoeffArithmetic', 'GaussianPhysical']:
        if not (args.gaussian_providers / (name + '.olean')).is_file():
            raise RuntimeError('Missing explicit Gaussian provider: ' + name)
    args.out.mkdir(parents=True, exist_ok=False)
    source = args.out / 'source'; source.mkdir()
    objects = args.out / 'objects'; objects.mkdir()
    files = []
    for module in MODULES:
        target = source / (module + '.lean')
        target.write_bytes((HERE / (module + '.lean')).read_bytes())
        files.append(digest(target))
    env = os.environ.copy()
    env['LEAN_PATH'] = ':'.join(map(str, [objects, args.gaussian_providers,
        args.lean_cert_providers, *context['generic_libraries']]))
    start = time.monotonic(); runs = []
    for module in MODULES:
        run = args.out / module; run.mkdir()
        command = ['/usr/bin/prlimit', '--as=68719476736', '--cpu=1800', '--',
            '/usr/bin/time', '-v', str(compiler), '-j1', '--root=' + str(source),
            str(source / (module + '.lean')), '-o', str(objects / (module + '.olean'))]
        tick = time.monotonic()
        with (run/'stdout').open('w') as stdout, (run/'stderr').open('w') as stderr:
            result = subprocess.run(command, env=env, stdout=stdout, stderr=stderr)
        raw = (run/'stderr').read_text()
        match = re.search(r'Maximum resident set size \(kbytes\): (\d+)', raw)
        row = {'module': module, 'command': command, 'exit_code': result.returncode,
               'elapsed_seconds': time.monotonic()-tick,
               'max_rss_KiB': int(match.group(1)) if match else None,
               'source': digest(source/(module+'.lean'))}
        atomic(run/'RESULT.json', row); runs.append(row)
        if result.returncode != 0:
            atomic(args.out/'RESULT.json', {'status': 'FAILED', 'runs': runs})
            raise RuntimeError('Compiler rejected ' + module)
    final = (args.out/'GaussianFourierAudit/stdout').read_text()
    if 'GAUSSIAN_FOURIER_AUDIT_PASS roots=21 edges=16' not in final:
        raise RuntimeError('Missing exact completed proof-value/axiom audit')
    result = {'status': 'PASS_FRESH_FOURIER_PROOFS_WITH_DECLARED_EXISTING_PROVIDERS',
        'elapsed_seconds': time.monotonic()-start,
        'scope': 'All7 Fourier application modules freshly compiled; Gaussian numerical and LeanCert providers reused explicitly, not a full clean numerical rerun.',
        'source_files': files, 'runs': runs, 'context': digest(args.context),
        'compiler': digest(compiler), 'lean_path': env['LEAN_PATH'],
        'existing_gaussian_provider_objects': [digest(args.gaussian_providers/(x+'.olean'))
            for x in ['GaussianSources', 'GaussianCoeffs', 'GaussianCoeffArithmetic', 'GaussianPhysical']],
        'standard_axioms_only': ['propext', 'Classical.choice', 'Quot.sound'],
        'source_first_PV': False}
    atomic(args.out/'RESULT.json', result)
    print(json.dumps({'status': result['status'], 'elapsed_seconds': result['elapsed_seconds'],
        'max_child_RSS_KiB': max(x['max_rss_KiB'] for x in runs),
        'receipt_sha256': digest(args.out/'RESULT.json')['sha256']}))

if __name__ == '__main__':
    main()
