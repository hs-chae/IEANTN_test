#!/usr/bin/env python3
"""Reproduce the pinned authors' numerical checks without changing their code.

Requires Python>=3.10,Linux /usr/bin/time andprlimit. The default creates an
ownedvenv and installs python-flint0.9.0. Outputs are ordinary numericalevidenceE.
"""
from pathlib import Path
import argparse, hashlib, io, json, os, re, subprocess, sys, time, urllib.request, zipfile

HERE = Path(__file__).resolve().parent
URL = 'https://zenodo.org/records/24429650/files/prime-gaps-v2-supplement.zip'
ARCHIVE_SHA256 = 'e354818288972e88ca0a1cf2b332e1446e1bacc99291c6aa44b26c2f2837fd81'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, data):
    temporary = path.with_name(path.name+'.fresh-tmp')
    with temporary.open('x') as stream:
        stream.write(json.dumps(data, indent=2, allow_nan=False)+'\n')
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)


parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
parser.add_argument('--out', required=True, type=Path)
parser.add_argument('--archive', type=Path)
parser.add_argument('--python-flint', type=Path)
args = parser.parse_args()
args.out = args.out.absolute()
if sys.flags.optimize != 0:
    raise RuntimeError('Original programs require assertions enabled; run this driver without-O/-OO')
args.out.mkdir(parents=True, exist_ok=False)
(args.out/'reproduce.executed.py').write_bytes(Path(__file__).read_bytes())
data = args.archive.read_bytes() if args.archive else urllib.request.urlopen(URL, timeout=60).read()
if hashlib.sha256(data).hexdigest() != ARCHIVE_SHA256:
    raise RuntimeError('pinned original archive hash mismatch')
(args.out/'ORIGINAL_SUPPLEMENT.zip').write_bytes(data)
source = args.out/'original-source'
source.mkdir()
archive = zipfile.ZipFile(io.BytesIO(data))
original = {}
for info in archive.infolist():
    if info.is_dir():
        continue
    path = source/info.filename
    if not path.resolve().is_relative_to(source.resolve()):
        raise RuntimeError('archive member outside owned source directory')
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(archive.read(info))
    original[info.filename] = sha(path)
for line in (source/'SHA256SUMS').read_text().splitlines():
    digest, name = line.split(maxsplit=1)
    if sha(source/name.lstrip('*')) != digest:
        raise RuntimeError('original SHA256SUMS mismatch')
save(args.out/'ORIGINAL_SOURCE_HASHES.json', original)
env = os.environ.copy()
env.pop('PYTHONOPTIMIZE', None)
env['PYTHONDONTWRITEBYTECODE'] = '1'
if args.python_flint:
    python = args.python_flint.absolute()
else:
    subprocess.run([sys.executable, '-m', 'venv', str(args.out/'venv')], check=True)
    python = (args.out/'venv/bin/python').absolute()
    subprocess.run([str(python), '-m', 'pip', 'install', '--disable-pip-version-check',
                    '--report', str(args.out/'FLINT_INSTALL.json'), 'python-flint==0.9.0'], check=True)
version = subprocess.run([str(python), '-c', 'import flint,importlib.metadata;print(importlib.metadata.version("python-flint"))'], capture_output=True, text=True, check=True)
if version.stdout.strip() != '0.9.0':
    raise RuntimeError('wrong python-flint version')
certificates = source/'certificates'
witnesses = [str(certificates/name) for name in ['witness-gap.json','witness-grh.json','witness-ap.json']]
commands = [
    ('integer', [sys.executable,'-B',str(certificates/'certify_integer.py'),*witnesses,'--grid-size','1048576']),
    ('Arb', [str(python),'-B',str(certificates/'certify.py'),*witnesses,'--grid-size','1048576']),
    ('explicit', [str(python),'-B',str(certificates/'uniforme.py')]),
    ('retuned', [str(python),'-B',str(HERE/'retuned_margin.py'),'--out',str(args.out/'retuned-results')])]
rows = []
for label, command in commands:
    run = args.out/label
    run.mkdir(exist_ok=True)
    full = ['/usr/bin/prlimit','--as=68719476736','--cpu=7200','--','/usr/bin/time','-v',*command]
    started = time.monotonic()
    process = subprocess.run(full, cwd=certificates, env=env, capture_output=True)
    (run/'stdout').write_bytes(process.stdout)
    (run/'stderr').write_bytes(process.stderr)
    if process.returncode != 0:
        raise RuntimeError('original numerical run failed:'+label)
    peak = re.search(rb'Maximum resident set size \(kbytes\): (\d+)', process.stderr)
    rows.append({'label':label,'command':full,'seconds':time.monotonic()-started,
                 'peak_child_RSS_KiB':int(peak.group(1)) if peak else None,
                 'stdout_sha256':sha(run/'stdout'),'stderr_sha256':sha(run/'stderr')})
if {name:sha(source/name) for name in original} != original:
    raise RuntimeError('original source files changed')
integer = json.loads((args.out/'integer/stdout').read_text())
expected = {'witness-gap.json':'0.834050622349','witness-grh.json':'0.851246419624','witness-ap.json':'0.851127042054'}
if len(integer)!=3 or any(row['grid_size']!=1048576 or row['ratio_upper_bound']!=expected.get(row['file']) for row in integer):
    raise RuntimeError('integer archive output mismatch')
if not (args.out/'retuned-results/RESULT.json').is_file():
    raise RuntimeError('missing counterfactual comparison result')
save(args.out/'RESULT.json', {'status':'PASS_PINNED_ORIGINAL_NUMERICAL_REPRODUCTION_AND_SEPARATE_RETUNED_COMPARISON',
     'archive_sha256':ARCHIVE_SHA256,'original_source_files':len(original),
     'original_source_unchanged':True,'grid':1048576,'original_assertions_enabled':True,
     'python_flint':'0.9.0','reproduce_sha256':sha(args.out/'reproduce.executed.py'),'runs':rows,
     'boundary':'ordinary numericalevidenceE; no source-firstPV/kernelD/completeLeananalyticproofclaim'})
print('PASS',len(rows),'runs')
