#!/usr/bin/env python3
"""Incremental kernel proof run against read-only accepted predecessor banks.

This is development evidence; the root will separately replay complete source.
No source-first PV claim is made by this compiler wrapper.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, resource, shutil, subprocess, time

B = Path(__file__).resolve().parent
N = B.parents[2]
CONTEXT = N / 'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json'
OLD = Path('/data/ivy-rh-continuation-20261122/ramanujan')
BANKS = [OLD / 'node-publication-v9/objects', OLD / 'strong-source-v2/objects',
         OLD / 'strong-source-v2/union']

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(ok, msg):
    if not ok: raise ValueError(msg)

def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--module', default='SpectralGMRefined')
    p.add_argument('--extra-library', type=Path, action='append', default=[])
    p.add_argument('--foundation-library', type=Path, action='append', default=[])
    # Explicit fresh foundation paths replace historical application banks.
    a = p.parse_args(); out = a.out.resolve()
    runner_hash=sha(Path(__file__))
    need(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*',a.module) is not None,'module identifier')
    need(not out.exists(), 'fresh output required')
    ctx = json.loads(CONTEXT.read_text())
    need(sha(ctx['compiler']) == ctx['compiler_sha256'], 'compiler identity')
    out.mkdir(parents=True); (out/'source').mkdir(); (out/'objects').mkdir()
    source = B/(a.module+'.lean'); snapshot = out/'source'/source.name
    shutil.copyfile(source, snapshot); before = sha(source)
    banks = [*[x.resolve() for x in a.foundation_library or BANKS], *[x.resolve() for x in a.extra_library]]
    bank_snapshot = []
    for bank in banks:
        need(bank.is_dir(), 'missing predecessor bank')
        for obj in sorted(bank.rglob('*.olean')):
            bank_snapshot.append({'file':str(obj),'bytes':obj.stat().st_size,'sha256':sha(obj)})
    (out/'BANK_SNAPSHOT.json').write_text(json.dumps(bank_snapshot,indent=2)+'\n')
    env = os.environ.copy()
    env['LEAN_PATH'] = ':'.join([str(out/'objects'), *map(str, banks), *ctx['generic_libraries']])
    command = [ctx['compiler'], '--root='+str(out/'source'), '-j8', '-o',
               str(out/'objects'/(a.module+'.olean')), str(snapshot)]
    def limit(): resource.setrlimit(resource.RLIMIT_AS, (80<<30, 80<<30))
    start = time.monotonic()
    cp = subprocess.run(['/usr/bin/time','-v',*command], cwd=out/'source', env=env,
                        capture_output=True, text=True, preexec_fn=limit)
    (out/'stdout').write_text(cp.stdout); (out/'stderr').write_text(cp.stderr)
    receipt = {'status': 'PASS' if cp.returncode == 0 else 'FAIL', 'command': command,
               'source_sha256': before, 'compiler_sha256': ctx['compiler_sha256'],
               'returncode': cp.returncode, 'elapsed_seconds': time.monotonic()-start,
               'development_only': True, 'proof_banks': list(map(str,banks)),
               'source_first_PV': False,'runner_sha256':runner_hash}
    need(sha(source)==before and sha(snapshot)==before, 'proof source changed during build')
    need(sha(Path(__file__))==runner_hash,'compiler controller changed during build')
    for row in bank_snapshot:
        need(Path(row['file']).stat().st_size==row['bytes'] and sha(row['file'])==row['sha256'],
             'read-only predecessor bank changed during compilation')
    receipt['current_bank_snapshot_sha256']=sha(out/'BANK_SNAPSHOT.json')
    receipt['bank_status']='Previously accepted application banks, current object snapshot checked; not a new full-source proof replay.'
    if cp.returncode==0:
        audits=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",cp.stdout,re.S)
        need(audits,'missing actual final axiom outputs')
        allowed={'propext','Classical.choice','Quot.sound'}
        need(all({x.strip() for x in ax.split(',') if x.strip()}<=allowed for _,ax in audits),
             'nonstandard execution or proof axiom')
        receipt['axiom_audits']=[{'theorem':name,'axioms':ax}for name,ax in audits]
    (out/'RESULT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt))
    if cp.returncode: print(cp.stdout[-14000:]); raise SystemExit(cp.returncode)

if __name__ == '__main__': main()
