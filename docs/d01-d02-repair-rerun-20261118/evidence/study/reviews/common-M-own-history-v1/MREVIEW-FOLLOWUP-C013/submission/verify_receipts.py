#!/usr/bin/python3.10
"""Verify captured original replays against the candidate's locked receipts."""
import json,hashlib
from pathlib import Path
p=Path(__file__).resolve().parent; q=Path('/work/c013')
def sha(x):return hashlib.sha256(x.read_bytes()).hexdigest()
jobs=[
 ('verify.py-gap.log','verify.py root gap','gap-replay.txt','quotient counts at n and floor(n/e); old gap cells and tails 36.75–400, 400/550/850 to infinity'),
 ('verify.py-trade.log','verify.py trade','trade-replay.txt','supplementary old prefix cells and strong degree-19 tail at 850'),
 ('mcheck.py-mcheck.py.log','mcheck.py','mcheck-replay.txt','old CH2 [26,210] and density tail joins and frozen coefficients'),
 ('orders.py-50.log','orders.py 0 6 12 19 25 50','orders-replay.txt','six exact rational all-order algorithm examples'),
 ('claims.py-orders.log','claims.py early rays orders','claims-replay.txt','new early intervals, full advanced cells and tails, all printed numeric spectral and all-order constants'),
 ('localgap.py-localgap.py.log','localgap.py','localgap-replay.txt','near-root derivative and closed short integer-cell bridge 38358837683–38358847682'),
 ('mnew.py-mnew.py.log','mnew.py','mnew-replay.txt','new frozen power caps and log-quarter cells [26,190] or shorter ranges, and matched endpoints'),
 ('mfinite.py-mfinite.py.log','mfinite.py','mfinite-replay.txt','closed x=2 to 100000 prefix prime-knot cells and directed products'),
 ('comparison.py-comparison.py.log','comparison.py','comparison-replay.txt','furnished model floors and density-free fallback endpoint budgets')]
entry={}
for fn,args,ref,cov in jobs:
 v=(p/fn).read_bytes()
 assert v.endswith(b'exit=0\n')
 assert not any(z in v for z in (b'Traceback',b'FAILED candidate',b'unverified'))
 assert v.removesuffix(b'exit=0\n')==(q/ref).read_bytes(),fn
 entry[fn]=dict(argv=['/usr/bin/python3.10','-B','-u',*args.split()],exit=0,stderr='None observed in combined program capture',coverage=cov,sha256_log=sha(p/fn),candidate_stdout_ref=ref,candidate_stdout_sha256=sha(q/ref))
a=p/'ancillary.log'
assert Path('/work/anc-new.log').read_bytes()==a.read_bytes().removesuffix(b'exit=0\n')
entry['ancillary.log']=dict(argv=['/usr/bin/python3.10','-B','-c','exec(compile(open("/work/submission/ancillary.py").read(),"ancillary.py","exec"))'],exit=0,stderr='',sha256_log=sha(a),coverage='exact case endpoints, suffixes, original literal-reading counterexamples and repeated failed sufficient tests; see source')
z=p/'sieve-run.stdout'
assert z.read_bytes()==(q/'sieve-results.txt').read_bytes()
entry['sieve-run.stdout']=dict(commands=['/usr/bin/python3.10 -B tables.py >/work/tables','/usr/bin/g++ -O3 -std=c++17 -Wall -Wextra sieve.cpp -o /work/primes-cert','/work/primes-cert </work/tables'],exit=0,tool_session=75458,stderr='Only shell startup locale warning, no compiler or sieve diagnostics observed',input_sha256=sha(Path('/work/tables')),binary_sha256=sha(Path('/work/primes-cert')),stdout_sha256=sha(z),coverage='constants through 100000000; whole stream through 195730000000 with 7842936328 primes, 7453651 closed real cells',candidate_stdout_match=True)
p.joinpath('replay_receipts.json').write_text(json.dumps(dict(cwd='/work/c013',restore=['/usr/bin/python3.10','/task/RESTORE_CANDIDATE.py','--out','/work/c013'],shell='non-login /bin/bash, export LC_ALL=C',versions=p.joinpath('versions.log').read_text(),results=entry,effort='Entire candidate source and formula/source dependency audit; all material submitted numeric certificates rerun; nine Python CLI replays plus exact ancillary checks and full GCC sieve with streaming only. No independent reconstruction of published finite computations.',packaging_attempt='First transcription of synthesized sieve stdout file had an extra trailing LF; removed that packaging LF and exact bytes then matched the observed 22 output lines and locked receipt.'),indent=2)+'\n')
print('All observed receipts match.')

