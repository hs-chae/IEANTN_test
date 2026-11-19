#!/bin/bash
# Run with /bin/bash --noprofile --norc; offline. Fresh destination argument.
set -eu
export LC_ALL=C
unset PYTHONOPTIMIZE
root=${1:-/work/replay-c022}
p=/usr/bin/python3.10
here=${BASH_SOURCE[0]%/*}
[[ "$here" == "${BASH_SOURCE[0]}" ]] && here=.
here="$(cd "$here"; pwd)"
P="$p"
"$P" /task/RESTORE_CANDIDATE.py --out "$root"
cd "$root"
run(){ local n=$1; shift; printf '%q ' "$@" > "$n.replay.cmd"; local s=0; "$@" > "$n.replay.out" 2> "$n.replay.err" || s=$?; printf '%s\n' "$s" > "$n.replay.status"; }
run compile /usr/bin/g++ -O3 -std=c++17 finite_opt.cpp -o "$root/finopt"
run compile_new /usr/bin/g++ -O3 -std=c++17 d02finite.cpp -o "$root/find02"
run compile_older /usr/bin/g++ -O3 -std=c++17 D01__SUBMITTED_005.cpp -o "$root/finold"
run compile_exact /usr/bin/g++ -O3 -std=c++17 D01__SUBMITTED_007.cpp -o "$root/fin24"
run finite26 "$root/finopt"
run finite20b "$root/finopt" 20000000000 200000
run finite100m "$root/finopt" 100000000 1000000
run d02finite "$root/find02"
run older24 "$root/finold"
run exact24 "$root/fin24"
for s in d02ram d02m d02secondary endpoint_check portfolio_check mertens_new audit_summaries secondary_check analytic_check mertens_check ray_check extra_check d02screen count refine; do
  run "$s" "$P" -B "$s.py"
done
run portDus "$P" -B portfolio_check.py --dusart-only
run mertDus "$P" -B mertens_new.py --dusart-only
run portFree "$P" -B portfolio_check.py --qrh-free-prefix
for v in d02ram d02m d02secondary d02screen; do
  [[ -r "$v.py" ]]
done
# Separate destination for conditional-panel deletion.
"$P" - "$root" <<'PY'
from pathlib import Path
import sys
p=Path(sys.argv[1]); q=p/'firstpanel'; q.mkdir()
# Copy only executable modules and candidate data files, no generated artifacts.
for f in p.iterdir():
    if f.suffix not in ('.py','.txt') or f.name.startswith(('OWN_','D01_M')): continue
    data=f.read_bytes()
    if f.name=='d02screen.py':
        assert data.count(b'for tab in (old,new):')==1
        data=data.replace(b'for tab in (old,new):',b'for tab in (old,):')
    (q/f.name).write_bytes(data)
PY
cd "$root/firstpanel"
for s in d02screen d02ram d02m d02secondary; do
  run "${s}First" "$P" -B "$s.py"
done
PYTHONPATH="$PWD" run panel_audit "$P" -B "$here/panel_audit.py"
PYTHONPATH="$PWD" MERT_REPLAY="$root/mertens_check.replay.out" run ancillary_final "$P" -B "$here/ancillary.py"

