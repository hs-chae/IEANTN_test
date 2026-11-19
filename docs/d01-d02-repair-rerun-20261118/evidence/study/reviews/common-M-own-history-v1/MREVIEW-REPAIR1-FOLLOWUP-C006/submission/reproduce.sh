#!/bin/bash
# Run in non-login /bin/bash with fresh destination (optional argument).
set -eu
export PYTHONDONTWRITEBYTECODE=1
unset PYTHONOPTIMIZE
case ${BASH_SOURCE[0]} in */*) here=${BASH_SOURCE[0]%/*};; *) here=.;; esac
here=$(cd "$here"; pwd)
PY=/usr/bin/python3.10
out=$($PY -c 'import sys; from pathlib import Path; print(Path(sys.argv[1]).resolve())' "${1:-/work/review-reproduction}")
$PY -c 'import sys; from pathlib import Path; Path(sys.argv[1]).mkdir()' "$out"
$PY /task/RESTORE_CANDIDATE.py --out "$out/exact" > "$out/restore.stdout" 2> "$out/restore.stderr"
cd "$out/exact"
r=0; $PY replay_repair.py > "$out/replay.stdout" 2> "$out/replay.stderr" || r=$?
printf '%s\n' "$r" > "$out/replay.exit"
s=0; $PY "$here/ancillary.py" "$out/exact" > "$out/ancillary.stdout" 2> "$out/ancillary.stderr" || s=$?
printf '%s\n' "$s" > "$out/ancillary.exit"
$PY -c 'import hashlib,sys; from pathlib import Path; d=Path(sys.argv[1]); [print(hashlib.sha256(f.read_bytes()).hexdigest(),f.name) for f in sorted(d.iterdir()) if f.is_file()]' "$out"
test "$r" = 0 && test "$s" = 0
