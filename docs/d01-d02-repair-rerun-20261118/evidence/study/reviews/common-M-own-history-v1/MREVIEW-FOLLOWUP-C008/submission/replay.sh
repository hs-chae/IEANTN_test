#!/bin/bash
# Reproduce from the permitted packet on the approved offline runtime.
# Supply existing writable output directory and a FRESH candidate restore destination.
set -eu
export LC_ALL=C PYTHONDONTWRITEBYTECODE=1
out=${1:?absolute output directory required}
dst=${2:?fresh candidate restore directory required}
here=$PWD
[[ $out == /* && $dst == /* && -d $out ]]
/usr/bin/python3.10 /task/RESTORE_CANDIDATE.py --out "$dst"
cd "$dst"
job () {
    local name="$1${2-}" status=0
    /usr/bin/python3.10 "$@" >"$out/$name.stdout" 2>"$out/$name.stderr" || status=$?
    printf '%s\n' "$status" >"$out/$name.status"
    [[ "$status" -eq 0 ]]
}
job verify.py --endpoint
job bridge.py
job general.py
job early.py
job weighted.py
job smallprod.py
job mverify.py
job tradeoff.py
job receipts.py
job spectral_repair.py
job power_bridge.py
job gap_repair.py
job optimize_d02.py
job finite_d02.py
job finite_d02.py --extended
job power_new.py
job run_d02.py
status=0
PYTHONPATH="$dst" /usr/bin/python3.10 "$here/ancillary.py" >"$out/ancillary.py.stdout" 2>"$out/ancillary.py.stderr" || status=$?
printf '%s\n' "$status" >"$out/ancillary.py.status"
[[ "$status" -eq 0 ]]
