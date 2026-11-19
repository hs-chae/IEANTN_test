#!/bin/bash
# Invoke with non-login /bin/bash. Must run against the same read-only packet.
# Replay writes only flat evidence to the specified review output directory.
set -u
export LC_ALL=C PYTHONDONTWRITEBYTECODE=1
A=${1:-/work/exact}
S=${2:-/work/submission}
export A S
/usr/bin/python3.10 -c 'from pathlib import Path;import os;Path(os.environ["S"]).mkdir(parents=True,exist_ok=True)'
if [[ ! -d $A ]]; then
 /usr/bin/python3.10 /task/RESTORE_CANDIDATE.py --out "$A" || exit
fi
cd "$A" || exit
run() {
 local s=$1 f=$2; shift 2
 /usr/bin/python3.10 "$f" "$@" >"$S/$s.stdout" 2>"$S/$s.stderr"
 printf '%s\n' "$?" >"$S/$s.status"
}
for s in finite_mertens repair_finite second_finite power_prefix certify repair_r second_r compact_r second_m repair_spectral root_zoom endpoint finite_zoom finite_joins repair_joins fixed_x_check source_audit second_portfolio repair_portfolio; do
 run "$s" "$s.py" &
done
wait
run repair_evaluate-log_200 repair_evaluate.py log 200
run repair_evaluate-x_1e70 repair_evaluate.py x 1e70
run evaluate-log_200 evaluate.py log 200
run finite_query-10007 finite_query.py 10007
# ancillary.py and build_review.py use /work/exact as restored root by default.
run ancillary "$S/ancillary.py"
run historical_log "$S/historical_log.py"
run check_evidence "$S/check_evidence.py" "$A"
