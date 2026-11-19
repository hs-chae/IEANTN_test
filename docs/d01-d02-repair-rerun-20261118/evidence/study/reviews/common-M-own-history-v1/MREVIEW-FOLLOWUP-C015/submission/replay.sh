#!/bin/bash
# Restored candidate source bytes; assertions enabled, as in the actual runs.
# Use /bin/bash --noprofile --norc /work/submission/replay.sh (fresh /work/c15).
set -e
/usr/bin/python3.10 /task/RESTORE_CANDIDATE.py --out /work/c15
cd /work/c15
export PYTHONDONTWRITEBYTECODE=1
unset PYTHONOPTIMIZE
for args in 'verify02.py R local' 'verify02.py M' 'ablation02.py' 'replay_repair.py'; do
  (set +e; set -- $args; /usr/bin/python3.10 -u "$@"; printf 'EXIT %s\n' "$?") >"/work/submission/run-${args%%.*}-${args##* }.out" 2>"/work/submission/run-${args%%.*}-${args##* }.err" &
done
wait
cd /work/submission
(set +e; /usr/bin/python3.10 -u ancillary.py; printf 'EXIT %s\n' "$?") >ancillary.out 2>ancillary.err
