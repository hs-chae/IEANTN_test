#!/bin/bash
# Run with /bin/bash --noprofile --norc, cwd /work/submission.
set -eu
export LC_ALL=C
unset PYTHONOPTIMIZE
P=/usr/bin/python3.10
/usr/bin/g++ -O3 -std=c++17 d02finite_repair.cpp -o /work/d02finite_repair
/work/d02finite_repair > /work/d02finite_replay.out
"$P" - <<'END'
from pathlib import Path
assert Path('/work/d02finite_replay.out').read_bytes() == Path('repair_tape.txt').read_bytes()
END
for s in d02ram d02m d02secondary endpoint_check repair_limits
do
  "$P" -B -u "$s.py" > "/work/${s}_repair_replay.out"
done
