#!/bin/bash
# /bin/bash --noprofile --norc /work/submission/replay_repair.sh
set -eu
export LC_ALL=C
cd /work/submission
OUT=/work/repair-replay
/usr/bin/python3.10 -B -c "from pathlib import Path; Path('$OUT').mkdir(exist_ok=True)"
record() {
 local name="$1"; shift
 printf 'command:'; printf ' %q' "$@"; printf '\n'
 if "$@" >"$OUT/$name.stdout" 2>"$OUT/$name.stderr"; then
  printf '%s status=0\n' "$name"
 else
  local code="$?"
  printf '%s status=%s\n' "$name" "$code"
  return "$code"
 fi
}
record primecount-build /usr/bin/g++ -std=c++17 -O3 primecount.cpp -o "$OUT/pc"
record sieve-build /usr/bin/g++ -std=c++17 -O3 sieve.cpp -o "$OUT/sieve"
record endpoint /usr/bin/python3.10 -B endpoint.py "$OUT/pc"
record repair-anchor /usr/bin/python3.10 -B repair_anchor.py "$OUT/pc"
record ramanujan /usr/bin/python3.10 -B verify.py
record higher /usr/bin/python3.10 -B higher.py
record mertens /usr/bin/python3.10 -B mertens.py
record sieve "$OUT/sieve"
record enhanced /usr/bin/python3.10 -B enhanced.py
