#!/bin/bash
# Run with /bin/bash --noprofile --norc /work/submission/replay.sh
# Fresh work directory required. Does not edit candidate or locked review.
set -u
export LC_ALL=C
root=/work/recheck-c012
out=/work/submission
/usr/bin/python3.10 /task/RESTORE_CANDIDATE.py --out "$root" || exit
cd "$root" || exit
run() {
  local name="$1"; shift
  printf 'command:'; printf ' %q' "$@"; printf '\n'
  "$@" >"$root/$name.stdout" 2>"$root/$name.stderr"
  local code=$?
  printf 'status=%s stdout=%s stderr=%s\n' "$code" "$root/$name.stdout" "$root/$name.stderr"
  return "$code"
}
run primecount-build /usr/bin/g++ -std=c++17 -O3 primecount.cpp -o "$root/pc" || exit
run sieve-build /usr/bin/g++ -std=c++17 -O3 sieve.cpp -o "$root/sieve" || exit
run endpoint /usr/bin/python3.10 -B endpoint.py "$root/pc" || exit
run ramanujan /usr/bin/python3.10 -B verify.py || exit
run mertens /usr/bin/python3.10 -B mertens.py || exit
run sieve "$root/sieve" || exit
export PYTHONPATH=.
run anchor-and-join /usr/bin/python3.10 -B "$out/ramanujan_audit.py" "$root/pc" || exit
run original-pdf /usr/bin/python3.10 -B "$out/pdf_exponent.py" || exit
