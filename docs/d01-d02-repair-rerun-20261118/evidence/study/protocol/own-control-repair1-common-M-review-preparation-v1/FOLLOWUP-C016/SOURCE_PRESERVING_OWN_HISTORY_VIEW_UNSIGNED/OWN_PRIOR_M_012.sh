#!/bin/bash
# Run from a fresh writable evidence directory; no -O for Python or -DNDEBUG for C++.
# The assessed run used /work/exact for the byte-identical restoration.
set -u
export PYTHONDONTWRITEBYTECODE=1
/usr/bin/python3.10 /task/RESTORE_CANDIDATE.py --out /work/exact || exit
o=$PWD
cd /work/exact
{ g++ -O3 pcount.cpp -o /work/pcount && /usr/bin/python3.10 endpoint.py; echo endpoint_status=$?; } >"$o/endpoint.log" 2>&1 &
{ /usr/bin/python3.10 cert.py; echo cert_status=$?; } >"$o/cert.log" 2>&1 &
{ /usr/bin/python3.10 ram_early.py; echo early_status=$?; } >"$o/early.log" 2>&1 &
{ /usr/bin/python3.10 mertens.py; echo mertens_status=$?; } >"$o/mertens.log" 2>&1 &
{ g++ -O3 -Wall -Wextra -std=c++17 mertens.cpp -o /work/mertens_packet && /work/mertens_packet >/work/sieve_replay.txt; echo sieve_status=$?; } >"$o/sieve.log" 2>&1 &
{ /usr/bin/python3.10 anchor.py; echo anchor_status=$?; } >"$o/anchor.log" 2>&1 &
wait
# For byte-linked inputs, verify /work/sieve_replay.txt == /work/exact/sieve_receipt.txt.
cd "$o"
/usr/bin/python3.10 -c 'from pathlib import Path; Path("sieve_stdout.txt").write_bytes(Path("/work/sieve_replay.txt").read_bytes())'
{ g++ -O3 -std=c++17 readback.cpp -o /work/readback && /work/readback; echo readback_status=$?; } >readback.log 2>&1
/usr/bin/python3.10 -B check.py >check.log 2>&1
echo check_status=$? >>check.log
