#!/bin/bash
# Run in /work/submission with non-login /bin/bash; assertions required.
set -eu
export PYTHONDONTWRITEBYTECODE=1
py=/usr/bin/python3.10
g++ -O3 -Wall -Wextra -std=c++17 repair_m.cpp -o /work/repair_m
$py repair_m.py > /work/repair_m_stdout.txt
$py anchor.py > /work/anchor_stdout.txt
$py bridge14.py > /work/bridge14_stdout.txt
$py sieve14.py
g++ -O3 -Wall -Wextra -std=c++17 /work/sieve14.cpp -o /work/sieve14
/work/sieve14 > /work/sieve14_stdout.txt
$py bridge_opt.py > /work/bridge_opt_stdout.txt
$py sieve_opt.py
g++ -O3 -Wall -Wextra -std=c++17 /work/sieve_opt.cpp -o /work/sieve_opt
/work/sieve_opt > /work/sieve_opt_stdout.txt
$py repair_ram.py > /work/repair_ram_stdout.txt
$py fixed49.py > /work/fixed49_stdout.txt
$py m_tail_extra.py > /work/m_tail_extra_stdout.txt
$py - <<'PY2'
from pathlib import Path
for k in ['repair_m','anchor','bridge14','sieve14','bridge_opt','sieve_opt','repair_ram','fixed49','m_tail_extra']:
    assert Path(k+'_receipt.txt').read_bytes()==Path('/work',k+'_stdout.txt').read_bytes(), k
print('all repaired receipts match')
PY2
