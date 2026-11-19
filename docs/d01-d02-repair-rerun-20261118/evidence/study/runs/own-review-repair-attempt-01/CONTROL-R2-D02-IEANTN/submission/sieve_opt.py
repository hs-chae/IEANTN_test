#!/usr/bin/python3.10
from pathlib import Path
p=Path(__file__).with_name('mertens.cpp')
s=p.read_text()
i=s.index('   t.push_back({form,223,10000});')
j=s.index('\n }',i)
Path('/work/sieve_opt.cpp').write_text(s[:i]+'   t.push_back({form,form==2?2127:2209,100000});'+s[j:])
