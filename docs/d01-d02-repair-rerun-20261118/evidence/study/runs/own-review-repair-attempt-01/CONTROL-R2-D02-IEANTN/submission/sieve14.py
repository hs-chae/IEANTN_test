#!/usr/bin/python3.10
from pathlib import Path
p=Path(__file__).with_name('mertens.cpp')
s=p.read_text()
i=s.index('   t.push_back({form,223,10000});')
j=s.index('\n }',i)
Path('/work/sieve14.cpp').write_text(s[:i]+'   t.push_back({form,2214,100000});'+s[j:])
