#!/usr/bin/python3.10
"""Run unchanged locked Mertens certificates with observer-only V<1 tests."""
from pathlib import Path
from contextlib import redirect_stdout
import sys, io, hashlib
sys.path.insert(0,'/work/review_candidate')
import bounds as b
import finite_m as f
raw=b.I.__truediv__
checks={('bounds.py',348):0,('bounds.py',395):0,('bounds.py',412):0,
        ('bounds.py',443):0,('bounds.py',451):0,('finite_m.py',128):0}
maximal={}
def division(x,y):
    frame=sys._getframe(1)
    loc=(frame.f_code.co_filename.rsplit('/',1)[-1],frame.f_lineno)
    if loc in checks:
        t=b.I(y)
        assert t.l>0,(loc,t)
        checks[loc]+=1
        maximal[loc]=min(maximal.get(loc,t.l),t.l)
    return raw(x,y)
def observed(function):
    out=io.StringIO()
    with redirect_stdout(out): function()
    return out.getvalue()
b.I.__truediv__=division
text=observed(b.mertens)
orig=Path('/work/review_candidate/replay.txt').read_text().splitlines(keepends=True)
assert text==''.join(orig[54:83])
text=observed(f.run)
assert text==Path('/work/review_candidate/finite_replay.txt').read_text()
assert all(checks.values())
for loc in checks:
    print(loc, 'number of positive-denominator guards',checks[loc],'minimum lower endpoint',maximal[loc])
print('Unchanged locked arithmetic continued unmodified; observed output matches original Mertens receipts.')
