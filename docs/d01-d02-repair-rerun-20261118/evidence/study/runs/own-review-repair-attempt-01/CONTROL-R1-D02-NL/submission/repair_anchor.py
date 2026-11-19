"""Certify every strengthened finite pi anchor, exact inclusive counts."""
from verify import *
from subprocess import run
import sys
xs=(16,24)
ns=[ex(u).a//S for u in xs]
assert ns==[8886110,26489122129] and ns==[ex(u).b//S for u in xs]
lines=run([sys.argv[1]],input=' '.join(map(str,ns)),text=True,check=True,capture_output=True).stdout
rows=[tuple(map(int,l.split())) for l in lines.splitlines()]
assert rows==list(zip(ns,[595341,1154106844]))
for u,(_,count),caps in zip(xs,rows,[(Q('-.000396122'),0),(-D24_MINUS,D24_PLUS)]):
 d=Q(u)*(count-li_anchor(Q(u)))/ex(u)
 assert (d-caps[0]).yes() and (caps[1]-d).yes()
 print('anchor',u,'exact count',count,'normalized signed radius enclosure',d)
for up in (False,True):
 e=early(Q(58),up)
 assert (Q('3.145e-11')-e).yes()
 assert (weight(Q(58),2,Q(1,2))/PI8-e).yes()
 print('58 transported cap',up,e)
assert (ex(24)-2657).yes() and (ex(24)-599).yes()
assert (I(Q('2.169e25'))-ex(58)).yes()
