from pathlib import Path
from html.parser import HTMLParser
class N:
 def __init__(self,t,a=None,line=0):self.t=t;self.a=dict(a or []);self.c=[];self.line=line
class P(HTMLParser):
 def __init__(self):super().__init__();self.root=N('root');self.s=[self.root]
 def handle_starttag(self,t,a):
  n=N(t,a,self.getpos()[0]);self.s[-1].c.append(n)
  if t not in ['area','base','br','col','embed','hr','img','input','link','meta','param','source','track','wbr']:self.s.append(n)
 def handle_startendtag(self,t,a):self.s[-1].c.append(N(t,a,self.getpos()[0]))
 def handle_endtag(self,t):
  for i in range(len(self.s)-1,0,-1):
   if self.s[i].t==t:self.s=self.s[:i];break
 def handle_data(self,t):self.s[-1].c.append(t)
def r(n):
 if isinstance(n,str):return n
 if n.t in ['style','script']:return ''
 z=[r(c) for c in n.c]
 if n.t=='mfrac' and len(z)==2:return '('+z[0]+')/('+z[1]+')'
 if n.t=='msqrt':return 'sqrt('+''.join(z)+')'
 if n.t=='msup' and len(z)==2:return z[0]+'^('+z[1]+')'
 if n.t=='msub' and len(z)==2:return z[0]+'_('+z[1]+')'
 if n.t=='msubsup' and len(z)==3:return z[0]+'_('+z[1]+')^('+z[2]+')'
 if n.t=='munder' and len(z)==2:return z[0]+'_('+z[1]+')'
 if n.t=='munderover' and len(z)==3:return z[0]+'_('+z[1]+')^('+z[2]+')'
 if n.t=='mover' and len(z)==2:return 'over('+','.join(z)+')'
 return ' '.join(z)
def blocks(n,out):
 if isinstance(n,str):return
 if n.t=='body':out.append('BODY')
 cl=n.a.get('class','')
 block=n.t in ['h1','h2','h3','h4','p','li','tr','pre','figcaption','summary'] or n.t=='div' and cl in ['formula','eq','tag']
 if block:
  text=' '.join(r(n).split());out.append(f'{len(out):04d} [source line {n.line}; {n.t}#{n.a.get("id","")}.{cl}] {text}')
  return
 for c in n.c:blocks(c,out)
for lang in ['EN','KO']:
 p=P();p.feed(Path(f'/ryu/hyunsik/playground/independence/codex/ivy/ieantn-rh-propagation-20261120/reports/RH_PROPAGATION_REPORT_{lang}.html').read_text());out=[];blocks(p.root,out);Path(f'/data/ivy-rh-propagation-20261120/review/fresh-report-reader-v1/{lang}.full.txt').write_text('\n'.join(out));print(lang,len(out))
