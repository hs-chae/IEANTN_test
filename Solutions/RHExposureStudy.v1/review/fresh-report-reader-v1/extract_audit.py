from html.parser import HTMLParser
from pathlib import Path
import json,hashlib
base=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-rh-propagation-20261120/reports')
s=(base/'RH_PROPAGATION_REPORT_EN.html').read_text()
class A(HTMLParser):
 def __init__(self):super().__init__(convert_charrefs=False);self.lines=[0];self.start=None;self.end=None;self.depth=0
 def off(self):l,c=self.getpos();return self.lines[l-1]+c
 def handle_starttag(self,t,a):
  if self.start is None and t=='details' and dict(a).get('class')=='audit':self.start=self.off();self.depth=1
  elif self.start is not None and self.end is None and t=='details':self.depth+=1
 def handle_endtag(self,t):
  if self.start is not None and self.end is None and t=='details':
   self.depth-=1
   if self.depth==0:self.end=self.off()+len('</details>')
p=A();p.lines=[0]+[i+1 for i,c in enumerate(s) if c=='\n'];p.feed(s);f=s[p.start:p.end]
out=Path('/data/ivy-rh-propagation-20261120/review/fresh-report-reader-v1');(out/'audit_original.fragment.html').write_text(f)
class T(HTMLParser):
 def __init__(self):super().__init__(convert_charrefs=False);self.stack=[];self.nodes=[]
 def handle_starttag(self,t,a):
  if t not in ['br','hr','meta','link','img','input','wbr']:self.stack.append(t)
 def handle_startendtag(self,t,a):pass
 def handle_endtag(self,t):
  for i in range(len(self.stack)-1,-1,-1):
   if self.stack[i]==t:self.stack=self.stack[:i];break
 def handle_data(self,d):
  if not set(self.stack)&{'math','code','pre','style','script'} and d.strip():self.nodes.append(d)
t=T();t.feed(f);(out/'audit_text_nodes.json').write_text(json.dumps(t.nodes,ensure_ascii=False,indent=2)+'\n')
for i,v in enumerate(t.nodes):print(i,repr(v))
print('fragment bytes',len(f.encode()),'sha256',hashlib.sha256(f.encode()).hexdigest())
