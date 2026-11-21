from pathlib import Path
import json,hashlib,re
from html.parser import HTMLParser
B=Path(__file__).resolve().parent
R=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-rh-propagation-20261120/reports')
class N:
 def __init__(self,tag='',attrs=()):self.tag=tag;self.attrs=dict(attrs);self.c=[]
 def all(self,tags):
  for x in self.c:
   if isinstance(x,N):
    if x.tag in tags:yield x
    yield from x.all(tags)
 def txt(self):
  vals=[x.txt()if isinstance(x,N)else x for x in self.c];v=' '.join(x.strip()for x in vals if x.strip())
  if self.tag=='mfrac'and len(vals)==2:return '('+vals[0]+')/('+vals[1]+')'
  if self.tag=='msup'and len(vals)==2:return vals[0]+'^('+vals[1]+')'
  if self.tag=='msub'and len(vals)==2:return vals[0]+'_('+vals[1]+')'
  if self.tag=='msubsup'and len(vals)==3:return vals[0]+'_('+vals[1]+')^('+vals[2]+')'
  if self.tag=='msqrt':return 'sqrt('+v+')'
  return v
class P(HTMLParser):
 def __init__(self):super().__init__(convert_charrefs=True);self.root=N();self.stack=[self.root]
 def handle_starttag(self,t,a):
  n=N(t,a);self.stack[-1].c.append(n)
  if t not in ['meta','link','img','br','hr','input','source','mspace']:self.stack.append(n)
 def handle_startendtag(self,t,a):self.stack[-1].c.append(N(t,a))
 def handle_endtag(self,t):
  for i in range(len(self.stack)-1,0,-1):
   if self.stack[i].tag==t:self.stack=self.stack[:i];break
 def handle_data(self,s):self.stack[-1].c.append(s)
rows=[]
for lang in ['EN','KO']:
 p=R/f'RH_PROPAGATION_REPORT_{lang}.html';raw=p.read_text();q=P();q.feed(re.sub(r'<(?:style|script)\b[^>]*>.*?</(?:style|script)>','',raw,flags=re.S));main=list(q.root.all(['main']))[0]
 sections=[];part={'id':'lead','text':[]};blocks=[]
 for el in main.c:
  if not isinstance(el,N):continue
  if el.tag=='h2':
   sections.append(part);part={'id':el.attrs.get('id'),'text':[el.txt()]}
  else:part['text'].append(el.txt())
  blocks.append({'tag':el.tag,'id':el.attrs.get('id'),'class':el.attrs.get('class'),'text':el.txt()})
 sections.append(part)
 for i,row in enumerate(sections):
  row['text']='\n\n'.join(row['text']);(B/f'{lang}_{i:02}_{row["id"]}.txt').write_text(row['text'])
 (B/f'{lang}_SECTIONS.json').write_text(json.dumps(sections,indent=2,ensure_ascii=False)+'\n')
 (B/f'{lang}_BLOCKS.json').write_text(json.dumps(blocks,indent=2,ensure_ascii=False)+'\n')
 (B/f'{lang}_TEXT.txt').write_text(main.txt())
 rows.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size,'text_chars':len(main.txt()),'sections':[{'id':x['id'],'characters':len(x['text'])}for x in sections]})
print(json.dumps(rows,indent=2,ensure_ascii=False))
(B/'INPUT_HASHES.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n')
