"""Readable Markdown projection of the same report, without raw TeX.

Static MathML becomes Unicode operators with HTML sup/sub and explicit
parenthesized fractions. This is presentation only, not a proof transform.
"""
from html.parser import HTMLParser
from html import escape
import re,xml.etree.ElementTree as ET
def formula(node):
 tag=node.tag.rsplit('}',1)[-1];c=list(node);v=[formula(x) for x in c]
 if tag in ['mi','mn','mo','mtext']:return escape(''.join(node.itertext()))
 if tag=='mfrac':return '('+v[0]+')/('+v[1]+')'
 if tag=='msqrt':return '√('+''.join(v)+')'
 if tag in ['msup','msub']:return v[0]+'<'+('sup' if tag=='msup' else 'sub')+'>'+v[1]+'</'+('sup' if tag=='msup' else 'sub')+'>'
 if tag in ['msubsup','munderover']:return v[0]+'<sub>'+v[1]+'</sub><sup>'+v[2]+'</sup>'
 if tag in ['munder','mover']:return v[0]+'<'+('sub' if tag=='munder' else 'sup')+'>'+v[1]+'</'+('sub' if tag=='munder' else 'sup')+'>'
 if tag=='mspace':return ' '
 if tag=='mtr':return ' ; '.join(v)
 if tag=='mtable':return '('+' | '.join(v)+')'
 return ''.join(v) or escape(node.text or '')
class Markdown(HTMLParser):
 def __init__(self):super().__init__(convert_charrefs=True);self.out=[];self.body=False;self.table=None;self.cell=None;self.row=None;self.links=[];self.listdepth=0
 def emit(self,s):
  if self.cell is not None:self.cell.append(s)
  else:self.out.append(s)
 def handle_starttag(self,t,attrs):
  a=dict(attrs)
  if t=='body':self.body=True;return
  if not self.body:return
  if t=='table':self.table=[];return
  if t=='tr' and self.table is not None:self.row=[];return
  if t in ['td','th'] and self.table is not None:self.cell=[];return
  if t in ['h1','h2','h3','h4']:self.emit('\n\n'+'#'*int(t[1])+' ')
  elif t in ['p','div','section','details','article']:self.emit('\n\n')
  elif t=='summary':self.emit('\n\n**')
  elif t=='br':self.emit('  \n')
  elif t in ['strong','b']:self.emit('**')
  elif t in ['em','i']:self.emit('*')
  elif t in ['sup','sub']:self.emit('<'+t+'>')
  elif t=='code':self.emit('`')
  elif t=='li':self.emit('\n- ')
  elif t=='a':self.links.append(a.get('href',''));self.emit('[')
 def handle_endtag(self,t):
  if t=='body':self.body=False;return
  if not self.body:return
  if t in ['td','th'] and self.cell is not None:self.row.append(''.join(self.cell).strip().replace('|','\\|').replace('\n',' '));self.cell=None;return
  if t=='tr' and self.table is not None:self.table.append(self.row);self.row=None;return
  if t=='table' and self.table is not None:
   rows=self.table;self.table=None
   if rows:self.out.append('\n\n'+'\n'.join('| '+' | '.join(r)+' |'+ ('\n| '+' | '.join(['---']*len(r))+' |' if i==0 else '') for i,r in enumerate(rows))+'\n\n')
   return
  if t in ['h1','h2','h3','h4','p','div','section','details','article']:self.emit('\n\n')
  elif t=='summary':self.emit('**\n\n')
  elif t in ['strong','b']:self.emit('**')
  elif t in ['em','i']:self.emit('*')
  elif t in ['sup','sub']:self.emit('</'+t+'>')
  elif t=='code':self.emit('`')
  elif t=='span':self.emit(' ')
  elif t=='a':self.emit(']('+self.links.pop()+')')
 def handle_data(self,s):
  if self.body:self.emit(s)
def convert(source):
 # Preserve each independently downloadable figure without leaking SVG CSS/defs into prose.
 names=['RAMANUJAN_MATCHED_VECTOR_ONSETS.svg','MERTENS_FOUR_ERROR_FRONTIERS.svg','RAMANUJAN_EARLY_FRONTIERS.svg'];svg_count=0
 def figure_link(m):
  nonlocal svg_count
  if svg_count>=len(names):raise ValueError('unexpected inline figure count')
  name=names[svg_count];svg_count+=1
  return '<p><a href="frontiers/'+name+'">Download figure '+str(svg_count)+': '+name+'</a></p>'
 source=re.sub(r'<svg\b[^>]*>.*?</svg>',figure_link,source,flags=re.S)
 if svg_count not in (0,3):raise ValueError('incomplete final figure set')
 source=re.sub(r'<style\b[^>]*>.*?</style>','',source,flags=re.S)
 formulas=[]
 def take(m):
  formulas.append(formula(ET.fromstring(m[0])));return 'STATIQMATH'+str(len(formulas)-1)+'ENDMATH'
 source=re.sub(r'<math\b[^>]*>.*?</math>',take,source,flags=re.S);p=Markdown();p.feed(source);s=''.join(p.out)
 for i,f in enumerate(formulas):s=s.replace('STATIQMATH'+str(i)+'ENDMATH',f)
 s=re.sub(r'\n{3,}','\n\n',s).strip()+'\n'
 if re.search(r'\\(?:[()[\]]|frac|sum|operatorname)|\$\$',s):raise ValueError('raw TeX in human Markdown')
 return s,len(formulas)
