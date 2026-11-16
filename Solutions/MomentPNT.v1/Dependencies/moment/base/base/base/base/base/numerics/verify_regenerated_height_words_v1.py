"""Check regenerated C bytes against the exact proposal words in Lean sources.
This is numerical-data reproducibility, not source-first PV or a math proof.
"""
from pathlib import Path
import argparse,hashlib,json,re,sys

def need(ok,message):
 if not ok:raise ValueError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ints(path,name):
 s=path.read_text();m=re.search(r'\bdef\s+'+re.escape(name)+r'\s*:\s*List\s+Int\s*:=\s*\[(.*?)\]',s,re.S);need(m,'missing exact Int list '+name);parts=[p.strip()for p in m[1].split(',')if p.strip()];need(all(re.fullmatch(r'-?\d+',p)for p in parts),'nonliteral list '+name);return list(map(int,parts))
def boxes(path,name):
 s=path.read_text();m=re.search(r'\bdef\s+'+re.escape(name)+r'\s*:\s*List\s+ProofBox\s*:=\s*\[(.*?)\]',s,re.S);need(m,'missing exact box list '+name);pairs=re.findall(r'⟨\s*(-?\d+)\s*,\s*(-?\d+)\s*⟩',m[1]);rest=re.sub(r'⟨\s*-?\d+\s*,\s*-?\d+\s*⟩','',m[1]);need(not rest.replace(',','').strip(),'nonliteral box list');return[(int(a),int(b))for a,b in pairs]
def box(path,name):
 m=re.search(r'\bdef\s+'+re.escape(name)+r'\s*:\s*ProofBox\s*:=\s*⟨\s*(-?\d+)\s*,\s*(-?\d+)\s*⟩',path.read_text());need(m,'missing exact box '+name);return[int(m[1]),int(m[2])]
def words(path):
 data=path.read_bytes();need(len(data)%64==0,'512-bit stream width');return[int.from_bytes(data[i:i+64],'little')for i in range(0,len(data),64)]
def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=Path,required=True);p.add_argument('--raw-root',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();need(not a.out.exists(),'fresh output receipt');s=a.source_root/'SynergyAnalytic';r=a.raw_root
 paths=[s/'HeightPointChecks.lean',s/'HeightPointConstants.lean',s/'HeightPointGrid.lean',s/'HeightPointLogGridDefs.lean',s/'HeightBudgetBlocks.lean'];pins={str(f):sha(f)for f in paths};c=ints(paths[0],'cWords');D=ints(paths[0],'DWords');b=ints(paths[4],'blockWords');need(len(c)==768 and len(D)==768 and len(b)==24,'full768/24 coverage required')
 cw=words(r/'height-point-768-full-v1/output.bin');need(len(cw)==1538,'point stream exact1538words');need(all(cw[2*i]==c[i]+21600*(1<<128)and cw[2*i+1]==D[i]for i in range(768)),'point proposal mismatch')
 cv=boxes(paths[1],'constantValues');v=words(r/'height-point-constants-v1/output.bin');need(len(cv)==58 and v==[x for pair in cv for x in pair],'all58constants mismatch')
 hv=words(r/'height-point-h-v1/output.bin');qv=words(r/'height-point-q-v1/output.bin');need(len(hv)==118 and hv[:116]==v and hv[-2:]==box(paths[2],'hValue'),'logH stream/prefix mismatch');need(len(qv)==118 and qv[:116]==v and qv[-2:]==box(paths[3],'survivalEnd'),'survival endpoint stream/prefix mismatch')
 bv=words(r/'height-point-polybudget-v1/output.bin');need(len(bv)==50 and[bv[2*i+1]for i in range(24)]==b,'all24budgetword mismatch');need(sum(bv[2*i]for i in range(24))==bv[-2]and sum(bv[2*i+1]for i in range(24))==bv[-1],'C aggregate block consistency')
 need(all(sha(Path(f))==h for f,h in pins.items()),'source changed during validation');receipt={'status':'ALL_REGENERATED_WORDS_MATCH_KERNEL_PROPOSALS','python_optimization':sys.flags.optimize,'source_files':pins,'point_cells':768,'constant_boxes':58,'budget_blocks':24,'h_and_q_boxes':2,'source_first_PV':False,'qualification':'Exact source/data association only. Real semantics and selected theorem validity are established by the separate fresh Lean build; actual C source execution correctness remains a separate PV obligation.'};a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(receipt,indent=2)+'\n');print(receipt['status'])
if __name__=='__main__':main()
