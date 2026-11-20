#!/usr/bin/env python3
"""Preserve exact records/data while splitting only kernel-check declarations."""
from pathlib import Path
import argparse,hashlib,json,math,shutil,time
S=Path(__file__).resolve().parents[1]
def need(v,m):
    if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--manifest',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--subchunk',type=int,default=4096);p.add_argument('--preserve-chunk',type=int,action='append',default=[]);a=p.parse_args()
    d=json.loads(a.manifest.read_text());need(d['status']=='UNTRUSTED_PROPOSAL_REQUIRES_ALL_KERNEL_CHECKS','input proposal');need(0<a.subchunk<=d['proof_chunk'],'smaller positive proof declaration')
    out=a.out.resolve();own=Path('/data/ivy-ramanujan-source-pv-20261119');need(out.is_relative_to(own)and not out.exists(),'fresh owned output');out.mkdir(parents=True);start=time.monotonic();root=out/'source';root.mkdir();namespace=d['namespace'];updated=[]
    for m in d['modules']:
        original=Path(m['source']);need(sha(original)==m['sha256'],'unchanged original source');target=root/original.relative_to(Path(d['source_root']));target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(original,target)
        if m['kind']=='check'and not m['module'].endswith('.GapCheck'):
            part=int(m['module'].rsplit('Check',1)[1]);lo=part*d['proof_chunk'];size=min(d['proof_chunk'],d['records']-lo)
            if part not in a.preserve_chunk:
                text=original.read_text();header=text[:text.index('namespace ')];header+='import RamanujanPV.QuotientPartition\nnamespace '+namespace+'\nopen QuotientDemandCheck\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\nset_option Elab.async false\n'
                terms=[]
                for k,offset in enumerate(range(0,size,a.subchunk)):
                    n=min(a.subchunk,size-offset);name='piece_'+format(part,'04d')+'_'+str(k);terms.append((name,offset,n));header+='theorem '+name+' : allFrom (checkEntry nodes gaps gapCount) '+str(lo+offset)+' '+str(n)+'=true := by decide +kernel\n'
                previous=terms[0][0];length=terms[0][2]
                for k,(name,offset,n)in enumerate(terms[1:],1):
                    result='range_'+format(part,'04d')+'_'+str(k)
                    header+='theorem '+result+' : allFrom (checkEntry nodes gaps gapCount) '+str(lo)+' '+str(length+n)+'=true := QuotientPartition.append_checked (i:='+str(lo)+') (n:='+str(length)+') (m:='+str(n)+') '+previous+' '+name+'\n';previous=result;length+=n
                header+='theorem part_'+format(part,'04d')+' : allFrom (checkEntry nodes gaps gapCount) '+str(lo)+' '+str(size)+'=true := '+previous+'\n#print axioms part_'+format(part,'04d')+'\nend '+namespace+'\n';target.write_text(header)
        copy=dict(m,source=str(target),source_root=str(root),sha256=sha(target),bytes=target.stat().st_size)
        if m['kind']=='check'and not m['module'].endswith('.GapCheck')and int(m['module'].rsplit('Check',1)[1])not in a.preserve_chunk:copy['dependencies']=m['dependencies']+['RamanujanPV.QuotientPartition']
        updated.append(copy)
    result=dict(d,source_root=str(root),modules=updated,proof_subchunk=a.subchunk,preserved_original_chunks=a.preserve_chunk,original_proposal=str(a.manifest.resolve()),original_proposal_sha256=sha(a.manifest),partitioner_sha256=sha(__file__),partition_seconds=time.monotonic()-start,qualification=d['qualification']+' Only proof declaration partitioning changes; packed data, all arithmetic records, proposed values, outer proof ranges and final mathematical theorem are identical.')
    tmp=out/'PROPOSAL.json.pending';tmp.write_text(json.dumps(result,indent=2)+'\n');tmp.replace(out/'PROPOSAL.json');print(json.dumps(dict(status=result['status'],out=str(out),partition_seconds=result['partition_seconds'],packed_sha256=result['packed_sha256'])))
if __name__=='__main__':main()
