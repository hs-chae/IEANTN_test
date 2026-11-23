#!/usr/bin/env python3
"""Complete fixed7301-row partition; each block is independently kernel proved."""
from pathlib import Path
import argparse,json
HERE=Path(__file__).resolve().parent

def generate():
    files={}
    for b in range(115):
        first=b*64;depth=6 if b<114 else 2
        name=f'OcticEndpointBlock{b:03d}'
        text='''import OcticCellData
namespace RHOcticPush.Moments.Endpoint
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
'''+f'lemma checked{b:03d} : tree allRow {first} {depth}=true := by decide +kernel\n'
        if b==114:text+='lemma checked_last : allRow 7300=true := by decide +kernel\n#print axioms checked_last\n'
        text+=f'#print axioms checked{b:03d}\nend RHOcticPush.Moments.Endpoint\n'
        files[name+'.lean']=text
    return files

def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--check',action='store_true');a=p.parse_args()
    for n,t in generate().items():
        f=HERE/n
        if a.check:
            if f.read_text()!=t:raise ValueError('Block source differs:'+n)
        else:f.write_text(t)
    print(json.dumps(dict(status='BLOCKS_MATCH' if a.check else 'BLOCKS_GENERATED',blocks=115,rows=7301,classification='ordinary kernel certificates, NOT source-first PV')))
if __name__=='__main__':main()
