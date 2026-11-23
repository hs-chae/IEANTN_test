#!/usr/bin/env python3
"""Reuse the checked607 paired gap template for stronger fixed margins."""
from pathlib import Path
import argparse
import json
from generate607 import generate as generate607
HERE=Path(__file__).resolve().parent

def generate():
    old=json.loads((HERE/'CORRELATED_607_SCOUT.json').read_text())
    new=json.loads((HERE/'CORRELATED_STRONG_SCOUT.json').read_text())
    template=generate607()['Corr607Cell0.lean']
    result={}
    for group in new['groups']:
        for i,row in enumerate(group['rows']):
            text=template
            for field in ['l','u','a','b']:
                text=text.replace('('+old['rows'][0][field]+':ℝ)','('+row[field]+':ℝ)')
            text=text.replace('('+old['K']+':ℝ)','('+new['K']+':ℝ)')
            text=text.replace('(1/10000:ℝ)','('+group['target']+':ℝ)')
            text=text.replace('607_0','Strong'+group['name']+'_'+str(i))
            result['CorrStrong'+group['name']+str(i)+'.lean']=text
    return result

def main():
    p=argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--check',action='store_true')
    a=p.parse_args();files=generate()
    for name,text in files.items():
        path=HERE/name
        if a.check:
            if path.read_text()!=text:raise ValueError('Generated goal mismatch:'+name)
        else:path.write_text(text)
    print(json.dumps(dict(status='GOALS_MATCH' if a.check else 'GOALS_GENERATED',modules=len(files))))
if __name__=='__main__':main()
