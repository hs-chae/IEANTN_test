#!/usr/bin/env python3
"""Reuse the checked610 goal template for the separate stronger607 candidate."""
from pathlib import Path
import argparse
import json
from generate_correlated610 import generate as generate610

HERE=Path(__file__).resolve().parent


def generate():
    old=json.loads((HERE/'CORRELATED_610_SCOUT.json').read_text())
    new=json.loads((HERE/'CORRELATED_607_SCOUT.json').read_text())
    template=generate610()['Corr610Cell0.lean']
    result={}
    for i,row in enumerate(new['rows']):
        text=template.replace('import CorrelatedNumeric','import PairedRamInterface')
        for field in ['l','u','a','b']:
            text=text.replace('('+old['rows'][0][field]+':ℝ)','('+row[field]+':ℝ)')
        text=text.replace('('+old['K']+':ℝ)','('+new['K']+':ℝ)')
        text=text.replace('(1/1000:ℝ)','(1/10000:ℝ)')
        text=text.replace('610_0','607_'+str(i))
        header=f'''theorem gap607_{i} (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)'''
        if text.count(header)!=1:
            raise ValueError('Exact reused template header differs')
        text=text.replace(header,f'theorem gap607_{i}_of_pair (paired : PairTransfer)')
        text=text.replace('actual_margin hRH hGM hP hJ hTab hL hU',
                          'actual_margin_of_pair paired hTab hL hU')
        text=text.replace('certify_bound 40','certify_bound 60')
        text=text.replace(f'#print axioms gap607_{i}',f'#print axioms gap607_{i}_of_pair')
        result[f'Corr607Cell{i}.lean']=text
    return result


def main():
    p=argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--check',action='store_true')
    a=p.parse_args()
    result=generate()
    for name,text in result.items():
        path=HERE/name
        if a.check:
            if not path.exists() or path.read_text()!=text:
                raise ValueError('Generated607 goal differs:'+name)
        else:
            path.write_text(text)
    print(json.dumps({'status':'GOALS_MATCH' if a.check else 'GOALS_GENERATED',
                      'modules':len(result),'Lean_acceptance':'Separate'}))


if __name__=='__main__':
    main()
