#!/usr/bin/env python3
"""Three exact scalar population-width formulas, with their source/onset labels.

The CSV is exact rational arithmetic. The SVG/PDF are visualizations, not a new
ANT transfer or source-first PV. Existing source and figure files are untouched.
"""
import argparse
import csv
from fractions import Fraction as Q
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--render-package',type=Path)
    ap.add_argument('--out',type=Path,default=Path(__file__).resolve().parent)
    a=ap.parse_args()
    if a.render_package:sys.path.insert(0,str(a.render_package.resolve()))
    import matplotlib
    need(matplotlib.__version__=='3.10.7','Pinned Matplotlib3.10.7 required')
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.lines import Line2D
    out=a.out.resolve();out.mkdir(parents=True,exist_ok=True)
    names=['COMPETITION_FRONTIER.svg','COMPETITION_FRONTIER.pdf','COMPETITION_FRONTIER.csv','COMPETITION_FRONTIER.json']
    need(not any(os.path.lexists(out/name)for name in names),'Fresh competition output files required')
    q=Q(82325773717,98718416336);i1=Q(851127043,10**9);s1=Q(1505827,10**6);i2=Q(85124642,10**8);s2=Q(1505237,10**6)
    oi=Q(163827,160000);oslope=Q(9,8);floor=Q(103,100)
    G=lambda x:q*(1+2*x);P1=lambda x:i1+s1*x;P2=lambda x:i2+s2*x
    P=lambda x:min(P1(x),P2(x));O=lambda x:max(floor,oi+oslope*x)
    points={'G_P1':(i1-q)/(2*q-s1),'G_P2':(i2-q)/(2*q-s2),'P1_P2':(i2-i1)/(s1-s2),
        'P2_O':(oi-i2)/(s2-oslope),'P1_O':(oi-i1)/(s1-oslope),'G_O':(oi-q)/(2*q-oslope),'O_floor':(floor-oi)/oslope}
    a0,c0,b0=points['G_P1'],points['P1_P2'],points['P2_O']
    need(0<a0<c0<points['G_O']<b0<2,'Exact displayed crossing order differs')
    alpha=sorted(set([Q(k,1000)for k in range(2001)]+list(points.values())))
    with (out/names[2]).open('w',newline='')as stream:
        writer=csv.writer(stream);writer.writerow(['alpha_exact','G56_limiting_width_exact','Published2026_q1_envelope_exact','Octic_width_exact','minimum_of_these_three_exact','smallest_displayed_formulas','published_active_branch'])
        for x in alpha:
            values={'G56':G(x),'Published2026':P(x),'Octic':O(x)};best=min(values.values())
            writer.writerow([str(x),str(G(x)),str(P(x)),str(O(x)),str(best),'|'.join(name for name,v in values.items()if v==best),'P1'if P1(x)<=P2(x)else'P2'])
    plt.rcParams.update({'svg.fonttype':'path','svg.hashsalt':'IEANTN-RH080-COMPETITION-20261125','font.family':'DejaVu Sans','font.size':10})
    colors={'G56':'#215c99','Published2026':'#b4640a','Octic':'#17795b'}
    fig,axes=plt.subplots(1,2,figsize=(11.2,5.2),gridspec_kw={'width_ratios':[1.15,1]},layout=None)
    fig.subplots_adjust(left=.065,right=.985,bottom=.24,top=.80,wspace=.23)
    fig.suptitle('Population widths: competition among three stated formulas',x=.51,y=.985,fontsize=14,weight='bold')
    fig.text(.51,.925,'Thicker segments show the minimum of these three scalar formulas',ha='center',fontsize=10,color='#3c4753')
    handles=[Line2D([0],[0],color=colors['G56'],lw=2.3,label='G56: limiting curve, + ε'),
        Line2D([0],[0],color=colors['Published2026'],lw=2.3,label='2026 paper: q = 1'),
        Line2D([0],[0],color=colors['Octic'],lw=2.3,label='Preserved octic: explicit')]
    fig.legend(handles=handles,loc='upper center',bbox_to_anchor=(.51,.885),ncol=3,frameon=False,fontsize=10)
    for ax,right in zip(axes,[Q(2),Q(3,5)]):
        domain=[x for x in alpha if x<=right]
        ax.plot(list(map(float,domain)),[float(G(x))for x in domain],color=colors['G56'],lw=1.5)
        ax.plot(list(map(float,domain)),[float(P(x))for x in domain],color=colors['Published2026'],lw=1.5)
        ax.plot(list(map(float,domain)),[float(O(x))for x in domain],color=colors['Octic'],lw=1.5)
        for left,end,f,color in [(Q(0),a0,G,colors['G56']),(a0,b0,P,colors['Published2026']),(b0,right,O,colors['Octic'])]:
            chosen=[x for x in domain if left<=x<=min(end,right)]
            if chosen:ax.plot(list(map(float,chosen)),[float(f(x))for x in chosen],color=color,lw=3.8)
        for point in [a0,b0]:ax.axvline(float(point),color='#8e99a4',ls=':',lw=.9)
        ax.set_xlim(0,float(right));ax.set_ylim(.80,4.30 if right==2 else 1.9)
        ax.set_xlabel('Population target α');ax.grid(alpha=.18);ax.spines[['top','right']].set_visible(False)
    axes[0].set_ylabel('Interval coefficient in C √x log(x)')
    axes[0].set_title('Full displayed range: 0 ≤ α ≤ 2',fontsize=10)
    axes[1].set_title('Detail: early changes in the smaller formula',fontsize=10)
    axes[1].annotate('G56 = paper\nα ≈ '+format(float(a0),'.6f'),xy=(float(a0),float(G(a0))),xytext=(.03,1.43),fontsize=8.5,
        arrowprops={'arrowstyle':'-','color':'#657585'},color='#273643')
    axes[1].annotate('Paper = octic\nα ≈ '+format(float(b0),'.6f'),xy=(float(b0),float(P(b0))),xytext=(.36,1.78),fontsize=8.5,
        arrowprops={'arrowstyle':'-','color':'#657585'},color='#273643')
    axes[1].axvline(float(points['G_O']),color='#8995a2',ls='--',lw=.8)
    axes[1].annotate('G56 = octic at 0.349929;\npaper curve is smaller here',xy=(float(points['G_O']),float(G(points['G_O']))),xytext=(.17,1.02),fontsize=8,
        arrowprops={'arrowstyle':'-','color':'#8995a2'},color='#566473')
    footer=('G56: RH + general CMS source inputs; eventual, with positive ε; no explicit onset.\n'
        '2026 paper: Theorem 2 / Eq. (ap-weighted), q = 1 under RH; eventual population count.\n'
        'Octic: preserved RH/explicit-formula input package; explicit x ≥ exp(24).\n'
        'Different stated inputs/onsets: this is an exact formula comparison, not a new ANT transfer.')
    fig.text(.065,.145,footer,ha='left',va='top',fontsize=8.5,color='#3d4a57',linespacing=1.45)
    fig.savefig(out/names[0],metadata={'Date':None,'Title':'Three stated population-width formulas'})
    fig.savefig(out/names[1],metadata={'CreationDate':None,'ModDate':None,'Title':'Three stated population-width formulas'})
    plt.close(fig)
    coefficients={'G56_q':str(q),'published_P1_intercept':str(i1),'published_P1_slope':str(s1),'published_P2_intercept':str(i2),
        'published_P2_slope':str(s2),'octic_intercept':str(oi),'octic_slope':str(oslope),'octic_floor':str(floor)}
    receipt=dict(status='EXACT_FRACTION_THREE_FORMULA_COMPARISON_FIGURE_NOT_NEW_ANT_PROOF',matplotlib=matplotlib.__version__,
        controller_sha256=sha(Path(__file__)),coefficients=coefficients,domain='0<=alpha<=2',rows=len(alpha),
        crossings={name:dict(exact=str(value),approx=float(value))for name,value in points.items()},
        scalar_minimum_regions=[dict(from_inclusive='0',to_inclusive=str(a0),formula='G56'),dict(from_inclusive=str(a0),to_inclusive=str(c0),formula='PublishedP1'),dict(from_inclusive=str(c0),to_inclusive=str(b0),formula='PublishedP2'),dict(from_inclusive=str(b0),to_inclusive='2',formula='Octic')],
        source_paper=dict(primary_url='https://doi.org/10.5281/zenodo.24429650',version='2, November21,2026',
            manuscript_sha256='2f15da8545766012902e6dcc46f9bc4daa9951661dae2cc4809b97fd729dc380',
            statement='Theorem2 (thm:grh), equation ap-weighted',RH_q1='Section3 proof and moduli1,2 remark, lines738–772 of archived primary TeX',
            claim='C_Q(alpha) < min(0.851127043+1.505827alpha,0.85124642+1.505237alpha); for q=1 the same eventual count requires only RH.'),
        mathematical_scope='Only rational scalar formulas, different declared onset/input packages; no new numerical ANT assumption, source-first PV, global optimum or ANT theorem.',
        original_population_figure_changed=False,
        old_G_O_crossing_order=dict(alpha=str(points['G_O']),paper=str(P(points['G_O'])),G56=str(G(points['G_O'])),octic=str(O(points['G_O'])),paper_is_strictly_lower=P(points['G_O'])<G(points['G_O'])==O(points['G_O'])),
        files={name:dict(sha256=sha(out/name),bytes=(out/name).stat().st_size)for name in names[:3]})
    fd,tempname=tempfile.mkstemp(prefix='.competition-',dir=out);temporary=Path(tempname)
    try:
        with os.fdopen(fd,'w')as stream:json.dump(receipt,stream,indent=2);stream.write('\n');stream.flush();os.fsync(stream.fileno())
        os.link(temporary,out/names[3])
    finally:temporary.unlink()
    print(json.dumps(dict(status=receipt['status'],rows=len(alpha),G_to_P=float(a0),P_to_O=float(b0))))


if __name__=='__main__':main()
