"""Every plotted source identity/domain and diagnostic ordinate; not ANT PV."""
from collect import O,load,need,pin,save
from compare import original_case,canonical_intervals,best,val,eligible,case_allowed
from fractions import Fraction as Q
import csv,math,collections

def main():
    bounds=load(O/'FINITE_EXPLICIT_FUNCTIONS.json')['bounds'];universe=load(O/'ALL24_SOURCE_BOUND_OBJECTS.json');ports={p['candidate_id']:p for p in universe['portfolios']};grouped=collections.defaultdict(list);by={}
    for b in bounds:b['_case']=original_case(b);b['_intervals']=canonical_intervals(b);grouped[b['candidate_id']].append(b);by[b['bound_id']]=b
    groups=collections.defaultdict(list);rows=list(csv.DictReader((O/'PLOT_VALUES_AND_CHOSEN_SOURCE_FUNCTIONS.csv').open()));need(len(rows)==53415,'ALL53415_PLOTTED_VALUE_SOURCE_POINTS')
    selected=collections.Counter();ineligible_empty=0
    for r in rows:
        cid=r['candidate_id'];scenario=r['scenario'];target=r['target'];L=float(r['L']);need(math.isfinite(L)and L>0,'FINITE_REAL_LOG_COORDINATE');need(cid in ports and scenario in ['B0','D02']and target in ['G','ES','EP','EQ','EW'],'EXACT_PLOT_POINT_IDENTITY');need(scenario!='D02'or'D02'in ports[cid]['stage_id'],'NO_UNSTUDIED_D02_PORTFOLIO');z,chosen=best(grouped[cid],L,target,scenario)
        if chosen is None:need(r['chosen_bound_id']==''and r['plot_y']=='','NO_VALUE_WITHOUT_ELIGIBLE_SOURCE_FUNCTION');ineligible_empty+=1
        else:
            need(r['chosen_bound_id']==chosen,'EXACT_SELECTED_GLOBAL_DIAGNOSTIC_MIN_OR_MAX_ID');b=by[chosen];need(b['quantity']==target and b['candidate_id']==cid and case_allowed(b,scenario)and eligible(b,L),'ACTUAL_TARGET_PREMISE_AND_SOURCE_DOMAIN');y=z if target=='G'else math.exp(z+(2 if target=='EW'else 3)*math.log(L));need(r['plot_y']==format(y,'.14g'),'EVERY_EXPORTED_ORDINATE_REPRODUCES_FROM_SOURCE_FUNCTION');selected[chosen]+=1
        groups[(cid,scenario,target)].append(L)
    expected=set()
    for cid,p in ports.items():
        expected.add((cid,'B0','G'))
        if'D02'in p['stage_id']:expected.add((cid,'D02','G'))
        for target in ['EP','EQ','ES','EW']:expected.add((cid,'D02'if'D02'in p['stage_id']else'B0',target))
    need(set(groups)==expected and len(groups)==135,'EXACT39_G_AND96_M_CURVE_MENU_NO_QUALITY_SELECTION')
    for key,points in groups.items():
        n=481 if key[-1]=='G'else 361;lo=25 if key[-1]=='G'else 10;hi=85 if key[-1]=='G'else 300;need(len(points)==n and points[0]==lo and points[-1]==hi and all(a<b for a,b in zip(points,points[1:])),'COMPLETE_ORDERED_PLOT_GRID');need(all(abs(L-float(Q(lo)+Q(i*(hi-lo),n-1)))<=1e-12 for i,L in enumerate(points)),'FIXED_MATCHED_EQUISPACED_LOG_GRID')
    save('ACTUAL_ALL53415_PLOT_POINTS_SOURCE_DOMAIN_AND_ORDINATE_RECHECK.json',{'status':'PASS_ALL53415_POINTS_COMPLETE135_CURVES_EXACT_SELECTED_SOURCE_TARGET_PREMISE_DOMAIN_AND_DIAGNOSTIC_ORDINATE','sources':[pin(O/n)for n in ['verify_plot_source_lineage.py','compare.py','FINITE_EXPLICIT_FUNCTIONS.json','PLOT_VALUES_AND_CHOSEN_SOURCE_FUNCTIONS.csv']],'points':len(rows),'G_curves':39,'M_curves':96,'points_without_eligible_function':ineligible_empty,'selected_source_function_counts':dict(selected),'unverified_math_or_source_first_PV_promoted':False,'scope':'Ordinary deterministic diagnostic point checking. Exact accepted source formulas/domains and independent source-scope receipts supply mathematical contract; this is not a new analytic proof or exhaustive evaluation of unevaluated operators.'})
    print('PASS53415_SOURCE_POINTS_39G96M_CURVES')
if __name__=='__main__':main()
