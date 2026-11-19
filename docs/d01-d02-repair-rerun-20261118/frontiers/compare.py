"""Matched mathematical functions, exact vector implications, diagnostic plots.

No sieve, ANT source program, model, compiler or analytic verifier is executed.
The plotted envelope is explicitly the expanded scalar/vector subfrontier; the
complete source-defined integral/parametric operator frontier is retained too.
"""
from collect import *
from fractions import Fraction as Q
import csv,functools,math,os,re,sys
def q(x):return Q(int(x['numerator']),int(x['denominator']))
def original_case(b):
    from premises import branch_case
    return branch_case(b)
def coord(z):
    if z is None:return None
    if 'log_of_rational'in z:return math.log(q(z['log_of_rational']))
    v=q(z['rational']);return math.log(v)if z['coordinate']=='x'else float(v)
def canonical_intervals(b):
    return [{'lower_L_diagnostic':coord(i['lower']),'upper_L_diagnostic':coord(i['upper']),
             'exact_original':i}for i in b['domain'].get('plot_intervals',b['domain']['numeric_intervals'])]
def eligible(b,L):
    if 'integer'in str(b['domain']['integer_or_real']).lower()and'real'not in str(b['domain']['integer_or_real']).lower():return False
    for i in b['_intervals']:
        lo,hi=i['lower_L_diagnostic'],i['upper_L_diagnostic'];e=i['exact_original']
        # Avoid numerical evaluation on an x-to-log boundary; exact endpoints
        # and strictness stay in the data. This shrinks the plot domain only.
        eps=1e-10 if e['lower']['coordinate']=='x'or'log_of_rational'in e['lower']else 0
        if L<lo+eps or(L==lo and not e['left_closed']):continue
        if hi is not None and(L>hi-eps or(L==hi and not e['right_closed'])):continue
        return True
    return False
@functools.lru_cache(None)
def vector_logs(serial):
    return [(i,math.copysign(1,x),math.log(abs(x.numerator))-math.log(x.denominator))for i,x in enumerate(serial)if x]
def val(b,L):
    if b['kind']in ['M_positive_sum','M_exp_positive_sum']:
        logs=[math.log(q(t['coefficient']))+t['pi_power']*math.log(math.pi)-float(q(t['x_decay_exponent']))*L-t['log_denominator_degree']*math.log(L)for t in b['positive_terms']];top=max(logs);z=top+math.log(math.fsum(math.exp(v-top)for v in logs))
        if b['kind']=='M_positive_sum':return z
        radius=math.exp(z);return math.log(math.expm1(radius))if 1e-280<radius<700 else z if radius<=1e-280 else math.inf
    if b['kind']=='R_inverse_log_polynomial':
        return math.fsum(sign*math.exp(z-i*math.log(L))for i,sign,z in vector_logs(tuple(q(v)for v in b['coefficients'])))
    a=float(q(b['x_decay_exponent']));c=q(b['coefficient']);d=b['log_denominator_degree']
    z=math.log(c.numerator)-math.log(c.denominator)+float(q(b['coefficient_log_shift']))if c and 'coefficient_log_shift'in b else math.log(c.numerator)-math.log(c.denominator)if c else -math.inf
    z=z-a*L-d*math.log(L)
    if b['kind']=='M_exp_log_enclosure':
        # exp(radius)-1 is the actual relative conversion; its logarithm is
        # stable without replacing it by the radius.
        radius=math.exp(z)
        return (math.log(math.expm1(radius))if radius<700 and radius>1e-280 else(z if radius<=1e-280 else math.inf))
    return z
def coefficientwise(b,target):
    v=[q(x)for x in b['coefficients']];n=max(len(v),len(target))
    return all((v[i]if i<len(v)else 0)>=(target[i]if i<len(target)else 0)for i in range(n))
def case_allowed(b,scenario):return b['_case']=='B0'or(scenario=='D02'and b['_case']=='D02')
def best(bs,L,target,scenario):
    out=[]
    for b in bs:
        if b['quantity']!=target or not case_allowed(b,scenario)or not eligible(b,L):continue
        z=val(b,L)
        if math.isfinite(z):out.append((z,b['bound_id']))
    return (max(out)if target=='G'else min(out))if out else(None,None)
def compact(b):
    return {k:v for k,v in b.items()if not k.startswith('_')}
def main():
    universe=load(O/'ALL24_SOURCE_BOUND_OBJECTS.json');nd=load(O/'NORMALIZED_OBJECTS.json');bs=load(O/'FINITE_EXPLICIT_FUNCTIONS.json')['bounds']
    raw={tuple(r['key']):r for r in universe['objects']};port={p['candidate_id']:p for p in universe['portfolios']}
    for b in bs:
        b['_case']=original_case(b);b['_intervals']=canonical_intervals(b)
    grouped={cid:[b for b in bs if b['candidate_id']==cid]for cid in port}
    # Benchmarks are chosen independently of outcomes: exact full canonical
    # factorial prefix degrees. They do not select the source-claim universe.
    from normalize import coefficients
    degrees=[0,1,2,3,4,6,10,16,40,80,124,188];rtable=[]
    for cid,p in port.items():
      for scenario in ['B0','D02']if'D02'in p['stage_id']else['B0']:
       for degree in degrees:
        target=coefficients(degree);rays=[];windows=[]
        for b in grouped[cid]:
         if b['kind']!='R_inverse_log_polynomial'or not case_allowed(b,scenario)or not coefficientwise(b,target):continue
         for dom in b['_intervals']:
          x={'bound_id':b['bound_id'],'lower_L_diagnostic':dom['lower_L_diagnostic'],'upper_L_diagnostic':dom['upper_L_diagnostic'],
             'original_domain':dom['exact_original'],'source':b['source'],'strictness':b['strictness'],'coefficient_vector':[str(q(v))for v in b['coefficients']],
             'implication':'Exact coefficientwise nonnegative difference for all positive L; profile source domain and strictness preserved.'}
          (rays if dom['upper_L_diagnostic']is None else windows).append(x)
        # Closed parametric rules are used algebraically, not left out of the
        # same-target table merely because they are not scalar source rows.
        for obj in nd['objects']:
          if obj['candidate_id']!=cid:continue
          src=raw[tuple(obj['key'])];st=src['raw_M_row']['exact_statement'];ds=src['raw_M_row']['full_domain']
          probe={'scope':obj['scope'],'assumptions':obj['assumptions_exact'],'object_key':obj['key']}
          ca=original_case(probe)
          if ca!='B0'and not(scenario=='D02'and ca=='D02'):continue
          onset=None;rule=None
          if cid=='FOLLOWUP-C014'and obj['claim_id'].startswith('R2-growing-'):
            m=re.search(r'm=floor\(L/(\d+)\), m0=(\d+)',st)
            if m:
              c,m0=map(int,m.groups());onset=Q(c*max(m0,degree+1));rule='Source P_m has degree m-1 and positive coefficients. L>=c*max(m0,d+1) gives floor(L/c)>=d+1, preserving every order transition.'
          if cid=='FOLLOWUP-C013'and obj['claim_id'].startswith('R-all-linear-'):
            m=re.search(r'j>=([0-9]+).*?t>=([0-9]+)\(j\+5\)',ds)
            if m:
              j=max(int(m[1]),degree);onset=Q(int(m[2])*(j+5));rule='Use the already proved all-j family at j=max(j0,d); positive extra coefficients and the positive premium imply the identical full degree-d prefix.'
          exact_onset=None
          if cid=='FOLLOWUP-C022'and obj['claim_id']=='D02.R.uniform32':
            n=max(6,degree+5);onset=Q(32*n);rule='Source sum j=4..n-1 has canonical degree n-5. Set n=max(6,d+5); all omitted higher coefficients are positive.'
          if cid=='FOLLOWUP-C022'and obj['claim_id']=='D02.R.uniformc':
            n=max(20,degree+5);constant=Q('27.6443')*n-2
            onset=float(constant)-4*math.log(n)
            exact_onset={'coordinate':'L','affine_log_rational':{'constant':{'numerator':str(constant.numerator),'denominator':str(constant.denominator)},'log_coefficient':'-4','log_argument':str(n)},'exact_original':'27.6443*n-4*log(n)-2 at n='+str(n)}
            rule='Source full prefix through kernel n-1 has degree n-5; n=max(20,d+5), with exact source affine-log onset (the float is diagnostic only).'
          if cid=='FOLLOWUP-C023'and obj['claim_id'].startswith('R02-variable-'):
            mm=re.search(r'L≥([0-9.]+), every integer 40≤n≤L/([0-9.]+)',ds)
            need(mm is not None,'complete C023 variable-family source parameters')
            n=max(40,degree+5);onset=max(Q(mm[1]),Q(mm[2])*n)
            rule='Choose n=max(40,d+5). The full preceding prefix has degree n-5 and the half-C_n term at degree n-4 is nonnegative; retain both the family start and n<=L/c.'
          if onset is not None:
            if exact_onset is None:exact_onset={'coordinate':'L','rational':{'numerator':str(onset.numerator),'denominator':str(onset.denominator)}}
            rays.append({'bound_id':cid+':'+obj['claim_id']+':PARAMETRIC_PREFIX_'+str(degree),'source_object_key':obj['key'],
                'lower_L_diagnostic':float(onset),'upper_L_diagnostic':None,'original_domain':{'lower':exact_onset,'upper':None,'left_closed':True,'right_closed':False},
                'source':src['source'],'strictness':src['raw_M_row']['strictness'],'coefficient_vector':[str(v)for v in target],'implication':rule,'source_family_remains_retained_in_full':True})
        earliest=min(rays,key=lambda x:x['lower_L_diagnostic'])if rays else None
        rtable.append({'candidate_id':cid,'stage_id':p['stage_id'],'scenario':scenario,'benchmark_degree':degree,
            'target_coefficients':[str(v)for v in target],'earliest_recorded_ray_with_this_coefficientwise_implication':earliest,
            'all_supporting_whole_ray_functions':rays,'all_eligible_finite_windows_kept_separately':windows,
            'not_globally_least_onset_or_full_operator_optimization':True})
    save('MATCHED_R_COEFFICIENT_VECTOR_TABLE.json',{'benchmark_criterion':'All full factorial prefix degrees in explicit fixed menu 0,1,2,3,4,6,10,16,40,80,124,188; coordinator descriptive benchmark, not an audit or theorem selection.',
        'exact_implication_test':'Coefficientwise positivity over L>0 only; all other polynomials and operators remain retained. Earliest recorded qualifying ray is not a universal onset optimum.', 'rows':rtable})
    # Every source-defined mathematical object remains in the whole envelope.
    whole=[]
    for cid,p in port.items():
        own=[x for x in nd['objects']if x['candidate_id']==cid]
        whole.append({'candidate_id':cid,'stage_id':p['stage_id'],'all_active_object_keys':[r['key']for r in own],
            'whole_R_rule':'At each real x take the supremum of all applicable accepted lower profiles, sign/root/local formulas and instantiated parameter-family/operator outputs; no source/argument/parameter domain is enlarged.',
            'whole_M_rule':'Intersect all applicable signed intervals first; map [l,u] to ES/EW maxima and to separate EP=max(|exp(-l)-1|,|exp(-u)-1|), EQ=max(|exp(l)-1|,|exp(u)-1|); then minimize with every eligible direct relative/power/log/finite bound. Arbitrary admissible heights and kernels stay quantified, not sampled replacements.',
            'operator_and_parameter_objects':[r for r in own if r['object_role']in ['SIGNED_OR_POINTWISE_OPERATOR','PARAMETRIC_OR_OPERATOR_FAMILY','FINITE_ONSET_SIGN_OR_ROOT_FUNCTION']],
            'partly_expanded_source_objects_with_remaining_explicit_receiving_operators':[r for r in own if r['symbolic_definition'].get('additional_source_defined_receiving_operators')],
            'all_nonfinite_expression_objects_including_grouped_providers_limits_and_diagnostics':[r for r in own if not r['finite_bound_ids']],
            'numeric_evaluation_of_entire_quantified_operator_frontier_claimed':False,
            'data_lineage':{'Root_finalization':p['Root_finalization'],'floor':p['Root_floor'],'complete_source':p['complete_source'],'fresh_review':p['complete_fresh_M']}})
    save('WHOLE_SYMBOLIC_OPERATOR_FRONTIERS.json',{'portfolios':whole,'scope':'All11411 admitted scoped objects; proof providers/diagnostics/conditionals are typed separately, not each counted as quantitative target theorems.'})
    # Same-onset diagnostic values carry the actually chosen function ID.
    points=[]
    for cid,p in port.items():
      for scenario in ['B0','D02']if'D02'in p['stage_id']else['B0']:
       for L in [30,40,50,60,100,170,200,300,500,1000,4000]:
        for target in ['G','ES','EW','EP','EQ']:
         z,k=best(grouped[cid],L,target,scenario)
         points.append({'candidate_id':cid,'stage_id':p['stage_id'],'scenario':scenario,'L':L,'target':target,'diagnostic_value_or_log_value':z,'value_coordinate':'ordinary G'if target=='G'else'natural log of error bound','chosen_bound_id':k})
    save('SAME_ONSET_DIAGNOSTIC_FUNCTION_VALUES.json',{'not_new_theorems_or_numerical_certificates':True,'rows':points})
    eligibility={'all11411_source_object_keys_preserved':len(nd['objects'])==11411,'expanded_function_count':len(bs),'function_case_counts':dict(collections.Counter(b['_case']for b in bs)),
        'exact_root_domains':'Root-defined rays keep their exact source boundary and rational bracket. Diagnostic curves use only the separately declared conservative upper-bracket projection; the exact function is never redefined by that projection.','plotting_inclusion':'Every expanded positive scalar/vector function with explicit numeric intervals, real domain, resolved B0/D02 case and one of G/ES/EW/EP/EQ. No quality filter. Exact predicate remains the authority; plots shrink x-coordinate boundaries by1e-10 in L.',
        'plotting_exclusion':'Source identities and proof providers without a receiving clause, diagnostics, true refutations, hypothetical/full-RH branches, unresolved quantified case parameters, exact-root microbands outside the conservative projection, auxiliary log-Q observations and unevaluated integral/parameter operators. Provisional source-role labels never exclude a concrete receiving clause. All remain present with their exact source expressions in the whole registry.',
        'all_not_numerically_plotted_explicit_functions':[compact(b)for b in bs if not b['_intervals']or b['_case']not in ['B0','D02']or b['quantity']not in ['G','ES','EW','EP','EQ']],
        'whole_symbolic_object_role_counts':nd['object_role_counts'],'no_inference_of_independent_experiments_from_object_or_function_counts':True}
    save('PLOT_DOMAIN_CASE_AND_REPRESENTATION_COVERAGE.json',eligibility)
    # Exact illustrative crossing: both functions occur in the preserved source
    # comparison, and subtraction gives (100-L)/L² without numerical roots.
    crossings={'R_example':{'left_coefficients':['1','13','100'],'right_coefficients':['1','14'],'difference':'(100-L)/L^2','crossing_L_exact':'100',
        'positive_difference':'0<L<100','zero_difference':'L=100','negative_difference':'L>100',
        'source_objects':[r for r in nd['objects']if r['claim_id']=='R-comparisons'and r['candidate_id']in ['FOLLOWUP-C006','FOLLOWUP-C015']]},
       'M_generic':{'bound':'c exp(-alpha L)/L^d','comparison_ratio':'(c1/c2) exp(-(alpha1-alpha2)L) L^(d2-d1)',
        'log_ratio_derivative':'-(alpha1-alpha2)+(d2-d1)/L','consequence':'On any common eligible interval this derivative gives monotonicity, with at most one turn and at most one crossing on each monotone side. A late power branch does not dominate before its source onset.',
        'published_same_method_crossing_examples':[r for r in nd['objects']if r['candidate_id']=='FOLLOWUP-C002'and r['claim_id']in ['M-new-cross-first3','M-new-cross-weighted']]},
       'comparison_scope':'Exact algebra/source claims only; no new optimization, causal exposure ranking or arithmetic lower-error bound.'}
    save('EXACT_COMPARISON_ALGEBRA_AND_SOURCE_EXAMPLES.json',crossings)
    # Scientific plotting dependencies are kept outside every trusted runtime.
    sys.path.insert(0,os.environ.get('IEANTN_PLOT_DEPENDENCIES',str(O/'plot-dependencies')));os.environ['MPLCONFIGDIR']=str(O/'plot-cache')
    if "--data-only" in sys.argv:
        print("PASS_COMPARISON_DATA_ONLY_NO_PLOT_DEPENDENCIES");return
    import numpy as np,matplotlib
    matplotlib.use('Agg');import matplotlib.pyplot as plt
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.titlesize':11,'axes.labelsize':10,'legend.fontsize':8,'svg.fonttype':'path','svg.hashsalt':'IEANTN_24_FUNCTION_FRONTIER_V1','figure.dpi':150,'axes.spines.top':False,'axes.spines.right':False})
    styles={cid:dict(color=plt.get_cmap('turbo')(i/23),linestyle='--'if'LEGACY'in p['stage_id']else(':'if'CONTROL'in p['stage_id']else'-'))for i,(cid,p)in enumerate(port.items())}
    labels={cid:cid[-4:]+' '+p['stage_id'].replace('FRESH-','').replace('CONTROL-','ctrl ').replace('LEGACY-','legacy ')for cid,p in port.items()}
    lineage=[]
    def curve(cid,scenario,target,grid):
        ys=[]
        for L in grid:
            z,k=best(grouped[cid],float(L),target,scenario)
            y=(z if target=='G'else(math.exp(z+(2 if target=='EW'else 3)*math.log(L))if z is not None and z+(2 if target=='EW'else 3)*math.log(L)<700 else None))if z is not None else None
            ys.append(np.nan if y is None else y);lineage.append({'candidate_id':cid,'scenario':scenario,'target':target,'L':repr(float(L)),'plot_y':None if y is None else format(y,'.14g'),'chosen_bound_id':k})
        return np.array(ys)
    grid=np.linspace(25,85,481);fig,axes=plt.subplots(1,2,figsize=(16,7),sharey=True)
    for ax,scenario in zip(axes,['B0','D02']):
        curves=[]
        for cid,p in port.items():
            if scenario=='D02'and'D02'not in p['stage_id']:continue
            y=curve(cid,scenario,'G',grid);curves.append(y);ax.plot(grid,y,label=labels[cid],linewidth=1.2,alpha=.9,**styles[cid])
        if curves:
            a=np.array(curves);good=np.any(np.isfinite(a),axis=0);top=np.full(len(grid),np.nan);top[good]=np.nanmax(a[:,good],axis=0);ax.plot(grid,top,color='black',linewidth=2.1,label='recorded vector subfrontier')
        ax.set(xlabel=r'$L=\log x$',title='Original premises B0'if scenario=='B0'else'B0 plus direct D02 where actually studied',ylim=(0,2.1),xlim=(25,85));ax.grid(alpha=.2)
    axes[0].set_ylabel(r'Certified lower-function value for $G(L)=L^6R(e^L)e^{-2L}$')
    handles,labels0=axes[0].get_legend_handles_labels();fig.legend(handles,labels0,loc='lower center',ncol=4,bbox_to_anchor=(.5,-.04));fig.subplots_adjust(bottom=.34,wspace=.08)
    fig.suptitle('Ramanujan: real-domain scalar/vector subfrontiers; finite windows remain finite',y=.99);fig.savefig(O/'RAMANUJAN_EARLY_FRONTIERS.svg',bbox_inches='tight',metadata={'Date':None});plt.close(fig)
    grid=np.linspace(10,300,361);fig,axes=plt.subplots(2,2,figsize=(16,10),sharex=True)
    for ax,target in zip(axes.flat,['EP','EQ','ES','EW']):
        curves=[]
        for cid,p in port.items():
            scenario='D02'if'D02'in p['stage_id']else'B0';y=curve(cid,scenario,target,grid);curves.append(y);ax.semilogy(grid,y,label=labels[cid],linewidth=1.0,**styles[cid])
        a=np.array(curves);good=np.any(np.isfinite(a),axis=0);low=np.full(len(grid),np.nan);low[good]=np.nanmin(a[:,good],axis=0);ax.semilogy(grid,low,color='black',linewidth=2.2,label='recorded scalar subfrontier')
        bench=.3 if target=='EW'else .2;ax.axhline(bench,color='#777777',linewidth=.9,linestyle='-.')
        ax.set(title={'ES':'Centered reciprocal-prime sum','EW':'Centered logarithmic prime sum','EP':'Relative ordinary product','EQ':'Relative reciprocal product'}[target],ylabel=(r'$L^2$ times absolute error bound'if target=='EW'else r'$L^3$ times absolute error bound'),ylim=(1e-22,10));ax.grid(alpha=.2)
    for ax in axes[-1]:ax.set_xlabel(r'$L=\log x$')
    handles,lab=axes[0,0].get_legend_handles_labels();fig.legend(handles,lab,loc='lower center',ncol=4,bbox_to_anchor=(.5,-.01));fig.subplots_adjust(bottom=.29,hspace=.26)
    fig.suptitle('Four Mertens observables: resolved actual-stage premises, source domains and log factors',y=.99);fig.savefig(O/'MERTENS_FOUR_ERROR_FRONTIERS.svg',bbox_inches='tight',metadata={'Date':None});fig.savefig(O/'MERTENS_FOUR_ERROR_PREVIEW.png',bbox_inches='tight',dpi=120);plt.close(fig)
    # Matched full-vector onset plot: actual labels are canonical degrees.
    fig,ax=plt.subplots(figsize=(12,8))
    for cid,p in port.items():
        scenario='D02'if'D02'in p['stage_id']else'B0';rr=[r for r in rtable if r['candidate_id']==cid and r['scenario']==scenario and r['earliest_recorded_ray_with_this_coefficientwise_implication']]
        if rr:ax.plot([r['benchmark_degree']for r in rr],[r['earliest_recorded_ray_with_this_coefficientwise_implication']['lower_L_diagnostic']for r in rr],marker='.',label=labels[cid],linewidth=1.1,**styles[cid])
    ax.set(xlabel='Canonical highest inverse-log degree d (not source order label)',ylabel=r'Recorded sufficient whole-ray onset in $L=\log x$',yscale='log',xlim=(-1,190),title='Identical full factorial coefficient vectors: sufficient recorded onsets')
    ax.grid(alpha=.2);ax.legend(ncol=3,loc='upper left',bbox_to_anchor=(0,-.15));fig.subplots_adjust(bottom=.3);fig.savefig(O/'RAMANUJAN_MATCHED_VECTOR_ONSETS.svg',bbox_inches='tight',metadata={'Date':None});plt.close(fig)
    with (O/'PLOT_VALUES_AND_CHOSEN_SOURCE_FUNCTIONS.csv').open('w')as f:
        w=csv.DictWriter(f,fieldnames=['candidate_id','scenario','target','L','plot_y','chosen_bound_id']);w.writeheader();w.writerows(lineage)
    save('ACTUAL_PLOT_RECEIPT.json',{'status':'COMPLETE_DIAGNOSTIC_PLOT_GENERATION_NOT_NEW_MATHEMATICAL_VERIFICATION','python':sys.version,'executable':sys.executable,'matplotlib':matplotlib.__version__,'numpy':np.__version__,
        'sources':[pin(O/f)for f in ['compare.py','collect.py','normalize.py','ALL24_SOURCE_BOUND_OBJECTS.json','NORMALIZED_OBJECTS.json','FINITE_EXPLICIT_FUNCTIONS.json','plot-requirements.lock']],
        'outputs':[pin(O/f)for f in ['RAMANUJAN_EARLY_FRONTIERS.svg','MERTENS_FOUR_ERROR_FRONTIERS.svg','RAMANUJAN_MATCHED_VECTOR_ONSETS.svg','PLOT_VALUES_AND_CHOSEN_SOURCE_FUNCTIONS.csv']],
        'numeric_values_are_diagnostics_only':True,'entire_operator_frontier_numerically_evaluated':False,'source_premise_or_safety_boundary_changes':False})
    print(json.dumps({'status':'GENERATED_MATCHED_FUNCTION_COMPARISONS_AND_THREE_SVGS','all_source_objects':len(nd['objects']),'expanded_functions':len(bs),'lineage_points':len(lineage),'benchmarks':len(rtable)}))
if __name__=='__main__':main()
