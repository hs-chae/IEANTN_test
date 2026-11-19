from pathlib import Path
from fractions import Fraction as Q
import collections,hashlib,json,re,sys
sys.dont_write_bytecode=True
R=Path(__file__).resolve().parents[2];D=R/'coordinator-private/twentyfour-normalized-frontiers-v1';sys.path.insert(0,str(D));import premises

def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def q(x):return Q(int(x['numerator']),int(x['denominator']))
def pin(p):return {'path':str(p),'sha256':sha(p)}
def atom(t):return(q(t['coefficient']),q(t['x_decay_exponent']),t['log_denominator_degree'],t['pi_power'])
def interval(b):
 xs=b['domain']['numeric_intervals'];need(len(xs)==1,'one exact explicit finite/ray component');x=xs[0]
 def end(z):return None if z is None else(z['coordinate'],q(z['rational']))
 return end(x['lower']),end(x['upper']),x['left_closed'],x['right_closed']
def finite_L(lo,hi):return('L',Q(str(lo))),('L',Q(str(hi))),True,True

def main():
 bp=D/'FINITE_EXPLICIT_FUNCTIONS.json';tp=D/'REVIEWED_M_LITERAL_RECEIVER_INTERFACES_V1.json';op=D/'ALL24_SOURCE_BOUND_OBJECTS.json';snapshots=[pin(x)for x in [bp,tp,op]];bounds=json.loads(bp.read_text())['bounds'];table=json.loads(tp.read_text())['entries'];by={tuple(x['key']):x for x in json.loads(op.read_text())['objects']};fns=collections.defaultdict(list)
 for b in bounds:fns[tuple(b['object_key'])].append(b)
 roots=[x for x in table if any('explicit_source_root'in b for b in x['functions'])];need(len(roots)==20,'exact20 newly reviewed fixed-root source objects');rootchecks=[]
 for e in roots:
  key=tuple(e['key']);cid,ident=key;row=by[key];text=e['exact_statement'];src=e['exact_written_source'];need(sha(Path(src['file']))==src['sha256'],'root source physical bytes');need(e['exact_statement']==row['raw_M_row']['exact_statement']and e['exact_domain']==row['raw_M_row']['full_domain']and e['exact_assumptions']==row['raw_M_row']['assumptions'],'root source claim binding')
  if cid=='FOLLOWUP-C010':
   names={'M-local-75':('EQ',2278379),'M-local-76':('EP',2278379),'M-local-77':('ES',2278379),'M-local-78':('EW',912559)};target,base=names[ident];m=re.search(r't in \(([^,]+),([^\)]+)\)',text);need(m is not None,'literal increment bracket');bracket=[Q(base)+Q(m[1]),Q(base)+Q(m[2])];targets={target}
  else:
   m=re.search(r'(?:in |∈)\(([^,]+),([^\)]+)\)',text);need(m is not None,'literal exact root bracket');bracket=[Q(m[1]),Q(m[2])]
   if ident.startswith('M-new-root-'):targets={'M-new-root-16':{'EP','EQ'},'M-new-root-17':{'EP'},'M-new-root-18':{'ES'},'M-new-root-19':{'EP','EQ','ES','EW'}}[ident]
   elif ident.startswith('M-exact-onset-'):targets={{'S':'ES','W':'EW','P':'EP','Q':'EQ'}[ident[-1]]}
   else:targets={'M-root-Q-joint':{'EP','EQ'},'M-root-P':{'EP'},'M-root-u':{'ES'},'M-root-j':{'EW'}}[ident]
  actual=fns[key];need(len(actual)==len(targets)and{b['quantity']for b in actual}==targets,'root exact target set');has_global_strict=cid not in ['FOLLOWUP-C010','FOLLOWUP-C011'];newpower=ident.startswith('M-new-root-');need(bracket[0]<bracket[1],'open rational bracket ordered')
  for b in actual:
   target=b['quantity'];expectedc=Q('.25665')if newpower else Q('.3')if target=='EW'else Q('.2');expecta=Q(5,32)if newpower else Q(0);expectd=(0 if target=='EW'else 1)if newpower else(2 if target=='EW'else 3);need(q(b['coefficient'])==expectedc and q(b['x_decay_exponent'])==expecta and b['log_denominator_degree']==expectd and b['quantity']==target and b['operator']==('<='if newpower else row['raw_M_row']['strictness']),'exact fixed root function and source inequality')
   need(b['domain']['numeric_intervals']==[],'root cannot be silently replaced by a rational onset');exact=b['domain']['exact_symbolic_intervals'];need(len(exact)==1,'one exact source-root ray');z=exact[0];lower=z['lower'];need(lower['coordinate']=='x'and list(map(q,lower['certified_open_rational_bracket']))==bracket and lower['root_defined_by_source_object']==list(key)and z['upper']is None and z['left_closed']is True and z['right_closed']is False,'exact source root coordinate/bracket/reference/closedness');plots=b['domain']['plot_intervals'];need(len(plots)==1 and plots[0]['lower']['coordinate']=='x'and q(plots[0]['lower']['rational'])==bracket[1]and plots[0]['left_closed']is False and plots[0]['upper']is None,'separate conservative upper-bracket plot projection');need(b['domain'].get('unplotted_root_microband_is_not_a_claimed_failure')is True,'no claimed failure in the unplotted valid microband')
   if has_global_strict:need(b['domain']['strict_open_subray']=={'root_defined_by_source_object':list(key),'left_closed':False},'only source-explicit strict open subray')
   else:need('strict_open_subray'not in b['domain']and'global strictness not claimed'in b['strictness'],'C10/C11 conservative accepted non-strict ray, no invented global strictness')
   need(premises.branch_case(b)==('D02'if newpower else'B0'),'fixed root antecedent preserved')
  rootchecks.append({'key':list(key),'targets':sorted(targets),'source':src,'exact_open_bracket':[str(x)for x in bracket],'axis':'x, with t=log x only inside the source equation','closed_nonstrict_ray':True,'source_global_strict_open_subray':has_global_strict,'plot_projection_separate':True})
 # Compare complete literal term tuples, including exact powers of mathematical
 # pi. This is source serialization validation, not new numerical evaluation.
 sumchecks=[]
 for cid in ['FOLLOWUP-C002','FOLLOWUP-C008']:
  key=(cid,'M-W');xs=fns[key];need(len(xs)==12,'all3 W finite pieces times4 receivers')
  pieces=[(17,29,[(Q('3.25'),Q(1,2),0,0)]),(29,58,[(Q(1,8),Q(1,2),-2,-1),(Q(3),Q(1,2),0,0)]),(58,189,[(Q('1.048e-12'),Q(0),0,0),(Q(117),Q(1,2),0,0),(Q('5e-11'),Q(1,8),0,0)])]
  for lo,hi,terms in pieces:
   got=[b for b in xs if interval(b)==finite_L(lo,hi)];need(len(got)==4 and{b['quantity']for b in got}=={'ES','EP','EQ','EW'},'complete W finite source piece')
   for b in got:
    scale=Q('1.0001')if b['quantity']in ['EP','EQ']else Q(1);delta=0 if b['quantity']=='EW'else 1;expected=sorted((c*scale,a,d+delta,p)for c,a,d,p in terms);need(b['kind']=='M_positive_sum'and sorted(map(atom,b['positive_terms']))==expected and premises.branch_case(b)=='B0','exact W terms/units/1.0001 product conversion/case')
   sumchecks.append({'key':list(key),'exact_L_interval':[lo,hi],'quantity_count':4,'full_literal_positive_terms_and_pi_factor_checked':True})
 for cid in ['FOLLOWUP-C020','FOLLOWUP-C023']:
  key=(cid,'M-signed-early-weighted');xs=fns[key];need(len(xs)==1,'one weighted sum bound');b=xs[0];need(b['kind']=='M_positive_sum'and b['quantity']=='EW'and interval(b)==finite_L(18,'29.9'),'exact early weighted finite domain');expected=sorted([(Q('1.837401'),Q(1,2),0,0),(Q('2.67'),Q(2,3),0,0),(Q('3.2e-12'),Q(1,8),0,0),(Q(2),Q(1),0,0)]);need(sorted(map(atom,b['positive_terms']))==expected and premises.branch_case(b)=='B0','all4 exact EW terms, no dropping a term or changing source variable');sumchecks.append({'key':list(key),'exact_L_interval':[18,'29.9'],'all_four_source_terms_checked':True})
 key=('FOLLOWUP-C017','M-new-power-joins');xs=fns[key];need(len(xs)==12,'first .117 block and two middle branches');H=Q(3000000000000)
 for case,a,upper in [('B0',Q(1,8),185),('D02',Q(5,32),166)]:
  got=[b for b in xs if b.get('case')==case and b['kind']in ['M_positive_sum','M_exp_positive_sum']];need(len(got)==4,'all4 middle receivers per case')
  for b in got:
   delta=0 if b['quantity']=='EW'else 1;expected=sorted([(1/H,Q(0),delta,1),(Q(115),Q(1,2),delta,0),(21/H,a,delta,0),(Q(3),Q(1),delta,0)]);need(sorted(map(atom,b['positive_terms']))==expected and interval(b)==finite_L(32,upper)and premises.branch_case(b)==case,'middle exact H/pi/positive sum/closed case domain');need(b['kind']==('M_exp_positive_sum'if b['quantity']in ['EP','EQ']else'M_positive_sum'),'middle log-product converted with expm1')
  sumchecks.append({'key':list(key),'case':case,'exact_L_interval':[32,upper],'H':'3000000000000','full_middle_terms_and_relative_conversion_checked':True})
 bridge=[b for b in xs if b['kind']=='M_power_log'];need(len(bridge)==4,'all4 inverse-log bridge quantities')
 for b in bridge:need(q(b['coefficient'])==Q('.117')and q(b['x_decay_exponent'])==0 and b['log_denominator_degree']==(2 if b['quantity']=='EW'else 3)and interval(b)==finite_L(17,32)and premises.branch_case(b)=='B0','exact .117 bridge')
 key=('FOLLOWUP-C017','M-three-pieces');xs=fns[key];need(len(xs)==12,'3 component caps times4 quantities')
 expected_intervals=[(('x',Q(10**7)),('x',Q(10**13)),True,True),(('x',Q(10**13)),('x',Q(10**19)),True,True),(('x',Q(10**19)),('L',Q(190)),True,True)]
 for no,inter in enumerate(expected_intervals):
  got=[b for b in xs if interval(b)==inter];need(len(got)==4,'complete exact mixed-axis join component')
  for b in got:
   c=(Q('.165')if b['quantity']=='EW'else Q('.166'))if no==0 else Q('.002')if no==1 else Q('.00008');need(q(b['coefficient'])==c and q(b['x_decay_exponent'])==0 and b['log_denominator_degree']==(2 if b['quantity']=='EW'else 3)and premises.branch_case(b)=='B0','source-specific join constants and unsigned error units')
 key=('FOLLOWUP-C012','M-old-directional');xs=fns[key];need(len(xs)==2 and{b['quantity']for b in xs}=={'EP','EQ'},'only original two product consequences')
 for b in xs:need(b['kind']=='M_exp_log_enclosure'and q(b['coefficient'])==Q('.1973')and q(b['x_decay_exponent'])==0 and b['log_denominator_degree']==3 and interval(b)==(('x',Q(767135587)),None,True,False),'literal exp(.1973/L3)-1 product bounds on own exact domain')
 for cid in ['FOLLOWUP-C021','FOLLOWUP-C024']:
  xs=fns[(cid,'M-power-420000')];need({b['quantity']for b in xs}=={'ES','EP','EQ'}and len(xs)==3,'no unlicensed weighted420000 function')
  xs=fns[(cid,'M-power-550000')];need(len(xs)==1 and xs[0]['quantity']=='EW'and q(xs[0]['coefficient'])==Q('.01325')and q(xs[0]['x_decay_exponent'])==Q(1,8)and xs[0]['log_denominator_degree']==0,'only weighted550000 source declaration')
  if cid=='FOLLOWUP-C021':need(xs[0]['bound_id']=='FOLLOWUP-C021:M-power-550000:3','preserve the valid old weighted suffix3 identity')
 for old in snapshots:need(sha(Path(old['path']))==old['sha256'],'snapshot changed during independent source peer')
 result={'status':'PASS_FIXED_ROOT_AND_FIXED_COMPOSITE_M_SOURCE_SERIALIZATION_PEER_AFTER_EIGHT_STRICTNESS_SCOPE_CORRECTIONS','source_snapshots':snapshots,'fixed_root_source_objects':len(rootchecks),'fixed_root_error_functions':sum(len(fns[tuple(x['key'])])for x in rootchecks),'root_checks':rootchecks,'fixed_composite_checks':sumchecks,'current_eight_C010_C011_closed_rays_do_not_claim_unlicensed_global_strictness':True,'source_equation_locators':{'new_power_roots':'C024 m_d02.md LF3–8 defines observables/log x and power/log units; LF12–21 states each exact bracket and conditional closed/open ray; LF45–49 gives fixed-gap equations e^(kt)(A−t),e^(kt)t(1−t/A),e^(kt)t(V0−log t),e^(kt)(B−t), k=5/32.','old_log_roots':'C010 mertens.md LF73–96 gives actual increment brackets, squared/cubic log scaling, signed fixed-gap derivatives and source-ray join; C011 mertens.md LF110–117 gives actual brackets and explicitly non-strict later join; C021/C024 mertens-new.md LF49–57 gives equations and strict open rays.','W_finite_pieces':'C002/C008 mertens.md LF101–115; c=1.048e-12 in samecase ramanujan.md LF48 and verify.py LF51. Last W=D+(1+1/L)J2+Vb,L>=189 remains the exact fixed source-defined unevaluated operator, not a free parameter or discarded theorem.','early_weighted_sum':'C020/C023 mertens_postreview.md LF20 defines s,t,r,X and LF31 gives all4 positive terms on closed18<=L<=29.9.','middle_power_joins':'C017 own_repair.md LF257–282; spectral.md LF3 H=3000000000000 and profiles.py LF4 same; products use exp(log radius)−1.','original_product_consequences':'Dusart2018 primary PDFp20, physical textLF1722–1747; the −S allowance is already paid inside .1973; no extra tail or first-sum bound is introduced.'},'mathematical_proofs_or_original_parameters_changed':False,'source_first_PV':False,'full_analytic_Lean':False,'new_scientific_numerical_program_compiler_or_model_calls':0,'claim_limit':'This verifies source serialization and scope only. It does not claim every preserved fixed/integral operator is numerically optimized, and it does not count root functions as independent experiments.'};out=D/'FINISH_REPRO_M_ROOT_AND_COMPOSITE_SOURCE_PEER_V4.json';need(not out.exists(),'fresh independent receipt');out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'receipt':pin(out),'fixed_root_source_objects':20,'fixed_root_error_functions':result['fixed_root_error_functions'],'composite_source_checks':len(sumchecks),'source_snapshot_function_count':len(bounds)}))
if __name__=='__main__':main()
