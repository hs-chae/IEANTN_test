from pathlib import Path
from fractions import Fraction as Q
import argparse,collections,hashlib,json,math,os,re,sys,tempfile
sys.dont_write_bytecode=True
R=Path(__file__).resolve().parents[2];D=R/'coordinator-private/twentyfour-normalized-frontiers-v1';sys.path.insert(0,str(D));import premises

def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p):return {'path':str(p),'sha256':sha(p)}
def load(p):
 def pairs(rows):
  d={}
  for k,v in rows:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 def finite(v):
  n=float(v);need(math.isfinite(n),'JSON overflow');return n
 return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_float=finite,parse_constant=lambda v:(_ for _ in()).throw(ValueError(v)))
def atomic_fresh_json(p, value):
 fd,name=tempfile.mkstemp(prefix='.'+p.name+'.',dir=p.parent)
 try:
  with os.fdopen(fd,'w') as stream:
   stream.write(json.dumps(value,indent=2)+'\n');stream.flush();os.fsync(stream.fileno())
  os.link(name,p)
 finally:
  os.unlink(name)
 dfd=os.open(p.parent,os.O_DIRECTORY)
 try:os.fsync(dfd)
 finally:os.close(dfd)

def q(z):return Q(int(z['numerator']),int(z['denominator']))
def mono(b,c,a,d,target):return b['kind']=='M_power_log'and b['quantity']==target and q(b['coefficient'])==c and q(b['x_decay_exponent'])==a and b['log_denominator_degree']==d

def main():
 parser=argparse.ArgumentParser(allow_abbrev=False);parser.add_argument('--root-composite-peer',type=Path,required=True);parser.add_argument('--out',type=Path,required=True);args=parser.parse_args();need(not args.out.exists()and args.out.parent.is_dir(),'fresh closure receipt');inputs=[D/x for x in ['ALL24_SOURCE_BOUND_OBJECTS.json','NORMALIZED_OBJECTS.json','FINITE_EXPLICIT_FUNCTIONS.json','CONCRETE_FOUNDATION_M_BINDING_WORKLIST.json','M_LITERAL_RECEIVER_SCOPE_DISPOSITIONS_V1.json','ROOT_NONFOUNDATION32_M_LITERAL_BINDINGS_V1.json']]+[args.root_composite_peer];snaps=[pin(p)for p in inputs];source,normalized,finite,work,dispo,aliases,peer=map(load,inputs);need(peer['status'].startswith('PASS_FIXED_ROOT_AND_FIXED_COMPOSITE_'),'completed source-semantic peer');need(next(x['sha256']for x in peer['source_snapshots']if Path(x['path']).name=='FINITE_EXPLICIT_FUNCTIONS.json')==snaps[2]['sha256'],'peer uses exact current mathematical data');need(aliases['functions']['sha256']==snaps[2]['sha256'],'Root32 aliases use exact current mathematical data');by={tuple(x['key']):x for x in source['objects']};norm={tuple(x['key']):x for x in normalized['objects']};bm={b['bound_id']:b for b in finite['bounds']};grouped=collections.defaultdict(list)
 for b in finite['bounds']:grouped[tuple(b['object_key'])].append(b)
 need(len(by)==len(norm)==11411 and len(bm)==len(finite['bounds']),'full current source identities and unique function identities');need(len(work['groups'])==100,'exact100 assigned foundation M groups');scope=[];keys=[]
 lower={'M-signed-weight':('EW','signed lower .054*x^-1/2'),'M-signed-log':('ES and log(Qnorm)','signed lower .06*x^-1/2/L'),'MA-signed-weight1':('EW','signed lower .0012*x^-1/2'),'MA-signed-weight2':('EW','signed lower .0556*x^-1/2'),'MA-signed-log1':('ES and log(Qnorm)','signed lower .00015*x^-1/2/L'),'MA-signed-log2':('ES and log(Qnorm)','signed lower .0889*x^-1/2/L'),'M-sign-Q/P':('log(Qnorm), Qnorm and Pnorm','positive signed log lower .003*exp(-L/2)/L; Qnorm>1,Pnorm<1'),'M-sign-D2':('EW','positive signed lower .10*exp(-L/2)'),'M-signed-q,u':('ES and log(Qnorm)','positive signed lower .003/(sqrt(x)*L); log(Pnorm)=-log(Qnorm)'),'M-signed-j':('EW','positive signed lower .10/sqrt(x)')}
 for group in work['groups']:
  dispositions=[]
  for k in group['exact_keys']:
   key=tuple(k);keys.append(key);row=by[key];n=norm[key];raw=row['raw_M_row'];s=row['source'];need(sha(Path(s['file']))==s['sha256'],'actual written source SHA');need(n['statement_exact']==raw['exact_statement']and n['assumptions_exact']==raw['assumptions'],'whole normalized native statement/premises retained');need(n['source_defined_function_interface']['exact_body']==(n['current_qualified_statement']or raw['exact_statement']),'lossless source-native function body');fs=grouped[key]
   if fs:
    need(set(n['finite_bound_ids'])=={b['bound_id']for b in fs},'all literal canonical functions joined to source object')
    for b in fs:
     need({p:b['source'][p]for p in ['file','sha256','physical_LF','physical_LF_end']}=={p:s[p]for p in ['file','sha256','physical_LF','physical_LF_end']},'canonical function exact written identity');need(premises.branch_case(b)in ['B0','D02'],'concrete finite receiver has an actual source case, not unresolved paired metadata')
    status='ALL_SOURCE_LITERAL_FIXED_UPPER_FUNCTIONS_REPRESENTED_WITH_EXACT_SOURCE_CASE_AND_DOMAIN';reason='Exact literal scalar/root/sum functions are linked; all signs, raw formulas, Root qualifications and proof operations remain in the native source object.'
    if key[1]=='M-W':status='CANONICAL_THREE_FIXED_FINITE_PIECES_PLUS_EXACT_SPECIFIC_UNEVALUATED_FIXED_TAIL';reason='Finite[17,29],[29,58],[58,189] W functions have all4 exact receiving/error conversion functions. OnL>=189 retain exactly W=D+(1+1/L)J2+Vb with complete source definitions and guards. This is a fixed source function, not a free parameter; its full compound evaluation is explicitly unoptimized, and finite plots are not claimed as the fully optimized operator envelope.'
    elif key==('FOLLOWUP-C017','M-three-pieces'):
     tail=grouped[('FOLLOWUP-C017','M-log-14')];need(len(tail)==4,'all4 explicit source analytic tail functions');need(all(mono(b,Q('.00008'),Q(0),2 if b['quantity']=='EW'else 3,b['quantity'])and premises.branch_case(b)=='B0'for b in tail),'samecase same cap and units in the joined analytic tail');reason+=' The source finite component throughL190 joins the separately source-proved M-log-14 whole ray fromlog(10^19), which retains the beyond190 cap.'
    elif key==('FOLLOWUP-C017','M-new-power-joins'):reason+=' The .117 first bridge and both exact middle fixed sums are represented; parameterized choice-of-h certificates and the own already-encoded terminal power menu remain proof operations, not new scalar claims.'
   elif key[1]in lower:
    target,formula=lower[key[1]];need('>'in raw['exact_statement']or'strictly exceeds'in raw['exact_statement'],'native lower-constraint direction must be literal');need(n['source_defined_function_interface']['all_domain_and_parameter_guards']==n['domain'],'all native lower constraint guards retained');status='EXACT_QUANTITATIVE_SIGNED_LOWER_CONSTRAINT_RETAINED_NATIVELY';reason=formula+' for '+target+'. It is an explicit lower/sign constraint, not an unsigned upper radius: casting it as a min-eligible upper error bound would reverse the theorem or confuse log-product and relative-product quantities.'
   elif key==('FOLLOWUP-C017','M-finite-only'):
    need('not asserted as early whole-ray'in raw['exact_statement'],'the native historical scope restriction must remain explicit');status='HISTORICAL_CERTIFICATE_SCOPE_RESTRICTION_NOT_AN_EXTRA_POSITIVE_BOUND';reason='The source is the own prior review restriction: .10 sweep and .11 weighted results were finite-only at their computed endpoints. It gives no new scalar onset; later accepted extension theorems have their own separate source keys. No infinite ray is inferred from this sentence.'
   else:raise ValueError('Unresolved concrete M source clause: '+str(key))
   dispositions.append({'key':list(key),'source':{p:s[p]for p in ['file','sha256','physical_LF','physical_LF_end']},'exact_statement':raw['exact_statement'],'exact_domain':raw['full_domain'],'exact_assumptions':raw['assumptions'],'canonical_function_ids':[b['bound_id']for b in fs],'status':status,'source_based_reason':reason,'native_source_definition_and_domain_retained':True,'pending_fixed_numeric_clause':False})
  scope.append({'group':group['group'],'exact_keys':group['exact_keys'],'source_dispositions':dispositions})
 need(len(keys)==len(set(keys))==119,'exact119 unique foundation source keys; no key collapse');aliaschecks=[]
 need(len(aliases['records'])==32,'exact32 Root concrete nonfoundation keys')
 for x in aliases['records']:
  key=tuple(x['key']);row=by[key];raw=row['raw_M_row'];s=row['source'];need(x['exact_statement']==raw['exact_statement']and x['original_domain']==raw['full_domain']and x['exact_assumptions']==raw['assumptions'],'Root alias exact current source statement/domain/premises');need({p:s[p]for p in ['file','sha256','physical_LF','physical_LF_end']}==x['source']and sha(Path(s['file']))==s['sha256'],'Root alias exact actual written identity');targets=x['actual_current_target_records'];need(targets and[x['bound_id']for x in targets]==x['target_bound_ids'],'all explicit target IDs preserved')
  for b in targets:need(bm[b['bound_id']]==b and b['candidate_id']==key[0],'actual whole target function body and same candidate')
  if x['status']=='DIRECT_EXACT_SOURCE_RECEIVER_FUNCTIONS':
   need(all(tuple(b['object_key'])==key for b in targets),'direct exact source key, not another receiver cast');reason='Current same-written-source canonical functions, including the exact finite positive part or exact-root domain when the object is compound; the separate true violation witness/failure or limiting operator is not erased.'
   if 'M-old-power-'in key[1]:
    c=Q('.019851')if key[1].endswith('.019851')else Q('.01985');expected={'ES','EP','EQ'}if c==Q('.019851')else{'EW'};need({b['quantity']for b in targets}==expected,'old first3 versus weighted target set');need(all(mono(b,c,Q(1,8),0 if b['quantity']=='EW'else 1,b['quantity'])for b in targets),'all exact old power units')
   if key==('FOLLOWUP-C022','OwnD02.old.M24'):need({b['quantity']for b in targets}=={'ES','EP','EQ','EW'}and all(mono(b,Q('.24'),Q(5,32),0 if b['quantity']=='EW'else 1,b['quantity'])and premises.branch_case(b)=='D02'for b in targets),'exact old common .24 D02 case, not an actual-error floor')
  elif key==('FOLLOWUP-C007','M-basic-mid-comparison'):
   need({b['quantity']for b in targets}=={'ES','EP','EQ','EW'}and all(mono(b,Q('9.727e-10'),Q(0),2 if b['quantity']=='EW'else 3,b['quantity'])and premises.branch_case(b)=='D02'for b in targets),'exact source method .9727e-9 target vector')
   for b in targets:
    z=b['domain']['numeric_intervals'];need(len(z)==1 and z[0]['lower']['coordinate']=='L'and q(z[0]['lower']['rational'])==230 and z[0]['upper']is None and z[0]['left_closed']is True,'exact target fullL230ray')
   reason='Identical coefficient9727/10^13, alpha0, first3degree3/weighteddegree2, same explicit D02 premise and exact closed whole L>=230 ray. Source endpoint not projected or borrowed.'
  elif key[1]=='M-D02-tail-finite-analytic':
   need({b['quantity']for b in targets}=={'ES','EP','EQ','EW'},'all4 noQRH .09 target quantities')
   for b in targets:
    need(mono(b,Q('.09'),Q(0),2 if b['quantity']=='EW'else 3,b['quantity'])and b['assumptions']==raw['assumptions'],'same exact weaker noQRH/no-hypothesis premise and cap');z=b['domain']['numeric_intervals'];need(len(z)==1 and z[0]['lower']['coordinate']=='x'and q(z[0]['lower']['rational'])in [20000000,35000000]and q(z[0]['lower']['rational'])<=2**28 and z[0]['upper']is None and z[0]['left_closed']is True,'exact rational earlier source onset and full ray')
   reason='Same strict .09 cap/observable units and exactly the same noQRH/no-hypothesis assumptions; actual source table rays start at20million(first3) or35million(weighted), both<=2^28. No QRH-dependent stronger recipe is substituted.'
  else:raise ValueError('Unreviewed Root alias type: '+str(key))
  aliaschecks.append({'key':list(key),'status':'INDEPENDENT_EXACT_SOURCE_CLAUSE_BINDING_CHECKED','source':x['source'],'canonical_function_ids':x['target_bound_ids'],'reason':reason,'pending_fixed_numeric_clause':False})
 for s in snaps:need(sha(Path(s['path']))==s['sha256'],'input changed during source-scope closure')
 result={'status':'PASS_COMPLETE100_FOUNDATION_M_GROUPS_AND32_ROOT_CONCRETE_M_KEYS_SOURCE_BASED_SCOPE_CLOSURE_NO_PENDING_FIXED_NUMERIC_CLAUSES','source_snapshots':snaps,'foundation_groups':100,'foundation_exact_source_keys':119,'foundation_source_dispositions':scope,'Root_nonfoundation_exact_keys':32,'Root_nonfoundation_independent_checks':aliaschecks,'pending_fixed_numeric_clauses':0,'native_quantitative_lower_or_sign_constraint_keys':sum(x['status']=='EXACT_QUANTITATIVE_SIGNED_LOWER_CONSTRAINT_RETAINED_NATIVELY'for g in scope for x in g['source_dispositions']),'native_historical_proof_scope_restrictions':sum(x['status']=='HISTORICAL_CERTIFICATE_SCOPE_RESTRICTION_NOT_AN_EXTRA_POSITIVE_BOUND'for g in scope for x in g['source_dispositions']),'specific_fixed_compound_operators_retained_unoptimized':['C002/C008W(L)=D(L)+(1+1/L)J2(L)+Vb(L),L>=189,with exact source density/primitive/prime-power definitions.','Signed/correlated interval intersections, pointwise observed-boundary options and parameterized height/kernel/certificate menus retain their complete source definitions. Literal fixed caps/root domains and finite explicit elementary sums are serialized separately.'],'not_a_free_parameter_or_role_heuristic_exclusion':'Every source disposition was checked against actual literal statements, domain and direction. The original object_role is not a proof or exclusion rule.','entire_operator_frontier_numerically_optimized':False,'new_mathematics_source_parameters_numerical_programs_or_original_experimental_outcomes_changed':False,'source_first_PV':False,'full_analytic_Lean':False};atomic_fresh_json(args.out,result);print(json.dumps({'receipt':pin(args.out),'foundation_groups':100,'foundation_exact_keys':119,'Root_nonfoundation_keys':32,'native_signed_lower_constraints':result['native_quantitative_lower_or_sign_constraint_keys'],'native_proof_scope_restrictions':result['native_historical_proof_scope_restrictions'],'pending_fixed_numeric_clauses':0}))
if __name__=='__main__':main()
