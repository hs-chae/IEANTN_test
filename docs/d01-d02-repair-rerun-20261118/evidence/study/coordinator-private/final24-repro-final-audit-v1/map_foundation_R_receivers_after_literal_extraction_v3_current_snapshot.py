from pathlib import Path
from fractions import Fraction as Q
import json,hashlib,math,re,sys,collections,os,tempfile
sys.dont_write_bytecode=True
R=Path(__file__).resolve().parents[2];D=R/'coordinator-private/twentyfour-normalized-frontiers-v1';sys.path.insert(0,str(D));import premises

def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def fresh_atomic_json(path,value):
 need(not path.exists(),'fresh additive output required')
 fd,name=tempfile.mkstemp(prefix='.'+path.name+'.',dir=path.parent)
 try:
  with os.fdopen(fd,'w')as stream:
   stream.write(json.dumps(value,indent=2)+'\n');stream.flush();os.fsync(stream.fileno())
  os.link(name,path)
 finally:os.unlink(name)

def rat(v):v=Q(str(v));return {'numerator':str(v.numerator),'denominator':str(v.denominator)}
def unrat(v):return Q(int(v['numerator']),int(v['denominator']))
def coeff(d):return [Q(sum(math.factorial(i)*math.comb(j,i)-math.factorial(i)*math.factorial(j-i)for i in range(j+1)))for j in range(4,d+5)]
def part(v,lo,hi=None,case='B0',note=''):
 return {'coefficients':[rat(x)for x in v],'degree':len(v)-1,'case':case,'explicit_interval_L':[rat(lo),rat(hi)]if hi is not None else None,'explicit_onset_L':rat(lo)if hi is None else None,'left_closed':True,'right_closed':hi is not None,'strictness':'strict','operator':'>','quantity':'G','kind':'R_inverse_log_polynomial','source_clause_explanation':note}
def domain_part(v,row,case='B0'):
 intervals=row['full_domain']['numeric_intervals'];need(len(intervals)==1,'one source-defined exact L interval');x=intervals[0];need(x['lower']['coordinate']=='L'and'rational'in x['lower']and(x['upper']is None or x['upper']['coordinate']=='L'and'rational'in x['upper']),'exact rational L domain');out=part(v,unrat(x['lower']['rational']),unrat(x['upper']['rational'])if x['upper']else None,case);out['left_closed']=x['left_closed'];out['right_closed']=x['right_closed'];return out

def declarations(row):
 gid=row['group'];s=row['exact_literal_statement'];cid,ident=row['exact_keys'][0]
 if gid in [19,298]:return [domain_part([1],row)]
 if gid==159:return [part([1],'43.16',note='G>1 target; original sign-only ray is separately retained native source predicate.')]
 if gid==170:return [part(coeff(11),550)]
 if gid in [171,813]:return [part(coeff(18)+[Q('15700000000000000000000')],850)]
 if 379<=gid<=382:return [domain_part([Q(re.search(r'q=(\.?\d+(?:\.\d+)?)',s)[1])],row)]
 if 383<=gid<=385:return [domain_part([Q(re.search(r'margin is (\.?\d+(?:\.\d+)?)',s)[1])],row)]
 if gid==69:return [part([1],60,269,note='EC closed finite join'),part([1],269,note='P4 direct-D01 tail, D01 already B0-supported')]+[part(coeff(n-4),lo,note='Explicit additional P_n tail in exact source context')for n,lo in [(5,303),(6,338),(8,412),(12,562),(17,755)]]
 if gid==468:return [part([Q('.163')],'39.47',40,note='Early finite source cell; stronger B0-independent finite proof retained. Other logged cells remain native certificate object.')]
 if gid==571:return [part([1,7],'46.6',note='Exact k=1,m=7 literal code tuple shared by both branches; B0 proof also available under D02.')]
 if gid==572:return [part([1,14,Q('80.9')],50,case='D02',note='Only the B1 fixed-onset gain. The failed81-at49 diagnostic is not a bound.')]
 if gid==580:return [part([Q('.16')],'39.32',note='Exact k=0,m=.16 code tuple shared by both branches')]
 if gid==668:return [part([1],'42.8',60,note='F0 attached finite join'),part([1],60,280,note='CH2 finite F0'),part([1],280,note='No-density F0 tail; original restriction retained')]
 if gid==669:return [part([1,14],'47.5',170,note='Original B0 finite F1'),part([1,14],170,190,note='Refined B0 finite F1 join'),part([1,14],190,note='Refined B0 F1 tail; the separate unrefined method holes are not erased')]
 if 670<=gid<=676:
  m=re.search(r'R>(\.?\d+(?:\.\d+)?)x²/L\^6',s);need(m is not None,'literal R margin');return [domain_part([Q(m[1])],row)]
 if 747<=gid<=753:
  m=re.search(r'R\(x\)>(\.?\d+(?:\.\d+)?)x²/L\^6',s);need(m is not None,'literal R margin');return [domain_part([Q(m[1])],row)]
 if 754<=gid<=761:
  m=re.search(r'\((\.?\d+(?:\.\d+)?)\)/L\^(\d+).*?k=(\d+).*?=\[([^]]*)\]',s);need(m is not None and m[2]==m[3],'complete finite recovered polynomial');v=[Q(x.strip())for x in m[4].split(',')if x.strip()]+[Q(m[1])];need(len(v)==int(m[2])+1,'full recovered vector');return [domain_part(v,row)]
 if gid==762:return [part([Q('.015')],28,'29.9'),part([Q('.53')],29,'29.9')]
 if gid==1041:return [domain_part([0],row)]
 if gid==1042:return [domain_part([Q('.5')],row)]
 if gid==1043:return [domain_part([1,14,78],row)]
 if gid in [1413,1703]:return [domain_part([1,3],row)]
 if gid in [1415,1705]:return [part([1,14,Q('4.25')],58)]+[part(coeff(deg),lo)for deg,lo in [(2,225),(3,260),(4,330),(5,400)]]+[part([1,12],58,note='Original +12/L term, separate from the shifted shrink reserve (which is not a G bound)')]
 if gid in [1417,1707]:return [domain_part([Q('.1')],row)]
 if gid in [1420,1710]:return [domain_part([Q('.03')],row)]
 if 1696<=gid<=1702:
  expression=s.split('>',1)[1].rstrip('.');v=[]
  for term in expression.split('+'):
   m=re.fullmatch(r'(\.?\d+(?:\.\d+)?)(?:/L(?:²)?)?',term);need(m is not None,'complete normalized source polynomial');v.append(Q(m[1]))
  return [domain_part(v,row)]
 return []

def exact_intervals(bound):
 out=[]
 for x in bound['domain']['numeric_intervals']:
  if x['lower']['coordinate']!='L'or'rational'not in x['lower']or x['upper']is not None and(x['upper']['coordinate']!='L'or'rational'not in x['upper']):continue
  out.append((unrat(x['lower']['rational']),unrat(x['upper']['rational'])if x['upper']else None,x['left_closed'],x['right_closed']))
 return out

def contains(outer,inner):
 lo,hi,lc,rc=outer;a,b,ac,bc=inner
 return (lo<a or lo==a and(lc or not ac))and(hi is None or b is not None and(hi>b or hi==b and(rc or not bc)))

def desired_interval(part):
 if part['explicit_interval_L']:a,b=map(unrat,part['explicit_interval_L'])
 else:a,b=unrat(part['explicit_onset_L']),None
 return a,b,part['left_closed'],part['right_closed']

def vector_dominates(bound,target):
 a=list(map(unrat,bound['coefficients']));b=list(map(unrat,target['coefficients']));size=max(len(a),len(b));a +=[Q(0)]*(size-len(a));b +=[Q(0)]*(size-len(b));return all(x>=y for x,y in zip(a,b)),a==b

flags_file=D/'FINISH_REPRO_CONCRETE_FOUNDATION_RECEIVER_BINDING_FLAGS_V1.json';bounds_file=D/'FINITE_EXPLICIT_FUNCTIONS.json';bounds_hash=sha(bounds_file);flags=json.loads(flags_file.read_text())['groups'];rflags=[row for row in flags if any('CONCRETE_RAMANUJAN'in t for t in row['dispositions'])];rbounds=[x for x in json.loads(bounds_file.read_text())['bounds']if x['kind']=='R_inverse_log_polynomial'];records=[];missing=[];overrides=[];native=[]
for row in rflags:
 clauses=declarations(row)
 if not clauses:
  native.append({'group':row['group'],'exact_keys':row['exact_keys'],'status':'PRESERVED_EXACT_NATIVE_SIGN_ROOT_AFFINE_OR_COMPARATIVE_PROFILE_PREDICATE','exact_statement':row['exact_literal_statement'],'full_domain':row['full_domain'],'exact_assumptions':row['exact_assumptions'],'source':row['exact_source_spans'],'no_positive_margin_or_infinite_ray_invented':True,'note':'A root/sign/integer/affine formula, explicit source comparator, limit, or the proof contract of already-named profiles is retained literally. It is not silently assigned a positive G constant or used to remove a finite gap.'});continue
 for key in row['exact_keys']:
  entry={'key':key,'group':row['group'],'exact_statement':row['exact_literal_statement'],'full_domain':row['full_domain'],'assumptions':row['exact_assumptions'],'source':[v for v in row['exact_source_spans']],'Root_current_qualification':[v for v in row['Root_current_qualifications']],'parts':[]}
  for no,clause in enumerate(clauses):
   eligible=[]
   for b in rbounds:
    if b['candidate_id']!=key[0]or b['operator']!='>':continue
    case=premises.branch_case(b)
    if case not in(['B0']if clause['case']=='B0'else['B0','D02']):continue
    dominates,equal=vector_dominates(b,clause)
    if not dominates:continue
    for interval in exact_intervals(b):
     if contains(interval,desired_interval(clause)):eligible.append((not equal,sum(map(abs,map(unrat,b['coefficients']))),b));break
   if eligible:
    eligible.sort(key=lambda x:(x[0],x[1],x[2]['bound_id']));b=eligible[0][2];_,equal=vector_dominates(b,clause);entry['parts'].append({'part':no,'literal_clauses_full_vector':clause,'status':'EXACT_FULL_VECTOR_OR_COEFFICIENTWISE_STRONGER_OVER_ENTIRE_EXACT_RATIONAL_DOMAIN','bound_id':b['bound_id'],'bound_object_key':b['object_key'],'bound_case':premises.branch_case(b),'bound_source_operator':b['operator'],'bound_source_strictness_qualification':b['strictness'],'bound_full_vector':b['coefficients'],'bound_full_domain':b['domain'],'bound_source':b['source'],'coefficient_vectors_exactly_equal':equal,'rational_coefficientwise_proof':'After padding both complete coefficient vectors by zeros, every existing coefficient is >= the literal coefficient; all receiving-domain L values are positive. No last-coefficient shortcut or float onset is used.','exact_domain_inclusion_proved':True,'source_weaker_premise_properties_not_erased':'The original exact assumption text and proof contract are separately retained; this numerical binding describes the common B0/B0+D02 comparison only, not a proof that a QRH/density-free source theorem can acquire additional premises.'})
   else:
    item={'key':key,'group':row['group'],'part':no,'clause':clause,'source':row['exact_source_spans'],'exact_statement':row['exact_literal_statement'],'full_domain':row['full_domain'],'assumptions':row['exact_assumptions'],'status':'NO_EXISTING_SINGLE_COEFFICIENTWISE_DOMINATING_FULL_DOMAIN_FUNCTION_FOUND_NOT_MATHEMATICAL_FAILURE'};missing.append(item);entry['parts'].append(item)
    overrides.append({'key':key,'group':row['group'],'source':[v for v in row['exact_source_spans']],'expected_statement':row['exact_literal_statement'],'expected_domain':row['full_domain'],'expected_assumptions':row['exact_assumptions'],'branch':clause,'basis':'Independent literal/source-context reading of already Root-qualified current theorem, no new mathematics/algorithm/constant/parameter. Add this exact source branch without changing older records.'})
  records.append(entry)
# Root assigned one additional compound historical C022 row outside foundation.
allrows=json.loads((D/'ROOT_UNEXPANDED2252_EXACT_SOURCE_SCOPE_REVIEW.json').read_text())['rows'];extra=next(x for x in allrows if x['key']==['FOLLOWUP-C022','OwnD02.old.A-gaps']);extra_parts=[part([Q('.01')],'39.75',case='D02'),part([1,14,60],50,case='D02'),part([1,14,60],50,169,'B0','The exact source explicitly proves the bounded50..169 part unconditionally; this weaker-case source allowance must be separately reviewed in the premise gate.')]
extra_entry={'key':extra['key'],'current_source':extra,'parts':[]}
for no,clause in enumerate(extra_parts):
 matches=[]
 for b in rbounds:
  if b['candidate_id']!='FOLLOWUP-C022'or b['operator']!='>':continue
  case=premises.branch_case(b)
  if case not in(['B0']if clause['case']=='B0'else['B0','D02']):continue
  dominates,equal=vector_dominates(b,clause)
  if dominates and any(contains(x,desired_interval(clause))for x in exact_intervals(b)):matches.append(b)
 if matches:extra_entry['parts'].append({'part':no,'clause':clause,'status':'EXACT_SAMECASE_FULL_VECTOR_DOMAIN_MAPPING','bound_id':matches[0]['bound_id'],'bound_object_key':matches[0]['object_key'],'bound_full_vector':matches[0]['coefficients'],'bound_full_domain':matches[0]['domain']})
 else:missing.append({'key':extra['key'],'part':no,'clause':clause,'source':extra['source'],'status':'NO_EXISTING_COEFFICIENTWISE_SAMECASE_FULLDOMAIN_FUNCTION'});overrides.append({'key':extra['key'],'source':[extra['source']],'expected_statement':extra['full_qualified_statement'],'expected_domain':extra['full_domain'],'expected_assumptions':extra['assumptions_exact'],'branch':clause,'basis':'Exact historical source LF178–188 gives both global D02 claims, plus the explicit unconditional50..169 bounded piece. Original Root qualification retained.'});extra_entry['parts'].append({'part':no,'clause':clause,'status':'EXACT_SOURCE_ADDITIVE_FUNCTION_REQUIRED'})
need(sha(bounds_file)==bounds_hash,'function snapshot changed during exact mapping; rerun against one fresh snapshot')
out={'status':'INDEPENDENT_FOUNDATION_R_RECEIVER_MAPPING_WITH_NATIVE_PREDICATES_AND_EXPLICIT_PENDING_ADDITIONS','current_functions':{'path':str(bounds_file),'sha256':bounds_hash},'input_flags':{'path':str(flags_file),'sha256':sha(flags_file)},'fixed_receiving_entries':records,'native_exact_predicates':native,'extra_Root_assigned_compound_case':extra_entry,'unmapped_clauses':missing,'candidate_additive_source_branches':overrides,'scope_warning':'Single coefficientwise rational dominance search is sufficient when it succeeds; failure is not non-dominance, a source error, or a mathematical failure. Preserve native predicates, exact source assumptions and all full vectors/domains. No bound is admitted by heuristic role or a numerical float.','no_scientific_or_math_inputs_changed':True};p=D/'FINISH_REPRO_R_EXACT_RECEIVER_MAPPING_V3.json';fresh_atomic_json(p,out);p2=D/'FINISH_REPRO_R_ADDITIVE_EXACT_SOURCE_BRANCHES_V3.json';fresh_atomic_json(p2,{'status':'ROOT_REVIEW_PENDING_EXACT_CURRENT_SOURCE_EXTRACTION_ONLY','branches':overrides,'unmapped_clauses':missing,'current_functions_sha256':bounds_hash});print(json.dumps({'mapping':{'path':str(p),'sha256':sha(p)},'additions':{'path':str(p2),'sha256':sha(p2)},'numeric_entries':len(records),'native_groups':len(native),'unmapped_clauses':len(missing),'additive_candidates':len(overrides),'unmapped_keys':[x['key']for x in missing]}))
