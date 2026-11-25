#!/usr/bin/env python3
"""Bounded alternative-budget research, not a new analytic source premise.

All source constants are exact Table3 bounds from Blanquer--Robles2026v2.
Arb probes are external arithmetic; the separate Lean file proves the selected
whole-real negative-budget statement. No result is promoted to the network.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse,json,hashlib,time,sys
from flint import arb,ctx,fmpq

def need(c,msg):
 if not c:raise ValueError(msg)
def aq(q):
 q=Q(q);return arb(fmpq(q.numerator,q.denominator))
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();need(not a.out.exists(),'fresh output required');a.out.mkdir(parents=True);start=time.monotonic();ctx.prec=192
 D=aq('0.92045248904315389');Ul=aq('0.78353189999069');Uh=aq('0.78353189999070');K=aq('1.101508373007')
 def margin(c,t):return (c*D-Uh)*t/2+Ul*(c*t*arb(2).log()/2).log()-K
 rows=[]
 for c in ['0.8','0.805','0.8105','0.811','0.8185','0.833945448','0.85125']:
  vals=[]
  for t in [44,59,60,70,100]:
   v=margin(aq(c),arb(t));vals.append({'log_x':t,'enclosure':v.str(55),'positive':bool(v>0),'negative':bool(v<0)})
  rows.append({'coefficient':c,'conservative_margin':vals,'asymptotic_slope':((aq(c)*D-Uh)/2).str(55)})
 need(all(x['positive']for x in next(r for r in rows if r['coefficient']=='0.811')['conservative_margin']if x['log_x']in[44,59,60]),'prior retuned endpoints changed')
 need(all(x['negative']for x in next(r for r in rows if r['coefficient']=='0.8')['conservative_margin']),'new negative probe changed')
 N=Q('0.7484161247');J=Q('0.0313377324');A=Q(36,11);den=1-A*J;ratio=N/den;eta=Q(4,5)*den/N;criticalA=(1-N/Q(4,5))/J
 sensitivity=[{'hypothetical_zero_envelope_multiplier':str(e),'conditional_inverse_budget':str(e*ratio),'decimal':float(e*ratio),'below_point_eight':e*ratio<Q(4,5)}for e in [Q(1),Q(97,100),Q(96,100),Q(959,1000),Q(95,100)]]
 prefix=[]
 for x,p in [(4,5),(5,7),(7,11)]:
  endpoint=arb(x)+aq('0.8')*arb(x).sqrt()*arb(x).log();need(endpoint>p,'small explicit endpoint failed');prefix.append({'x':x,'next_prime':p,'right_endpoint':endpoint.str(55),'strictly_above_next_prime':bool(endpoint>p)})
 need(2/arb(1).exp()<aq('0.8'),'log^2 normalization bound failed')
 r={'status':'PASS_BOUNDED_EXTERNAL_ALTERNATIVE_BUDGET_EXPERIMENT_NOT_NEW_ANALYTIC_THEOREM','precision_bits':192,'seconds':time.monotonic()-start,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'Python':sys.version,'primary':{'url':'https://doi.org/10.5281/zenodo.24429650','locator':'2026v2 physicalpp13--14, Eq20--21 and Table3; finite-range proof immediately afterTable3','exact_constants':{'D_lower':'0.92045248904315389','U_lower':'0.78353189999069','U_upper':'0.78353189999070','kappa_upper':'1.101508373007'}},'retuned_scalar_rows':rows,'new_Lean_negative_statement':'RetunedBudgetBarrier.retuned_eight_tenths_negative proves this conservative margin(.8,t)<=−1/20 for every real t>=44. This is failure of this sufficient lower bound only.','source_quantifier_gap':'Printed analytic theorem fixes c=681/800. Reusing its budgets at smaller c requires the separate monotonic parameter proof in SOURCE_PARAMETER_ARGUMENT.json; no new source premise is inserted into Lean.','prospective_G56_sensitivity':{'mass_upper':str(N),'leak_upper':str(J),'F0':'1','current_A':str(A),'current_ratio':str(ratio),'sufficient_A_for_certified_budget_point_eight':str(criticalA),'sufficient_A_decimal':float(criticalA),'uniform_zero_envelope_eta_at_point_eight':str(eta),'eta_decimal':float(eta),'sufficient_zero_envelope_budget_saving_fraction':str(1-eta),'hypothetical_rows':sensitivity,'example_sufficient_missing_cancellation_input':'For the fixed actual Gaussian F, prove uniformly in relevant centers a and d~c log(a)/(2sqrt(a)) that d*|sum_gamma a^(i gamma) F(d gamma/(2pi))| <= eta*||F||_1*log(1/d)+o(log(1/d)), with eta below the reported sufficient budget threshold, together with the original arithmetic/tail applicability. Existing absolute-value estimates only supply eta=1. No such ordinary-RH theorem has been obtained here.'},'finite_prefix_source_corollary':{'statement':'The paper finite-range argument, using its cited prime-gap computation p_next-p<log(p)^2 for11<=p<=4e18, also supports c=.8 for real4<=x<=4e18. This remains conditional on that literature-backed finite computation and its domain; no full certificate is newly verified here.','scalar_small_endpoints':prefix,'log_over_sqrt_bound':'log(y)/sqrt(y)<=2/e<.8; same monotone endpoint transfer as primary proof.'},'limits':['No universal .8 obstruction outside the fixed functional class.','No optimality or global record.','These upper-budget sensitivity thresholds are sufficient, not necessary for the actual witness or all methods; hypothetical savings or smaller A are not proved analytic inputs.','Native Arb arithmetic here is neither Lean nor source-first PV.']}
 pending=a.out/'RESULT.pending';pending.write_text(json.dumps(r,indent=2)+'\n');pending.rename(a.out/'RESULT.json');print(r['status'],'Acritical',float(criticalA),'eta',float(eta))
if __name__=='__main__':main()
