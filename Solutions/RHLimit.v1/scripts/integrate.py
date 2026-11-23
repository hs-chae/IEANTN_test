#!/usr/bin/env python3
"""Versioned statements and explicitly conditional canonical propagation adapters.

Original conclusions and scored outcomes stay fixed. Generated Challenge files
are statement scaffolds, never imported by any Solution/proof consumer.
"""
from pathlib import Path
import yaml
S=Path(__file__).resolve().parents[1];N=S.parents[1]
H='''/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
'''
def write(p,s):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
def edge(s):
 node,con=s.rsplit(':',1);return {'node':node,'conclusion':con}
def node(family,version,body,rows,description,source_open=False):
 ident=family+'.'+version;p=N/'IEANTN/Nodes'/family/version
 write(p/'Conclusions.lean',H+body)
 conclusion=[]
 for name,imports in rows:
  conclusion.append({'id':name,'declaration':ident+'.'+name,'challenge':ident+'.challenge_'+name,'imports':[edge(x)for x in imports],'imports_status':'identified'if imports else'none','justifications':[{'id':'analytic-open'if source_open else'local-proof','kind':'none-yet'if source_open else'lean-noncompliant','note':('Unchanged analytic contract exposed separately from four now-proved elementary components. Full explicit-formula/zero-estimate formalization remains open.'if source_open else'Actual standard-three-axiom conditional Solution, rebuilt from captured source. Official Comparator receipt pending; source-first PV only where the exact C execution chain is documented.')}],'designated':'analytic-open'if source_open else'local-proof'})
 d={'version':'v0.4','node':{'id':ident,'family':family,'version':version,'kind':'pipeline','status':'awaiting-verification'},'project':{'name':ident,'description':description,'authors':['OpenAI (Codex)'],'license':'Apache-2.0','responsible_maintainers':['hschae']},'repository':{'role':'substantive-development'},'classification':{'arxiv':['math.NT'],'msc2020':['11N05','11M26']},'conclusions':conclusion,'sources':[{'id':'RHLimit20261122','title':'Post-lock RH limit continuation','authors':['OpenAI (Codex)'],'type':'original-proof','relationship':'other','note':'Exact source and mathematical contracts in Solutions/RHLimit.v1; historical results unchanged.'}],'limitations':['No official Comparator receipt. Conditional kernel proofs do not discharge named analytic inputs. Native/kernel numerical evaluation is not source-first PV.']}
 write(p/'formalization.yaml',yaml.safe_dump(d,sort_keys=False))

def main():
 rh='RH.v1:hypothesis';gm='RHPrimeCounting.v1:gm_source';bp='Buthe.v1:theorem_2_psi';bj='Buthe.v1:theorem_2_li_minus_riemann_pi'
 common=[rh,gm,bp,bj]
 body='''import IEANTN.Nodes.RHPrimeCounting.v1.Conclusions
import IEANTN.Vocabulary.ErrorTerms
namespace RHPrimeCounting.v2
open Real IEANTN
noncomputable def correction (L : ℝ) : ℝ :=
  2*log 4+(693/5000:ℝ)/(L-6)+L/(2*exp (L/4))+
    L*log (L/log 2)/exp (L/6)+(411/25:ℝ)*L/exp (L/2)
noncomputable def refinedCorrection (x : ℝ) : ℝ :=
  361/25+(693/5000:ℝ)*sqrt x/(log x*(log x-6))
def elementary_prime_powers : Prop := ∀ L : ℝ, 2 ≤ L →
  riemannPrimeCounting (exp L)-primeCounting (exp L) ≤
    2*log 4*exp (L/2)/L+exp (L/4)/2+exp (L/3)*log (L/log 2)
def refined_transfer : Prop := ∀ x : ℝ, exp 12 ≤ x →
  |riemannPrimeCounting x-li x-(Chebyshev.psi x-x)/log x| ≤ refinedCorrection x
def transfer_gain : Prop := ∀ x : ℝ, exp 16 ≤ x →
  (1/5:ℝ) < RHPrimeCounting.v1.transferCorrection x-refinedCorrection x
def ch_Epi : Prop := ∀ L : ℝ, 34 ≤ L →
  Eπ (exp L) ≤ (RHSmoothing.chBound L+correction L)*exp (-L/2)
def box_Epi : Prop := ∀ L : ℝ, 35 ≤ L →
  Eπ (exp L) ≤ (RHSmoothing.fastBound L+correction L)*exp (-L/2)
def ch_classical_gain : Prop := ∀ L : ℝ, 100 ≤ L →
  |primeCounting (exp L)-Li (exp L)| < exp (L/2)*(L/(8*π)-1/3)
def box_point_100 : Prop := Eπ (exp 100) < (357041/1000:ℝ)*exp (-50)
end RHPrimeCounting.v2
'''
 rows=[('elementary_prime_powers',[]),('refined_transfer',common),('transfer_gain',[]),('ch_Epi',common+['RHSmoothing.v1:recovered_ch_psi']),('box_Epi',common+['RHSmoothing.v1:box_psi']),('ch_classical_gain',common+['RHSmoothing.v1:recovered_ch_psi']),('box_point_100',common+['RHSmoothing.v1:box_psi'])]
 node('RHPrimeCounting','v2',body,rows,'Entirely elementary ordinary-pi bounds and sharper GM transfer; actual existing psi providers propagate unchanged.')
 body='''import IEANTN.Vocabulary.PrimeWindows
namespace PrimeKernelInputs.v2
open Real Set IEANTN.PrimeWindows
def octic_215_explicit_formula : Prop := ExplicitFormula 4 (43/20)
def octic_215_zero_estimate : Prop := ZeroEstimate 4 (43/20) (911/500) (3/2) (3/125)
def octic_family_explicit_formula : Prop := ∀ C ∈ Icc (103/100:ℝ) 16, ExplicitFormula 4 C
def octic_family_zero_estimate : Prop := ∀ C ∈ Icc (103/100:ℝ) 16,
  ZeroEstimate 4 C (911/500) (3/2) (3/20)
end PrimeKernelInputs.v2
'''
 node('PrimeKernelInputs','v2',body,[(n,[])for n in ['octic_215_explicit_formula','octic_215_zero_estimate','octic_family_explicit_formula','octic_family_zero_estimate']],'Only the original octic explicit-formula and zero-estimate obligations remain; no changed numerical parameters.',True)
 # Existing old pack is now derived from the two exact analytic components.
 p=N/'IEANTN/Nodes/PrimeKernelInputs/v1/formalization.yaml';d=yaml.safe_load(p.read_text())
 for c in d['conclusions']:
  tag='215'if c['id']=='octic_215'else'family'
  c['imports']=[edge('PrimeKernelInputs.v2:octic_'+tag+'_explicit_formula'),edge('PrimeKernelInputs.v2:octic_'+tag+'_zero_estimate')];c['imports_status']='identified'
  c['justifications']=[x for x in c['justifications']if x['id']!='four-components-proved'];c['justifications'].append({'id':'four-components-proved','kind':'lean-noncompliant','note':'Original six-component pack constructed from unchanged two analytic predicates and four unconditional kernel proofs in RHLimit.v1. Original conclusion statement unchanged; official Comparator pending.'});c['designated']='four-components-proved'
 write(p,yaml.safe_dump(d,sort_keys=False))
 # Existing analytic leaf gets an unconditional solution; all descendants reuse it.
 p=N/'IEANTN/Nodes/BoxMellinInputs/v1/formalization.yaml';d=yaml.safe_load(p.read_text())
 for c in d['conclusions']:
  if c['id']=='stieltjes_trapezoid':
   c['justifications']=[x for x in c['justifications']if x['id']!='unconditional-limit-proof'];c['justifications'].append({'id':'unconditional-limit-proof','kind':'lean-noncompliant','note':'Actual sequence convergence to limUnder and exact128 trapezoid bound proved unconditionally by RHLimit.v1/analytic/StieltjesTrapezoid.lean; cold48-source replay passed. No numerical or RH hypothesis. Official Comparator pending.'});c['designated']='unconditional-limit-proof'
 d['limitations']=['First and second Mellin identities remain explicit unresolved analytic inputs. The Stieltjes/trapezoid conclusion now has an unconditional local kernel proof.','No official Comparator receipt; historical outcomes unchanged.']
 write(p,yaml.safe_dump(d,sort_keys=False))
 write(N/'Solutions/BoxMellinInputs.v1/Solution.lean',H+'''import StieltjesTrapezoid
namespace BoxMellinInputs.v1
theorem challenge_stieltjes_trapezoid : stieltjes_trapezoid :=
  RHLimit.Stieltjes.stieltjes_trapezoid
#print axioms challenge_stieltjes_trapezoid
end BoxMellinInputs.v1
''')
 write(N/'Solutions/PrimeKernelInputs.v1/Solution.lean',H+'''import OcticTwoInputs
import IEANTN.Nodes.PrimeKernelInputs.v1.Conclusions
import IEANTN.Nodes.PrimeKernelInputs.v2.Conclusions
namespace PrimeKernelInputs.v1
open RHLimit.OcticGeometry RHLimit.OcticPrimePowers
theorem challenge_octic_215 (hef : PrimeKernelInputs.v2.octic_215_explicit_formula)
    (hz : PrimeKernelInputs.v2.octic_215_zero_estimate) : octic_215 :=
  ⟨hef,hz,primepower_cost_215,trivial_cost_215,scalar_geometry_215,forward_coverage_215⟩
theorem challenge_octic_family (hef : PrimeKernelInputs.v2.octic_family_explicit_formula)
    (hz : PrimeKernelInputs.v2.octic_family_zero_estimate) : octic_family := by
  intro C hC
  exact ⟨hef C hC,hz C hC,primepower_cost_family 4 hC,trivial_cost_family 4 hC,
    scalar_geometry_family hC,forward_coverage_family hC⟩
#print axioms challenge_octic_215
#print axioms challenge_octic_family
end PrimeKernelInputs.v1
''')
 print('Wrote2newnodeversions; strengthened2existingproviders without changingtheir mathematical statements.')
if __name__=='__main__':main()
