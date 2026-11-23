#!/usr/bin/env python3
"""Exhaustive typed assembly of all115 kernel blocks; no row can be omitted."""
from pathlib import Path
import argparse,json
HERE=Path(__file__).resolve().parent

def generate():
    text=''.join(f'import OcticEndpointBlock{i:03d}\n'for i in range(115))+'''namespace RHOcticPush.Moments.Endpoint
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem all_checked (i : Nat) (hi : i < 7301) : allRow i=true := by
'''
    def branch(lo,hi,indent):
        pad=' '*indent
        if hi-lo==1:
            if lo==114:
                return pad+'''by_cases hlast : i < 7300
'''+pad+'''· exact tree_at allRow 2 7296 checked114 i (by omega) (by norm_num <;> omega)
'''+pad+'''· have he : i=7300 := by omega
'''+pad+'''  simpa only [he] using checked_last
'''
            return pad+f'exact tree_at allRow 6 {lo*64} checked{lo:03d} i (by omega) (by norm_num <;> omega)\n'
        mid=(lo+hi)//2
        return pad+f'by_cases h{mid} : i < {mid*64}\n'+pad+'· '+branch(lo,mid,indent+2).lstrip()+pad+'· '+branch(mid,hi,indent+2).lstrip()
    text+=branch(0,115,2)
    text+='''
#print axioms all_checked
end RHOcticPush.Moments.Endpoint
'''
    final='''import OcticEndpointAssembly
import OcticFiniteCaps
namespace RHOcticPush.Moments.Endpoint
set_option maxHeartbeats 0

theorem actual_M0 : FourierMoments.M0 ≤ (143/25:ℝ) :=
  actual_M0_of_checked all_checked

theorem actual_M1 : FourierMoments.M1 ≤ (23/5:ℝ) :=
  actual_M1_of_checked all_checked

theorem certified_moments : FourierMoments.M0 ≤ (143/25:ℝ) ∧
    FourierMoments.M1 ≤ (23/5:ℝ) := ⟨actual_M0,actual_M1⟩

#print axioms actual_M0
#print axioms actual_M1
#print axioms certified_moments
end RHOcticPush.Moments.Endpoint
'''
    return {'OcticEndpointAssembly.lean':text,'OcticCertifiedMoments.lean':final}

def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--check',action='store_true');a=p.parse_args()
    for n,t in generate().items():
        f=HERE/n
        if a.check:
            if f.read_text()!=t:raise ValueError('Assembly mismatch:'+n)
        else:f.write_text(t)
    print(json.dumps(dict(status='ASSEMBLY_MATCH' if a.check else 'ASSEMBLY_GENERATED',blocks=115,rows=7301,remaining_numerical_premises_in_final_theorem=0)))
if __name__=='__main__':main()
