#!/usr/bin/env python3
"""Deterministic adversarial source changes; never accepted as original source."""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
def main():
    original=(HERE/'population_norm.c').read_text();out=HERE/'negative';out.mkdir(exist_ok=True)
    mutations=[('sine_constant','3141592654ULL','3141592653ULL'),
      ('grid_bound','k < 256ULL','k < 255ULL'),
      ('rounding_allowance','absolute + 100000000000000ULL','absolute + 99999999999999ULL')]
    body=['import PopulationSource\nset_option autoImplicit false\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace RH080Next.PopulationPV\nopen GoldbachDirect\n']
    receipts=[]
    for name,before,after in mutations:
        if original.count(before)!=1:raise ValueError('Mutation anchor not unique: '+name)
        source=original.replace(before,after);raw=source.encode('ascii');p=out/(name+'.c');p.write_bytes(raw)
        body.append('def '+name+'Chars : List Char := ['+', '.join('Char.ofNat '+str(x)for x in raw)+']\n')
        body.append('''theorem '''+name+'''_rejected :
    checkedSyntax (String.ofList '''+name+'''Chars) program = false := by
  unfold checkedSyntax checkedSource
  rw [actual_ast_tokens]
  unfold tokenize
  simp only [String.toList_ofList,String.length_ofList]
  decide +kernel
#print axioms '''+name+'''_rejected
''')
        receipts.append(dict(name=name,before=before,after=after,sha256=hashlib.sha256(raw).hexdigest()))
    body.append('end RH080Next.PopulationPV\n');(HERE/'lean/PopulationMutations.lean').write_text('\n'.join(body))
    (out/'MANIFEST.json').write_text(json.dumps(dict(original_sha256=hashlib.sha256(original.encode()).hexdigest(),mutations=receipts),indent=2)+'\n')
if __name__=='__main__':main()
