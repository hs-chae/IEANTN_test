#!/usr/bin/env python3
"""Preserve the locked Fap400 rational input; exact rescaling1e12→1e16.
Candidate numerical values are checked by subsequent closed Lean execution proofs.
"""
import contextlib,importlib.util,io,json,re,subprocess,tempfile,sys
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent;R=HERE.parents[2]
def need(x,m):
    if not x:raise ValueError(m)
def main():
    original=R/'Solutions/RH080Study.v1/ablation/followup/independent-global-chord/inputs/witness-ap.json'
    raw=json.loads(original.read_text());need(raw['m']==80 and raw['scale']==10**12 and len(raw['coefficients'])==400,'Locked Fap input differs')
    (HERE/'fap_original.json').write_bytes(original.read_bytes())
    scaled=dict(m=80,scale=10**16,coefficients=[10000*x for x in raw['coefficients']]);(HERE/'fap_scaled.json').write_text(json.dumps(scaled,indent=2)+'\n')
    source=(HERE/'window_scalars.c').read_text();a=source.index('uint64_t encoded_node');b=source.index('uint64_t positive_part',a)
    generator=importlib.util.spec_from_file_location('scalar_candidate_generator',HERE/'generate_scalars.py');g=importlib.util.module_from_spec(generator);generator.loader.exec_module(g)
    def select(lo,hi):
        if hi-lo==1:return 'return '+str(scaled['scale']+scaled['coefficients'][lo])+'ULL;'
        mid=(lo+hi)//2;return 'if (j < '+str(mid)+'ULL) { '+select(lo,mid)+' } else { '+select(mid,hi)+' }'
    selector='uint64_t encoded_node(uint64_t j) {\n  if (j >= 400ULL) { return 10000000000000000ULL; }\n  '+select(0,400)+'\n}\n\n'
    body=source[b:].replace('2520ULL','400ULL').replace('360ULL','80ULL');csource=source[:a]+selector+body;(HERE/'fap_scalars.c').write_text(csource)
    with tempfile.TemporaryDirectory(prefix='rh080-fap-candidate-')as td:
        work=Path(td);(work/'lean').mkdir();(work/'window_scalars.c').write_text(csource);(work/'w4.json').write_text(json.dumps(scaled)+'\n')
        spec=importlib.util.spec_from_file_location('fap_candidate_frontend',HERE/'generate_frontend.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);module.HERE=work
        with contextlib.redirect_stdout(io.StringIO()):module.main()
        subprocess.run(['gcc','-std=c11','-O2',str(work/'window_scalars.c'),'-o',str(work/'native')],check=True,capture_output=True)
        observed=subprocess.check_output([str(work/'native')],text=True);new=[int(x)for x in observed.splitlines()];need(len(new)==7,'Unexpected source output shape')
        previous=[3599999999999999998,73712934591273687,1146154494119977,14033179036371096,40713308729275680,69452659995205718,6911696218056550]
        def rename_only(text):
            text=text.replace("RH080Next.WindowPV","RH080Next.FapPV")
            for n in ["AST","Source","Execution","Data","AffineData","Model","RationalBridge","Main","SourceFinal","TrustAudit","ActualF0","ActualArea","ActualHeight","ActualV0","ActualV1","ActualMu2","ActualMaximum"]:
                text=text.replace("import Window"+n+"\n","import Fap"+n+"\n")
            return text

        def convert(text):
            text=text.replace('RH080Next.WindowPV','RH080Next.FapPV')
            for n in ['AST','Source','Execution','Data','AffineData','Model','RationalBridge','Main','SourceFinal','TrustAudit','ActualF0','ActualArea','ActualHeight','ActualV0','ActualV1','ActualMu2','ActualMaximum']:
                text=text.replace('import Window'+n+'\n','import Fap'+n+'\n')
            for old,n in [(2521,401),(2520,400),(2519,399),(2160,320),(360,80)]:text=re.sub(r'\b'+str(old)+r'\b',str(n),text)
            for old,n in zip(previous,new):text=text.replace(str(old),str(n))
            return text.replace("original w4","locked Fap400")
        for n in ['AST','Source','Execution']:(HERE/'lean'/('Fap'+n+'.lean')).write_text(rename_only((work/'lean'/('Window'+n+'.lean')).read_text()))
        (HERE/'lean/FapData.lean').write_text(convert((work/'lean/WindowData.lean').read_text()))
        for n in ['AffineData','Model','RationalBridge','Main','SourceFinal','TrustAudit','ActualF0','ActualArea','ActualHeight','ActualV0','ActualV1','ActualMu2','ActualMaximum']:
            (HERE/'lean'/('Fap'+n+'.lean')).write_text(convert((HERE/'lean'/('Window'+n+'.lean')).read_text()))
    # The same limb FFT algorithm, preserving every exact rescaled rational node.
    for suffix in ['', '_recursive']:
        fft=(HERE/'fft'/('w4_fft'+suffix+'.c')).read_text();a=fft.index('uint64_t encoded_node');b=fft.index('uint64_t zero_words',a)
        fft=fft[:a]+selector+fft[b:];fft=fft.replace('2520ULL','400ULL').replace('16777216ULL','131072ULL').replace('w4_norm_upper','fap_norm_upper').replace('w4_recursive_norm_upper','fap_recursive_norm_upper')
        fft=fft.replace('status=(status+divide_small(total,6ULL,100ULL,1ULL));','').replace('status=(status+divide_small(quad,6ULL,3ULL,1ULL));','status=(status+multiply_small(quad,6ULL,100ULL));status=(status+divide_small(quad,6ULL,3ULL,1ULL));').replace('answer=((first+second)+100ULL);','answer=((first+second)+20ULL);')
        (HERE/'fft'/('fap_fft'+suffix+'.c')).write_text(fft)
    (HERE/'fap_candidate_outputs.json').write_text(json.dumps(dict(status='UNTRUSTED_NATIVE_CANDIDATES_PENDING_KERNEL',outputs=new,input_original_scale=10**12,input_source_scale=10**16,exact_multiplier=10000),indent=2)+'\n')
    print(json.dumps(dict(status='GENERATED_UNTRUSTED_FAP_SOURCE_AND_PROOF_TARGETS',outputs=new)))
if __name__=='__main__':main()
