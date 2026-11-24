#!/usr/bin/env python3
"""Read-only association check for the five report outputs and formula sources.

This verifies rendered formula identity, not the mathematical truth of formulas;
the independent written source/math review is recorded separately in REVIEW.json.
"""
import argparse, hashlib, importlib.util, json, pathlib, re, subprocess, sys
from html.parser import HTMLParser

def strict_json(path):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result: raise ValueError('Duplicate JSON key: '+key)
            result[key] = value
        return result
    return json.loads(path.read_text(), object_pairs_hook=pairs,
        parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))

def module(name, path):
    spec=importlib.util.spec_from_file_location(name,path)
    result=importlib.util.module_from_spec(spec); spec.loader.exec_module(result)
    return result

def identity(path):
    data=path.read_bytes()
    return {'file':str(path),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}

class MathReader(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.stack=[];self.formulas=[];self.annotations=[];self.prose=[]
    def handle_starttag(self,tag,attrs):
        attrs=dict(attrs); parent=self.stack[-1] if self.stack else (None,None,False,False)
        fid=attrs.get('data-formula',parent[1])
        if 'data-formula' in attrs:self.formulas.append(fid)
        blocked=parent[2] or tag in ['script','style','math','svg'] or 'katex' in attrs.get('class','').split()
        annotation=tag=='annotation' and attrs.get('encoding')=='application/x-tex'
        if tag not in ['area','base','br','col','embed','hr','img','input','link','meta','param','source','track','wbr']:
            self.stack.append((tag,fid,blocked,annotation))
        if annotation:self.annotations.append([fid,''])
    def handle_endtag(self,tag):
        for n in range(len(self.stack)-1,-1,-1):
            if self.stack[n][0]==tag:
                del self.stack[n:];return
    def handle_data(self,data):
        if self.stack and self.stack[-1][3]:self.annotations[-1][1]+=data
        if not self.stack or not self.stack[-1][2]:self.prose.append(data)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--capsule',type=pathlib.Path,required=True)
    parser.add_argument('--katex',type=pathlib.Path,required=True)
    parser.add_argument('--out',type=pathlib.Path,required=True)
    args=parser.parse_args();rd=args.capsule/'reports'
    sys.path.insert(0,str(rd))
    op=module('review_op',rd/'oneprime_sections.py');sp=module('review_sp',rd/'paper_sections.py')
    ko=module('review_ko',rd/'ko_math_labels.py')
    formulas={}
    for source in [op.FORMULAS,sp.SUMMARY_FORMULAS,strict_json(rd/'NETWORK_FORMULAS.json'),strict_json(rd/'GAUSSIAN_FORMULAS.json')]:
        for key,value in source.items():
            if key in formulas:raise ValueError('Formula identifier duplicated: '+key)
            formulas[key]=value
    build=strict_json(rd/'REPORT_BUILD.json');claims={x['path']:x for x in build['reports']}
    for row in build['report_inputs']:
        if identity(rd/row['path'])['sha256']!=row['sha256']:
            raise ValueError('Current renderer input changed: '+row['path'])
    allforms=dict(formulas)
    allforms.update({'KO_'+key:ko.translate(value) for key,value in formulas.items()})
    renderer=rd/'render_math.js'
    rendered=json.loads(subprocess.run(['node',str(renderer),str(args.katex.resolve())],
        input=json.dumps(allforms),text=True,capture_output=True,check=True).stdout)
    rendered={key:re.sub(r'<annotation[^>]*>.*?</annotation>','',value,flags=re.S)
        for key,value in rendered.items()}
    if strict_json(args.katex/'package.json')['version']!=build['katex_version']:
        raise ValueError('KaTeX version differs from actual report build')
    expected={'RH_ONE_PRIME_FRONTIER_EN.html':52,'RH_ONE_PRIME_FRONTIER_KO.html':52,
        'RH_NETWORK_EVOLUTION_EN.html':67,'RH_NETWORK_EVOLUTION_KO.html':67,'RH_PAPER_SUMMARY_EN.html':8}
    reports=[]
    for name,count in expected.items():
        path=rd/name; ident=identity(path)
        if claims[name]['sha256']!=ident['sha256']:raise ValueError('Output/receipt hash mismatch: '+name)
        html=path.read_text();reader=MathReader();reader.feed(html)
        matches=list(re.finditer(r'<div class="formula"[^>]*data-formula="([^"]+)">',html))
        if len(reader.formulas)!=count or len(matches)!=count:
            raise ValueError('Missing actual rendered formula: '+name)
        for match in matches:
            fid=match.group(1)
            if fid not in formulas:raise ValueError('Unknown formula: '+fid)
            want=rendered[('KO_'+fid) if name.endswith('_KO.html') else fid]
            if not html.startswith(want+'</div>',match.end()):
                raise ValueError('Actual MathML differs from current strict rendering: '+name+':'+fid)
        prose=' '.join(' '.join(reader.prose).split())
        for bad in ['external directed-interval calculation for the same degree-twelve',
            '같은 12차 후보의 외부 방향성 구간 계산보다', 'its imported canonical research module']:
            if bad in prose:raise ValueError('Withdrawn claim remains: '+name+':'+bad)
        reports.append(dict(ident,formula_count=count,actual_MathML_matched=True))
    result={'status':'PASS_EXACT_RENDERED_MATHML_SOURCE_ASSOCIATION',
        'limits':'Formula identity and explicit regression checks only; source/math validity reviewed independently.',
        'reports':reports,'build_receipt':identity(rd/'REPORT_BUILD.json'),
        'renderer':identity(renderer),'katex_version':build['katex_version'],
        'raw_TeX_annotations_intentionally_stripped':True,
        'inputs':[identity(rd/x) for x in ['oneprime_sections.py','paper_sections.py','gaussian_sections.py',
            'network_sections.py','ko_math_labels.py','NETWORK_FORMULAS.json','GAUSSIAN_FORMULAS.json']]}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    if args.out.exists():raise FileExistsError(args.out)
    temp=args.out.with_suffix(args.out.suffix+'.tmp');temp.write_text(json.dumps(result,indent=2)+'\n');temp.replace(args.out)
    print(json.dumps({'status':result['status'],'counts':[x['formula_count'] for x in reports],
        'receipt_sha256':identity(args.out)['sha256']}))

if __name__=='__main__':main()
