#!/usr/bin/env python3
"""Build four offline reports. Mathematical proof acceptance is a separate gate."""
import argparse
import base64
import hashlib
import json
from html import escape
from html.parser import HTMLParser
from pathlib import Path
import re
import subprocess
import sys

HERE=Path(__file__).resolve().parent
S=HERE.parent
R=S.parents[1]
sys.path.insert(0,str(HERE))
from network_sections import render_network
from oneprime_sections import render_oneprime, FORMULAS
from paper_sections import render_summary, SUMMARY_FORMULAS
from ko_math_labels import translate

class Prose(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True);self.skip=0;self.words=[];self.tags=[];self.stack=[];self.links=[]
    def handle_starttag(self,tag,attrs):
        self.tags.append(tag); self.stack.append(tag)
        if tag in ('math','style','script'):self.skip+=1
        if tag=='a': self.links.append(dict(attrs).get('href',''))
    def handle_endtag(self,tag):
        if tag in ('math','style','script'):self.skip-=1
        if self.stack and self.stack[-1]==tag:self.stack.pop()
    def handle_data(self,data):
        if not self.skip:self.words.append(data)

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def readj(p):return json.loads(p.read_text()) if p.exists() else None

def verification(lang,run):
    ko=lang=='KO'
    def t(a,b):return b if ko else a
    def p(a,b):return '<p>'+escape(t(a,b))+'</p>'
    e=readj(run/'EXECUTION.json'); progress=readj(run/'PROGRESS.json')
    audit=readj(run.parent/'audit/RESULT.json') or readj(run.parent/'integration-review/fresh-v1/RESULT.json')
    gaussian_run=readj(S/'gaussian_gap/FINAL_VERIFICATION.json')
    pin=readj(S/'SOURCE_PIN.json')
    status=(e or {}).get('status','IN_PROGRESS')
    body='<section id="verification"><h2>'+t('Verification, resources and trust boundary','검증, 자원 및 신뢰 경계')+'</h2>'
    body+=p('The new numerical and endpoint proofs are Lean kernel verification (D), not source-first program verification. The source analytic inputs are explicit propositions (B). Ordinary RH is a mathematical hypothesis (A); it is not the generalized RH for Dirichlet functions. External interval computations and witness searches are experiments (E). No new C/C++/CUDA source-first verified computation was completed in this campaign.','새 수치 및 끝점 증명은 Lean 커널 검증(D)이며 소스 우선 프로그램 검증이 아니다. 해석학 원문 입력은 명시적 명제(B)이다. 보통 RH는 수학적 가정(A)이며 디리클레 함수의 일반화 RH가 아니다. 외부 구간 계산과 증인 탐색은 실험(E)이다. 이번 연구에서 새로운 C/C++/CUDA 소스 우선 검증 계산을 완성하지 않았다.')
    body+=p('The selected final theorem closures are checked separately for exact types, actual proof-body providers, consumed node parameters, and transitive axioms. The allowed standard axioms are propext, Classical.choice and Quot.sound. Neither generated Challenge templates nor their deliberate sorry placeholders are imported by the accepted solution proofs. Kernel-only numerical proofs should not be described as source-first PV.','선택한 최종 정리 경로는 정확한 타입, 실제 증명 본문의 공급자, 실제 사용한 노드 인자와 추이적 공리를 따로 검사한다. 허용하는 표준 공리는 propext, Classical.choice, Quot.sound이다. 자동 생성 Challenge의 의도적인 sorry 자리표시는 채택한 Solution 증명이 임포트하지 않는다. 커널 전용 수치 증명을 소스 우선 PV라고 부르면 안 된다.')
    body+='<div class="card"><strong>'+escape(t('Fresh transitive rebuild: ','새 추이적 전체 빌드: '))+escape(t('Passed','통과') if status=='PASS_FRESH_TRANSITIVE_COMPILATION' else status)+'</strong>'
    if e:
        rows=[(t('Compiled application modules','컴파일한 응용 모듈'),str(e['compiled_modules'])+'/'+str(e['required_modules'])),(t('Elapsed wall time','경과 시간'),f"{e['seconds']:.3f} s"),(t('Sampled peak owned process-tree RSS','소유 프로세스 트리 RSS 표본 최고치'),f"{e['sampled_peak_owned_tree_RSS_bytes']/2**30:.3f} GiB"),(t('Largest individual compiler RSS','개별 컴파일러 RSS 최고치'),f"{e['peak_individual_child_RSS_KiB']/2**20:.3f} GiB"),(t('Final allocated owned disk','소유 디스크 최종 할당량'),f"{e['owned_allocated_disk_bytes']/2**20:.3f} MiB"),(t('Observed compiler SIGKILL events','관측한 컴파일러 SIGKILL 횟수'),str(e['observed_SIGKILL_compiler_events']))]
        body+='<dl>'+''.join('<dt>'+escape(a)+'</dt><dd>'+escape(b)+'</dd>' for a,b in rows)+'</dl>'
    elif progress:body+=p(f"{progress['finished']} of {progress['total']} application modules completed. This draft is not a final acceptance receipt.",f"응용 모듈 {progress['total']}개 중 {progress['finished']}개 완료. 이 초안은 최종 채택 영수증이 아니다.")
    body+='</div>'
    if audit:body+=p('Independent final-consumer audit receipt: '+('passed' if audit.get('status')=='PASS_INDEPENDENT_EXACT_TYPE_AXIOM_VALUE_AUDIT' else str(audit.get('status','see receipt')))+'. This original frontier audit covers24canonical headline roots; the separate fresh Gaussian audit covers6additional canonical conclusions. This is not the entire IEANTN declaration universe.','독립 최종 소비자 감사 영수증: '+('통과' if audit.get('status')=='PASS_INDEPENDENT_EXACT_TYPE_AXIOM_VALUE_AUDIT' else str(audit.get('status','영수증 참고')))+'. 기존 경계 감사는 정식 대표 정리 24개를 다루며, 별도의 새 가우스 감사가 정식 결론 6개를 더 다룬다. IEANTN 전체 선언을 검토했다는 뜻은 아니다.')
    else:body+=p('The final fresh-object independent audit is still pending in this draft. Focused development audits are already recorded separately.','이 초안에서는 새 객체에 대한 독립 최종 감사가 아직 대기 중이다. 집중 개발 감사는 별도로 기록되어 있다.')
    summary=readj(S/'evidence/reproduction/RUN_SUMMARY.json')
    if summary:
        rows={row['label']:row for row in summary['runs']}
        body+='<h3>'+t('The two complete clean reproduction pipelines','완료한 두 개의 깨끗한 재현 파이프라인')+'</h3><div class="tablewrap" tabindex="0"><table><thead><tr>'+''.join('<th>'+escape(x)+'</th>' for x in [t('Pipeline','파이프라인'),t('Total wall time','전체 경과 시간'),t('Recorded CPU','기록된 CPU 시간'),t('Sampled compiler-tree RAM','컴파일러 트리 RAM 표본 최고치'),t('Largest compiler','최대 개별 컴파일러'),t('Final owned disk','최종 소유 디스크'),t('SIGKILL','SIGKILL')])+'</tr></thead><tbody>'
        for label,title in [('relocated300',t('300-source frontier / old consumers','300소스 경계 및 기존 소비자')),('gaussian53',t('53-source Gaussian / Fourier / ANT','53소스 가우스·푸리에·정수론'))]:
            row=rows[label]
            cells=[title,f"{row['full_pipeline_wall_seconds']:.3f} s",f"{row['recorded_user_CPU_seconds']+row['recorded_system_CPU_seconds']:.3f} s",f"{row['compiler_phase_sampled_peak_tree_RSS_bytes']/2**30:.3f} GiB",f"{row['max_recorded_individual_compiler_RSS_KiB']/2**20:.3f} GiB",f"{row['current_final_owned_run_tree_bytes']/2**20:.3f} MiB",str(row['observed_compiler_SIGKILL_events'])]
            body+='<tr>'+''.join('<td>'+escape(x)+'</td>' for x in cells)+'</tr>'
        body+='</tbody></table></div>'
        body+=p('CPU totals sum recorded GNU user/system times for compiler and control processes. Aggregate RAM was sampled during compilation; individual compiler maxima are recorded across the logged phases. Disk is the final run-tree allocation, not an exact measured peak. Both packets rebuilt every selected application module and exercised their final proof and negative-control checks; only the pinned generic libraries were reused.','CPU 합계는 기록된 컴파일러·대조 프로세스의 GNU 사용자 및 시스템 시간을 합한 값이다. 전체 RAM은 컴파일 중 표본 측정했으며, 개별 컴파일러 최고치는 기록된 단계 전체에서 구했다. 디스크는 실행 디렉터리의 최종 할당량으로 정확한 최고치 측정이 아니다. 두 묶음 모두 선택한 응용 모듈 전체를 다시 컴파일하고 최종 증명 및 거부 대조 검사를 수행했으며, 고정된 일반 라이브러리만 재사용했다.')
    body+=p('The unchanged octic baseline was also rebuilt from 244 application source modules, without predecessor application objects. The final run uses only pinned generic Lean/Mathlib dependencies and freshly compiled application objects. Lean 4.34.0-rc2 and mathlib 71a80585ee495fc24472fd0eaffc89d94e4fd8d6 are pinned. Compiler, runtime, operating system and hardware correctness remain trusted infrastructure; external Arb runs do not inherit Lean-kernel status.','변경하지 않은 옥틱 기준도 이전 응용 객체 없이 244개 응용 소스 모듈에서 재빌드했다. 최종 실행은 고정된 일반 Lean/Mathlib 의존성과 새로 컴파일한 응용 객체만 사용한다. Lean 4.34.0-rc2 및 mathlib 71a80585ee495fc24472fd0eaffc89d94e4fd8d6을 고정했다. 컴파일러, 런타임, 운영체제, 하드웨어는 신뢰하는 기반이며 외부 Arb 실행이 Lean 커널 검증 지위를 얻지는 않는다.')
    body+=p('At startup the host had approximately 1.07 TiB of available RAM and 6.98 TB of free data-disk space, measured independently. Four fresh-build workers were admitted with a 64 GiB per-process address-space limit and a host reserve; no obsolete 4 GiB cap was used. Process-tree peak memory is sampled, individual compiler peaks use GNU time, and disk is measured at the end, not claimed as an exact peak. A SIGKILL counter alone does not establish absence of host-wide OOM events. The recorded failures include an incomplete generic cache, a stopped trial-division attempt and failed external optimization; they are not promoted to successful certificates.','시작 시 호스트의 사용 가능한 RAM은 약 1.07 TiB, 데이터 디스크 여유는 6.98 TB였고 각각 측정했다. 새 빌드는 네 작업자로 실행하며 프로세스당 주소공간 64 GiB와 호스트 여유를 유지했다. 오래된 4 GiB 제한을 사용하지 않았다. 프로세스 트리 메모리는 표본 측정, 개별 컴파일러 최고치는 GNU time으로 측정하고 디스크는 종료 시점 값이며 정확한 최고치라고 주장하지 않는다. SIGKILL 횟수만으로 호스트 전체 OOM 부재를 증명하지 않는다. 불완전한 일반 캐시, 중단한 시험 나눗셈, 실패한 외부 최적화는 성공한 인증서로 승격하지 않는다.')
    body+=p('Official generated Challenge/fingerprint checks and the independently compiled solution audit are different processes. Node metadata retains local-review status until the official approval workflow supplies its own receipt; this report is not an author-written Comparator approval. Exact commands, source hashes, frozen controller identities and receipts are included in the evidence package and REPRODUCE.md. Regenerable duplicate scratch may be removed only after reproduction checks, while accepted evidence and original sources are preserved.','공식 Challenge 및 지문 생성 검사와 독립적으로 컴파일한 Solution 감사는 서로 다른 과정이다. 공식 승인 절차가 자체 영수증을 제공하기 전까지 노드 메타데이터는 지역 검토 상태를 유지한다. 이 보고서는 저자가 작성한 Comparator 승인이 아니다. 정확한 명령, 소스 해시, 동결 제어기 식별자와 영수증은 증거 묶음과 REPRODUCE.md에 포함된다. 재생성 가능한 중복 작업 파일만 재현 확인 뒤 제거하며 채택한 증거와 원 소스는 보존한다.')
    body+='<p><a href="../REPRODUCE.md">REPRODUCE.md</a> · <a href="../ONE_PRIME_AND_NETWORK_THEOREM_MATRIX.md">'+t('Full theorem matrix','전체 정리 행렬')+'</a></p>'
    if pin:body+='<p>'+escape(t('Pinned mathematical source commit: ','고정한 수학 소스 커밋: '))+escape(pin['commit'])+'</p>'
    body+='</section>'
    return body

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--katex',required=True,type=Path)
    ap.add_argument('--run',required=True,type=Path)
    ap.add_argument('--output',type=Path,default=HERE)
    args=ap.parse_args()
    formulas={**FORMULAS,**SUMMARY_FORMULAS};forms=json.loads((HERE/'NETWORK_FORMULAS.json').read_text())
    if set(formulas)&set(forms):raise SystemExit('Duplicate formula identity')
    gaussian_forms=json.loads((HERE/'GAUSSIAN_FORMULAS.json').read_text())
    if set(formulas)&set(gaussian_forms) or set(forms)&set(gaussian_forms):raise ValueError('Duplicate Gaussian formula identity')
    formulas.update(forms)
    formulas.update(gaussian_forms)
    formulas.update({'KO_'+key:translate(value) for key,value in list(formulas.items())})
    renderer=HERE/'render_math.js'
    rendered=json.loads(subprocess.run(['node',str(renderer),str(args.katex.resolve())],input=json.dumps(formulas),text=True,capture_output=True,check=True).stdout)
    rendered={k:re.sub(r'<annotation[^>]*>.*?</annotation>', '', v, flags=re.S) for k,v in rendered.items()}
    args.output.mkdir(parents=True,exist_ok=True)
    oldfonts=HERE/'fonts'
    font=base64.b64encode((oldfonts/'STIXGeneral.ttf').read_bytes()).decode('ascii')
    pin=readj(S/'SOURCE_PIN.json');revision=pin['commit'] if pin else 'research/rh-one-prime-network-20261124'
    visited=['Solutions/RHOnePrimeEvolution.v1/REPRODUCE.md',
             'Solutions/RHOnePrimeEvolution.v1/ONE_PRIME_AND_NETWORK_THEOREM_MATRIX.md']
    def m(key):return '<div class="formula" tabindex="0" role="group" aria-label="Mathematical expression" data-formula="'+key+'">'+rendered[('KO_'+key) if lang=='KO' else key]+'</div>'
    def link(path,label):
        clean=path.split('#',1)[0]
        if not (R/clean).is_file():raise ValueError('Missing actual source link: '+path)
        visited.append(path)
        return '<a href="https://github.com/hs-chae/IEANTN_test/blob/'+revision+'/'+escape(path,quote=True)+'">'+escape(label)+'</a>'
    def source(url,label):
        if not url.startswith('https://'):raise ValueError('Expected HTTPS primary link')
        return '<a href="'+escape(url,quote=True)+'">'+escape(label)+'</a>'
    css='''@font-face{font-family:STIX;src:url(data:font/ttf;base64,FONT) format("truetype");font-display:swap}*{box-sizing:border-box}html{scroll-behavior:smooth}body{margin:0;background:#f2f5f8;color:#17233a;font:17px/1.65 system-ui,sans-serif;overflow-wrap:anywhere}main{max-width:1050px;margin:auto;padding:40px 24px 90px}header{border-bottom:3px solid #294fb2;padding:0 0 24px}h1{font-size:clamp(28px,4vw,42px);line-height:1.2;letter-spacing:-.025em}h2{margin:0 0 14px;font-size:25px;line-height:1.3;color:#17396f}h3{font-size:20px;line-height:1.3}section{background:white;border:1px solid #d6dfeb;border-radius:12px;padding:26px;margin:24px 0}p{margin:12px 0}#lee{border-left:5px solid #a43d38;background:#fff8f6}a{color:#2046a2;text-underline-offset:3px;overflow-wrap:anywhere}a:hover{color:#792061}a:focus-visible,summary:focus-visible{outline:3px solid #b06d08;outline-offset:4px}nav{display:flex;flex-wrap:wrap;gap:8px 18px;margin-top:20px}.lead{background:#e5effe;border-left:5px solid #2958ba;padding:16px 22px;margin:24px 0}.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(min(100%,270px),1fr));gap:14px}.card{padding:18px;background:#f0f6f2;border:1px solid #bdcec6;border-radius:10px}.status{font-weight:700;font-size:14px;text-transform:uppercase;color:#764714}.formula{overflow-x:auto;overflow-y:hidden;padding:12px 0;margin:7px 0;max-width:100%}math{font-family:STIX,"STIX Two Math",serif;font-size:1.12em}code{font-size:.87em;overflow-wrap:anywhere}dt{font-weight:650}dd{margin:0 0 6px}summary{cursor:pointer;font-weight:650}.source-links{font-size:14px;line-height:1.65}.tablewrap{overflow-x:auto;max-width:100%}.tablewrap table{min-width:760px}table{border-collapse:collapse;min-width:0;width:100%;font-size:14px}th,td{padding:10px;text-align:left;border-bottom:1px solid #d6dfeb}th{background:#edf2fa}footer{font-size:14px;color:#4b5c75} @media(max-width:500px){main{padding:22px 13px 55px}section{padding:19px 15px}h2{font-size:23px}.formula{font-size:14px}body{font-size:16px}}@media print{body{background:white}section{break-inside:avoid}main{max-width:none;padding:0}.formula{overflow:visible}nav{display:none}}'''.replace('FONT',font)
    output=[]
    for kind,render,title_en,title_ko in [('ONE_PRIME_FRONTIER',render_oneprime,'RH one-prime frontier','RH 한 소수 경계'),('NETWORK_EVOLUTION',render_network,'RH network evolution','RH 네트워크 확장'),('PAPER_SUMMARY',render_summary,'Conditional open-prime frontiers and population transport','')]:
      for lang in ['EN','KO']:
        if kind=='PAPER_SUMMARY' and lang=='KO':continue
        title=title_ko if lang=='KO' else title_en
        body=render(lang,m,link,source)+(verification(lang,args.run) if kind!='PAPER_SUMMARY' else '')
        if '$' in body or r'\(' in body or r'\[' in body:raise ValueError('Unrendered mathematical delimiters')
        prose=Prose();prose.feed(body)
        if 'script' in prose.tags:raise ValueError('Runtime script forbidden')
        headings=re.findall(r'<section id="([^"]+)"><h2>(.*?)</h2>',body)
        nav=''.join('<a href="#'+i+'">'+label+'</a>' for i,label in headings)
        filename='RH_'+kind+'_'+lang+'.html'
        status='Research report · source-conditional theorems · numerical experiments separate' if lang=='EN' else '연구 보고서 · 원문 조건부 정리 · 수치 실험 별도'
        if not (args.run/'EXECUTION.json').exists():status='DRAFT — final fresh verification in progress' if lang=='EN' else '초안 — 새 최종 검증 진행 중'
        html='<!doctype html><html lang="'+lang.lower()+'"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>'+title+'</title><style>'+css+'</style></head><body><main><header><p class="status">'+escape(status)+'</p><h1>'+title+'</h1><p>IEANTN · 2026-11-24 · '+escape(revision)+'</p><nav aria-label="Sections">'+nav+'</nav></header>'+body+'<footer><p>Static MathML · embedded STIX font · no network needed to read.</p><p>Font license and source identity are included with the reproducibility files.</p></footer></main></body></html>'
        target=args.output/filename;target.write_text(html)
        output.append({'path':filename,'sha256':digest(target),'bytes':target.stat().st_size,'math_occurrences':len(re.findall('data-formula=',body)),'prose_sha256':hashlib.sha256(''.join(prose.words).encode()).hexdigest(),'prose_text':''.join(prose.words)})
    (args.output/'REPORT_BUILD.json').write_text(json.dumps({'status':'STATIC_RENDERING_PASS_NOT_MATHEMATICAL_ACCEPTANCE','formula_count':len(formulas),'source_revision':revision,'renderer_sha256':digest(renderer),'katex_version':json.loads((args.katex/'package.json').read_text())['version'],'report_inputs':[{'path':p.name,'sha256':digest(p)} for p in [HERE/'oneprime_sections.py',HERE/'network_sections.py',HERE/'NETWORK_FORMULAS.json',HERE/'GAUSSIAN_FORMULAS.json',HERE/'gaussian_sections.py',HERE/'paper_sections.py',HERE/'ko_math_labels.py',Path(__file__)]],'actual_repository_links':sorted(set(visited)),'reports':output},indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'status':'STATIC_RENDERING_PASS','reports':[{k:v for k,v in x.items() if k!='prose_text'} for x in output]},ensure_ascii=False))
if __name__=='__main__':main()
