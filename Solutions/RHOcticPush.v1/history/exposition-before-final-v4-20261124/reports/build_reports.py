#!/usr/bin/env python3
"""Create standalone research reports from a separately sealed status receipt.

The renderer runs only at build time. Its output is native static MathML.
No report sentence can promote an unfinished certificate into an accepted theorem.
"""
import argparse, base64, hashlib, html, json, re, subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
CAMPAIGN = HERE.parent
REPO = CAMPAIGN.parents[1]
parser = argparse.ArgumentParser(allow_abbrev=False)
parser.add_argument('--status', type=Path, required=True)
parser.add_argument('--katex', type=Path, required=True)
parser.add_argument('--out', type=Path, required=True)
args = parser.parse_args()
args.katex = args.katex.resolve()
status = json.loads(args.status.read_text())
if status.get('status') not in {'DRAFT_RESEARCH_IN_PROGRESS', 'REVIEWED_RESEARCH_RESULTS'}:
    raise SystemExit('Missing explicit research status')
if args.out.exists():
    raise SystemExit('Use a fresh report output directory')
katex_version = json.loads((args.katex/'package.json').read_text())['version']
if katex_version != '0.16.47':
    raise SystemExit('Wrong pinned KaTeX version')
math = json.loads(subprocess.check_output(
    ['node', str(HERE/'render_math.js'), str(args.katex)],
    input=(HERE/'FORMULAS.json').read_bytes()))
snapshot_commit = status.get('source_snapshot_commit')
if status['status'] == 'REVIEWED_RESEARCH_RESULTS' and not (
        isinstance(snapshot_commit, str) and re.fullmatch('[0-9a-f]{40}', snapshot_commit)):
    raise SystemExit('Reviewed reports require an exact published source snapshot commit')
base = 'https://github.com/hs-chae/IEANTN_test/blob/' + (
    snapshot_commit or 'research/rh-octic-full-network-20261123') + '/'

def link(path, title=None):
    return '<a href="'+base+html.escape(path, quote=True)+'">'+html.escape(title or path.rsplit('/',1)[-1])+'</a>'
def source(url, locator):
    return '<a href="'+html.escape(url, quote=True)+'">'+html.escape(locator)+'</a>'
def m(key):
    return '<div class="formula" tabindex="0" role="region" aria-label="Mathematical formula">'+math[key]+'</div>'
def card(title, text, tone='blue'):
    return '<article class="card '+tone+'"><h3>'+title+'</h3>'+text+'</article>'
def section(anchor,title,text):
    return '<section id="'+anchor+'"><h2>'+title+'</h2>'+text+'</section>'

def reproduction_observation(lang):
    prose = status.get('clean_reproduction_summary_'+lang.lower())
    return '<p>'+html.escape(prose)+'</p>' if prose else ''

def ram_bridge(lang):
    text = ('The factorial coefficients come from the shifted logarithmic-integral expansion and the convolution obtained by squaring its finite polynomial. A bounds the remaining analytic expansion terms, including the square of the factorial remainder. D_aR bounds the two prime-counting errors, their cross term and their square. The existing signed consumer therefore gives the following lower bound before the piecewise maxima and finite bands are assembled.'
            if lang == 'EN' else
            '계승 계수는 이동한 로그 적분의 전개와 유한 다항식의 제곱에서 나온 합성곱이다. A는 계승 나머지의 제곱까지 포함한 해석 전개 오차를 제한하고 D_aR은 두 소수계수 오차·교차항·제곱항을 제한한다. 기존 부호 보존 소비 정리는 아래 하한을 주며, 이후 구간별 최댓값과 유한 구간 여유를 결합한다.')
    return '<p>'+text+'</p>'+m('ram_lower_bridge')

def ram_assumptions(lang):
    data = json.loads((HERE/'RAMANUJAN_INPUTS.json').read_text())
    names = {'R1':'RH', 'R2':'GM', 'R3':'Buthe2018', 'R4':'Buthe2018',
             'R5':'Buthe2018', 'R6':'Buthe2018', 'R7':'Buthe2018',
             'R8':'Buthe2018', 'R9':'Buthe2016', 'A1':'Nicolas', 'A2':'Hildebrand'}
    intro = ('R1–R9 are the unchanged original nine inputs. A1 and A2 are the two additional inputs for the606-billion global theorem. They remain explicit literature propositions, not new numerical program outputs. The definitions of π, ψ, J and principal-value li are those fixed above. Indexed packet names in A1 and A2 are local to those input rows, distinct from the integration-by-parts packets.'
             if lang == 'EN' else
             'R1–R9는 보존한 원래 아홉 입력이고 A1·A2는6060억 전역 정리에 추가한 두 입력이다. 새 수치 프로그램 출력이 아니라 명시적인 문헌 명제로 남는다. π·ψ·J·주값 li는 앞에서 정의한 실제 산술 함수다. A1·A2의 첨자가 있는 영점 항 이름은 각 입력 행 안에서만 쓰며 부분 적분 절의 항과 구분한다.')
    body = '<p>'+intro+'</p>'+m('ram_partial_RH')
    for row in data['inputs']:
        ident = row['actual_Lean']
        title = row['id']+' · '+row['readable_name']
        if row['id'] == 'R9':
            title = ('R9 · Preserved formal input for ordinary π' if lang == 'EN' else
                     'R9 · 보존한 일반 π 형식 입력')
        url = data['primary_urls'].get(names[row['id']])
        primary = source(url, row['primary_locator']) if url else html.escape(row['primary_locator'])
        if row['id'] == 'R9':
            body += '<p>'+('The following is the unchanged Lean package contract, stated for ordinary π at each fixed partial height. It is an explicit input, not a newly proved endpoint adapter. The original paper uses half weight at prime endpoints; the application below needs only its full-RH ordinary-π consequence.' if lang == 'EN' else
                '다음은 각 고정 부분 높이에서 일반 π를 사용하는 원래 Lean 입력 계약이다. 새로 증명한 끝점 연결 정리가 아니라 명시적인 보존 입력이다. 원 논문은 소수 끝점에서 절반 가중치를 사용하며, 여기의 적용에는 완전한 RH 아래 일반 π로 얻는 결과만 필요하다.')+'</p>'
        body += ('<h3>'+html.escape(title)+'</h3>'+m('ram_input_'+row['id'])+
                 '<p>'+link(ident['file']+'#L'+str(ident['physical_line']),
                            ident['declaration'])+'; '+primary+'.</p>')
        if row['id'] == 'R9':
            body += '<p>'+('For the source convention, π₀ gives half weight to a prime at the endpoint. Under full RH, choose nonprime points approaching x from above, before the next prime, and freely enlarge the height for each point. The displayed limit gives the ordinary π value needed here. The formal nine-input package still lists the stronger preserved fixed-height contract; this argument does not claim a formal proof of every such endpoint variant.' if lang == 'EN' else
                '원문의 π₀는 소수 끝점에 절반 가중치를 준다. 완전한 RH 아래에서는 다음 소수보다 작은 비소수 점들을 x 위쪽에서 접근시키고 각 점의 높이를 자유롭게 크게 잡는다. 아래 극한으로 여기서 필요한 일반 π 값을 얻는다. 형식적인 아홉 입력 묶음에는 더 강한 원래 고정 높이 계약이 그대로 남으며, 이 설명이 그 모든 끝점 변형의 형식 증명을 뜻하지는 않는다.')+'</p>'+m('ram_endpoint_transfer')
    tables = ('Both complete dyadic tables follow. Each row gives X and the two lower/upper pairs; its interval is the closed real interval [X,2X]. All displayed decimals are exact rationals. The last row reaches2X=1.024×10¹⁹, and its full interval is part of the table hypothesis; the separate finite theorem inputs have their own stated10¹⁹ cutoff.'
              if lang == 'EN' else
              '아래는 두 dyadic 표의 전체 행이다. 각 행은 X와 두 하한·상한 쌍을 주며 구간은 닫힌 실수 구간 [X,2X]다. 표시된 십진수 상수는 모두 정확한 유리수다. 마지막 행의2X=1.024×10¹⁹까지가 표 전제의 범위이며 별도 유한 정리 입력의10¹⁹ 상한과 구분한다.')
    body += '<p>'+tables+'</p>'+m('ram_full_tables')
    return '<details><summary>'+('Preserved formal inputs, source conventions and complete finite tables' if lang == 'EN' else '보존한 형식 입력·원문 계수 관례·전체 유한 표')+'</summary>'+body+'</details>'

def experiment_history(lang):
    title = 'Optional context: earlier agent comparisons' if lang == 'EN' else '선택 배경: 이전 에이전트 비교'
    text = ('The repository also archives earlier comparisons of agents given different access to mathematical context and verification tools. Their recorded tasks and outcomes are preserved. “Locked” means that this earlier record is kept fixed. The label NL_RH identifies an archived written parabolic-window argument; below we call it the earlier written argument. The mathematics in this paper is later combined research, not a retroactive success or a causal test of those earlier conditions.' if lang == 'EN' else
            '저장소에는 수학적 맥락과 검증 도구에 대한 접근 조건을 달리한 이전 에이전트 비교도 보존되어 있다. “고정”은 당시의 과제와 결과 기록을 바꾸지 않는다는 뜻이다. NL_RH는 이전의 서면 포물선 구간 논증을 가리키는 저장소 이름이며, 아래에서는 이전 서면 논증이라고 부른다. 이 문서의 수학은 그 이후의 종합 연구이고, 이전 조건의 성과를 소급해서 바꾸거나 인과적 우위를 입증하는 결과가 아니다.')
    return '<details id="experiment-history"><summary>'+title+'</summary><p>'+text+'</p></details>'

def early_reader_context(lang):
    if lang == 'EN':
        text = ('BPT abbreviates Richard P. Brent, David J. Platt and Timothy S. Trudgian, whose published zero-count estimate is an explicit source input. A “Box” kernel is uniform averaging with weight 1/2 on [−1,1]; its cosine transform is sinc, sin(y)/y, with value 1 at zero. These are different from the octic test kernel.'
                ' We use three verification labels: B means a Lean theorem conditional on explicitly named analytic source propositions; D means that its finite numerical certificates are checked by the Lean kernel; C means executable source is linked to a verified execution model, program correctness and outputs consumed by the actual IEANTN theorem. B+D is not C.')
        rows = [('Octic prime windows','RH, Green, Nicolas and BPT','B+D'),
                ('Box ψ and prime-square PNT feedback','RH, general integrated Perron, Nicolas and BPT','B+D'),
                ('Signed compensation','RH, Nicolas and general integrated Perron','B+D'),
                ('Ramanujan profiles','The unchanged nine inputs; the separate 606-billion result adds Nicolas and Perron','B+D'),
                ('Separate fixed C counter example','Program/model and platform contracts; kernel-derived count; no RH input','C+D')]
        heads = ['Result','Explicit input package','Verification']
        tail = ('The exact Box moment identities themselves are unconditional. The finite C example is separate: none of the analytic bounds uses that count as a premise. The source theorems and model/platform contracts are not silently turned into new Lean axioms.')
    else:
        text = ('BPT는 Richard P. Brent, David J. Platt, Timothy S. Trudgian을 줄인 이름이며, 이들의 영점 계수 상한은 명시적인 문헌 입력이다. Box 커널은 [−1,1]에서 가중치 1/2로 균등 평균하는 함수다. 코사인 변환은 0에서 값 1을 갖는 sinc, sin(y)/y이며 octic 시험 커널과 다르다.'
                ' 검증 표기 B는 명명한 해석 문헌 명제를 조건으로 하는 Lean 정리, D는 유한 수치 인증서의 Lean 커널 검사를 뜻한다. C는 실제 실행 소스를 검증한 실행 모델·프로그램 정확성·출력과 연결하여 실제 IEANTN 정리가 그 출력을 사용하는 경우다. B+D만으로 C가 되지는 않는다.')
        rows = [('Octic 소수 구간','RH, Green, Nicolas, BPT','B+D'),
                ('Box ψ와 소수 제곱 PNT 보정','RH, 일반 적분 Perron, Nicolas, BPT','B+D'),
                ('부호 보존 보정','RH, Nicolas, 일반 적분 Perron','B+D'),
                ('라마누잔 함수','보존한 아홉 입력; 별도 6060억 결과에는 Nicolas와 Perron 추가','B+D'),
                ('별도의 고정 C 계수 예제','프로그램·모델·플랫폼 계약과 커널 계수 증거; RH 입력 없음','C+D')]
        heads = ['결과','명시적인 입력 묶음','검증']
        tail = 'Box 모멘트 항등식 자체는 무조건부다. 유한 C 예제는 별도 결과이며 해석 상한의 전제로 사용하지 않는다. 문헌 정리와 모델·플랫폼 계약을 새 Lean 공리로 바꾸는 것은 아니다.'
    table = '<div class="tablewrap"><table><tr>'+''.join('<th>'+x+'</th>' for x in heads)+'</tr>'+''.join('<tr>'+''.join('<td>'+x+'</td>' for x in row)+'</tr>' for row in rows)+'</table></div>'
    return '<p>'+text+'</p>'+table+'<p>'+tail+'</p>'+experiment_history(lang)

def octic_budget_bridge(lang):
    if lang == 'EN':
        title = 'From moment bounds to the quantitative prime population'
        first = ('The zero estimate first keeps the actual two Fourier moments. Put D_C=CL/2−1. The extra 32δ/9 term in the transport theorem is added to the same term already in its residual; this explains the total 64δ/9 below. The domains are L≥24 and 1.03≤C≤16, with the sharper budget evaluated separately at C=43/20.')
        second = ('The original caps M₀≤5.72 and M₁≤4.6 give the rounded coefficients 1.822 and 1.5. The stronger certified caps M₀≤3574/625 and M₁≤572/125 give A=1.8203 and B=1.457. The total residual is at most 0.15 for the family and 0.024 for C=2.15. Thus the two moments enter the zero bound separately; they are not themselves prime counts.')
        third = ('The explicit formula pays that zero bound from the kernel mass m=16/9. Subtract the prime-power allowance and the trivial-zero term T₄ as well. The coefficient of L and the remaining constant are then exactly the following two parts of the lower bound for the weighted prime population Sₚ.')
        last = ('The table lists upper allowances R and P_pow, with the actual residual at most R, and uses T₄≤1/1000 in both rows. Its final column is a deliberately smaller proved constant: the family retains η=4.2, while the sharper fixed-width budget retains η=5.8. The resulting count has normalized lower bound 8C/9−0.91015+η/log(u), after the coverage argument places the left endpoint at u. These two allowances belong to their respective domains and must not be interchanged.')
    else:
        title = '모멘트 상한에서 정량적인 소수 개수로'
        first = '영점 상한은 먼저 실제 푸리에 모멘트 두 개를 그대로 유지한다. D_C=CL/2−1로 둔다. 연결 정리의 추가 32δ/9를 원래 나머지의 같은 항과 더하므로 아래에는 총 64δ/9가 나타난다. 범위는 L≥24, 1.03≤C≤16이며 C=43/20에서는 더 작은 별도 예산을 사용한다.'
        second = '원래 M₀≤5.72, M₁≤4.6에서 반올림 계수 1.822, 1.5를 얻는다. 더 강한 인증 상한 M₀≤3574/625, M₁≤572/125는 A=1.8203, B=1.457을 준다. 전체 나머지는 가족에서 0.15, C=2.15에서 0.024 이하다. 두 모멘트는 각각 영점 상한에 들어가며 그 자체가 소수 개수는 아니다.'
        third = '명시적 공식은 커널 질량 m=16/9에서 이 영점 상한을 지불한다. 소수 거듭제곱 예산과 자명한 영점 항 T₄도 뺀다. 그러면 실제 소수 가중합 Sₚ 하한은 아래의 L 계수와 남은 상수로 나뉜다.'
        last = '표의 R과 P_pow는 위쪽 여유이며 실제 나머지는 R 이하다. 두 행 모두 T₄≤1/1000을 사용한다. 마지막 열은 남은 상수보다 작게 선택한 증명된 값이다. 가족에는 η=4.2, 고정 폭에는 η=5.8을 남긴다. 전 범위 덮개로 왼쪽 끝점을 u에 맞추면 정규화 개수 하한은 8C/9−0.91015+η/log(u)다. 서로 다른 적용 범위의 두 여유를 섞지 않는다.'
    refs = '; '.join([link('Solutions/RHOcticPush.v1/octic/OcticMomentTransport.lean#L147','full_zero_bound_in_terms_of_moments'),link('Solutions/RHOcticPush.v1/octic/OcticOptimizedCertified.lean#L82','scalar_family'),link('Solutions/RHOcticPush.v1/octic/OcticOptimizedCertified.lean#L100','scalar_215')])
    return '<h3>'+title+'</h3><p>'+first+'</p>'+m('octic_pre_rounding')+'<p>'+second+'</p><p>'+third+'</p>'+m('octic_scalar_assembly')+m('octic_budget_table')+'<p>'+last+'</p><p>'+refs+'.</p>'

def box_pointwise_bridge(lang):
    if lang == 'EN':
        title = 'Why the averaged identity bounds the original ψ'
        first = ('The Box kernel is the uniform weight below. For L≥35 and shifts σ=−1,+1, average ψ over the corresponding one-sided logarithmic window. Mσ is its main-term average. Tσ is the average of the displayed trivial-zero function; it does not include log(2π). The integrated Perron formula gives the exact identity, with the complex zero packets already defined above.')
        second = ('Monotonicity of the actual ψ places its value between the two averages. The main term, full zero sum and combined constant/trivial term are bounded separately. The combined term is |Tσ−log(2π)|, paid once. Their numerical allowances add to 0.133, below the retained 0.14. In the final envelope v=L/2−log L and the proved moments give J₀=log 2, J₁≤0.70871.')
        last = ('The averaged identity uses general integrated Perron. The final pointwise theorem also uses RH, Nicolas and BPT for its zero bound. The moment identities are proved internally without these analytic assumptions. Thus averaging, summing zeros and taking a pointwise bound are separate established steps, all consumed by the actual Box theorem.')
    else:
        title = '평균 항등식이 원래 ψ의 상한을 주는 이유'
        first = 'Box 커널은 아래의 균등 가중치다. L≥35와 σ=−1,+1에서 한쪽 로그 구간의 ψ 평균을 구한다. Mσ는 주항의 평균이다. Tσ는 표시한 자명한 영점 함수의 평균이며 log(2π)를 포함하지 않는다. 적분 Perron 공식은 앞에서 정의한 복소 영점 항으로 정확한 평균 항등식을 준다.'
        second = '실제 ψ의 단조성으로 그 값은 두 평균 사이에 놓인다. 주항·전체 영점 합·상수와 자명한 영점의 결합 항을 각각 제한한다. 결합 항 |Tσ−log(2π)|는 한 번만 지불한다. 수치 여유의 합 0.133은 유지한 0.14보다 작다. 최종 함수에서는 v=L/2−log L이며 증명한 모멘트 J₀=log 2, J₁≤0.70871을 사용한다.'
        last = '평균 항등식에는 일반 적분 Perron을 사용한다. 최종 한 점의 ψ 상한에는 영점 상한을 위한 RH·Nicolas·BPT도 필요하다. 모멘트 항등식 자체는 이 가정 없이 내부에서 증명했다. 평균·무한 영점 합·한 점 상한을 각각 연결한 실제 Box 소비 정리다.'
    return '<h3>'+title+'</h3>'+m('box_kernel_definition')+'<p>'+first+'</p>'+m('box_averaged_identity')+'<p>'+second+'</p>'+m('box_brackets_budget')+'<p>'+last+'</p><p>'+link('Solutions/RHOcticPush.v1/box/perron/BoxExplicitFormula.lean#L40','averaged explicit formula')+'; '+link('Solutions/RHContinuation.v1/parabolic/PsiSmoothing.lean#L108','average_brackets')+'; '+link('Solutions/RHContinuation.v1/parabolic/PsiSmoothing.lean#L146','psi_from_smoothing')+'; '+link('Solutions/RHOcticPush.v1/box/BoxImproved.lean#L94','actual_psi_improved')+'.</p>'

def signed_constant_bridge(lang):
    if lang == 'EN':
        title = 'Assembling the signed profile without hiding the constant'
        text = ('Set L=log x≥24 and apply the weighted operator to the full zero part between 3 and x. The complete Nicolas mass β and the low integral I give the following bounds. The low integral is proved by eight analytic slabs and a majorant valid on its entire remaining ray.')
        tail = ('The zero contribution pays the fixed 104/125 exactly once. The actual anchor |D(3)|≤2, the linear source allowance 17/10 and the full trivial-zero allowance 1/10 then give 579/125. Hence the displayed profile P is an assembled bound for the original D, not a replacement error definition. This branch takes RH, Nicolas and general integrated Perron; it needs no BPT input.')
    else:
        title = '상수를 생략하지 않고 부호 보존 함수를 조립'
        text = 'L=log x≥24로 두고 3부터 x까지 전체 영점 부분에 가중 연산을 적용한다. Nicolas의 전체 질량 β와 낮은 적분 I가 아래 상한을 준다. 낮은 적분은 해석적인 구간 여덟 개와 나머지 전체 구간의 majorant로 증명했다.'
        tail = '영점 기여의 고정 여유 104/125는 한 번만 지불한다. 실제 앵커 |D(3)|≤2, 선형 문헌 항 17/10, 전체 자명한 영점 항 1/10을 더하면 579/125다. 따라서 P는 원래 D에 대한 조립된 상한이며 오차를 새로 정의한 것이 아니다. 이 경로는 RH·Nicolas·일반 적분 Perron을 사용하고 BPT는 필요하지 않다.'
    return '<h3>'+title+'</h3><p>'+text+'</p>'+m('signed_transport_definition')+m('signed_mass_assembly')+m('signed_constant_assembly')+'<p>'+tail+'</p><p>'+link('Solutions/RHOcticPush.v1/spectral-076/SpectralZeroEnvelope.lean#L19','full zero allowance')+'; '+link('Solutions/RHOcticPush.v1/spectral-076/SpectralFinal.lean#L14','complete signed profile')+'.</p>'

def prime_power_bridge(lang):
    if lang == 'EN':
        title = 'Where every prime-power and offset term comes from'
        text = ('Isolate squares in the exact prime-power identity. The terms with exponent at least three are bounded by the elementary count π(y)≤y and a harmonic-sum bound. For the square, the elementary Chebyshev estimate π(y)≤2(log 4)y/log y+√y gives the two displayed terms after substituting y=e^(L/2) and dividing by two. These steps require no RH; their complete allowance Q is valid for L≥2.')
        tail = ('The remaining additive 2 in the ordinary-π bound has a different origin: it is solely the principal-value/offset-integral constant li(2). It is not a prime-power term. Together these identities account for the full Q and the offset in the following theorem.')
    else:
        title = '소수 거듭제곱 항과 오프셋 항의 정확한 출처'
        text = '정확한 소수 거듭제곱 항등식에서 제곱 항을 분리한다. 지수 3 이상인 항은 기본 계수 π(y)≤y와 조화합 상한으로 제한한다. 제곱 항에는 기본 Chebyshev 상한 π(y)≤2(log 4)y/log y+√y를 대입하고 2로 나눈다. RH가 필요하지 않으며 전체 여유 Q는 L≥2에서 유효하다.'
        tail = '일반 π 상한의 추가 상수 2는 다른 출처다. 주값 적분과 오프셋 적분의 차이 li(2)만을 지불하며 소수 거듭제곱 항이 아니다. 아래 정리는 이 전체 Q와 오프셋을 모두 포함한다.'
    return '<h3>'+title+'</h3><p>'+text+'</p>'+m('prime_power_decomposition')+m('Q')+m('li_offset_allowance')+'<p>'+tail+'</p><p>'+link('Solutions/RHLimit.v1/pi/ExplicitPrimePower.lean','complete prime-power allowance')+'; '+link('Solutions/RHContinuation.v1/ramanujan/LiPVDefinition.lean','principal-value offset')+'.</p>'

def feedback_allowance_bridge(lang):
    text = ('Using J at the lower height replaces the old estimate for the square term. The raw feedback function deliberately retains the positive exp(L/4)/2 allowance from Q, even though the new square estimate no longer needs it. It is slack carried forward, not another square or higher-power contribution. The tail for exponents at least three is unchanged. The full lower-scale input needs L/2≥35, so this step starts at L=70; the simpler J estimate used for the strict comparison needs L/2≥50, hence L≥100.' if lang == 'EN' else
            '낮은 높이의 J를 사용하여 원래 제곱 항 상한을 바꾼다. 새 제곱 항 상한에는 필요하지 않지만 원래 Q의 양의 exp(L/4)/2 여유를 raw 보정 함수에 의도적으로 남긴다. 추가 제곱 항이나 고차 거듭제곱 기여가 아니라 보존한 여유다. 지수 3 이상인 꼬리는 그대로다. 전체 낮은 높이 입력은 L/2≥35이므로 L=70부터 적용하며, 엄밀한 함수 비교에 쓰는 간단한 J 상한은 L/2≥50, 즉 L≥100에서 적용한다.')
    return m('feedback_retained_allowance')+'<p>'+text+'</p>'

def ram_application(lang):
    if lang == 'EN':
        heading = 'The signed transfer inside the Ramanujan inequality'
        first = ('The following names distinguish the Ramanujan quantities from the octic scale and the spectral weight w(t). Define the natural coefficient K_R(L)=2w_R(L). The normalized deficit d_R is nonnegative on the finite range used here, by the explicit positivity input R8. The exact decomposition below separates ψ, the higher prime powers and the signed compensation D.')
        second = ('The coefficient-difference polynomial P₂₀ displayed above supplies the sharper main-term lower bound B_sharp. The loss 3/8000 replaces the old 1/1000 only on L≥27, so the increase is exactly 1/1600. Expand the actual Ramanujan expression in its two deficits. Its negative quadratic term remains present.')
        third = ('For a closed logarithmic cell [l,u], a conservative constant k≤2p_fac,20(u)≤K_R(L) can replace the natural coefficient because d_R(L)≥0. Lower-bound A_R(L) by a and upper-bound A_R(L−1) by b. The finite li-gap upper input gives d_R≤q, so the negative square is bounded below by −Q_R q², not discarded. This leaves the following explicit cell test.')
        fourth = ('The original nine-input advance uses the correlated GM pair bound above for B(k,L), with 0≤k≤e. The five new 606-billion cells instead use the spectral bound B(k,L)=kP(L)+eP(L−1). These are separate arguments: the latter needs Nicolas and integrated Perron and does not inherit the GM cancellation saving. Its smaller signed profiles still give the cell margins shown below. In every row k=5199/2500 and the proved normalized margin is at least 1/1000.')
        last = ('The table entries a and b are exact rational bounds for A_R(L) and A_R(L−1), respectively. Every cell has 27≤l≤L≤u≤42 and 480 billion≤e^L≤640 billion. At x=e^L, the Büthe Table 1 row X=320 billion is eligible on [320,640] billion and supplies the lower value −0.88. At y=x/e, its row X=160 billion is eligible on [160,320] billion and supplies the upper value +0.68; 2 &lt; e &lt; 3 proves those endpoint checks. The proved prime-power bounds complete a≤−0.88+lowerPowers(l,u) and +0.68+upperPowers(l−1)≤b. R7 supplies the upper li-gap bound and R8 its positivity, throughout the finite source domain.')
        final = ('Certified outer exponentials and the adjacent closed cells cover every real x from 606 to 610 billion. The previous stronger whole function applies from 610 billion onward. The global 606-billion result preserves R1–R9 and adds Nicolas and integrated Perron. The local cell transport uses RH, these two added inputs, Table 1, R7 and R8. It is neither a same-premise onset record nor a finite prime-count proof.')
        heads = ['Cell','Closed logarithmic interval','a','b','Margin']
    else:
        heading = '라마누잔 부등식 안에서 실제로 사용하는 부호 보존 연결'
        first = '아래 기호는 라마누잔 양을 octic 척도와 스펙트럼 가중치 w(t)에서 구분한다. 자연 계수는 K_R(L)=2w_R(L)다. 실제 유한 범위에서 정규화 차이 d_R는 명시적인 양수 입력 R8에 의해 비음수다. 정확한 분해로 ψ·높은 소수 거듭제곱·부호 보존 보정 D를 나눈다.'
        second = '앞에서 표시한 계수 차이 다항식 P₂₀은 더 강한 주항 하한 B_sharp를 준다. L≥27에서만 기존 1/1000을 3/8000으로 줄이므로 증가분은 정확히 1/1600이다. 실제 라마누잔 식을 두 차이로 전개하며 음의 이차항을 그대로 유지한다.'
        third = '닫힌 로그 셀 [l,u]에서 d_R(L)≥0이므로 자연 계수 대신 더 작은 상수 k≤2p_fac,20(u)≤K_R(L)를 사용할 수 있다. A_R(L)의 하한을 a, A_R(L−1)의 상한을 b로 둔다. 유한 li 차이 상한에서 d_R≤q를 얻으므로 음의 제곱항을 버리지 않고 −Q_R q²로 제한한다. 따라서 아래 명시적인 셀 검사를 얻는다.'
        fourth = '원래 아홉 입력의 개선은 위의 상관된 GM 쌍 상한을 B(k,L)에 사용하며 0≤k≤e다. 새 6060억 셀 다섯 개는 대신 스펙트럼 상한 B(k,L)=kP(L)+eP(L−1)을 사용한다. 이 경로에는 Nicolas·적분 Perron이 추가되며 GM 소거의 절약을 그대로 물려받는 것이 아니다. 더 작은 부호 보존 함수로 아래 여유를 증명한다. 모든 행에서 k=5199/2500이고 정규화 여유는 1/1000 이상이다.'
        last = 'a와 b는 각각 A_R(L)의 정확한 유리수 하한과 A_R(L−1)의 정확한 유리수 상한이다. 모든 셀은 27≤l≤L≤u≤42와 4800억≤e^L≤6400억을 만족한다. x=e^L에서 Büthe 표 1의 X=3200억 행은 [3200억,6400억]에서 하한 −0.88을 준다. y=x/e에서는 X=1600억 행을 [1600억,3200억]에 적용하여 상한 +0.68을 얻고 2 &lt; e &lt; 3으로 끝점 자격을 확인한다. 증명한 소수 거듭제곱 상한으로 a≤−0.88+lowerPowers(l,u), +0.68+upperPowers(l−1)≤b를 얻는다. R7은 유한 li 차이의 상한, R8은 양수성을 공급하며 원문의 유한 적용 범위를 유지한다.'
        final = '인증한 바깥 지수 끝점과 인접한 닫힌 셀로 6060억부터 6100억까지 모든 실수를 덮는다. 6100억 이상에서는 이전의 더 강한 전체 함수를 사용한다. 전역 6060억 결과는 R1–R9에 Nicolas·적분 Perron을 더한다. 국소 셀 연결은 RH·두 추가 입력·표 1·R7·R8을 사용한다. 동일 전제의 시작점 기록이나 유한 소수계수 증명은 아니다.'
        heads = ['셀','닫힌 로그 구간','a','b','여유']
    table = '<div class="tablewrap"><table><tr>'+''.join('<th>'+h+'</th>' for h in heads)+'</tr>'
    for i in range(5):
        table += '<tr><td>'+str(i)+'</td><td>'+m('ram_cell_interval_'+str(i))+'</td><td>'+m('ram_cell_a_'+str(i))+'</td><td>'+m('ram_cell_b_'+str(i))+'</td><td>'+m('ram_cell_margin')+'</td></tr>'
    table += '</table></div>'
    return section('ramanujan',heading,m('ram')+m('ram_coefficients')+m('ram_tail_terms')+ram_bridge(lang)+m('ram_retained_profile')+'<p>'+first+'</p>'+m('ram_signed_quantities')+'<p>'+second+'</p>'+m('ram_nonlinear_decomposition')+'<p>'+third+'</p>'+m('ram_cell_test')+'<p>'+fourth+'</p>'+table+'<p>'+last+'</p>'+m('ram_cell_eligibility')+'<p>'+final+'</p>'+m('ram606')+'<p>'+link('Solutions/RHOcticPush.v1/ramanujan/SharpBase.lean#L29','sharpBase_eq_full')+'; '+link('Solutions/RHOcticPush.v1/ramanujan/signed-spectral/SpectralRamCore.lean','actual signed cell transport')+'; '+link('Solutions/RHOcticPush.v1/ramanujan/signed-spectral/SpectralRam606Cells.lean#L212','bridge606')+'.</p>')


def tier_legend(lang):
    if lang == 'EN':
        entries = [
            ('A','Fully checked Lean theorem conditional on RH alone.'),
            ('B','Checked Lean theorem conditional on additional explicit analytic or literature propositions.'),
            ('C','Source-first program verification: actual executable source, verified execution model, correctness and verified outputs connected to the actual IEANTN theorem.'),
            ('D','Kernel-checked numerical certificate; this alone is not source-first PV.'),
            ('E','Written proof with independent checks.'),
            ('F','Exploratory numerical candidate.'),
            ('G','Open conjectural target.')]
        title = 'How to read the verification labels'
        note = 'B+D means that a source-conditional mathematical proof uses kernel-checked numerical leaves. It does not imply A or C. The exact remaining link is stated for each result.'
    else:
        entries = [
            ('A','RH만을 조건으로 하는 완전히 확인된 Lean 정리.'),
            ('B','명시적인 추가 해석·문헌 명제를 조건으로 하는 확인된 Lean 정리.'),
            ('C','Source-first 프로그램 검증: 실제 실행 소스, 검증된 실행 모델과 정확성 증명에서 검증한 출력을 실제 IEANTN 정리까지 연결.'),
            ('D','커널로 확인한 수치 인증서. 이것만으로 source-first PV가 되지는 않는다.'),
            ('E','독립 검토를 거친 서면 증명.'),
            ('F','탐색적인 수치 후보.'),
            ('G','열린 추측 또는 목표.')]
        title = '검증 등급을 읽는 방법'
        note = 'B+D는 문헌 조건을 명시한 수학 증명에서 커널로 검증한 수치 부분을 사용한다는 뜻이다. A나 C를 뜻하지 않는다. 각 결과에서 남아 있는 연결을 별도로 명시한다.'
    return ('<details open><summary>'+title+'</summary><ul>'+''.join(
        '<li><strong>'+key+'</strong> — '+value+'</li>' for key,value in entries)+
        '</ul><p>'+note+'</p></details>')

def metadata_graph(lang):
    folder = HERE/'network'
    if not (folder/'NETWORK_GRAPH.json').is_file():
        return '<p class="muted">'+('Final graph snapshot pending.' if lang=='EN' else '최종 그래프 스냅샷 작성 중.')+'</p>'
    graph = json.loads((folder/'NETWORK_GRAPH.json').read_text())
    pictures = [(folder/name).read_text() for name in ['NETWORK_FOCUS.svg','NETWORK_FEEDBACK.svg']]
    for picture in pictures:
        if re.search(r'<script|<foreignObject|\bon\w+\s*=|(?:href|src)\s*=', picture, re.I):
            raise SystemExit('Unexpected active or external graph content')
    stats = str(graph['node_count'])+' / '+str(graph['conclusion_count'])+' / '+str(graph['edge_count'])
    if lang=='EN':
        prose = ('<p>The complete current metadata census contains <strong>'+stats+
                 '</strong> node versions / typed conclusions / declared edges. Every endpoint is resolved. '
                 'This counts metadata, not completed proofs or checked source provenance. The displayed focus is '
                 'a coordinator-selected subset; the full inventory and exact selection rule are preserved separately. '
                 'Typed theorem bodies and their value dependencies are checked by separate Lean audits.</p>')
    else:
        prose = ('<p>현재 전체 메타데이터에는 노드 버전 / 타입이 있는 결론 / 선언된 연결이 각각 <strong>'+stats+
                 '</strong>개 있으며 모든 연결 끝점이 확인된다. 메타데이터 계수이며 완료된 증명이나 원문 검증 계수가 아니다. '
                 '표시한 그림은 총괄자가 고른 일부이고 전체 목록과 정확한 선택 기준을 별도로 보존했다. '
                 '실제 타입·증명 본문의 의존성은 별도의 Lean 감사로 검사한다.</p>')
    captions = ['Signed compensation to Ramanujan','Prime-square feedback to ordinary π'] if lang=='EN' else ['부호 보존 오차에서 라마누잔으로','소수 제곱 항 보정에서 일반 π로']
    diagrams = ''.join('<h3>'+caption+'</h3><div class="tablewrap network-diagram" tabindex="0" role="region" aria-label="Typed network focus">'+picture+'</div>' for caption,picture in zip(captions,pictures))
    scroll = 'Scroll horizontally to read every label.' if lang=='EN' else '가로로 스크롤하면 모든 이름을 읽을 수 있다.'
    return prose+'<p>'+scroll+'</p>'+diagrams+'<p>'+link(
        'Solutions/RHOcticPush.v1/reports/network/NETWORK_GRAPH.json','Full metadata inventory / 전체 목록')+'; '+link(
        'Solutions/RHOcticPush.v1/reports/network/DISPLAY_SELECTION.json','Ramanujan display selection / 라마누잔 그림 선택')+'; '+link(
        'Solutions/RHOcticPush.v1/reports/network/FEEDBACK_SELECTION.json','Feedback display selection / 보정 그림 선택')+'.</p>'

def measurements(lang):
    rows = status.get('run_measurements', [])
    if not rows:
        return ''
    heads = ['Scope (overlapping closures)','Measured time and scope','Actual memory','Owned disk','Status'] if lang=='EN' else ['범위 (서로 겹치는 소스 집합)','측정 시간과 범위','실제 메모리','실험 디스크','상태']
    table = '<div class="tablewrap"><table><tr>'+''.join('<th>'+x+'</th>' for x in heads)+'</tr>'
    for row in rows:
        table += '<tr>'+''.join('<td>'+html.escape(str(row[k]))+'</td>' for k in ['scope','time','memory','disk','status'])+'</tr>'
    return table+'</table></div>'

finite = status.get('finite_count_snapshot', {})
count_status_en = ('Full numerical proof accepted' if finite.get('final_accepted') is True
                   else 'Exhaustive numerical proof incomplete')
count_status_ko = ('전체 수치 증명 승인' if finite.get('final_accepted') is True
                   else '전체 수치 증명 미완료')
finite_en = ('<p><strong>Recorded count status:</strong> '+count_status_en+
             '; '+str(finite.get('arithmetic','not established'))+'/'+str(finite.get('total_arithmetic',2768))+
             ' arithmetic parts, '+str(finite.get('observed_live_workers','not established'))+
             ' observed live workers at '+html.escape(str(finite.get('snapshot_utc','not established')))+
             '. This is a dated snapshot, not a claim that workers remain live after publication.</p>')
finite_ko = ('<p><strong>기록한 계수 검증 상태:</strong> '+count_status_ko+
             '; 산술 부분 '+str(finite.get('arithmetic','미확인'))+'/'+str(finite.get('total_arithmetic',2768))+
             ', 확인한 실행 중 작업 '+str(finite.get('observed_live_workers','미확인'))+'개. 관측 시각 '+
             html.escape(str(finite.get('snapshot_utc','미확인')))+
             '. 날짜가 있는 스냅샷이며 발행 이후에도 작업이 실행된다는 뜻은 아니다.</p>')

finite_kernel_done = finite.get('final_accepted') is True
finite_source_done = status.get('finite_source_completion', {}).get('accepted') is True
if finite_source_done and not finite_kernel_done:
    raise SystemExit('Completed finite source status requires the accepted numerical count')
ieantn_consumer = status.get('ieantn_consumer', {})
if type(ieantn_consumer) is not dict or type(ieantn_consumer.get('accepted', False)) is not bool:
    raise SystemExit('IEANTN consumer status requires an explicit Boolean acceptance flag')
finite_ieantn_done = ieantn_consumer.get('accepted', False)
if finite_ieantn_done and not (finite_source_done and finite_kernel_done):
    raise SystemExit('Accepted IEANTN consumer requires accepted source completion and kernel count')
if status.get('FinalSourceDone') is True and not finite_ieantn_done:
    raise SystemExit('FinalSourceDone requires the accepted actual IEANTN consumer')

def finite_ieantn_completion(lang):
    if not finite_ieantn_done:
        if finite_source_done:
            text = ('The selected source/model/count chain is complete, but its connection to the actual IEANTN real-variable prime-counting theorem remains pending. The prepared four-source byte consumer and its controls have not all been accepted. This is not yet a completed source-first PV-backed IEANTN result.'
                    if lang == 'EN' else
                    '선택한 소스·모델·계수 연결은 완료했지만 실제 IEANTN 실수 변수 소수계수 정리까지의 연결은 아직 미완료다. 준비한 네 소스의 바이트 소비 정리와 대조 검사가 모두 승인된 것은 아니다. 아직 source-first PV로 뒷받침한 IEANTN 결과의 완료를 뜻하지 않는다.')
        else:
            text = ('The exact count uses a kernel-derived numerical witness. Cold source/model/count completion and the prepared four-source consumer of the actual IEANTN real-variable prime-counting definition remain separate acceptance gates. The byte consumer is not reported as compiled or verified until its append and controls pass.'
                    if finite_kernel_done else
                    'The exhaustive kernel count and the prepared four-source consumer of the actual IEANTN real-variable prime-counting definition remain pending. No completed source-first PV-backed IEANTN result is claimed.') if lang == 'EN' else (
                    '정확한 계수값의 수치 증거는 커널로 도출했다. 캐시 없는 소스·모델·계수 연결과 실제 IEANTN 실수 변수 소수계수 정의를 사용하는 네 소스 소비 정리는 별도 승인 단계다. 추가 컴파일과 대조 검사를 통과하기 전에는 이 바이트 소비 정리가 컴파일·검증되었다고 보고하지 않는다.'
                    if finite_kernel_done else
                    '전체 커널 계수 증명과 실제 IEANTN 실수 변수 소수계수 정의를 사용하는 네 소스 소비 정리가 아직 미완료다. source-first PV로 뒷받침한 IEANTN 결과가 완료되었다고 주장하지 않는다.')
        return card('Actual IEANTN consumer link pending' if lang == 'EN' else '실제 IEANTN 소비 정리 연결은 미완료',
                    '<p>'+text+'</p>', 'amber')
    for field in ['basis305_accepted', 'append_accepted', 'controls_accepted']:
        if ieantn_consumer.get(field) is not True:
            raise SystemExit('Accepted IEANTN consumer requires '+field)
    for field in ['basis_RESULT_sha256', 'append_RESULT_sha256', 'controls_RESULT_sha256']:
        if not isinstance(ieantn_consumer.get(field), str) or not re.fullmatch('[0-9a-f]{64}', ieantn_consumer[field]):
            raise SystemExit('Accepted IEANTN consumer requires exact '+field)
    if ieantn_consumer.get('numerical_witness') != 'KERNEL_DERIVED_EXISTING_EXHAUSTIVE_COUNT':
        raise SystemExit('IEANTN consumer numerical witness must remain kernel-derived')
    for field in ['new_native_verification', 'physical_trace_claim', 'whole_ISO_C_adequacy_claim',
                  'canonical_point_node_added', 'full_Ramanujan_finite_coverage']:
        if ieantn_consumer.get(field) is not False:
            raise SystemExit('IEANTN consumer scope requires false '+field)
    def checked_identity(field, expected_file, expected_declaration):
        row = ieantn_consumer.get(field)
        if type(row) is not dict or not {'file', 'declaration', 'physical_line', 'sha256'} <= set(row):
            raise SystemExit('Completed IEANTN consumer requires exact '+field)
        if row['file'] != expected_file or row['declaration'] != expected_declaration:
            raise SystemExit('Wrong written theorem identity for '+field)
        path = Path(row['file'])
        if path.is_absolute() or '..' in path.parts or type(row['physical_line']) is not int or row['physical_line'] < 1:
            raise SystemExit('Invalid written identity for '+field)
        current = REPO/path
        if not isinstance(row['sha256'], str) or not re.fullmatch('[0-9a-f]{64}', row['sha256']) or not current.is_file() or hashlib.sha256(current.read_bytes()).hexdigest() != row['sha256']:
            raise SystemExit('Source identity differs for '+field)
        lines = current.read_bytes().decode('utf-8').split('\n')
        if row['physical_line'] > len(lines) or not re.search(r'^\s*theorem\s+'+re.escape(row['declaration'].rsplit('.',1)[-1])+r'\b', lines[row['physical_line']-1]):
            raise SystemExit('Wrong physical declaration line for '+field)
        return link(row['file']+'#L'+str(row['physical_line']), row['declaration'])+' · SHA-256 <code>'+row['sha256']+'</code>'
    consumer_folder = 'Solutions/RHOcticPush.v1/ramanujan/count-feasibility/ieantn-consumer/'
    theorem = checked_identity('theorem_identity', consumer_folder+'IEANTNCountConsumer.lean',
        'RHOcticPush.IEANTNCount.primeCounting_fixed_point')
    byte_lemma = checked_identity('byte_lemma_identity', consumer_folder+'WordBytesBounded.lean',
        'RHOcticPush.IEANTNCount.wordBytes_injective_below')
    sources = ieantn_consumer.get('source_code', [])
    if type(sources) is not list or len(sources) != 2 or len({row.get('file') for row in sources if type(row) is dict}) != 2:
        raise SystemExit('Completed IEANTN consumer requires both exact C source identities')
    source_links = []
    for row in sources:
        if type(row) is not dict or not {'file', 'sha256'} <= set(row) or not isinstance(row['file'], str):
            raise SystemExit('Invalid IEANTN consumer C source identity')
        path = Path(row['file'])
        if path.is_absolute() or '..' in path.parts or path.suffix != '.c' or not isinstance(row['sha256'], str) or not re.fullmatch('[0-9a-f]{64}', row['sha256']) or not (REPO/path).is_file() or hashlib.sha256((REPO/path).read_bytes()).hexdigest() != row['sha256']:
            raise SystemExit('Wrong actual C source bytes for IEANTN consumer')
        source_links.append(link(row['file'])+' · SHA-256 <code>'+row['sha256']+'</code>')
    if {row['sha256'] for row in sources} != {
            '85326ecb93d86c693d980352ebde59a350eef89b4f367c88b65fa88f58d991dd',
            '011738a2ee9879f25d3b24bf7b134ba20825105872a3e3d26d1a082db72140f7'}:
        raise SystemExit('IEANTN consumer requires the unchanged actual counter and high-driver sources')
    if lang == 'EN':
        title = 'Verified program outputs consumed by the actual IEANTN theorem'
        text = ('The independently kernel-verified count identifies the eight bytes of a constructed execution of the two actual C sources in the formal model. Generic program correctness applied to that same execution identifies its output with the bytes of the mathematical prime count. Injectivity of the eight-byte encoder on the proved bounded range equates the values; the existing floor-and-cast definition then gives the actual real-variable IEANTN theorem. This source-first PV chain uses a KERNEL-DERIVED numerical witness. The ordinary compiled execution is recorded separately under the listed platform contracts. No formal physical trace, general ISO-C adequacy theorem, canonical point node or full finite Ramanujan coverage is claimed.')
    else:
        title = '검증한 프로그램 출력을 실제 IEANTN 정리가 사용'
        text = ('독립적인 커널 계수 증명으로 두 실제 C 소스의 형식 실행 모델에서 구성한 실행의8바이트 출력을 식별한다. 같은 실행에 프로그램의 일반 정확성 정리를 적용하면 그 출력은 수학적 소수 개수의 바이트와 같다. 증명한 범위에서8바이트 인코딩의 단사성으로 두 값을 일치시키고, 기존 바닥 함수·형변환 정의를 통해 실제 IEANTN 실수 변수 정리를 얻는다. 이 source-first PV 연결의 수치 증거는 커널에서 도출한 것이다. 실제 컴파일 실행의 관측은 명시한 플랫폼 계약 아래 별도로 기록한다. 물리 실행 추적·일반 ISO-C 적합성 정리·새 정식 한 점 노드·전체 유한 라마누잔 구간 검증을 주장하지 않는다.')
    provenance_title = 'Exact source and theorem identities' if lang == 'EN' else '정확한 소스·정리 식별 정보'
    provenance = '<details><summary>'+provenance_title+'</summary><p>'+theorem+'</p><p>'+byte_lemma+'</p><p>'+'; '.join(source_links)+'.</p></details>'
    return card(title, m('finite_count')+'<p>'+text+'</p>'+provenance, 'green')

def finite_completion(lang):
    if not finite_kernel_done:
        return ''
    if not finite_source_done:
        title = 'Exact numerical theorem accepted; source completion separate' if lang == 'EN' else '정확한 수치 정리 승인; 소스 연결은 별도'
        text = ('The complete kernel certificate proves the displayed fixed count. The cold foundation and final source-indexed output consumer remain separate acceptance gates.'
                if lang == 'EN' else '전체 커널 인증서로 아래 고정 계수값을 증명했다. 캐시 없는 기반 재현과 최종 소스 인덱스 출력 소비 정리의 승인은 별도 단계다.')
        return card(title, m('finite_count')+'<p>'+text+'</p>', 'blue')
    info = status['finite_source_completion']
    identities = info.get('captured_sources', [])
    if len(identities) != 3 or any(not {'file', 'declaration', 'physical_line', 'sha256'} <= set(row) for row in identities):
        raise SystemExit('Completed finite source status requires three exact compiled source identities')
    references = '; '.join(link(row['file']+'#L'+str(row['physical_line']), row['declaration']) for row in identities)
    if lang == 'EN':
        title = 'Selected C source, execution model and exact output connected'
        body = ('<p>The complete fixed-count proof and the source-indexed mathematical consumer have passed. The actual cold foundation, remaining original arithmetic proofs, unchanged final theorem and new consumer are recorded separately. The final proof constructs a modeled execution of both actual C source texts and identifies its eight little-endian output bytes; a separate theorem covers every successful modeled run. The proof-value audit checks actual use of both independent source-grammar proofs, the counter correctness theorem and the exact numerical count.</p>'
                '<p>This completes the selected source/model/output chain under its stated model-applicability, compiler, headers, ABI/runtime, stdio/OS and hardware contracts. It is not a full ISO-C adequacy proof or a formal physical-machine trace. The point count does not supply the entire finite interval coverage needed for an independent Ramanujan onset proof.</p>'
                '<p>The actual high-result route composes the current campaign’s pure arithmetic proofs with a freshly compiled cold complement. The standalone source-only command regenerates the full locked workload; its bounded control was executed separately. The final status and receipts identify the precise executed route, elapsed-time scope, memory, disk and optimization-mode controls.</p>')
    else:
        title = '선택한 C 소스·실행 모델·정확한 출력의 연결 완료'
        body = ('<p>전체 고정 계수 증명과 소스 인덱스 수학 소비 정리가 통과했다. 실제 캐시 없는 기반, 나머지 원래 산술 증명, 보존한 최종 정리와 새 소비 정리를 별도로 기록한다. 최종 증명은 실제 C 텍스트 두 개의 모델 실행을 구성하고 little-endian 출력8바이트를 특정하며, 별도 정리는 모든 성공한 모델 실행을 다룬다. 증명 본문 감사로 독립 소스 문법 증명 두 개, 계수 프로그램의 정확성 정리와 정확한 수치 계수값을 실제로 사용하는지 확인한다.</p>'
                '<p>명시한 모델 적용·컴파일러·헤더·ABI/런타임·stdio/OS·하드웨어 계약 아래 선택한 소스·모델·출력 연결을 완료한 것이다. 전체 ISO-C 의미의 적합성이나 물리 기계 추적을 형식화한 것은 아니다. 이 한 점의 계수값이 라마누잔 시작점을 독립적으로 증명하는 데 필요한 전체 유한 구간을 덮지는 않는다.</p>'
                '<p>실제 높은 입력 결과는 이번 연구의 순수 산술 증명과 새로 컴파일한 캐시 없는 나머지 기반을 결합한다. 독립 소스 전용 명령은 고정된 전체 작업을 재생성하며 작은 대조 실행은 별도로 수행했다. 최종 상태와 영수증에 실제 실행 경로·시간 범위·메모리·디스크·최적화 모드 대조를 명시한다.</p>')
    return card(title, ('' if finite_ieantn_done else m('finite_count'))+body+'<details><summary>'+('Compiled source identities' if lang == 'EN' else '컴파일한 소스 식별 정보')+'</summary><p>'+references+'.</p></details>', 'green')

finite_executive_en = (card('Actual IEANTN output consumer completed',
    '<p>The accepted four-source append and its controls connect the same-run verified output bytes to the actual IEANTN real-variable prime-counting theorem. The numerical witness is kernel-derived. No new native verification, physical trace, whole ISO-C adequacy, canonical point node or full finite Ramanujan coverage is claimed.</p>', 'green') if finite_ieantn_done else card('Source/model/count complete; IEANTN link pending',
    '<p>The fixed high-count source/model/output chain is complete at the documented trust boundary. The prepared four-source link to the actual IEANTN real-variable theorem still needs acceptance with its controls. Source/model/count completion alone is not a completed source-first PV-backed IEANTN result.</p>', 'amber') if finite_source_done else
    card('What remains incomplete','<p>The full finite prime-count source-first verification route remains open. This is not a claim to have verified every numerical program in IEANTN. New source grammar and whole-main model proofs are complete for the counter and high driver; the exact finite-output proof and compiled-run/model applicability boundaries are reported separately below.</p>', 'amber'))
finite_executive_ko = (card('실제 IEANTN 출력 소비 정리 완료',
    '<p>승인한 네 소스의 추가 증명과 대조 검사가 같은 실행의 검증 출력 바이트를 실제 IEANTN 실수 변수 소수계수 정리까지 연결한다. 수치 증거는 커널로 도출했다. 새 native 검증·물리 추적·전체 ISO-C 적합성·정식 한 점 노드·전체 유한 라마누잔 구간 검증을 주장하지 않는다.</p>', 'green') if finite_ieantn_done else card('소스·모델·계수 완료; IEANTN 연결은 미완료',
    '<p>명시한 신뢰 경계에서 고정된 높은 입력의 소스·모델·출력 연결을 완료했다. 실제 IEANTN 실수 변수 정리까지의 네 소스 연결과 대조 검사는 아직 승인이 필요하다. 소스·모델·계수 연결 완료만으로 source-first PV로 뒷받침한 IEANTN 결과가 완료되었다고 보지 않는다.</p>', 'amber') if finite_source_done else
    card('남아 있는 작업','<p>전체 유한 소수계수 계산의 source-first PV는 미완료다. IEANTN의 모든 수치 프로그램을 검증했다고 주장하지 않는다. 계수 프로그램과 높은 입력 드라이버의 새 소스 문법·전체 main 모델 증명은 완료했다. 고정된 유한 출력 증명과 실제 컴파일 실행에 대한 모델 적용 경계는 아래에서 별도로 설명한다.</p>', 'amber'))

octic_done = status.get('octic_certificate_accepted') is True
proof_replay = status.get('complete_new_source_replay_accepted') is True
badge_en = 'Completed numerical and analytic bridge' if octic_done else 'Numerical certificate gate still open'
badge_ko = '수치·해석 연결 증명 완료' if octic_done else '수치 인증서 최종 검증 진행 중'
conditional_en = ('The two actual Fourier moment caps have been proved by kernel checking and are constructed inside the final consumer. '
                  'The original octic-specific analytic assumptions are discharged. ' if octic_done else
                  'The analytic adapters below compile, but the full kernel certificate has not yet been accepted. '
                  'Every octic conclusion in this draft remains conditional on the two actual moment caps. ')
conditional_en += ('RH and three general published inputs remain explicit: Green’s smooth explicit formula, '
                   'Nicolas’s full spectral summability/bound and BPT’s off-ordinate zero-count bound. '
                   'These literature theorems, including external computations used by BPT, are not proved from Mathlib in this campaign.')
conditional_ko = ('실제 푸리에 모멘트 상한 두 개를 커널로 검증하고 최종 정리 안에서 직접 구성했다. '
                  '기존 octic 전용 해석 가정은 모두 해소했다. ' if octic_done else
                  '아래 해석 연결 정리는 컴파일되지만 전체 커널 인증서는 아직 승인되지 않았다. '
                  '이 초안의 octic 결론에는 실제 모멘트 상한 두 개가 여전히 조건으로 남는다. ')
conditional_ko += ('RH와 일반 문헌 정리 세 개는 명시적 가정이다. Green의 매끄러운 명시적 공식, '
                   'Nicolas의 전체 스펙트럼 합 가능성·상한, BPT의 영점 높이를 피한 계수 상한이다. '
                   'BPT가 사용한 외부 수치 계산까지 Mathlib에서 새로 증명한 것은 아니다.')

font_bytes = (HERE/'fonts/STIXGeneral.ttf').read_bytes()
font_meta = json.loads((HERE/'fonts/IDENTITY.json').read_text())
if hashlib.sha256(font_bytes).hexdigest() != font_meta['sha256']:
    raise SystemExit('Wrong embedded math font bytes')
font_style = '@font-face{font-family:ReportSTIX;src:url(data:font/ttf;base64,'+base64.b64encode(font_bytes).decode()+')}math{font-family:ReportSTIX,serif}'
font_license = (HERE/'fonts/LICENSE.txt').read_text()
font_style += '.network-diagram svg{display:block;width:1350px;max-width:none;height:auto}'
font_style += 'p,li,a,summary{overflow-wrap:anywhere}'
css = font_style + '''body{margin:0;background:#f4f6fa;color:#192334;font:16px/1.65 system-ui,sans-serif}main{max-width:1120px;margin:auto;padding:30px 20px 70px}h1{font-size:2.1rem;line-height:1.2}h2{font-size:1.55rem;margin-top:2.7rem;border-bottom:2px solid #cbd4e3;padding-bottom:8px}h3{font-size:1.12rem;margin:0 0 10px}p{margin:12px 0}a{color:#164fa3;text-underline-offset:3px}nav{display:flex;gap:14px;flex-wrap:wrap;padding:12px 0}nav a{padding:5px 0}.card{background:white;border:1px solid #d7dfeb;border-left:5px solid #316cbd;border-radius:9px;padding:18px;margin:14px 0}.green{border-left-color:#23835a}.amber{border-left-color:#c8840b}.red{border-left-color:#b83d3d}.pill{display:inline-block;border-radius:20px;background:#e1eaf7;color:#143e76;padding:4px 12px;font-weight:650;font-size:.9rem}.muted{color:#536177}.formula{background:#fafbfe;border-radius:5px;padding:12px 8px;overflow-x:auto;margin:13px 0}.formula math{font-size:1.06rem}pre{white-space:pre-wrap;overflow-wrap:anywhere;font-size:.82rem}table{border-collapse:collapse;width:100%;background:white}th,td{padding:11px 12px;border:1px solid #d6deea;text-align:left;vertical-align:top}th{background:#e8eef7;font-weight:700}.tablewrap{overflow-x:auto}code{font-size:.85em;overflow-wrap:anywhere}details{background:#fff;border:1px solid #d7dfeb;border-radius:7px;padding:12px;margin:14px 0}summary{cursor:pointer;font-weight:650}summary:focus-visible,a:focus-visible{outline:3px solid #e0911c;outline-offset:3px}.chain{display:flex;flex-wrap:wrap;gap:8px}.chain span{border:1px solid #b6c8e3;background:#eaf1fb;padding:8px 12px;border-radius:5px}footer{border-top:1px solid #ccd5e3;margin-top:40px;padding-top:16px;font-size:.9rem}@media(max-width:600px){main{padding:22px 12px}h1{font-size:1.65rem}.card{padding:14px}th,td{min-width:120px;padding:9px}.formula math{font-size:.92rem}}@media print{body{background:white}main{max-width:none;padding:0}.card,details{break-inside:avoid}a{color:inherit}nav{display:none}}'''

ram_inputs = json.loads((CAMPAIGN/'ramanujan/RESULTS.json').read_text())['source_inputs']
ram_spectral_inputs = ram_inputs + ['NicolasContinuation.SourceNicolas119',
    'SourceIntegratedPsi (normalization from IntegratedPerron.v1.formula proved)']
ram_bands = [('607,000,000,000','0.0001'),('610,000,000,000','0.001'),
             ('619,000,000,000','0.01'),('620,000,000,000','0.0125'),
             ('640,000,000,000','Exact inherited nonlinear finalMargin / 기존 비선형 finalMargin 그대로')]
rows = ''.join('<tr><td>'+a+'</td><td>'+b+'</td></tr>' for a,b in ram_bands)
source_links = (
 source('https://people.maths.ox.ac.uk/greenbj/papers/primenumbers.pdf','Green, Definition 7.1 / Theorem 7.1, printed p.40; decay Lemma 7.1, pp.43–44')+'; '+
 source('https://maths-people.anu.edu.au/~brent/pd/rpb274-final.pdf','BPT, Corollary 1, p.743; Lemma 2, p.744; multiplicity, p.754')+'; '+
 source('https://arxiv.org/pdf/1202.0729v2','Nicolas, equations (1.19), (2.19)')+'; '+
 source('https://arxiv.org/pdf/1312.4465v4','Grenié–Molteni, Theorem 1.1, rational-field case')+'.')

contents_en = []
contents_en.append(section('results','Results and the exact proof boundary',
 '<p>This research closes the actual octic and Box analytic proof obligations, derives stronger prime-counting functions, and connects them to arithmetic consumers. RH remains a hypothesis. The strongest analytic results also take explicitly named general literature propositions; those source theorems are not silently promoted into new Lean axioms.</p>'+
 '<p class="muted">Wide formulas and tables scroll horizontally. On a keyboard, focus the formula or table with Tab, then use the arrow keys.</p>'+
 m('arithmetic_notation')+early_reader_context('EN')+
 '<p>Every prime sum is over actual primes, and the prime-power sums include every positive integer exponent. The symbol li denotes the principal-value logarithmic integral; it differs from the offset integral Li₂ by the constant li(2). That constant is paid explicitly in every ordinary-prime transfer. Throughout, L=log(x) or L=log(u), as specified beside each bound. Except in Green’s explicitly marked all-zero formula, ρ ranges over distinct nontrivial zeta zeros; mρ is the multiplicity and γρ the imaginary part. The symbol γ denotes Euler’s constant. The Box section defines the first Stieltjes constant γ₁ by its actual limiting sequence.</p>'+
 card('A stronger full PNT bound, with the same four inputs',m('feedback_clean')+
      '<p>The complete bound is stronger than this convenient corollary. It preserves the previous entire exp(35) ray and decreases its whole right side by more than1.67√x/log(x) for every real x≥exp(100). The exact inputs are RH, general integrated Perron, Nicolas and BPT. The new prime-square argument is acyclic: first π≤J, then a lower-scale J upper bound, then a sharper prime-power correction. Four source files,39 proof roots, independent mathematical reviews and a source-fresh718-module closure passed. This is mathematical kernel verification, not new source-first PV.</p>','green')+
 card('Original 2.15 target: '+badge_en, '<p>'+conditional_en+'</p>'+m('fixed')+
      '<p>The set excludes both endpoints. Separate theorems prove the ordinary prime-counting difference. '
      'Every argument is real and the domain is the entire ray; it is not a collection of numerical samples.</p>', 'green' if octic_done else 'amber')+
 card('An intermediate PNT corollary at the same onset',m('pnt_clean04')+m('pnt_clean_gain')+
      '<p>This strengthens the earlier displayed1/3 corollary. The complete new Box function remains stronger than this simplified statement. Its exact inputs are RH, general Perron, Nicolas and BPT; the scalar comparison introduces no GM or Büthe premise. Both source files and an independent12-identity review passed; a source-fresh two-module replay above the validated712 foundation also passed.</p>','green')+
 card('Stronger quantitative Ramanujan frontier',m('ram')+
      '<p>All nine original inputs are preserved. The new proof cancels a shared signed integral before bounding it, '
      'rather than subtracting two unrelated absolute error bars. The degree-20 main-term remainder is tightened '
      'from 1/1000 to 3/8000 on the actual logarithmic domain. Above 640 billion the full old nonlinear profile is retained.</p>'+
      '<div class="tablewrap"><table><tr><th>Every real x at or above</th><th>Proved normalized margin</th></tr>'+rows+'</table></div>'+ 
      '<details><summary>The entire retained nonlinear Ramanujan function</summary>'+m('ram_coefficients')+m('ram_tail_terms')+ram_bridge('EN')+m('ram_retained_profile')+'<p>These are the exact factorial coefficients, remainder and two retained maxima from the original640-billion consumer; the proof does not replace that function with a coarse constant.</p></details>'+
      '<p>'+link('Solutions/RHOcticPush.v1/ramanujan/RamStrongOverlay.lean','Actual full consumer')+'.</p>', 'green')+
 card('A separate spectral-to-Ramanujan synthesis',m('ram606')+
      '<p>The actual signed spectral profile now supplies a normalized margin of at least0.001 from606 billion. Five kernel-checked closed real intervals join606 to610 billion; the exact previous stronger profile is retained above610 billion. This uses the full function P at both heights, not the0.055 coefficient whose onset is higher. The global premise set is strictly larger: the old nine inputs plus Nicolas and general Perron, eleven in total. It is not a same-premise improvement or a published-onset record. All four source files, independent44-identity review and the additive source-fresh723 closure have passed.</p>','green')+
 card('Other completed mathematics','<p>The evolved GM function improves the full ordinary-prime-counting envelope; '
      'correlated Nicolas weights give actual multi-height Euler-product inequalities; the Box work proves full Fourier '
      'reconstruction and a justified Mellin series/integral interchange, while improving an existing moment cap.</p>', 'blue')+
 card('Actual signed spectral target and stronger coefficient',m('spectral_profile')+m('spectral_actual')+'<p>These are the unchanged arithmetic compensation error and the entire real rays. The proof retains complex phases through integration by parts, then uses Nicolas’s positive inverse-square zero mass. Exact inputs are RH, Nicolas’s spectral summability/bound and the general integrated Perron formula; GM and Büthe error estimates are not assumptions.</p>','green')+
 finite_executive_en))

contents_en.append(section('octic','The octic proof: an infinite analytic argument and a finite numerical kernel gate',
 '<p>The physical test kernel is compactly supported. Its actual transform, rather than a separately invented numerical function, '
 'is the object integrated and estimated in Lean.</p>'+m('kernel')+m('moments')+
 '<div class="chain"><span>Actual source explicit formula</span><span>Smooth octic approximations</span><span>Mellin/Fourier normalization</span>'
 '<span>All zeros + multiplicities</span><span>Full BPT integral</span><span>Certified moments</span><span>Prime powers + strict prime count</span></div>'+
 '<h3>Why the explicit formula adapter is substantive</h3><p>Let φ_j be the normalized even nonnegative smooth bump of radius ε_j below. Its convolution k_j tends to k. Here L is the logarithmic center of the kernel window, rather than automatically log(u); the all-real coverage argument selects L so that a=u. The weight w_j is zero on nonpositive arguments. Taking W_j(t)=w_j(2t) and X=2 meets Green’s support convention. '
 'The proof establishes support, nonnegativity, compactness, smoothness and pointwise convergence. It proves the actual Mellin '
 'normalization and its critical-line Fourier frequency, identifies all proper zeros and their orders, and passes to the '
 'original weighted Mangoldt population through genuine dominated limits. Trivial zeros are summed with their exact geometric series.</p>'+
 m('octic_physical')+m('mellin')+m('green')+'<p>'+source_links+'</p>'+
 '<h3>The entire infinite zero sum</h3><p>Write N(T) for the multiplicity-weighted count of positive ordinates in the closed interval (0,T]. The published source is used only off ordinates; the displayed all-height closed-count estimate is the adapter output. The BPT bridge first bounds arbitrary finite subsums, then proves summability and takes '
 'the actual infinite limit. The required regularity, weighted integrability and vanishing boundary term follow from the proved '
 'decay of the actual Fourier transform and its derivative. Conjugate pairing and the low-height exclusion include multiplicity '
 'and possible real-axis packets; no unverified finite zero table stands in for an infinite tail.</p>'+m('zero_count_def')+m('bpt')+m('infinite')+'<p>This generic infinite-tail display requires a≥2π and the linked Stieltjes regularity, weighted integrability, and vanishing-boundary hypotheses; the actual scaled octic transform satisfies all of them in the cited bridge.</p>'+
 '<p>The final paper does not separately define its counting convention at an ordinate jump. The new Lean endpoint adapter therefore '
 'uses the published bound only away from ordinates. Actual local finiteness gives an immediate right interval with constant closed count; '
 'continuity then transfers the inequality to every closed endpoint, including 2π, with no extra constant.</p>'+
 '<h3>Quadrature handles Fourier zeros correctly</h3>'+m('quadrature')+m('derivatives')+
 '<p>The absolute value need not be twice differentiable. Convex quadratic perturbations of the underlying smooth transform give '
 'the displayed absolute-value trapezoid bound, including cells crossing a zero. The mesh covers 0–10 in steps of 0.01, '
 '10–100 in steps of 0.05 and 100–1000 in steps of 0.2. Acceptance requires every one of the 7,301 endpoints to pass the kernel checker. '
 'The curvature bound switches to 40/a² on cells starting at a≥10.</p>'+m('certsum')+m('momenttails')+
 '<p>The negative interval from 0 to 1 is retained in the logarithmic moment. Dropping it would lose the target. '
 'Endpoint Fourier enclosures, logarithmic enclosures, upward-rounded cell budgets and their integer totals are separate checked links.</p>'+
 m('endpoint')+'<details><summary>Optional history: the numerical period reducer</summary><p>The supplemental checker uses a centered period choice. Its correctness theorem applies to every integer shift, so soundness does not depend on the shift heuristic. The predecessor’s downward period choice sometimes fell back to [−1,1], which was sound but too coarse. Original LeanCert sources are unchanged. This is kernel certificate checking (D), not source-first PV.</p></details>'+
 '<p>The full-range scalar proof turns those actual moments into the original zero bound, preserving the fixed prime-power '
 'budget 0.0155 and the family budget 0.058.</p>'+m('octic_zero_def')+m('zerofixed')+m('octic_count_bridge')+
 '<p>'+link('Solutions/RHOcticPush.v1/octic/OcticEndpointSourceConsumer.lean','Strict endpoint source consumer')+'; '+
 link('Solutions/RHOcticPush.v1/moments/OcticMomentAssembly.lean','Actual complete-moment assembly')+'; '+
 link('Solutions/RHOcticPush.v1/moments/endpoint/OcticFiniteCaps.lean','Finite certificate-to-integral interface')+'. '
 'In the last display S_p is the weighted prime population and S_Λ the weighted Mangoldt population. Since0≤k≤1 and log(t)/√t decreases for log(t)≥2, the upper inequality converts the analytic lower bound into an actual prime cardinality. Continuous forward coverage supplies a=u and b≤u+C√u log(u), and the scalar margin produces the strict bound on that whole real ray. No independent Blueprint label exists for these new internal lemmas; their public correspondence is the PrimeKernelInputs, '
 'PrimeInterval and PrimeQuantile node chain.</p>'))

contents_en.append(section('frontier','Stronger bounds and matched comparisons',
 '<p>The same fixed certificate arrays yield the stronger actual caps below and a separate sharper frontier. Its status is the same as the numerical gate above; '
 'the original preserved 2.15 statement and its constants remain preserved.</p>'+m('strongcaps')+octic_budget_bridge('EN')+m('strongfamily')+m('strongfixed')+m('strongsmall')+m('narrowest')+
 '<p>The smaller-width result has a different lower-order population allowance; it is not claimed to dominate the fixed-width theorem '
 'in every coordinate. At width 2.15 the population improvement is compared at exactly the same width and onset. '
 'The 2.149 result has a fixed positive leading excess over one. By contrast, a bound of only 1+4.2/log(u) '
 'would not establish a limiting normalized count strictly above one.</p>'+
 '<p>The following f_j and f_Box are our own complete envelopes, used to compare with the cited theorems. They are not definitions attributed to Lee–Nosal.</p>'+m('boxfunctions')+
 '<div class="tablewrap"><table><tr><th>Comparator</th><th>Actual scope</th><th>Permitted conclusion</th></tr>'+
 '<tr><td>'+source('https://arxiv.org/pdf/2005.02393v3','Chirre–Pereira Júnior–de Laat, §1.3, pp.1–2')+'</td><td>'+m('cpdl')+'</td><td>Asymptotic family; α=1 gives a coefficient below 2.5074. Compare the entire population target, not only a one-prime gap.</td></tr>'+
 '<tr><td>'+source('https://arxiv.org/pdf/1708.04122v2#page=5','Carneiro–Milinovich–Soundararajan, Theorem5, printed p.5')+'</td><td>'+m('cms_one_prime')+'The same paper also states an asymptotic prime-population family.</td><td>One prime in a shorter interval is a different observable from more than √u primes.</td></tr>'+
 '<tr><td>'+source('https://arxiv.org/pdf/1407.1901','Dudek–Platt, Theorem 1.3 and Lemma 3.4')+'</td><td>Last integer Ramanujan counterexample 38,358,837,682 under RH; finite real-range verification is part of the paper.</td><td>607 billion is not a new published onset record. The new result supplies a formal quantitative margin profile and signed transfer.</td></tr>'+
 '<tr><td>'+source('https://arxiv.org/html/2312.05628v4','Lee–Nosal v4, Theorems 1.1 and 1.2')+'</td><td>'+m('lee_strong')+m('lee')+'</td><td>The complete new Box function is strictly below both displayed normalized ψ functions for every real log(x)≥35. This unconditional scalar comparison is proved in BoxVsLee.lean; the actual Box theorem has RH plus its three explicit general source inputs. The additional height-dependent Lemma3.3 family and finite-range competitors prevent a global best-known claim.</td></tr>'+
 '<tr><td>'+source('https://arxiv.org/pdf/1202.0729v2','Nicolas, equation (2.19)')+'</td><td>Actual scaled logarithmic Euler-product profile, x&gt;599.</td><td>The new joint/existential result is compared with the sum of these full profiles, not marketed as a one-point constant record.</td></tr></table></div>'+
 '<p>A global best-known-result claim is not established. The report records the primary families inspected, exact observables '
 'and remaining literature/formalization boundaries. It does not transfer discoveries retroactively to earlier frozen exposure arms.</p>'+m('box_lee_comparison')+'<p>'+link('Solutions/RHOcticPush.v1/comparisons/BoxVsLee.lean','All-real comparison with both exact displayed Lee–Nosal functions')+'. The comparison is of complete envelopes, not actual measured errors or a finite grid.</p>'))

contents_en.append(section('additional-literature','Further whole-function literature limits',
 '<p>'+source('https://arxiv.org/html/2403.11814v4','Lee v4, Theorem1.1 (25 July2026)')+' gives the following full θ family. It can improve the large-C part of our family; no whole-function domination is claimed.</p>'+m('lee_L')+m('lee_short')+
 '<p>'+source('https://doi.org/10.1093/qmath/haad031','Lee, Theorem3.2 and Table4, printed p.1515')+' states the stronger late-onset family below. As an inference, two consecutive windows would yield a rich-prime coefficient arbitrarily close to2 at sufficiently late onset. A proof-passage audit remains unresolved, so we retain the published claim as a comparison limitation and make no asymptotic record claim.</p>'+m('lee_published')+
 '<p>For absolute ψ errors, '+source('https://arxiv.org/html/2312.05628v4#S3.SS2','Lee–Nosal v4, Lemma3.3')+' is another printed complete function. Its height-dependent formula must be considered in addition to Theorems1.1 and1.2. The numerical normalization used in its proof requires the separate correction below; we do not infer that the final published PNT theorems are false.</p>'+m('lee_T')+m('lee_lemma')+
 card('Confirmed source comparison: the reciprocal-zero sum counts both signs',
 '<p><strong>Actual Lean and Blueprint.</strong> '+link('Solutions/RHOcticPush.v1/comparisons/ZeroInversePaired.lean','actual_both_sign_inverse_lower')+' proves the full finite multiplicity-weighted sum is greater than28, conditional only on the general BPT count bound. The finite zero-set identity and conjugate pairing are proved. There is no standalone Blueprint statement for this new comparison; the exact network correspondence is '+link('IEANTN/Nodes/ZeroCount/v1/Conclusions.lean','ZeroCount.v1.zetaNClosed')+' and '+link('IEANTN/Vocabulary/Zeta.lean','Vocabulary.Zeta.zetaZeroesSum')+'.</p>'+
 '<p><strong>Named primary source, then antecedent.</strong> '+source('https://arxiv.org/pdf/2312.05628v4#page=4','Lee–Nosal v4, §2 equation(10), printed p.4')+' prints the first bound. Its cited input, '+source('https://arxiv.org/pdf/2204.02588v3#page=5','Fiori–Kadiri–Swidinsky v3, equation(2.4)/Table1, p.5')+', supplies the positive-only sum in the second line.</p>'+m('lee_eq10_printed')+m('fks_table_positive')+
 '<p><strong>Concrete mismatch and impact.</strong> The absolute ordinate in the printed Eq.(10) includes both conjugate zeros. The cited table constant counts positive ordinates. Independently of that table’s computation, BPT and elementary integration already contradict the printed both-sign upper bound:</p>'+m('positive_inverse_derivation')+
 '<p>The kernel proof uses no RH, finite zero table or native execution fact. A second independent source/Lean review and recompilation confirmed this precise mismatch. It does not refute the paper’s final PNT conclusions. We have not proved a replacement closed-endpoint upper bound; the cited table has a strict-open cutoff. The printed Lemma3.3 row is not promoted into the verified network, and the published final theorem families remain comparison limitations.</p>','amber')))

contents_en.append(section('nl-comparison','Comparing both objectives with the original 2.43 parabolic window',
 '<p>The earlier archived written argument used the following complete parabolic window. Its width tends to the coefficient2.43; at finite heights, comparing that number alone would discard the logarithmic terms. We therefore compare the actual endpoints and count functions at the same left endpoint.</p>'+m('nl_parabolic_full')+m('nl_matched_comparison')+
 '<p>A pure Lean proof establishes both scalar comparisons for every real L≥24, using a tangent bound for log(L),0&lt;δ≤0.0003 and sinh(δ)≥δ. A separate arithmetic consumer applies the actual new octic theorem and proves the old count objective in a strictly shorter interval. Its additional condition a≥exp(24) is essential: a at L=24 is slightly smaller than exp(24).</p>'+
 '<p>The old analytic argument remains a written, independently reviewed result; this comparison does not retroactively formalize the original written-comparison arm. The new arithmetic consumer explicitly uses RH, Green, Nicolas and BPT. The original and new transitive source packages differ, so this is a quantitative width/count comparison on the common eligible domain, with that assumption distinction retained.</p>'+
 '<p>'+link('Solutions/RHExposureStudy.v1/locked/NL_RH/files/Intervals.md','Original locked NL parabolic statement and proof')+'; '+link('Solutions/RHOcticPush.v1/comparisons/NLParabolicComparison.lean','Whole-function scalar comparisons')+'; '+link('Solutions/RHOcticPush.v1/comparisons/NLParabolicConsumer.lean','Actual strict-prime consumer')+'.</p>'))

contents_en.append(section('gm','Recovering information lost by separate error bars',
 '<p>This section compares the earlier GM method retrospectively. Its error E is exactly the signed compensation D defined above.</p>'+'<p>Let J denote Riemann’s prime-power counting function. Its difference from the ordinary prime-counting function is proved '
 'separately, with actual prime-power and offset-integral corrections.</p>'+m('gm_error_alias')+m('gmoldnew')+m('gmminimum')+
 '<p>The new b=5 function is not uniformly smaller near its first eligible point: its paid anchor constant is larger. '
 'Taking the minimum preserves the old full domain. A separate theorem proves a strict gain greater than 1/2 on every x≥exp(24).</p>'+
 m('pitransfer')+
 '<p>The prime-counting envelope is genuinely consumed. Its gain is measured relative to the same old ordinary-π envelope '
 'including the same offset correction; common minima elsewhere may mask that component gain.</p>'+
 '<h3>The pair estimate that enables the Ramanujan advance</h3><p>Here K is a constant weight in [0,e]. The Ramanujan application below chooses a lower bound for its natural coefficient; this display holds for every such constant.</p>'+m('gmpair')+m('gmpairbound')+m('gmprimitive')+
 '<p>The shared integral from the anchor to y cancels before an absolute value is applied. The coefficient multiplying the remaining '
 'anchor error is e−K rather than e+K. The actual Ramanujan cell proof also keeps the quadratic error term, the signs of upper/lower '
 'bounds, all real endpoints and the source-table eligibility checks.</p>'+
 '<details><summary>Optional comparison: a proved limitation of the unsigned method</summary>'+m('gm_transport_def')+m('gmunsigned')+
 '<p>The proof uses the actual nonnegative GM majorant on [x/4,x] and its upper endpoint. Each contributes '
 '0.0462√x/log²x. This is a limitation of that unsigned allowance, not an impossibility theorem about the true oscillatory error '
 'and not a proof of optimality. The signed approach in the preceding spectral section proves the actual 0.076 target and the stronger 0.055 high-ray bound.</p></details>'+ 
 '<p>'+link('Solutions/RHOcticPush.v1/spectral/GMPair.lean')+'; '+link('Solutions/RHOcticPush.v1/spectral/GMUnsignedObstruction.lean')+'. '
 'G is the displayed nonnegative envelope for the actual integral of ψ minus its main term. The four source terms are preserved verbatim from Theorem 1.1.</p>'))

contents_en.append(section('signed-transfer','A complete signed spectral transfer and a cheaper prime-counting proof',
 m('compensation_definition')+m('compensation_profile_only')+m('spectral_mass_cap')+m('spectral_signed')+
 '<p>The proof keeps the actual multiplicity and complex phase until after this identity. Full coefficient summability, compact domination and countable-support Fubini justify summing it over every actual zero. On RH the norm of each square coefficient is exactly the existing nonnegative Nicolas weight; its complete mass is at most β. The leading factor is β rather than the threefold allowance paid by the unsigned GM method.</p>'+signed_constant_bridge('EN')+m('spectral_remainder')+
 '<p>Under RH the existing Nicolas source gives the displayed summable mass cap by a genuine right limit x→1+. The low integral is bounded by eight analytic logarithmic slabs, followed by a proved majorant derivative on the entire tail. The valid proof uses the denominator L−8. The anchor is the actual |D(3)|≤2, proved from the principal-value definition of li and exact finite Mangoldt sums. Linear and full trivial-zero integrals are paid separately.</p><details><summary>Optional history: a rejected majorant</summary><p>The proposed L−6 denominator had the wrong derivative direction and was rejected. It is absent from the accepted proof, which uses L−8.</p></details>'+m('spectral_actual')+prime_power_bridge('EN')+m('spectral_pi')+
 '<p>For the actual Box profile f, the whole prime-counting and interval consumers construct all four former Box providers internally. They require only RH, general Perron, Nicolas and BPT. Within that existing Box input union, the ordinary-π branch now drops the old GM and two Büthe ψ/J inputs. The earlier GM and new standalone compensation providers use different source sets; a comparison of their functions does not hide that distinction. The displayed Q is the complete prime-power allowance. The baseline B_* is defined in the retrospective GM section below as the minimum of its two complete error functions. Thus the last line compares the old and new compensation components on identical domains; it keeps Q and the offset allowance2 unchanged.</p>'+
 '<p>'+link('Solutions/RHOcticPush.v1/spectral-076/SpectralFinal.lean','Actual compensation conclusions')+'; '+link('Solutions/RHOcticPush.v1/spectral-076/SpectralPi.lean','Actual π and interval consumers')+'; '+link('Solutions/RHOcticPush.v1/spectral-076/SpectralComparison.lean','Whole-function strict gain')+'. No global best-known or optimality claim is established.</p>'))

contents_en.append(section('clean-pnt','The whole function and its simpler PNT corollary',
 m('pnt_clean04')+m('pnt_clean_budget')+
 '<p>The second comparison holds on the entire real logarithmic ray: set t=L/2−4.6, use0≤L/2−log L≤t and log2≤0.7, then multiply by the positive8π and useπ≤22/7. The first comparison pays the full prime-power and logarithmic-integral offset through a previously proved scalar function. It does not invoke the old GM mathematical theorem.</p>'+m('pnt_clean_points')+
 '<p>The point values describe bounding-function coefficients, not computed prime counts at exp(100). The full function is already smaller than the simple2/5 display; the exact1/15 gain compares that display with the earlier1/3 display. These are not claims of a best-known result.</p>'+
 link('Solutions/RHOcticPush.v1/spectral-076/corollary/BoxClassicalCorollary.lean','Actual four-input ordinary-prime-counting theorem')))

contents_en.append(section('feedback','Prime-square feedback: a new mathematical reuse of the full bound',
 m('feedback_upper')+
 '<p>Higher prime powers are nonnegative, so ordinary π is at most Riemann J. The existing ψ bound and signed compensation estimate therefore provide an upper bound for J before any ordinary-π error estimate is used. At half the logarithmic height, that full function bounds the isolated square term π(√x)/2. This is a one-pass derivation and does not assume the improved conclusion.</p>'+
 m('feedback_q')+feedback_allowance_bridge('EN')+m('feedback_full')+
 '<p>Here Q₀ is exactly the earlier complete function Q. The actual lower-scale input starts at35, so raw feedback applies from L=70. The minimum preserves the entire old35-ray, including its full function below70. The positive exp(L/4)/2 allowance, higher-power floor-height tail, spectral profile P and offset2 are all retained. Above100, the derived simpler J upper bound gives the following strict comparison of whole functions:</p>'+
 m('feedback_whole_gain')+m('feedback_clean')+m('feedback_budget')+m('feedback_points')+
 '<p>The scalar proof uses0≤L/2−log L≤L/2−4.6 and π≤22/7 on the entire L≥100 ray. At the onset, the numbers are bounding-function coefficients; no prime count at exp(100) was computed. The full effective function is smaller than the clean21/50 corollary.</p>'+
 '<p>The actual Box branch uses exactly RH.v1.hypothesis, IntegratedPerron.v1.formula, Nicolas.v1.spectral_bound and BPTOffOrdinate.v1.bound, as did its previous whole function. The generic point-ψ transfer now also needs BPT for the lower-scale Box argument; the same-premise claim is specifically about the actual four-input Box branch. This extension improves ordinary π and interval bounds; it does not change ψ, LCM or primorial functions.</p>'+
 '<p>'+link('Solutions/RHOcticPush.v1/spectral-076/feedback/FeedbackPiUpper.lean','Independent J upper bound')+'; '+link('Solutions/RHOcticPush.v1/spectral-076/feedback/FeedbackPrimePowers.lean','Actual prime-square correction')+'; '+link('Solutions/RHOcticPush.v1/spectral-076/feedback/FeedbackPi.lean','Actual whole π and interval consumers')+'; '+link('Solutions/RHOcticPush.v1/spectral-076/feedback/FeedbackCorollary.lean','Clean21/50 corollary')+'. No optimality or global best-known claim is established.</p>'))

contents_en.append(section('spectral','Positive spectral weights give actual joint Euler-product theorems',
 m('nicolasbeta')+m('fejer')+m('euler')+m('nicolas_individual')+m('four')+m('block')+
 '<p>The full zero weights are summable and nonnegative under RH and the Nicolas spectral bound. The displayed individual source inequality is the separate link from those spectral weights to the actual normalized Euler product; applying it at x,x²,x³,x⁴ and then the positive polynomial gives the stated joint arithmetic bound. Applying the polynomial pointwise '
 'before summing gives the joint result. The independent bound would pay 10β in the four weighted profiles; the joint proof pays 2.5β. '
 'The exact gain is therefore 7.5β. A weighted-average argument yields the finite-block existential consequence.</p>'+
 '<p>This theorem concerns four actual Euler products at related heights, with the logarithmic normalization displayed. It does not '
 'replace a ratio by its logarithm or assert a better bound at every individual height. The separate signed transfer above closes the 0.076 target. '
 'The public Nicolas.v2 consumer uses the proof; it is not only a test example.</p>'))

contents_en.append(section('box','Box/Mellin: both exact moment identities are proved',
 m('boxmoments')+m('boxseries')+
 '<p>The complete Fourier series and nonnegative form justify the actual full-strip integral exchange. Euler beta/reflection, positive Laplace kernels and justified product Fubini evaluate the actual cosine Mellin integral.</p>'+m('boxgamma')+m('boxfactor')+
 '<p>Harmonic telescoping evaluates H at zero. Uniform summable derivative bounds differentiate H and the actual Euler integral series for zeta. Its exact finite coefficient sums equal the original Stieltjes sequence, so the derivative is linked to the actual original constant, not a replacement definition. The same Gamma/cosine expression defines the prefactor G_Box for |s|&lt;1; the derivatives at zero below concern that local extension. Differentiating Gamma reflection and duplication proves its needed second derivative; a proved L’Hôpital limit supplies a genuine second-order remainder.</p>'+m('boxnotation')+m('boxderivatives')+m('box_expansion')+m('boxcoefficients')+
 card('Two complete original predicates, no mathematical parameters','<p>The actual first_moment and second_moment_identity predicates include genuine integrability and the original J, q and Stieltjes limit. Both now compile without RH, external source propositions or numerical moment assumptions. They are constructed inside the new downstream consumer.</p>'+link('Solutions/RHOcticPush.v1/box/derivatives/BoxSecondMoment.lean','Exact second-moment proof')+'; '+link('Solutions/RHOcticPush.v1/box/gamma/BoxFirstMoment.lean','Exact first-moment proof')+'.','green')+
 m('box_actual')+m('boxgain')+
 '<p>Subtracting the Mellin pole leaves the displayed one-sided expansion; the actual integrals J₀ and J₁ are its constant and linear coefficients. Their identification is proved by domination and the Laurent-product limit. The positive logarithmic tail improves the cap from0.70875 to0.70871. Actual ψ, ordinary π, LCM logarithmic growth and primorial consumers use the resulting whole function; the π-component gain is e^(L/2)/L times the displayed gain.</p>'+
 card('Original full zero estimate proved',m('boxpacket')+m('boxzerobound')+'<p>Here σ is the real logarithmic shift, independent of the Mellin variable s above; mρ is the actual zero multiplicity. The exact original zero-estimate predicate is now derived from the general Nicolas and BPT inputs, with RH inside the predicate. The proof uses actual complex packets, both signs, multiplicity, finite low-height counting and the entire infinite quadratic tail. All four original Box predicates now have actual proof providers. The averaged explicit formula is derived from the following genuine general Perron theorem; its unformalized source proposition remains explicit.</p>'+link('Solutions/RHOcticPush.v1/box/zero/BoxZeroEstimate.lean','Actual full zero estimate')+'.','green')+m('perron_primary')+m('perron_general')+m('perron_transport')+m('perron_constant_transport')+'<p>The first display is Hildebrand’s actual Theorem5.18/(5.32), printed p.166; absolute convergence is (5.34), p.167. The next display is the weaker Lean source contract: it keeps the additive constant existential and uses only x&gt;1. The source zero sum is interpreted with multiplicities, as explicitly corroborated by the cited GM formulation. The following lines show exactly why no bound on the source constant is needed. The multiplicity convention is explicitly corroborated by Grenié–Molteni, equation (1.3a), p.2. The constant C cancels under the displayed operator; the proof uses the actual discontinuous ψ primitive and the entire zero/trivial sums. The Box formula is applied only at the two shifts σ=±1; the separate zero estimate is stronger and allows every σ≤1. The Box scale δ here differs from the octic scale (CL/2−1)exp(−L/2). The combined consumer constructs all four providers internally.</p>'+box_pointwise_bridge('EN')+link('Solutions/RHOcticPush.v1/integration/additive/BoxFullNetwork.lean','Actual complete Box network')+
 '<p>No standalone Blueprint label exists for the new internal coefficient lemmas. Their correspondence is the original BoxMellinInputs.v1 module and RHSmoothing node family. Original four-binder consumers and outcomes are preserved; the additive consumer supplies both proved moments internally.</p>'))

# Complete leading-claim premise matrix. Conditional providers are not hidden.
combined_inputs = json.loads((HERE/'COMBINED_PRIMARY_INPUTS.json').read_text())['inputs']
all_input_details = '<details><summary>All 27 explicit binders in the preserved primary combined consumer / 기존 통합 정리 입력 27개</summary><ul>'+''.join('<li><code>'+html.escape(x['declaration'])+'</code></li>' for x in combined_inputs)+'</ul><p>The two primary sharp-octic binders are historical conditional inputs. The later certified supplement discharges them from general sources and constructed moment proofs; the preserved primary record is not rewritten.</p></details>'
matrix = '<h3>Whole-function and assumption matrix / 전체 함수·가정 비교</h3><div class="tablewrap"><table><tr><th>Claim / conclusion</th><th>Whole function and domain</th><th>Entire transitive input list</th><th>Verification and consumer</th></tr>'
matrix += '<tr><td>Octic original and evolved</td><td>'+m('fixed')+m('family')+m('strongfamily')+m('strongfixed')+m('strongsmall')+m('narrowest')+'</td><td>RiemannHypothesis; SourceGreenSmooth; SourceNicolas119; SourceBPTOffOrdinate. The actual moment caps must be constructed, not added as external hypotheses. Original two octic assumptions are retained only in the preserved primary record.</td><td>Analytic adapters B; finite moment checking D; final source-built consumer status follows the gate above. No new source-first PV.</td></tr>'
matrix += '<tr><td>Sorted Goldbach triple counts</td><td>'+m('triples')+m('goldbach_input')+m('triplehyp')+m('triplebound')+'</td><td>RiemannHypothesis; SourceGreenSmooth; SourceNicolas119; SourceBPTOffOrdinate; GoldbachEvenUpTo(H), plus the displayed geometric conditions. Actual moment caps are constructed internally.</td><td>Actual finite-set injection and optimized prime-count consumer. Does not prove the finite binary input or a global ternary-existence record. No new source-first PV.</td></tr>'
matrix += '<tr><td>GM actual compensation and ordinary π</td><td>'+m('gmoldnew')+m('gmminimum')+m('pitransfer')+'</td><td>SharedRH.hypothesis; GM_Q_Theorem1_1; Buthe.v1.theorem_2_psi; Buthe.v1.theorem_2_li_minus_riemann_pi. The generic π transfer additionally takes the actual ψ-profile inequality for the displayed f; it is not a proof of that profile. Actual Box consumer uses the full Box list below.</td><td>Kernel mathematics, same four source inputs. Actual J, actual ordinary π, signed pair and Ramanujan consumers; no native execution leaf in audited roots.</td></tr>'
matrix += '<tr><td>Ramanujan</td><td>Full piecewise profile in the table above, every real x≥607 billion, exact inherited profile at640 billion onward.</td><td>'+''.join('<div><code>'+html.escape(x)+'</code></div>' for x in ram_inputs)+'</td><td>Same nine-input union. Source/model C components reused under their explicit renderer/model contract; new real-cell numerics kernel-only. Full source replay is separately recorded.</td></tr>'
matrix += '<tr><td>Actual signed compensation</td><td>'+m('spectral_profile')+m('spectral_actual')+'</td><td>RiemannHypothesis; NicolasContinuation.SourceNicolas119; general SourceIntegratedPsi (supplied from IntegratedPerron.v1.formula through the proved normalization). No GM, Büthe, BPT or desired-error premise.</td><td>Actual complete signed infinite-zero proof B; anchor, entire remainder and all-real scalar inequalities kernel-only. Actual π/interval consumers use the result.</td></tr>'
matrix += '<tr><td>Full prime-square feedback and strongest clean ordinary-π corollary</td><td>'+m('feedback_full')+m('feedback_whole_gain')+m('feedback_clean')+'</td><td>RH.v1.hypothesis; IntegratedPerron.v1.formula; Nicolas.v1.spectral_bound; BPTOffOrdinate.v1.bound. Same four inputs as the previous actual Box whole function and intermediate2/5 corollary. Earlier1/3 and standalone GM source packages differ.</td><td>B+D. Actual π and interval outputs;39 written and directly axiom-audited roots, independent reviews, source-fresh718 closure. No source-first PV claim. The full function is stronger than the clean display.</td></tr>'
matrix += '<tr><td>Separate606-billion spectral synthesis</td><td>'+m('ram606')+'Actual strict Ramanujan inequality and normalized margin≥0.001 on every real x≥606b. The old full stronger profile is exactly retained above610b.</td><td>'+''.join('<div><code>'+html.escape(x)+'</code></div>' for x in ram_spectral_inputs)+'The global input set strictly contains the old nine. The local typed consumer uses RHPrimeCounting.v5.compensation_profile and Büthe table1/li-minus-pi/li-greater-pi.</td><td>B+D; four source files,44 written identities,30 printed standard-axiom roots; five closed whole-interval kernel certificates. Independent source/math review and canonical source-fresh723 replay passed. No new PV or finite-prefix coverage claim.</td></tr>'
matrix += '<tr><td>Box ψ / ordinary π / LCM / primorial</td><td>'+m('boxfunctions')+m('spectral_pi')+'ψ error≤√x f(log x), x≥exp35. The new ordinary-π transfer uses the same f and the new complete compensation function. LCM log growth uses ψ; primorial adds the proved1.01√x prime-power allowance.</td><td>RiemannHypothesis; IntegratedPerron.v1.formula; SourceNicolas119; SourceBPTOffOrdinate. All four old Box predicates are constructed internally. The new ordinary-π/interval branch requires no additional GM or Büthe input. Primorial additionally uses Buthe2016.v1.theorem_2_psi. General Perron/Nicolas/BPT are explicit B-tier literature propositions.</td><td>Actual consumers B, numerical C-log contract reused; no newly completed whole-pipeline PV. A component gain does not imply an active global-minimum improvement. Old GM-dependent consumers are preserved separately.</td></tr>'
matrix += '<tr><td>Nicolas joint products</td><td>'+m('four')+m('block')+'</td><td>RiemannHypothesis; NicolasContinuation.SourceNicolas119; NicolasContinuation.SourceNicolas219. No additional desired product bound is a premise.</td><td>Kernel mathematics B and actual Nicolas.v2 consumer. Joint/existential result, not a one-point coefficient record.</td></tr></table></div>'
contents_en.append(section('matrix','Complete leading-claim matrix',tier_legend('EN')+matrix+all_input_details))

def matrix_row(label, formulas, premises, proof):
    return '<tr><td>'+label+'</td><td>'+formulas+'</td><td>'+premises+'</td><td>'+proof+'</td></tr>'

matrix_ko = '<h3>전체 함수와 가정</h3><div class="tablewrap"><table><tr><th>결론</th><th>전체 함수와 범위</th><th>모든 추이적 입력</th><th>검증과 실제 소비</th></tr>'
matrix_ko += matrix_row('기존·개선 octic',m('fixed')+m('family')+m('strongfamily')+m('strongfixed')+m('strongsmall')+m('narrowest'),
    'RiemannHypothesis; SourceGreenSmooth; SourceNicolas119; SourceBPTOffOrdinate. 실제 모멘트 상한은 정리 내부에서 증명으로 구성하며 추가 외부 가정이 아니다. 원래 octic 조건 두 개는 보존한 이전 기록에만 남는다.',
    '해석 연결은 B, 유한 수치 커널 검증은 D다. 새 source-first PV라고 부르지 않는다. 전체 소스 재현 상태는 앞의 검증 기록을 따른다.')
matrix_ko += matrix_row('정렬된 Goldbach 삼중항 개수',m('triples')+m('goldbach_input')+m('triplehyp')+m('triplebound'),
    'RiemannHypothesis; SourceGreenSmooth; SourceNicolas119; SourceBPTOffOrdinate; GoldbachEvenUpTo(H)와 표시된 기하 조건. 실제 모멘트 상한은 내부에서 구성한다.',
    '실제 유한 집합의 단사 대응과 개선된 소수 개수 정리를 사용한다. 유한 이진 Goldbach 입력이나 전역 삼진 존재 기록을 새로 증명한 것은 아니다.')
matrix_ko += matrix_row('GM 보정과 일반 π',m('gmoldnew')+m('gmminimum')+m('pitransfer'),
    'SharedRH.hypothesis; GM_Q_Theorem1_1; Buthe.v1.theorem_2_psi; Buthe.v1.theorem_2_li_minus_riemann_pi. 일반 π 연결은 표시된 f의 실제 ψ 상한도 받는다. 이 연결 자체를 ψ 상한의 증명으로 세지 않는다.',
    '동일한 네 문헌 입력에서 실제 J, 일반 π, 부호 보존 쌍과 라마누잔 소비 정리로 이어진다. 감사한 루트에는 native 실행 공리가 없다.')
matrix_ko += matrix_row('라마누잔', '6070억 이상의 모든 실수에서 앞 표의 전체 조각별 함수. 6400억 이상은 기존의 정확한 비선형 함수를 보존한다.',
    ''.join('<div><code>'+html.escape(x)+'</code></div>' for x in ram_inputs),
    '동일한 아홉 입력이다. C 소스·모델 구성요소는 명시된 렌더러·모델 해석 계약 아래 재사용한다. 새 실수 셀 수치는 커널 검증이며 전체 소스 재현은 별도로 기록한다.')
matrix_ko += matrix_row('실제 부호 보존 보정 오차',m('spectral_profile')+m('spectral_actual'),
    'RiemannHypothesis; NicolasContinuation.SourceNicolas119; 일반 SourceIntegratedPsi. 마지막 입력은 IntegratedPerron.v1.formula에서 실제 정규화 증명으로 공급한다. GM·Büthe·BPT·원하는 오차 상한을 전제로 넣지 않는다.',
    '실제 전체 부호 보존 영점 합 증명 B다. 앵커·전체 나머지 적분·모든 실수 범위의 스칼라 부등식을 커널로 증명하고 실제 π·구간 소비 정리에 사용한다.')
matrix_ko += matrix_row('일반 π의 간단한 따름정리',m('pnt_clean04')+m('pnt_clean_gain'),
    'RH.v1.hypothesis; IntegratedPerron.v1.formula; Nicolas.v1.spectral_bound; BPTOffOrdinate.v1.bound. 이전 전제 묶음과 다르다. 스칼라 비교에서 이전 GM·Büthe 수학 정리를 가정하지 않는다.',
    'B+D. 작성 선언12개와 표준 공리 루트12개를 독립 검토하고 검증된712개 위에서 소스 두 개를 새로 재현했다. 실제 일반 π와 오프셋Li2다. 전체 새 함수는 이 간단한 표시보다 더 강하다.')
matrix_ko += matrix_row('전체 소수 제곱 보정과 가장 강한 간단한 π 따름정리',m('feedback_full')+m('feedback_whole_gain')+m('feedback_clean'),
    'RH.v1.hypothesis; IntegratedPerron.v1.formula; Nicolas.v1.spectral_bound; BPTOffOrdinate.v1.bound. 이전의 실제 Box 전체 함수와2/5 따름정리와 동일한 네 입력이다. 더 오래된1/3 또는 독립 GM 결과의 전제 묶음은 다르다.',
    'B+D. 실제 π와 구간 소비 정리, 작성·직접 공리 검사 루트39개, 독립 수학 검토, 소스에서 새로 빌드한718개 범위를 확인했다. 새 source-first PV가 아니다. 전체 함수는 간단한 표시보다 더 강하다.')
matrix_ko += matrix_row('별도6060억 스펙트럼 결합',m('ram606')+'6060억 이상 모든 실수에서 실제 엄밀한 라마누잔 부등식과 정규화 여유0.001을 증명한다.6100억 이상에서는 이전의 더 강한 전체 함수를 그대로 유지한다.',
    ''.join('<div><code>'+html.escape(x)+'</code></div>' for x in ram_spectral_inputs)+'국소 typed 소비 정리는 RHPrimeCounting.v5.compensation_profile과 Büthe 표1/li-minus-pi/li-greater-pi를 사용한다. 전역 열한 전제는 기존 아홉 전제보다 엄밀히 큰 집합이다.',
    'B+D. 소스 네 개, 작성 선언44개, 표준 공리 루트30개, 닫힌 실수 구간 다섯 개의 커널 인증서다. 독립 검토와 canonical을 포함한 소스 재현723개가 통과했다. 새 PV 또는 전체 유한 접두구간 검증을 주장하지 않는다.')
matrix_ko += matrix_row('Box ψ / 일반 π / LCM / primorial',m('boxfunctions')+m('spectral_pi')+'ψ 오차는 exp(35) 이상에서 √x f(log x) 이하이다. 새 일반 π 연결에는 같은 f와 새 전체 보정 함수를 사용한다. LCM 로그 성장은 ψ, primorial에는 증명된 1.01√x 소수 거듭제곱 상한을 사용한다.',
    'RiemannHypothesis; IntegratedPerron.v1.formula; SourceNicolas119; SourceBPTOffOrdinate. 원래 Box 조건 네 개를 내부에서 증명한다. 새 일반 π·구간 정리는 GM·Büthe 입력을 추가하지 않는다. Primorial은 Buthe2016.v1.theorem_2_psi를 추가로 사용한다. 일반 Perron·Nicolas·BPT 문헌 명제는 명시적 B 등급 입력이다.',
    '실제 소비 정리는 B다. C 로그 계약을 재사용하며 전체 새 PV를 완료한 것은 아니다. 구성요소의 개선이 활성 전역 최솟값의 개선을 뜻하지는 않는다. 기존 GM 의존 소비 정리는 별도로 보존한다.')
matrix_ko += matrix_row('Nicolas 결합 오일러 곱',m('four')+m('block'),
    'RiemannHypothesis; NicolasContinuation.SourceNicolas119; NicolasContinuation.SourceNicolas219. 원하는 곱 상한을 새 전제로 넣지 않는다.',
    '커널 수학 B와 실제 Nicolas.v2 소비 정리다. 결합·존재 결과이며 한 높이의 계수 기록이 아니다.')
matrix_ko += '</table></div>'
all_input_details_ko = '<details><summary>보존한 이전 통합 정리의 명시적 입력 27개</summary><ul>'+''.join('<li><code>'+html.escape(x['declaration'])+'</code></li>' for x in combined_inputs)+'</ul><p>이전의 sharp-octic 입력 두 개는 역사적 조건부 입력이다. 이후 인증된 추가 정리에서 일반 문헌 입력과 실제 모멘트 증명으로 해소하며, 보존한 원래 기록을 소급 수정하지 않는다.</p></details>'

contents_en.append(section('network','What IEANTN propagation actually means here',
 '<p>A node conclusion is a typed proposition. A Solution provides a Lean proof from named predecessor conclusions. '
 'Shared vocabulary fixes the arithmetic objects and normalization. New versions preserve older published contracts. '
 'The canonical metadata records the edges; generated Challenge files describe proof tasks and are excluded from the proof closure.</p>'+
 '<div class="chain"><span>General source inputs</span><span>Actual analytic identities and bounds</span><span>ψ / θ / π providers</span>'
 '<span>Prime windows and quantiles</span><span>Ramanujan / products / LCM growth</span></div>'+
 '<p>The new proofs are composed in one actual combined consumer. Dependency audits inspect proof values transitively: '
 'an import, a read source file or a companion theorem is not counted as consumption. Official Comparator receipts are not '
 'invented; repository graph/fingerprint checks and the source-built mathematical consumers are reported separately.</p>'+
 metadata_graph('EN')+
 '<p>The broader graph is examined for applicability, including Goldbach and Möbius/Mertens. An unaffected or inactive minimum '
 'is recorded as such. No claim is made that every graph node acquired a new numerical record, or that this post-lock continuation '
 'demonstrates a causal advantage of the earlier exposure condition.</p>'))

contents_en.append(section('goldbach','A genuine new arithmetic consumer: sorted Goldbach counts',
 m('triples')+m('goldbach_input')+m('triplehyp')+m('triplebound')+
 '<p>Every prime in the proved strict window leaves an even residual between4 andH. The explicit finite binary input supplies a prime pair. Sorting that pair gives a≤b, and the large-window prime is larger than both. Distinct window primes give distinct largest coordinates, so the injection proves a lower bound for actual sorted triples, with no permutation double counting.</p>'+
 '<p>The source-closed consumer uses the certified moments internally. At the original2.15 width a separate consumer transfers the stronger fixed-width population too. The finite binary theorem and the displayed geometry are real additional hypotheses. This neither proves binary Goldbach nor claims a new global ternary-existence record.</p>'+
 '<p>'+link('Solutions/RHOcticPush.v1/goldbach/GoldbachTripleCount.lean','Actual finite set and injection')+'; '+link('Solutions/RHOcticPush.v1/octic/OcticOptimizedCertified.lean','Optimized source-closed consumer')+'. No standalone Blueprint label existed for this new transfer; its canonical Goldbach-count node records the prime-interval dependency.</p>'))

contents_en.append(section('downstream','Which arithmetic conclusions actually change',
 '<h3>Consecutive prime indices and cubes</h3>'+m('prime_quantiles')+m('cubes_consumer')+
 '<p>The sequence q is indexed from zero. The strict prime-count bound supplies every index in the displayed block, not only one prime or an unspecified selected index. The larger same-width population enlarges that block. Its actual consumer is PrimeQuantile.v3.optimized_octic_block. The existing successive-cubes consumer also remains usable; it is an RH consequence with the octic source inputs, not a new cubes record.</p>'+
 '<h3>LCM and prime products</h3>'+m('arithmetic_products')+
 '<p>The exact identities ψ(n)=log(lcm(1,…,n)) and θ(n)=log(∏p≤n p) transfer the entire Box function to these arithmetic objects. LCM growth uses RH, general Perron, Nicolas and BPT; the primorial relay additionally uses Buthe2016.v1.theorem_2_psi for its1.01√n prime-power allowance. The displayed improvement compares the original and sharpened Box moment functions, with the same downstream assumptions. It is not a new small-n six-prime witness or finite LCM-certificate result. The later prime-square feedback changes ordinary π, not these ψ/θ functions.</p>'+
 '<h3>Negative applicability results matter</h3>'+m('mertens_masking')+m('mertens_weight_gap')+
 '<p>The first-Mertens observable here is the weighted prime sum A, distinct from the Möbius sum M. Büthe’s finite ψ allowance0.94 applies for11&lt;x≤10^19. On the displayed common domain exp(35)≤x≤10^19, its minimum with the Box component is still0.94. Thus this component change alone gives no strict gain in the active minimum used by the existing first-Mertens route. There is also a distinct spectral issue: the existing Mertens input uses the ordinate weight wᴹ, while the Nicolas cap controls w. Direct substitution would omit the positive correction displayed above; no replacement numerical moment bound is claimed. The Nicolas joint theorem improves correlated Euler-product information. It is not a new bound for the Möbius sum M(x): that problem needs information about reciprocal-zeta residues absent from the inverse-square zero-mass input.</p>'+
 '<p>'+link('IEANTN/Nodes/PrimeQuantile/v3/Conclusions.lean','Exact prime-index and cube contracts')+'; '+link('Solutions/RHOcticPush.v1/integration/OcticVerifiedEvolution.lean','Actual interval-to-quantile proof')+'; '+link('Solutions/RHOcticPush.v1/integration/additive/BoxFullNetwork.lean','Actual ψ-to-LCM/primorial composition')+'; '+link('Solutions/RHOcticPush.v1/spectral/FiniteApplicability.lean','Whole-ray inactive-component comparison')+'.</p>'))

contents_en.append(section('pv','Program verification, finite coverage and infrastructure trust',
 card('No relabeling of kernel checks as source-first PV','<p>PV means actual C/C++/CUDA source correspondence to a formal execution model, '
 'mathematical correctness and a connection from verified outputs to the arithmetic theorem. The new octic certificates are '
 'ordinary kernel checking. They do not constitute a newly source-first verified C program.</p>', 'blue')+
 '<p>The reused fixed-point C logarithm routine has a generic execution/correctness theorem for integer inputs from 2 through '
 '2·10¹², not merely the previously exercised 2–128 inputs. The degree-20 coefficient program is reused only at proved indices 0–20. '
 'The actual C sources are unchanged. The RestrictedC backend supplies exact rendered-source identity and model execution proofs; '
 'an independent parser/renderer-soundness theorem is not established by that backend. Its renderer/model-interpretation contract '
 'must remain explicit for those reused programs. The bounded independent frontend for the prime counter and high driver is a separate new proof described below. Compiler, runtime, OS/API, hardware and source/build/run association are separate remaining boundaries.</p>'+finite_en+finite_completion('EN')+finite_ieantn_completion('EN')+
 ('<p>The earlier bounded-checker comparison is recorded separately from the completed fixed-count proof. A balanced tree checker is proved equivalent to the ' if finite_kernel_done else '<p>The full finite prime-count output realization remains unfinished. A balanced tree checker is proved equivalent to the ')+
 'unchanged original list checker and verifies the same 32,768-record chunk in independent runs of about 163 seconds, with about '
 '30.8 GiB peak RAM and only the standard propext axiom. A further pure-recursion variant proves the generic bridge and the same numerical chunk with an empty axiom list in 182.04 seconds (30.70 GiB child peak RSS). The earlier attribution of propext to Nat.brecOn was incorrect and is withdrawn. The old unsplit job was still running after several days. This is a '+
 ('censored, differently organized small-chunk comparison, not a controlled speedup benchmark. The complete high-count result has its own acceptance receipt. ' if finite_kernel_done else 'censored, differently organized verification comparison, not a controlled speedup benchmark or completion of all 90.67 million records. ')+
 'The original long-running workers and locked data are preserved.</p>'+
 '<p>The first full recovery verified 528 new modules and reached787 of2,768 arithmetic parts before a clean, requested drain. All active children finished naturally; the original five long-running workers were untouched. The additive resource-only V2 controller completed source/hash/dependency transport before launching numerical workers. It admits at most22 workers adaptively, preserving a512 GiB host reserve and accounting for active jobs’ potential growth. A partial counter does not establish final acceptance. Aggregate RSS/PSS, individual peaks, elapsed time and disk use are recorded; unavailable kernel OOM attribution stays unknown.</p>'+
 '<p>The old driver’s <code>main</code> and literal 38,358,837,683 remain unchanged. A separate additive C driver actually ran the same counter at 1,490,000,000,000 and wrote eight little-endian stdout bytes decoding to55,206,486,339 in1.116 seconds, with19.94 MiB peak RSS. Its formal whole-main theorem proves source-owned initialization, the counter call, output bytes and cleanup for every successful model execution; a constructive canonical model run is also proved. '+
 ('The fixed kernel count is now accepted; the final source-output connection is recorded above. ' if finite_kernel_done else 'The fixed numerical output adapter still needs the full kernel count certificate. ')+
 'Four new Lean modules now prove an independently specified C11-fragment surface grammar, general guarded-renderer soundness and actual acceptance of both C texts. A new source-indexed whole-main existence proof consumes both generic soundness theorems. '+
 ('The completed fixed-output consumer genuinely uses these proofs. ' if finite_source_done else 'The fresh application append is separate. ')+
 'These claims do not include general C name binding, type checking, header interpretation or ISO-C operational adequacy; compiled-run and model applicability contracts remain explicit. This bounded frontend covers the counter and high driver, not the separate reused logarithm/coefficient programs.</p>'+
 '<p>The source-fresh32-module whole application and the additive five-module grammar replay have passed, producing a37-module scoped closure. The grammar audit checks all186 compiler-owned theorems against standard axioms,19 proof-value edges and11 required endpoints. All36 actual normal/−O/−OO grammar controls passed. The historical application-reader V2 passed57 decisions; its separately preserved V3 passed60, including rejection of nested fixture-output paths. The mathematical application sources and original run are unchanged. These counts refer to different checked scopes, not additional numerical algorithms.</p>'+
 '<p>The original90,670,946-record data was deterministically regenerated in25 minutes56.59 seconds with42.97 GiB peak RSS: the packed SHA-256, all3,464 original Lean source hashes and all2,469 new pure-check recipes matched. After independent readback, exactly12,171,195,019 bytes of regenerable duplicate data were removed. Original inputs, accepted proofs and current verification inputs remain preserved. A separate source-clean complement covers the original994-module foundation; its status is disclosed in the status receipt rather than inferred from historical cached objects.</p>'))

contents_en.append(section('reproduce','Reproduce, inspect and retain the essential evidence',
 '<p>The baseline is commit <code>0e2638852a08de84e25f1d179a36356fb12333a5</code>. Lean is 4.34.0-rc2; '
 'Mathlib is <code>71a80585ee495fc24472fd0eaffc89d94e4fd8d6</code>. '
 'A separately measured fresh source build replays the 340-module baseline, followed by the new source closure and real combined '
 'consumers. The developer overlay and application caches are not accepted reproduction inputs.</p>'+
 '<p>Each accepted run records exact source, object, command and log hashes, include-string C inputs, elapsed time, peak RAM '
 'and experiment-owned disk usage. Python acceptance is tested under normal, −O and −OO execution with mutation controls. '
 'Nonzero development attempts and the distinction between OOM evidence, thread-creation failure and timeout are retained. '
 'Missing token counters are reported as unavailable, not inferred from file counts or elapsed time.</p>'+
 '<p>Substantial resources are admitted from actual available RAM and free disk independently. There is no obsolete 4 GiB cap. '
 'The earlier numerical moment batch used eight single-CPU lanes. Historical primary builds used a128 GiB address-space ceiling; repaired clean builds use64 GiB. The large count leaves use128 GiB and their final assembly256 GiB address ceilings. These ceilings are not physical RAM measurements. '
 'Actual observed use, rather than those ceilings, is recorded in the receipts.</p>'+
 reproduction_observation('EN')+measurements('EN')+'<p>Source-closure sets overlap and must not be added as disjoint totals. Per-child high-water RSS, sampled aggregate RSS/PSS and sampled owned-file bytes have different measurement scopes. OOM events are attributed only when supported by owned process evidence.</p>'+
 '<details><summary>Exact transitive Ramanujan input list</summary><ul>'+''.join('<li><code>'+html.escape(x)+'</code></li>' for x in ram_inputs)+'</ul></details>'+
 '<p>See the bundled README and immutable source/certificate manifests for clean setup and exact commands. Generated arrays are '
 'deterministic proposals which must pass the checker again; no CSV is accepted as a theorem. Cleanup is restricted to verified '
 'regenerable, experiment-owned scratch after reproduction is checked. Original research sources, locked inputs, accepted proof '
 'artifacts and essential evidence are retained.</p>'+
 '<details><summary>Machine-readable final status and receipts</summary><pre>'+html.escape(json.dumps(status,indent=2,ensure_ascii=False))+'</pre></details>'))

# The Korean exposition uses the same displayed mathematical contracts and explicit status gate.
contents_ko = [section('results','핵심 결과와 정확한 증명 경계',
 '<p>이 연구는 실제 octic·Box 해석 증명 의무를 해소하고 더 강한 소수계수 함수를 산술 소비 정리에 연결한다. RH는 가정으로 남는다. 가장 강한 해석 결과에도 명시적으로 이름 붙인 일반 문헌 명제가 필요하며, 이를 새 Lean 공리로 조용히 바꾸지 않는다.</p>'+
 '<p class="muted">넓은 수식과 표는 가로로 스크롤할 수 있다. 키보드에서는 Tab으로 수식이나 표를 선택한 뒤 방향키를 사용한다.</p>'+
 m('arithmetic_notation')+early_reader_context('KO')+
 '<p>소수 합은 실제 소수에 대해, 소수 거듭제곱 합은 모든 양의 정수 지수에 대해 계산한다. li는 주값 로그 적분이며 오프셋 적분 Li₂와 상수 li(2)만큼 다르다. 일반 소수계수 연결에서 이 상수를 명시적으로 지불한다. L은 각 식에서 정한 log(x) 또는 log(u)다. 모든 영점을 명시적으로 더하는 Green 공식을 제외하면 ρ는 서로 다른 비자명한 제타 영점을 나타내며 mρ는 중복도, γρ는 허수부다. γ는 Euler 상수이고 첫 Stieltjes 상수 γ₁은 Box 절에서 실제 극한 수열로 정의한다.</p>'+
 card('같은 네 입력으로 얻은 더 강한 PNT 전체 상한',m('feedback_clean')+
      '<p>전체 함수는 이 간단한 따름정리보다 더 강하다. exp(35) 이상의 이전 전체 범위를 보존하고 exp(100) 이상 모든 실수에서 전체 우변을1.67√x/log(x)보다 많이 줄인다. 정확한 입력은 RH, 일반 적분 Perron 공식, Nicolas와 BPT다. 먼저 π≤J를 증명하고 낮은 높이의 J 상한으로 실제 소수 제곱 항을 제한하므로 순환 논증이 없다. 소스 네 개, 증명 루트39개, 독립 수학 검토와 소스에서 새로 빌드한718개 범위가 통과했다. 수학적 커널 검증이며 새 source-first PV가 아니다.</p>','green')+
 card('기존 2.15 목표: '+badge_ko,'<p>'+conditional_ko+'</p>'+m('fixed')+
      '<p>집합의 양 끝점은 모두 제외한다. 일반 소수계수 함수의 차이에 대한 정리도 별도로 있다. '
      '모든 변수는 실수이며, 유한 표본이 아니라 명시된 전체 구간을 다룬다.</p>','green' if octic_done else 'amber')+
 card('라마누잔 부등식의 더 강한 정량적 범위',m('ram')+
      '<p>기존 아홉 입력을 유지한다. 두 독립 오차 상한을 더하는 대신 공통 적분을 먼저 소거한다. '
      '20차 계수 프로그램이 사용하는 실제 구간에서 주항 나머지를 1/1000에서 3/8000으로 줄였다. '
      '6400억 이상에서는 기존 비선형 오차 여유 함수를 그대로 보존한다.</p>'+
      '<details><summary>보존한 비선형 라마누잔 함수 전체</summary>'+m('ram_coefficients')+m('ram_tail_terms')+ram_bridge('KO')+m('ram_retained_profile')+'<p>원래6400억 소비 정리의 정확한 팩토리얼 계수, 나머지와 두 최댓값을 모두 유지한다. 이 함수를 거친 상수로 바꾸지 않는다.</p></details>'+
      '<div class="tablewrap"><table><tr><th>이 값 이상의 모든 실수 x</th><th>증명된 정규화 여유</th></tr>'+rows+'</table></div>','green')+
 card('별도의 스펙트럼–라마누잔 결합',m('ram606')+'<p>실제 부호 보존 오차 함수를 사용하여6060억 이상 모든 실수에서 정규화 여유0.001을 증명했다. 닫힌 실수 구간 다섯 개를 커널로 검증하여6060억부터6100억까지 빠짐없이 연결하고,6100억 이상에서는 이전의 더 강한 전체 함수를 그대로 유지한다. 기존 입력 아홉 개에 Nicolas와 일반 Perron을 더하여 총 열한 개를 사용하는 별도 결과다. 동일 전제의 개선이나 문헌상 시작점 기록을 주장하지 않는다. Lean 소스 네 개, 독립44개 선언 검토와 canonical을 포함한 소스 재현723개가 통과했다.</p>','green')+
 card('실제 부호 보존 오차 상한과 더 강한 계수',m('spectral_profile')+m('spectral_actual')+'<p>원래 산술 보정 오차의 전체 실수 구간에 대한 정리다. 부분 적분 전까지 복소 위상을 유지한 뒤 Nicolas의 양의 영점 역제곱 질량을 사용한다. 정확한 입력은 RH, Nicolas의 스펙트럼 상한과 일반 적분 Perron 공식이다. GM 또는 Büthe의 오차 상한을 가정하지 않는다.</p>','green')+
 finite_executive_ko),
 section('octic','Octic: 실제 무한합과 유한 커널 검증을 연결하는 방법',
 '<p>φ_j는 반지름 ε_j인 정규화된 짝함수 비음수 매끄러운 bump이고 k_j=φ_j*k다. L은 물리적 커널 중심의 로그이며 전 범위 덮개가 a=u인 L을 선택한다. w_j는 t≤0에서0이고 W_j(t)=w_j(2t), X=2로 Green의 지지집합 조건을 만족한다. 푸리에 부호와 척도는 아래 식과 같다.</p>'+
 '<p>수치식에 임의로 이름을 붙인 것이 아니라 아래 실제 적분의 푸리에 변환을 검증한다.</p>'+m('kernel')+m('moments')+
 '<p>매끄러운 범프와 실제 커널을 합성곱하여 지지집합·매끄러움·부호·수렴을 증명한다. '
 '실제 Mellin/Fourier 정규화, 영점의 차수와 켤레 대응, 자명한 영점의 기하급수, Mangoldt 합의 극한을 모두 연결한다. '
 '사용하는 일반 명시적 공식 자체는 공개된 문헌 입력으로 남는다.</p>'+m('octic_physical')+m('mellin')+m('green')+'<p>'+source_links+'</p>'+
 '<p>BPT 연결은 임의의 유한 부분합에서 출발해 합의 수렴과 무한 극한을 증명한다. '
 '실제 변환과 도함수의 감쇠로 적분 가능성과 경계항 소멸을 확인한다. 작은 영점 높이, 실수축, 중복도와 켤레쌍도 포함한다.</p>'+'<p>N(T)는 양의 높이 구간 (0,T]의 중복도를 센 닫힌 영점 개수다. 원문은 영점 높이가 아닌 곳에서만 사용하고 표시된 모든 높이의 닫힌 구간 상한은 새 끝점 연결의 결론이다.</p>'+m('zero_count_def')+m('bpt')+m('infinite')+
 '<p>표시된 일반 무한 꼬리 식은 a≥2π와 연결된 Stieltjes 정칙성, 가중 적분 가능성 및 경계항 소멸을 전제로 한다. 실제로 축척한 octic 변환에 대해 이 조건을 모두 증명했다.</p>'+
 '<p>문헌에서 영점 높이의 계단점 규약을 추측하지 않는다. 그 높이를 피한 상한에서 시작하여 '
 '실제 영점 집합의 국소 유한성과 오른쪽 극한으로 닫힌 끝점 계수까지 옮긴다. 추가 상수는 없다.</p>'+
 m('quadrature')+m('derivatives')+
 '<p>절댓값 함수 자체를 두 번 미분하지 않는다. 원래 매끄러운 함수에 이차식을 더한 함수의 볼록성을 이용하므로 '
 '푸리에 변환이 0을 지나는 셀도 처리한다. 0–10은 0.01 간격, 10–100은 0.05 간격, 100–1000은 0.2 간격으로 '
 '전체 구간을 덮으며 끝점 7,301개를 모두 검증한다. a≥10인 셀에서는 40/a² 곡률 상한을 사용한다.</p>'+m('certsum')+m('momenttails')+
 '<p>로그 모멘트에서 [0,1]의 음수 기여를 버리지 않는다. 끝점의 실제 함수값, 로그값, 위쪽으로 반올림한 셀 상한, '
 '정수 합계, 무한 꼬리와 최종 실제 적분 연결을 각각 검증한다. 기존 삼각함수 축약의 [−1,1] 대체 구간이 너무 넓은 '
 '문제는 중앙 주기 선택으로 개선했다. 어느 정수 주기를 고르든 성립하는 일반 정리가 건전성을 보장한다. '
 '이는 커널 인증서 검증이며 source-first PV가 아니다.</p>'+m('endpoint')+m('octic_zero_def')+m('zerofixed')+m('octic_count_bridge')+'<p>S_Λ는 실제 Mangoldt 가중합, S_p는 실제 소수 가중합이다. 0≤k≤1과 log(t)/√t의 감소 성질로 마지막 부등식이 실제 소수 개수를 준다. 연속적인 전 범위 덮개가 a=u, b≤u+C√u log(u)를 공급하며 정량적 스칼라 여유로 최종 엄밀한 개수 하한을 얻는다.</p>'),
 section('frontier','더 강한 결론과 공정한 비교',
 '<p>동일한 실제 모멘트 정보로 별도의 더 강한 범위를 얻는다. 아래 결과의 수치 검증 상태는 첫 카드의 상태와 같다. '
 '기존 2.15 정리와 고정 예산은 덮어쓰지 않는다. 같은 고정 배열에서 더 강한 실제 모멘트 상한도 얻는다.</p>'+m('strongcaps')+octic_budget_bridge('KO')+m('strongfamily')+m('strongfixed')+m('strongsmall')+m('narrowest')+
 '<p>2.15에서는 폭과 시작점을 동일하게 유지한 채 소수 개수 하한이 증가한다. 더 작은 폭에서는 다른 개수 보장을 제시하므로 '
 '모든 좌표에서 이전 결과를 지배한다고 말하지 않는다. 1+4.2/log(u)만으로는 정규화 개수의 극한 하한이 1보다 크다고 '
 '결론 낼 수 없다. 2.149 결과에는 고정된 양의 주항 여유가 있다.</p>'+m('cpdl')+
 '<p>Chirre–Pereira Júnior–de Laat의 §1.3(인쇄면 2쪽)은 RH와 모든 α≥0에서 위 점근적 가족을 제공한다. α=1에서는 계수 2.5074보다 작은 값이 나온다. '
 'CMS의 정리5(인쇄면5쪽)는 RH와 x≥4 아래 폭(22/25)√x log(x)의 닫힌 구간에 소수 한 개를 보장한다. 이는 √u개 이상이라는 목표와 다르다. '
 'Dudek–Platt는 이미 RH 아래 마지막 정수 반례를 38,358,837,682로 찾았다. 따라서 6070억을 새로운 문헌상 시작점 기록으로 '
 '홍보하지 않는다. 이번 결과의 가치는 형식화된 정량적 여유와 부호를 보존한 연결이다.</p>'+m('cms_one_prime')+'<p>다음 f_j와 f_Box는 이번 연구에서 정의한 전체 함수이며 Lee–Nosal에 귀속하지 않는다.</p>'+m('boxfunctions')+'<p>이제 문헌의 두 전체 함수를 표시한다.</p>'+m('lee_strong')+m('lee')+
 '<p>Lee–Nosal 최신 v4의 정리1.1과1.2에 표시된 두 전체 ψ 함수보다 새 Box 함수가 모든 실수 log(x)≥35에서 엄밀히 작음을 증명했다. 이는 실제 오차 측정이나 유한 표본이 아닌 전체 함수의 조건 없는 스칼라 비교다. 실제 Box 산술 정리는 RH와 명시된 일반 문헌 입력 세 개를 사용한다. 보조정리3.3의 높이 가족과 유한 구간의 다른 상한도 비교해야 하므로 세계 최선은 주장하지 않는다. '
 '세계 최선이라는 주장은 확립하지 않았다.</p>'+m('box_lee_comparison')+'<p>'+link('Solutions/RHOcticPush.v1/comparisons/BoxVsLee.lean','표시된 두 전체 함수의 실제 전 구간 비교 증명')+'.</p>'),
 section('gm','공통 오차를 소거하여 얻은 실제 개선','<p>앞에서 정의한 보정 D와 여기서 쓰는 오차 E는 같은 산술 함수다. 이 절은 이전 GM 방법을 비교하는 설명이다.</p>'+m('gm_error_alias')+m('gmoldnew')+m('gmminimum')+
 '<p>새 함수의 초기 상수는 더 크기 때문에 시작 구간 전체에서 무조건 더 작지는 않다. '
 '이전 함수와의 최솟값을 사용하여 원래 범위를 보존하고, exp(24) 이상 모든 실수에서 1/2보다 큰 개선을 증명한다.</p>'+m('pitransfer')+
 '<p>여기 K는 [0,e]의 상수 가중치다. 아래 라마누잔 적용에서는 자연 계수의 보수적인 하한을 선택하며, 이 식은 그 범위의 모든 상수에 성립한다.</p>'+m('gmpair')+m('gmpairbound')+m('gmprimitive')+
 '<p>앵커에서 y까지의 공통 적분을 절댓값을 취하기 전에 소거한다. 남는 앵커 오차의 계수는 e+K가 아니라 e−K다. '
 '실제 라마누잔 소비 정리는 이차 오차항, 상·하한의 부호, 문헌 표의 적용 구간, 실수 끝점까지 확인한다.</p>'+m('gm_transport_def')+m('gmunsigned')+
 '<p>마지막 부등식은 양의 GM majorant를 그대로 사용하는 방법에 대한 엄밀한 한계다. 실제 진동 오차에 대한 불가능성이나 '
 '최적성 정리가 아니다. 앞의 별도 부호 보존 증명은 실제 0.076 목표와 높은 구간의 0.055 상한까지 증명한다.</p>'),
 section('signed-transfer','전체 부호 보존 오차 증명과 더 적은 입력을 쓰는 소수계수 연결',
 m('compensation_definition')+m('compensation_profile_only')+m('spectral_mass_cap')+m('spectral_signed')+
 '<p>실제 무한 영점합에서 복소 위상을 부분 적분까지 보존한다. 원래 ρ(ρ+1) 분모가 정확한 경계항과 ρ² 분모의 적분으로 바뀐다. RH 아래 합 가능한 전체 가중치의 질량은 표시된 β 이하이며, Nicolas 입력의 x→1+ 극한에서 얻는다. 전체 합·적분 교환과 균등 지배를 증명한 뒤에만 RH를 사용하여 노름을 취한다. 그 결과 Nicolas의 실제 양의 역제곱 질량을 한 번 지불하며, 부호를 버린 GM 방법의 세 배 비용을 피한다.</p>'+signed_constant_bridge('KO')+m('spectral_remainder')+m('spectral_actual')+
 '<p>앵커의 실제 |D(3)|≤2, 3부터 x까지 전체 나머지 적분과 모든 L≥24의 스칼라 부등식은 문헌 오차 상한 없이 커널로 증명했다. 최종 증명은 L−8 분모와 실제 낮은 구간 여덟 조각을 사용한다.</p><details><summary>선택 배경: 폐기한 majorant</summary><p>L−6 분모의 도함수 방향이 잘못되어 폐기했으며 승인한 증명에는 사용하지 않는다.</p></details>'+prime_power_bridge('KO')+m('spectral_pi')+
 '<p>실제 Box 함수 f에 대한 보통 π와 구간 정리는 원래 Box 조건 네 개를 내부에서 증명한다. 입력은 RH, 일반 Perron, Nicolas와 BPT뿐이다. 기존 Box 입력 합집합 안에서는 GM과 두 Büthe ψ/J 입력을 제거한다. 독립적인 이전 GM 공급자와 새 공급자는 문헌 입력 집합이 다르므로 함수 비교와 동일 전제 비교를 구분한다. 표시된 Q는 전체 소수 거듭제곱 여유다. B_*는 뒤의 GM 비교 절에서 정의하는 이전 두 전체 오차 함수의 최솟값이다. Q와 오프셋 여유2는 그대로 포함한다.</p>'+
 '<p>'+link('Solutions/RHOcticPush.v1/spectral-076/SpectralFinal.lean','실제 보정 오차 결론')+'; '+link('Solutions/RHOcticPush.v1/spectral-076/SpectralPi.lean','실제 π·구간 소비 정리')+'; '+link('Solutions/RHOcticPush.v1/spectral-076/SpectralComparison.lean','전체 함수의 엄밀한 개선')+'. 세계 최선 또는 최적성 주장은 확립하지 않았다.</p>'),
 section('clean-pnt','전체 함수에서 얻은 중간 단계의 간단한 PNT 따름정리',
 m('pnt_clean04')+m('pnt_clean_gain')+m('pnt_clean_budget')+m('pnt_clean_points')+
 '<p>새 네 입력 경로와 동일한 exp(100) 시작점에서 이전1/3 표시보다 강한2/5를 증명했다. 이전1/3 결과의 문헌 입력 묶음은 다르며,2/5에서21/50으로의 후속 개선이 정확히 같은 네 입력을 유지하는 비교다. 이 결과는 아래21/50보다 먼저 증명한 중간 단계다. 전체 함수는 이 간단한 표시보다 더 강하다. 전체 실수 L≥100에서 t=L/2−4.6,0≤L/2−log L≤t,log2≤0.7과π≤22/7을 사용한다. 이전 GM 수학 정리를 가정하지 않으며, 점에서 표시한 값은 실제 소수 오차가 아닌 상한 함수의 계수다.</p>'),
 section('feedback','소수 제곱 항 보정: 전체 상한을 실제로 다시 사용하는 새 연결',
 m('feedback_upper')+
 '<p>고차 소수 거듭제곱의 기여가 비음수이므로 π(y)≤J(y)다. 기존 ψ 상한과 부호를 보존한 보정에서 J의 전체 상한을 먼저 얻고, 로그 높이의 절반에서 실제 제곱 항 π(√x)/2를 제한한다. 새 π 오차 상한을 전제로 넣지 않는 한 번의 비순환 논증이다.</p>'+
 m('feedback_q')+feedback_allowance_bridge('KO')+m('feedback_full')+
 '<p>Q₀는 앞에서 정의한 전체 함수 Q와 같다. 낮은 높이 입력은35부터 유효하므로 원래 함수에 직접 적용하는 보정은 L=70부터 사용한다. 이전 함수와의 최솟값으로 L≥35 전체 범위를 보존하며70 미만에서는 정확히 이전 함수다. 양의 exp(L/4)/2 항, 높은 거듭제곱과 정수 높이의 꼬리, P와 오프셋2를 모두 유지한다.100 이상에서는 더 간단한 J 상한으로 다음 전체 함수의 엄밀한 개선을 얻는다.</p>'+
 m('feedback_whole_gain')+m('feedback_clean')+m('feedback_budget')+m('feedback_points')+
 '<p>전체 L≥100에서0≤L/2−log L≤L/2−4.6과π≤22/7로 스칼라 여유를 증명한다. 시작점의 수치는 상한 함수의 계수이며 exp(100)에서 실제 소수 개수를 계산한 것이 아니다. 전체 유효 함수는21/50 따름정리보다 더 강하다.</p>'+
 '<p>실제 Box 경로는 이전과 정확히 같은 RH.v1.hypothesis, IntegratedPerron.v1.formula, Nicolas.v1.spectral_bound, BPTOffOrdinate.v1.bound를 사용한다. 일반적인 한 점의 ψ 입력을 받는 연결에는 낮은 높이 Box 논증을 위해 BPT가 추가되므로 동일 전제라는 주장은 실제 네 입력 Box 경로에 한정한다. 이 추가 결과는 일반 π와 구간 상한을 개선하며 ψ·LCM·primorial 함수를 바꾸지 않는다.</p>'+
 '<p>'+link('Solutions/RHOcticPush.v1/spectral-076/feedback/FeedbackPiUpper.lean','독립 J 상한')+'; '+link('Solutions/RHOcticPush.v1/spectral-076/feedback/FeedbackPrimePowers.lean','실제 제곱 항 보정')+'; '+link('Solutions/RHOcticPush.v1/spectral-076/feedback/FeedbackPi.lean','전체 π·구간 소비 정리')+'; '+link('Solutions/RHOcticPush.v1/spectral-076/feedback/FeedbackCorollary.lean','21/50 따름정리')+'. 최적성이나 세계 최선은 주장하지 않는다.</p>'),
 section('spectral','양의 영점 가중치와 실제 오일러 곱',m('nicolasbeta')+m('fejer')+m('euler')+m('nicolas_individual')+m('four')+m('block')+
 '<p>실제 중복도를 포함하는 무한합의 가중치가 비음수이고 합 가능하다는 사실을 사용한다. '
 '표시한 Nicolas의 개별 부등식이 영점합과 실제 정규화 오일러 곱을 연결한다. 이 문헌 입력을 네 높이 x,x²,x³,x⁴에 적용하고 각 영점의 제곱 다항식 부등식을 합한다. 독립적인 네 상한에서는 10β를 지불하지만 결합 정리는 2.5β만 '
 '지불하여 정확히 7.5β를 회복한다. 하나의 높이마다 더 좋은 계수를 얻었다는 주장이 아니라, 관련된 네 높이의 결합 및 '
 '유한 블록 안에서 적어도 한 곳에 대한 실제 산술 정리다.</p>'),
 section('box','Box/Mellin: 실제 모멘트 항등식 두 개 완료',m('boxmoments')+m('boxseries')+
 '<p>전체 푸리에 급수와 비음수 코사인 형태에서 실제 무한급수·적분 교환을 증명했다. Beta·Gamma 반사 공식, 양의 Laplace 적분과 Fubini 정리로 실제 Mellin 적분값을 계산한다.</p>'+m('boxgamma')+m('boxfactor')+
 '<p>조화수의 망원합으로 H(0)를 구하고, 합 가능한 균등 도함수 상한으로 실제 급수를 미분한다. 유한 계수합은 원래 Stieltjes 수열과 정확히 같으므로 새 상수를 원하는 값으로 정의하지 않는다. 같은 Gamma·코사인 식은 |s|&lt;1에서 전인자 G_Box를 정의하며 아래 s=0에서의 도함수는 이 국소 확장에 관한 것이다. Gamma 반사·배가 공식을 미분하고 실제 L’Hôpital 극한으로 이차 나머지를 확인한다.</p>'+m('boxnotation')+m('boxderivatives')+m('box_expansion')+m('boxcoefficients')+
 card('원래의 두 전체 모멘트 조건 증명 완료','<p>실제 적분 가능성과 원래 J, q, Stieltjes 극한을 포함한다. RH·외부 문헌 명제·수치 모멘트 가정 없이 컴파일되며 새 소비 정리 안에서 두 증명을 직접 구성한다.</p>','green')+m('box_actual')+m('boxgain')+
 '<p>Mellin 극점을 빼면 표시한 s→0+ 전개를 얻으며 실제 적분 J₀와 J₁은 각각 상수항과 일차항이다. 지배 수렴과 Laurent 곱 극한으로 이 식별을 증명한다. 양의 로그 급수 꼬리로 상한을 0.70875에서 0.70871로 개선하고 실제 ψ, 보통 π, LCM 로그 성장과 primorial 성장에 연결한다.</p>'+
 card('원래 전체 영점 상한 증명 완료',m('boxpacket')+m('boxzerobound')+'<p>일반 Nicolas·BPT 입력과 명제 안의 RH를 사용하여 실제 전체 합 가능성과 원래 영점 상한을 증명했다. 양·음 높이, 중복도, 낮은 높이의 실제 유한 계수, 전체 이차 꼬리와 복소 이동을 모두 포함한다. 평균 명시적 공식도 아래 일반 적분 Perron 정리에서 유도하여 원래 Box 조건 네 개에 대한 증명 공급자를 모두 완성했다. 일반 문헌 정리 자체는 형식화되지 않은 명시적 가정으로 남는다.</p>'+link('Solutions/RHOcticPush.v1/box/zero/BoxZeroEstimate.lean','실제 전체 영점 상한')+'.','green')+m('perron_primary')+m('perron_general')+m('perron_transport')+m('perron_constant_transport')+'<p>첫 표시는 Hildebrand 정리5.18/(5.32), 인쇄면166쪽의 실제 원문 식이며 절대 수렴은 식(5.34),167쪽에서 사용한다. 다음 표시는 더 약한 Lean 문헌 계약으로 덧셈 상수의 존재만 유지하고 x&gt;1에서 사용한다. 원문의 영점 합은 인용한 GM 공식에서 명시한 중복도 규약으로 해석한다. 뒤 계산은 왜 원문 상수의 크기 상한이 필요하지 않은지 정확히 보여 준다. 중복도 규약은 Grenié–Molteni 식 (1.3a), 2쪽에서 명시적으로 확인했다. 상수 C는 표시된 연산에서 소거하며, 불연속인 실제 ψ의 원시함수와 전체 영점·자명한 영점 합을 사용한다. 여기 σ는 Mellin 변수 s와 독립인 실수 로그 이동이고 mρ는 실제 영점 중복도다. Box 공식은 두 이동 σ=±1에서만 적용하며, 별도의 영점 상한은 더 강하게 모든 σ≤1을 다룬다. 여기 Box의 δ는 octic의 (CL/2−1)exp(−L/2)와 다르다. 통합 소비 정리는 네 증명 공급자를 내부에서 구성한다.</p>'+box_pointwise_bridge('KO')+link('Solutions/RHOcticPush.v1/integration/additive/BoxFullNetwork.lean','실제 전체 Box 네트워크')),
 section('additional-literature','추가 전체 함수 문헌 비교의 한계',
 '<p>'+source('https://arxiv.org/html/2403.11814v4','Lee v4, 정리 1.1, 2026년 7월 25일')+'은 아래 θ 전체 함수를 준다. 큰 C에서는 이 함수가 이번 결과보다 강할 수 있으므로 전체 함수 우월성을 주장하지 않는다.</p>'+m('lee_L')+m('lee_short')+
 '<p>'+source('https://doi.org/10.1093/qmath/haad031','Lee, 정리 3.2와 표 4, 인쇄면 1515쪽')+'는 아래의 더 늦은 시작점 가족을 서술한다. 두 연속 구간을 이용하면 충분히 늦은 시작점에서 소수가 많은 구간의 계수를 2에 임의로 가깝게 할 수 있다는 추론이 나온다. 이 추론의 명시적 시작점을 형식화하지 않았으며 해당 문헌의 증명 구절 감사도 남아 있다. 출판된 주장을 비교 한계로 유지하고 점근적 기록을 주장하지 않는다.</p>'+m('lee_published')+
 '<p>절대 ψ 오차에서는 '+source('https://arxiv.org/html/2312.05628v4#S3.SS2','Lee–Nosal v4, 보조정리 3.3')+'의 높이 의존 전체 함수도 정리 1.1·1.2와 함께 비교해야 한다. 그 증명에 사용하는 수치 정규화에는 아래와 같은 수정 문제가 있다. 최종 출판된 PNT 정리가 거짓이라는 결론은 내리지 않는다.</p>'+m('lee_T')+m('lee_lemma')+
 card('독립 확인된 문헌 비교: 영점 역수 합의 양·음 높이',
 '<p><strong>실제 Lean과 Blueprint.</strong> '+link('Solutions/RHOcticPush.v1/comparisons/ZeroInversePaired.lean','actual_both_sign_inverse_lower')+'는 일반 BPT 영점 계수 상한만으로 실제 전체 유한 합이28보다 큼을 증명한다. 유한 집합의 일치, 중복도, 켤레쌍 대응도 증명했다. 새 비교 정리 자체의 독립 Blueprint 명제는 없다. 대응하는 네트워크 정의는 '+link('IEANTN/Nodes/ZeroCount/v1/Conclusions.lean','ZeroCount.v1.zetaNClosed')+'와 '+link('IEANTN/Vocabulary/Zeta.lean','Vocabulary.Zeta.zetaZeroesSum')+'이다.</p>'+
 '<p><strong>먼저 명시된 원문, 다음으로 인용된 입력.</strong> '+source('https://arxiv.org/pdf/2312.05628v4#page=4','Lee–Nosal v4, §2 식(10), 인쇄면4쪽')+'는 첫 부등식을 표시한다. 그 문장이 인용한 '+source('https://arxiv.org/pdf/2204.02588v3#page=5','Fiori–Kadiri–Swidinsky v3, 식(2.4)·표1, 5쪽')+'은 두 번째 줄의 양의 높이만 계산한다.</p>'+m('lee_eq10_printed')+m('fks_table_positive')+
 '<p><strong>정확한 차이와 영향.</strong> 식(10)의 절댓값 높이는 양·음 켤레 영점을 모두 포함하지만 인용된 표의 상수는 양의 높이만 센다. 표의 계산 자체를 가정하지 않고도 BPT와 직접 적분으로 표시된 양·음 전체 상한을 배제한다.</p>'+m('positive_inverse_derivation')+
 '<p>이 커널 증명에는 RH·유한 영점 표·native 실행 사실이 없다. 별도의 독립 원문·Lean 검토와 재컴파일에서도 정확한 차이를 확인했다. 최종 PNT 결론을 반박한 것은 아니다. 인용된 표의 끝점은 엄격히 열린 구간이며, 이를 닫힌 끝점 상한으로 바꾸는 정리는 증명하지 않았다. 표시된 보조정리3.3의 행을 검증된 네트워크로 승격하지 않고 최종 출판 정리의 가족은 계속 비교 한계로 유지한다.</p>','amber')),
 section('nl-comparison','원래2.43 포물선 구간과 폭·개수 목표를 함께 비교',
 '<p>보존한 이전 서면 결과는 아래의 전체 포물선 구간을 사용했다. 폭의 계수는2.43으로 수렴하지만 유한 높이에서 이 숫자만 비교하면 로그 항을 버리게 된다. 같은 실제 왼쪽 끝점에서 전체 구간과 개수 함수를 비교한다.</p>'+m('nl_parabolic_full')+m('nl_matched_comparison')+
 '<p>순수 Lean 증명은 log(L)의 접선 상한,0&lt;δ≤0.0003과 sinh(δ)≥δ를 이용하여 모든 실수 L≥24에서 두 스칼라 비교를 증명한다. 별도의 실제 산술 소비 정리는 새 octic 정리를 적용하여 더 짧은 구간에서 이전의 전체 개수 목표보다 큰 하한을 얻는다. 추가 조건 a≥exp(24)가 필수다. L=24에서 a는 exp(24)보다 조금 작다.</p>'+
 '<p>이전 해석 논증은 독립 검토한 서면 결과로 남으며 원래 서면 비교 실험군을 소급해서 형식화했다고 주장하지 않는다. 새 산술 소비 정리는 RH·Green·Nicolas·BPT를 명시적으로 사용한다. 이전과 새 추이적 문헌 전제 묶음이 다르다는 조건을 유지한 채 공통 적용 범위의 폭과 개수 함수를 비교한다.</p>'+
 '<p>'+link('Solutions/RHExposureStudy.v1/locked/NL_RH/files/Intervals.md','고정한 원래 NL 문장과 증명')+'; '+link('Solutions/RHOcticPush.v1/comparisons/NLParabolicComparison.lean','전체 함수의 스칼라 비교')+'; '+link('Solutions/RHOcticPush.v1/comparisons/NLParabolicConsumer.lean','실제 엄밀한 소수 개수 소비 정리')+'.</p>'),
 section('matrix','주요 결과의 전체 함수와 전제',tier_legend('KO')+matrix_ko+all_input_details_ko),
 section('network','IEANTN에서 실제로 재사용되는 구조',
 '<p>노드의 결론은 타입이 있는 명제이고 Solution은 이름이 붙은 이전 결론에서 새 결론을 증명하는 Lean 증명이다. '
 '공유 vocabulary가 실제 산술 대상과 정규화를 고정한다. 새 버전은 기존 결과를 보존하며, 실제 통합 소비 정리가 '
 '각 연결을 사용한다. 증명 본문을 따라가는 의존성 감사를 수행하므로 단순 import나 소스 읽기를 재사용으로 세지 않는다.</p>'+
 '<p>생성된 Challenge는 문제 명세이며 완료된 증명이 아니다. 증명 경로에서 제외한다. 공식 Comparator 영수증을 '
 '수동으로 만들지 않는다. Goldbach, Möbius/Mertens 등도 적용 가능성을 점검하며, 개선되지 않은 노드나 비활성 최솟값은 '
 '그대로 구분한다. 새 결과를 과거에 고정한 실험군의 발견으로 소급하지 않는다.</p>'+metadata_graph('KO')),
 section('goldbach','실제 산술 소비 정리: 정렬된 Goldbach 표현 개수',m('triples')+m('goldbach_input')+m('triplehyp')+m('triplebound')+'<p>엄밀한 소수 구간의 각 소수 p에 대해 n−p는 4 이상 H 이하인 짝수다. 명시된 유한 이진 Goldbach 가정에서 소수 쌍을 고른 뒤 작은 순서대로 정렬한다. p는 n/2보다 크므로 가장 큰 항이다. 서로 다른 p는 서로 다른 마지막 좌표를 주기 때문에 중복 없는 실제 정렬 삼중항 개수의 하한을 얻는다. 순열을 여러 표현으로 중복 계산하지 않는다.</p><p>수치 모멘트는 소비 정리 안에서 직접 구성한다. 이진 Goldbach와 표시된 기하 조건은 실제 추가 가정이다. 이진 추측을 증명하거나 전역적인 삼진 존재 기록을 주장하는 결과가 아니다.</p>'),
 section('downstream','어떤 산술 결론이 실제로 달라지는가',
 '<h3>연속된 소수 인덱스와 세제곱 구간</h3>'+m('prime_quantiles')+m('cubes_consumer')+
 '<p>q의 인덱스는0부터 시작한다. 엄밀한 소수 개수 하한은 한 소수나 이름 없는 선택값만이 아니라 표시한 블록의 모든 인덱스를 제한한다. 같은 폭에서 더 큰 소수 개수를 보장하므로 이 블록이 커진다. 실제 소비 정리는 PrimeQuantile.v3.optimized_octic_block이다. 기존 연속 세제곱 구간 정리도 계속 사용할 수 있다. Octic의 명시적 문헌 입력을 포함한 RH 결과이며 새로운 세제곱 기록을 주장하지 않는다.</p>'+
 '<h3>LCM과 소수 곱</h3>'+m('arithmetic_products')+
 '<p>정확한 항등식 ψ(n)=log(lcm(1,…,n))과 θ(n)=log(∏p≤n p)으로 Box 전체 함수를 실제 산술 대상으로 옮긴다. LCM 성장은 RH·일반 Perron·Nicolas·BPT를 사용한다. Primorial에는1.01√n 소수 거듭제곱 여유를 위해 Buthe2016.v1.theorem_2_psi가 추가된다. 표시된 개선은 동일한 후속 가정에서 원래 Box 모멘트 함수와 더 강한 함수를 비교한다. 작은 n의 여섯 소수 증인이나 유한 LCM 인증서의 새 결과가 아니다. 후속 소수 제곱 보정은 일반 π를 개선하며 이 ψ·θ 함수를 바꾸지 않는다.</p>'+
 '<h3>적용되지 않는 경우도 구분한다</h3>'+m('mertens_masking')+m('mertens_weight_gap')+
 '<p>이 첫 Mertens 관측량은 가중 소수 합 A이며 Möbius 합 M과 다르다. Büthe의 유한 ψ 여유0.94는11&lt;x≤10^19에서 적용한다. 공통 구간 exp(35)≤x≤10^19의 표시된 최솟값은 그대로0.94다. 따라서 이 구성요소 개선만으로 기존 첫 Mertens 경로의 활성 최솟값이 더 작아지지는 않는다. 영점 가중치도 구분해야 한다. 기존 Mertens 입력은 높이 역제곱 wᴹ을 쓰고 Nicolas 상한은 w를 제한한다. 바로 대입하면 위의 양의 보정항을 빠뜨리며, 이를 대체할 새 수치 모멘트 상한을 주장하지 않는다. Nicolas 결합 정리는 관련된 오일러 곱 정보를 개선한다. 그러나 역제곱 영점 질량만으로는 역수 제타 함수의 유수 정보가 부족하므로 이를 Möbius 합 M(x)의 새 상한으로 바꾸지 않는다.</p>'+
 '<p>'+link('IEANTN/Nodes/PrimeQuantile/v3/Conclusions.lean','정확한 소수 인덱스·세제곱 계약')+'; '+link('Solutions/RHOcticPush.v1/integration/OcticVerifiedEvolution.lean','실제 구간에서 소수 인덱스로의 증명')+'; '+link('Solutions/RHOcticPush.v1/integration/additive/BoxFullNetwork.lean','실제 ψ에서 LCM·primorial로의 연결')+'; '+link('Solutions/RHOcticPush.v1/spectral/FiniteApplicability.lean','전체 구간의 비활성 구성요소 비교')+'.</p>'),
 section('pv','프로그램 검증과 유한 범위의 정확한 상태',
 '<p>PV는 실제 C/C++/CUDA 소스와 실행 모델의 대응, 프로그램의 수학적 정확성, 출력과 최종 산술 정리의 연결을 의미한다. '
 '새 octic 수치는 커널 인증서 검증이다. 새 source-first C 프로그램의 검증이라고 바꾸어 부르지 않는다.</p>'+
 '<p>재사용하는 C 로그 프로그램의 일반 증명 범위는 정수 2부터 2·10¹²까지이고, 계수 프로그램은 0–20 인덱스에서만 '
 '사용한다. 실제 C 소스는 변경하지 않았다. RestrictedC에는 정확한 렌더링 소스의 동일성과 실행 모델 증명이 있지만 '
 '독립적인 파서·렌더러 건전성 정리는 이 백엔드에서 증명하지 않았다. 렌더러와 모델 해석 계약, 컴파일러·런타임·OS/API·'
 '하드웨어, 소스·빌드·실행 대응의 신뢰 경계를 공개한다. 계수 프로그램과 높은 입력 드라이버의 독립적인 부분 프런트엔드는 아래의 별도 새 증명이다.</p>'+finite_ko+finite_completion('KO')+finite_ieantn_completion('KO')+
 ('<p>이전의 작은 검사기 비교는 완료한 고정 계수 증명과 별도로 기록한다. 기존과 정확히 같은 32,768개 레코드를 확인하는 균형 트리 검사기를 증명하고 ' if finite_kernel_done else '<p>전체 유한 소수계수 출력 연결은 미완료다. 기존과 정확히 같은 32,768개 레코드를 확인하는 균형 트리 검사기를 증명하고 ')+
 '약 163초의 독립 재실행 두 번과 약 30.8 GiB 개별 최고 RSS를 기록했다. 추가 순수 재귀 변형은 동일 수치 부분과 일반 연결을 빈 공리 목록으로 182.04초에 증명했으며 개별 최고 RSS는 30.70 GiB였다. Nat.brecOn이 propext의 원인이라는 이전 설명은 잘못되어 철회한다. 기존 비균형 작업은 며칠째 실행 중이었다. '+
 ('이 작은 부분의 비교는 조건이 맞춰진 속도 벤치마크가 아니며 전체 높은 계수 결과에는 별도의 승인 영수증이 있다. 원래 작업과 고정 입력은 보존한다.</p>' if finite_kernel_done else '이는 조건이 맞춰진 속도 벤치마크나 전체 9,067만 레코드 완료가 아니다. 원래 작업과 고정 입력은 보존한다.</p>')+
 '<p>첫 전체 복구에서는 새 모듈528개를 검증하여 산술 부분2,768개 중787개에 도달한 뒤 요청된 정상 종료를 마쳤다. 실행 중인 자식 작업은 모두 자연 종료했으며 기존의 장기 작업5개는 건드리지 않았다. 자원 정책만 바꾼 별도 V2는 실제 소스·해시·의존성 이관을 마친 뒤 수치 작업을 시작했다. 최대22개를 적응적으로 허용하고 호스트용512 GiB와 실행 중 작업의 잠재적 메모리 증가를 남긴다. 부분 계수는 최종 승인 영수증이 아니다. 전체 RSS/PSS, 개별 최고 메모리, 시간과 디스크를 기록하고 확인할 수 없는 커널 OOM 귀속은 미확인으로 남긴다.</p>'+
 '<p>기존 드라이버의 <code>main</code>과 입력38,358,837,683은 보존했다. 별도 추가 C 드라이버는 동일한 계수 프로그램을1,490,000,000,000에서 실제 실행하여55,206,486,339로 해석되는 little-endian 이진 바이트8개를 stdout에 썼다.1.116초, 최고 RSS19.94 MiB를 기록했다. 전체 main 모델 정리는 소스 자체 초기화·계수 함수 호출·출력 바이트·정리를 모든 성공 실행에 대해 증명하며, 구체적인 표준 모델 실행의 존재도 증명했다. '+
 ('고정된 커널 계수 정리는 승인했고 최종 소스·출력 연결은 위에 별도로 기록한다. ' if finite_kernel_done else '고정 수치 출력 연결에는 아직 전체 커널 계수 인증서가 필요하다. ')+
 '새 Lean 모듈 네 개에서 독립적인 C11 부분 표면 문법, 일반 guarded-renderer 건전성과 실제 C 텍스트 두 개의 승인을 증명했다. 새 소스 인덱스 main 존재 정리는 두 일반 건전성 정리를 실제로 사용한다. 해당 문법과 애플리케이션의 새 소스 재현37개는 통과했다. '+
 ('완료한 고정 출력 소비 정리가 이 증명들을 실제로 사용하고 캐시 없는 기반 재현도 통과했다. ' if finite_source_done else ('커널 Final은 승인했고 새 소스·출력 소비 정리와 캐시 없는 기반 재현은 별도 진행 단계다. ' if finite_kernel_done else '고정된 수치 출력의 Final과 캐시 없는 기반 재현은 별도 미완료 작업이다. '))+
 '일반 C 이름 결합·타입 검사·헤더 해석·ISO-C 실행 의미의 적합성을 증명한 것은 아니며, 실제 컴파일 실행과 모델 적용 계약을 명시적으로 남긴다. 이 프런트엔드는 계수 프로그램과 높은 입력 드라이버를 다루며 별도로 재사용한 로그·계수 생성 프로그램을 검증한 것은 아니다.</p>'+
 '<p>전체 애플리케이션32개 모듈의 새 소스 재현과 문법5개 모듈의 추가 재현을 모두 통과하여37개 범위를 확인했다. 문법 감사는 컴파일러가 소유한 실제 정리186개 전체의 표준 공리, 증명 본문 연결19개와 필수 도착점11개를 검사한다. 실제 일반/−O/−OO 문법 대조36개가 통과했다. 이전 애플리케이션 검사기 V2의57개 판정과 별도 보존한 V3의60개 판정도 통과했다. V3에는 중첩된 임시 출력 경로를 거부하는 검사 세 개가 포함된다. 수학적 애플리케이션 소스와 원래 실행은 바꾸지 않았다. 서로 다른 검증 범위의 계수이며 새로운 수치 알고리즘 수가 아니다.</p>'+
 '<p>원래90,670,946개 레코드를25분56.59초, 최고 RSS42.97 GiB로 결정적으로 재생성했다. 압축 데이터 SHA-256, 원래 Lean 소스3,464개의 모든 해시와 순수 검사식2,469개가 일치했다. 독립 검토 후 재생성 가능한 중복 데이터만 정확히12,171,195,019바이트 삭제했다. 원래 입력·승인된 증명·현재 검증 입력은 보존했다. 기존994개 기반의 캐시 없는 소스 재현은 별도 추가 작업이며 최종 상태를 영수증에 명시한다. 과거 캐시 객체만으로 완료를 추정하지 않는다.</p>'),
 section('reproduce','재현과 증거 보존',
 '<p>기준 커밋은 <code>0e2638852a08de84e25f1d179a36356fb12333a5</code>, Lean은 4.34.0-rc2, '
 'Mathlib은 <code>71a80585ee495fc24472fd0eaffc89d94e4fd8d6</code>다. '
 '기준 340개 모듈을 소스에서 새로 빌드한 뒤 새 전체 소비 정리를 확인한다. 개발용 객체 오버레이나 애플리케이션 캐시는 '
 '최종 재현 입력으로 허용하지 않는다. 소스·객체·명령·로그·C include의 해시와 실제 시간·최대 RAM·디스크를 기록한다.</p>'+
 '<p>Python 검증기는 일반 모드, −O, −OO와 변조 시험을 거친다. 실제 가용 RAM과 디스크를 독립적으로 확인하여 자원을 '
 '배정하며 과거 4 GiB 제한을 적용하지 않는다. 실패한 개발 시도, 시간 초과, 스레드 생성 실패와 OOM 증거를 구분한다. '
 '없는 토큰 수치를 파일 수나 시간으로 추측하지 않는다.</p>'+
 '<p>초기 모멘트 수치 배치는 단일 CPU 작업8개를 사용했다. 과거 기본 빌드의 주소 공간 제한은128 GiB, 수정한 깨끗한 빌드는64 GiB다. 큰 계수 증명의 부분 작업에는128 GiB, 최종 조립에는256 GiB 주소 공간 제한을 사용한다. 이 제한값은 실제 물리 RAM 측정치가 아니다.</p>'+reproduction_observation('KO')+measurements('KO')+
 '<p>소스 범위 집합은 서로 겹치므로 단순히 더하지 않는다. 개별 최고 RSS, 표본으로 관측한 전체 RSS/PSS와 실험 소유 파일 크기는 다른 측정 범위다. OOM은 실제 소유 프로세스 증거가 있을 때만 귀속한다.</p>'+
 '<p>재현 README와 고정 매니페스트에 정확한 명령이 있다. 생성된 수치 배열은 다시 검증해야 하는 결정적 제안일 뿐 '
 '그 자체가 정리의 전제가 아니다. 재생성 가능성이 확인된 실험 전용 임시 파일만 정리하고 원문·고정 입력·승인된 증명 '
 '산출물·필수 증거는 보존한다.</p>'+
 '<details><summary>라마누잔 정리의 정확한 입력 아홉 개</summary><ul>'+''.join('<li><code>'+html.escape(x)+'</code></li>' for x in ram_inputs)+'</ul></details>'+
 '<details><summary>기계 판독 최종 상태와 영수증</summary><pre>'+html.escape(json.dumps(status,indent=2,ensure_ascii=False))+'</pre></details>')]

contents_en.append(ram_application('EN'))
contents_ko.append(ram_application('KO'))

contents_en.append(section('ram-inputs', 'Exact Ramanujan hypotheses', ram_assumptions('EN')))
contents_ko.append(section('ram-inputs', '정확한 라마누잔 전제', ram_assumptions('KO')))

from html.parser import HTMLParser

class ProseSpacing(HTMLParser):
    """Normalize word/numeral spacing without changing mathematical or evidence bytes."""
    def __init__(self):
        super().__init__(convert_charrefs=False)
        self.parts = []
        self.skipped = []
    def handle_starttag(self, tag, attrs):
        self.parts.append(self.get_starttag_text())
        if tag in {'math','svg','style','code','pre','a'}:
            self.skipped.append(tag)
    def handle_startendtag(self, tag, attrs):
        self.parts.append(self.get_starttag_text())
    def handle_endtag(self, tag):
        self.parts.append('</'+tag+'>')
        if self.skipped and tag == self.skipped[-1]:
            self.skipped.pop()
    def handle_data(self, value):
        if not self.skipped:
            value = re.sub(r'([A-Za-z]{2,})(?=[0-9])', r'\1 ', value)
            value = re.sub(r'([가-힣])(?=[0-9])', r'\1 ', value)
        self.parts.append(value)
    def handle_entityref(self, name):
        self.parts.append('&'+name+';')
    def handle_charref(self, name):
        self.parts.append('&#'+name+';')
    def handle_comment(self, data):
        self.parts.append('<!--'+data+'-->')
    def handle_decl(self, decl):
        self.parts.append('<!'+decl+'>')

def prose_spacing(value):
    formatter = ProseSpacing()
    formatter.feed(value)
    formatter.close()
    return ''.join(formatter.parts)

def argument_order(parts):
    order = ['results','octic','frontier','box','signed-transfer','clean-pnt',
             'feedback','gm','ramanujan','spectral','nl-comparison','downstream','goldbach',
             'network','matrix','ram-inputs','additional-literature','pv','reproduce']
    keyed = {re.match(r'<section id="([^"]+)"', item).group(1): item for item in parts}
    if len(keyed) != len(parts):
        raise ValueError('Repeated report section identity')
    return [keyed.pop(name) for name in order if name in keyed]+list(keyed.values())

contents_en, contents_ko = argument_order(contents_en), argument_order(contents_ko)
args.out.mkdir(parents=True)
for lang, contents, title in [('EN', contents_en, 'RH Limit Breakthrough Campaign'),
                              ('KO', contents_ko, 'RH 한계 돌파 연구')]:
    names = [('results','Results' if lang=='EN' else '결과'),('octic','Octic'),('frontier','Comparisons' if lang=='EN' else '비교'),
             ('gm','GM / Ramanujan'),('spectral','Spectral' if lang=='EN' else '영점'),('box','Box / Mellin'),
             ('network','IEANTN'),('matrix','Assumptions' if lang=='EN' else '전제'),('goldbach','Goldbach'),('pv','PV / finite counts' if lang=='EN' else 'PV / 유한 계수'),('reproduce','Reproduce' if lang=='EN' else '재현')]
    nav = '<nav aria-label="'+('Contents' if lang=='EN' else '목차')+'">'+''.join('<a href="#'+a+'">'+b+'</a>' for a,b in names)+'</nav>'
    draft = status['status']!='REVIEWED_RESEARCH_RESULTS'
    stamp = ('DRAFT • final source replay and review pending' if lang=='EN' else '초안 • 전체 소스 재현·검토 진행 중') if draft else ('Reviewed results • remaining gaps disclosed' if lang=='EN' else '검토된 결과 • 미완료 조건 공개')
    subtitle = ('23 November 2026 · additive continuation · owner research branch · RH remains a hypothesis' if lang=='EN'
                else '2026년 11월23일 시작한 추가 연구 · 소유자 연구 브랜치 · RH는 가정')
    footer = ('Static offline HTML / MathML. No browser extension, CDN, JavaScript execution or external math font is required to read this report. Claims follow the explicit status receipt; source links open separately.' if lang=='EN'
              else '정적으로 렌더링한 오프라인 HTML / MathML이다. 수학을 읽기 위해 브라우저 확장·CDN·JavaScript 실행·외부 수학 글꼴이 필요하지 않다. 결론은 명시된 상태 영수증을 따르며 소스 링크는 별도로 열린다.')
    page = '<!doctype html><!--'+font_license+'--><html lang="'+('en' if lang=='EN' else 'ko')+'"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1"><title>'+title+'</title><style>'+css+'</style></head><body><main><p class="pill">'+stamp+'</p><h1>'+title+'</h1><p class="muted">'+subtitle+'</p>'+nav+''.join(contents)+'<footer>'+footer+'</footer></main></body></html>'
    page = page.replace('<div class="tablewrap">', '<div class="tablewrap" tabindex="0" role="region" aria-label="Comparison table">')
    (args.out/('RH_OCTIC_RESEARCH_'+lang+'.html')).write_text(prose_spacing(page))

# A separate mathematical exposition keeps the research argument together.
# Detailed execution ledgers remain in the two complete reports and bundle.
paper_title = 'Explicit prime windows and PNT feedback from verified kernel estimates'
paper_intro = section('abstract', 'Abstract',
 '<p>We close the kernel-specific analytic obligations in an explicit octic prime-window argument from named general literature propositions, proving its actual Fourier moment bounds by kernel-checked interval calculation and analytic tails. The resulting whole-ray frontier gives more than √u primes in intervals of width2.14891875√u log(u) for every real u≥exp(24), and a stronger population at unchanged width2.15. A separate Box/Mellin argument proves both exact moment identities and its explicit-formula and infinite-zero adapters. Retaining complex phases through a weighted integration-by-parts identity yields a signed compensation profile with coefficients0.076 and0.055 on their exact rays. Reusing that information at half the logarithmic height gives a noncircular prime-square correction and a stronger complete ordinary-prime-counting function, including a clean21/50 subtractive corollary. Typed arithmetic consumers retain quantitative Ramanujan, prime-index, product and Goldbach-count information. RH and every additional source proposition are explicit; numerical certificate checking, source-program verification and execution observations remain distinct.</p>')
paper_notation = section('notation','Objects and assumptions',
 m('arithmetic_notation')+early_reader_context('EN')+
 '<p>RH is a hypothesis throughout. Except in the explicitly marked Green all-zero formula, ρ denotes a distinct nontrivial zeta zero, mρ its multiplicity and γρ its imaginary part. Euler’s constant is γ. The principal-value logarithmic integral li differs from Li₂ by li(2); the ordinary-prime transfers retain that offset.</p>'+
 '<p>The octic branch takes RH, Green’s general smooth explicit formula, Nicolas’s full spectral summability/bound and BPT’s count estimate away from ordinates. The signed compensation branch takes RH, general integrated Perron and Nicolas. The complete Box ordinary-π branch additionally uses BPT. All three are checked Lean derivations from these explicit literature propositions, rather than a Mathlib-only formalization of the cited source theorems. The entire nine- and eleven-input Ramanujan packages are stated below.</p>')
paper_ram = ram_application('EN')+ram_assumptions('EN')
by_id = {re.match(r'<section id="([^"]+)"', item).group(1): item for item in contents_en}
paper_order = ['octic','frontier','box','signed-transfer','feedback','gm',
               'nl-comparison','spectral','downstream','goldbach','network','additional-literature']
paper_parts = [paper_intro, paper_notation]
for key in paper_order:
    part = by_id[key]
    if key == 'frontier':
        part = part.replace('Its status is the same as the numerical gate above;',
                            'The actual moment certificates and analytic tails establish these inequalities;')
    paper_parts.append(part)
    if key == 'gm':
        paper_parts.append(paper_ram)
paper_parts.append(section('proof-boundary','Mathematical and computational proof boundaries',
 tier_legend('EN')+finite_ieantn_completion('EN')+
 '<p>The mathematical consumer interfaces fix actual arithmetic objects and their full domains. A compiled proof may be conditional on RH and genuine general literature inputs while fully discharging the kernel-specific predicates. The source packages, rather than only a rounded coefficient, determine which comparisons use identical hypotheses. Pure function comparisons do not assert measured arithmetic errors or a global published minimum.</p>'+
 '<p>Numerical endpoint and all-real interval certificates are checked by the Lean kernel. They are not source-first PV. The finite prime-counter work separately connects the actual C source fragments to an independently specified syntax and an execution model, with explicit compiler, header, ABI, runtime, stdio, OS, hardware and model-applicability contracts. Its fixed numerical-output and clean-reproduction status follows the dated receipt in the complete research report; no unfinished numerical output is used as a premise of the analytic theorems here.</p>'+
 '<p>No optimality or global best-known-result claim is made. The displayed Lee–Nosal function comparison covers the two exact theorem envelopes, while its additional height family and other finite bounds remain relevant. The separate as-written reciprocal-zero normalization finding does not refute the paper’s final PNT conclusions. The optional context at the start explains the separately preserved earlier experiments.</p>'))
paper = '<!doctype html><!--'+font_license+'--><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1"><title>'+paper_title+'</title><style>'+css+'</style></head><body><main><p class="pill">'+('Draft mathematical exposition' if status['status']!='REVIEWED_RESEARCH_RESULTS' else 'Reviewed mathematical exposition')+'</p><h1>'+paper_title+'</h1><p class="muted">Source-conditional Lean mathematics · explicit real domains · preserved experimental outcomes</p>'+''.join(paper_parts)+'<footer>All mathematics is statically rendered for offline reading. The complete bilingual reports and reproducibility bundle provide the exact source, claim and execution receipts.</footer></main></body></html>'
paper = paper.replace('<div class="tablewrap">','<div class="tablewrap" tabindex="0" role="region" aria-label="Comparison table">')
(args.out/'RH_OCTIC_PAPER_EN.html').write_text(prose_spacing(paper))
manifest = {'status':'REPORTS_GENERATED_FROM_EXPLICIT_STATUS','draft':status['status']!='REVIEWED_RESEARCH_RESULTS',
            'status_sha256':hashlib.sha256(args.status.read_bytes()).hexdigest(),
            'renderer':'KaTeX0.16.47 build-time nativeMathML, no runtime/CDN',
            'files':[{'path':p.name,'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
                     for p in sorted(args.out.glob('*.html'))]}
(args.out/'REPORT_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(manifest))
