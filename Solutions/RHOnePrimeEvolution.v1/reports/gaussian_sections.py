"""New Gaussian Fourier/ANT result; all mathematical displays come from static m()."""
from html import escape


def _writers(lang, link, source):
    if lang.lower() not in ('en', 'ko'):
        raise ValueError('Gaussian report language must be EN or KO')
    ko = lang.lower() == 'ko'
    def t(en, kr): return kr if ko else en
    def p(en, kr): return '<p>' + escape(t(en, kr)) + '</p>'
    def h(en, kr): return '<h3>' + escape(t(en, kr)) + '</h3>'
    def refs(*xs): return '<p class="source-links">' + ' · '.join(xs) + '</p>'
    def section(identifier, en, kr, body):
        return '<section id="' + identifier + '"><h2>' + escape(t(en, kr)) + '</h2>' + body + '</section>'
    return t, p, h, refs, section


def _source_links(link, source, refs, t):
    return refs(
        source('https://arxiv.org/pdf/1708.04122v2#page=2', t('CMS (1.3): admissible functions and extremal constant', 'CMS (1.3): 허용 함수와 극값 상수')),
        source('https://arxiv.org/pdf/1708.04122v2#page=5', t('CMS (1.11)–(1.14): B, Theorem 3 and Corollary 4', 'CMS (1.11)–(1.14): 상수와 정리 3·따름정리 4')),
        link('Solutions/RHOnePrimeEvolution.v1/gaussian_gap/SOURCE_LEDGER.html', t('Rendered primary-source correspondence and allowance derivation', '수식이 렌더링된 원문 대응과 허용량 유도')),
        link('IEANTN/Nodes/CMSFunctionalInput/v1/Conclusions.lean', t('CMSFunctionalInput.v1: exact source contracts', 'CMSFunctionalInput.v1: 정확한 원문 계약')),
    )


def render_gaussian_frontier(lang, m, link, source):
    """Self-contained main-result exposition for the one-prime frontier report."""
    t, p, h, refs, section = _writers(lang, link, source)
    out = [
        '<div class="lead">',
        p('A new rational polynomial-Gaussian witness now gives a proved asymptotic prime-gap improvement. Its actual Fourier transform, full norm, positive Fourier leakage and final number-theoretic consumers have been connected in Lean. The analytic CMS reduction remains an explicit literature-backed mathematical input.',
          '새 유리수 다항식·가우스 증인으로 점근적 소수 간격 상수의 개선을 증명했다. 실제 푸리에 변환, 전체 노름, 푸리에 변환의 양의 꼬리 적분, 최종 정수론 소비 정리까지 Lean으로 연결했다. CMS의 해석학적 환원 정리는 문헌에 근거한 명시적 수학 입력으로 남긴다.'),
        '</div>',
        h('Functions, primes and endpoint conventions', '함수, 소수열, 끝점 규약'),
        p('Thirteen fixed rational coefficients determine two even rational polynomials of degree twenty-four. The physical function and its proposed transform are defined below; the equality with the actual Fourier integral is proved, not assumed. Prime counting includes the right endpoint, and the prime sequence starts at index zero.',
          '고정된 유리수 계수 13개가 24차 짝다항식 두 개를 결정한다. 물리 공간 함수와 그 변환 함수를 아래와 같이 정의한다. 실제 푸리에 적분과의 일치는 가정하지 않고 증명했다. 소수계수함수는 오른쪽 끝점을 포함하며 소수열의 인덱스는 0부터 시작한다.'),
        m('GF_functions'), m('GF_prime_objects'),
        p('The half-open population count used by the CMS asymptotic theorem is also fixed here. It includes a prime at the upper endpoint. The earlier explicit octic population nodes use a strictly open interval; their endpoint convention is preserved.',
          'CMS 점근 정리에 쓰는 반열린 구간의 소수 개수도 여기서 고정한다. 오른쪽 끝점의 소수는 포함한다. 앞선 명시적 옥틱 소수 개수 노드는 양쪽 끝점을 제외하는 열린 구간을 사용하며, 그 규약을 그대로 보존한다.'),
        m('GF_population_objects'),
        refs(link('Solutions/RHOnePrimeEvolution.v1/gaussian_kernel/GaussianSources.lean', 'Exact rational polynomial coefficients'),
             link('Solutions/RHOnePrimeEvolution.v1/gaussian_kernel/GaussianPhysical.lean', 'Actual physical functions'),
             link('IEANTN/Vocabulary/CMSFunctional.lean', 'Exact prime sequence, count and functional definitions')),
    ]
    out += [
        h('The new prime-gap theorem', '새 소수 간격 정리'),
        p('Assume RH and the universal CMS gap-reduction input specified below. Then every positive error allowance gives a bound at every sufficiently large prime index. The threshold is existential: no explicit starting index or real starting point is supplied by this asymptotic result.',
          'RH와 아래에 명시한 일반 CMS 간격 환원 입력을 가정한다. 그러면 임의의 양의 오차 허용량에 대해 충분히 큰 모든 소수 인덱스에서 다음 경계가 성립한다. 시작점은 존재만 증명하며, 이 점근 결과는 구체적인 시작 인덱스나 실수 시작점을 제시하지 않는다.'),
        m('GF_input_names'), m('GF_gap'), m('GF_gap_strict'),
        p('The strict eventual comparison follows by choosing an error allowance smaller than the gap between the two displayed constants. It compares the new coefficient with the strongest matched asymptotic one-prime benchmark examined in this study. The published statement itself is shown for comparison.',
          '엄격한 점근 비교는 두 상수의 차이보다 작은 오차 허용량을 선택해 얻는다. 이는 이번 연구에서 같은 점근적 한 소수 문제에 대해 확인한 가장 강한 비교 기준과 새 계수를 비교한 것이다. 비교 대상의 실제 원문 명제도 함께 표시한다.'),
        m('GF_published_gap'),
        p('The published bound is not asserted to be optimal, and this comparison is not an exhaustive global best-known-result claim. The new asymptotic theorem and the earlier finite-onset one-prime bounds answer different quantitative questions; the earlier explicit results remain available.',
          '원문 경계의 최적성을 가정하지 않으며, 이 비교가 모든 문헌을 포괄하는 세계 최선 기록 주장인 것도 아니다. 새 점근 정리와 앞선 명시적 시작점의 한 소수 정리는 서로 다른 정량적 질문에 답한다. 기존 명시적 결과도 계속 사용할 수 있다.'),
        refs(link('Solutions/RHOnePrimeEvolution.v1/gaussian_gap/GaussianAsymptoticConsumers.lean', 'Actual gap and strict-comparison proofs'),
             link('IEANTN/Nodes/RHAsymptoticGaussian/v1/Conclusions.lean', 'Canonical asymptotic conclusions'),
             source('https://zenodo.org/records/24429650/files/prime-gaps-v2.pdf#page=1', 'Blanquer Robles 2026 v2, Theorem 1, page 1')),
    ]
    out += [
        h('The numerical functional is an actual integral theorem', '수치 목적함수는 실제 적분에 관한 정리이다'),
        p('The complete real-line norm and the complete positive exterior leakage are bounded. The value at zero and these two bounds prove a positive denominator and the inverse-functional estimate by exact arithmetic. None of these numerical bounds is an extra premise of the final witness.',
          '실수축 전체의 노름과 푸리에 변환의 양의 바깥 꼬리 적분 전체에 경계를 준다. 원점의 값과 이 두 경계를 사용하여 분모의 양수성과 역목적함수 경계를 정확한 산술로 증명한다. 이 수치 경계들은 최종 증인의 추가 가정으로 주어지지 않는다.'),
        m('GF_integral_definitions'), m('GF_integral_bounds'), m('GF_denominator_steps'),
        p('The real Fourier pair is eligible for the source theorem: continuity, evenness, integrability, nonzero physical function, genuine Fourier identity and integrability of the positive exterior part are all discharged by proved declarations.',
          '이 실수 푸리에 쌍은 원문 정리에 사용할 수 있는 조건을 만족한다. 연속성, 짝함수 성질, 적분 가능성, 영함수가 아니라는 사실, 실제 푸리에 항등식, 양의 바깥 꼬리의 적분 가능성을 모두 증명된 선언으로 해결했다.'),
        refs(link('Solutions/RHOnePrimeEvolution.v1/gaussian_kernel/GaussianWings.lean', 'Full exterior integral and functional proof'),
             link('Solutions/RHOnePrimeEvolution.v1/gaussian_gap/GaussianEligibility.lean', 'Every eligibility condition and positive denominator'),
             link('Solutions/RHOnePrimeEvolution.v1/gaussian_kernel/GaussianNumericalAudit.lean', 'Exact numerical theorem types and axiom audits')),
        h('Why the proposed transform is the true Fourier transform', '제시한 변환 함수가 실제 푸리에 변환인 이유'),
        p('The proof starts from Mathlib’s Gaussian Fourier identity and differentiates the Fourier integral under proved integrability hypotheses. The map T below is the rational-linear transformation on even polynomials, fixed by its value on the constant polynomial and the displayed recurrence. Multiplication by the squared scaled physical argument applies E to the output polynomial. Iterating this rule from T(1)=1 and checking all twenty-five coefficient positions proves the exact transform association of the two actual source polynomials.',
          'Mathlib의 가우스 푸리에 항등식에서 출발하여, 증명된 적분 가능성 조건 아래에서 푸리에 적분을 미분한다. 아래의 T는 짝다항식 공간의 유리수 선형 변환이며, 상수 다항식에서의 값과 표시한 점화식으로 정한다. 물리 공간의 스케일된 변수의 제곱을 곱하면 출력 다항식에 E를 적용한다. T(1)=1에서 이 규칙을 반복하고 계수 위치 25개를 모두 확인하여 실제 소스 다항식 두 개의 정확한 변환 관계를 증명한다.'),
        m('GF_fourier_recurrence'),
        p('The finite rational-list interpreter is proved correct for polynomial evaluation before its actual coefficient identity is checked in the kernel. A Laguerre-family label, an optimizer’s output or a numerical Fourier sample does not supply this identity.',
          '유한 유리수 리스트 해석기가 실제 다항식 평가와 일치함을 먼저 증명한 뒤, 실제 계수 항등식을 커널에서 확인한다. 라게르 계열이라는 이름, 최적화기의 출력, 수치 푸리에 표본으로 이 항등식을 대신하지 않는다.'),
        refs(link('Solutions/RHOnePrimeEvolution.v1/gaussian_fourier/GaussianFourierCore.lean', 'Gaussian transform and differentiated Fourier semantics'),
             link('Solutions/RHOnePrimeEvolution.v1/gaussian_fourier/GaussianFourierEven.lean', 'Proved even-step recurrence'),
             link('Solutions/RHOnePrimeEvolution.v1/gaussian_fourier/GaussianActualTransform.lean', 'Actual exact coefficient association'),
             link('Solutions/RHOnePrimeEvolution.v1/gaussian_fourier/GaussianActualFourier.lean', 'Actual Fourier identity and admissibility facts')),
    ]
    out += [
        h('How the numerical proof closes the integrals', '수치 증명이 적분을 완성하는 방법'),
        p('The untrusted generator proposes a rational partition and polynomial majorants. A general soundness theorem checks exact affine substitution of the actual source polynomial, its absolute-value or positive-part majorant, its Taylor product, exact polynomial integration, exponential range reduction and the final inequality. Cells near an uncertain sign change use a proved constant majorant, so no unproved root certificate is needed.',
          '신뢰하지 않는 생성기가 유리수 분할과 다항식 우세함수를 제안한다. 일반 건전성 정리는 실제 소스 다항식의 정확한 아핀 치환, 절댓값 또는 양의 부분을 덮는 우세함수, 테일러 곱, 정확한 다항식 적분, 지수함수 범위 축소, 최종 부등식을 확인한다. 부호 변화가 불확실한 셀에서는 증명된 상수 우세함수를 사용하므로, 증명되지 않은 근 인증서에 의존하지 않는다.'),
        m('GF_cell_taylor'), m('GF_polynomial_integral'),
        p('The proof consumes every cell: three hundred ten norm cells and two hundred fifty-four positive-wing cells, stored in eight finite certificate modules. A separate analytic theorem bounds the infinite tail for every monomial degree used by the witness. It is then summed with the actual rational coefficients, and the full-line symmetry and pi scaling are proved.',
          '노름 셀 310개와 양의 꼬리 셀 254개를 모두 증명에서 소비하며, 유한 인증서는 모듈 8개에 담는다. 별도의 해석학 정리로 증인에 사용한 모든 단항식 차수의 무한 꼬리를 제어한다. 이를 실제 유리수 계수로 합한 뒤, 실수축 전체에 대한 대칭성과 원주율을 포함한 스케일 변환까지 증명한다.'),
        m('GF_tail'), m('GF_finite_and_tail'), m('GF_raw_scaling'),
        p('These are kernel-verified mathematical computations, classified as D here. They are not source-first PV: this work does not claim a verified correspondence from a C, C++ or CUDA implementation to the execution model. The linear-programming search and the Python certificate generator remain untrusted suggestions; the mathematical statements follow from the checked Lean proofs.',
          '이는 커널로 검증한 수학적 계산이며, 여기서는 D로 분류한다. 소스 우선 프로그램 검증인 PV라고 부르지 않는다. 이 작업은 C, C++, CUDA 구현과 실행 모델의 대응을 증명했다고 주장하지 않는다. 선형계획 탐색과 파이썬 인증서 생성기는 신뢰하지 않는 제안자이며, 수학적 명제는 검사된 Lean 증명에서 나온다.'),
        refs(link('Solutions/RHOnePrimeEvolution.v1/gaussian_kernel/GaussianCertificate.lean', 'General certificate soundness theorem'),
             link('Solutions/RHOnePrimeEvolution.v1/gaussian_kernel/GaussianAssembly.lean', 'Every accepted cell is assembled'),
             link('Solutions/RHOnePrimeEvolution.v1/gaussian_kernel/GaussianTail.lean', 'Actual infinite-tail theorem'),
             link('Solutions/RHOnePrimeEvolution.v1/gaussian_kernel/GaussianFullRays.lean', 'Exact tails and pi bounds'),
             link('Solutions/RHOnePrimeEvolution.v1/gaussian_kernel/reproduce.py', 'Deterministic regeneration and fresh verification')),
    ]
    out += [
        h('The precise literature input that turns the witness into primes', '증인에서 소수로 넘어가는 정확한 문헌 입력'),
        p('CMS defines the following extremal problem over even continuous real integrable functions. The source’s short-interval Brun–Titchmarsh constant and its published upper bound determine the exterior penalty used by this witness.',
          'CMS는 짝함수인 연속 실수 적분 가능 함수에 대해 다음 극값 문제를 정의한다. 원문의 짧은 구간 브룬–티치마시 상수와 그 문헌 상한이 이 증인에서 사용하는 바깥 꼬리 벌점을 결정한다.'),
        m('GF_CMS_extremal'), m('GF_CMS_B'),
        p('The actual source theorems give the normalized-gap bound and the population-coefficient infimum below. In the population expression, a coefficient is good only when its limiting normalized prime count is strictly above the requested density.',
          '실제 원문 정리는 아래의 정규화된 간격 경계와 소수 개수 계수 집합의 하한 경계를 준다. 소수 개수 식에서는 정규화한 개수의 극한 하한이 요구 밀도보다 엄격히 큰 계수만 허용한다.'),
        m('GF_CMS_conclusions'), m('GF_source_allowance'),
        p('The displayed allowance is the full transfer: positive leakage makes replacing the source penalty by its upper bound safe; the admissible witness bounds the source supremum from below; inversion gives the inverse-functional upper bound. Lean consumes the two universal source-reduction clauses as explicit B inputs. The CMS analytic argument itself is not formalized from RH inside Mathlib, and those clauses contain no Gaussian coefficient or improved numerical result.',
          '표시한 식이 변환의 전 과정을 보여 준다. 꼬리 적분이 음이 아니므로 원문 벌점을 그 상한으로 바꾸어도 유효하고, 허용된 증인이 원문 상한을 아래에서 제어하며, 역수를 취해 역목적함수 상한을 얻는다. Lean은 두 일반 원문 환원 절을 명시적 B 입력으로 사용한다. CMS의 해석학 논증 자체를 Mathlib 안에서 RH로부터 형식화한 것은 아니며, 이 두 절에는 가우스 계수나 개선된 수치 결론이 들어 있지 않다.'),
        p('The new contracts have no separate Blueprint theorem label; the linked definitions-only node and generated Challenge are their Blueprint-facing correspondence. The source ledger states the primary formulas and the derived allowances explicitly.',
          '새 계약에는 별도의 Blueprint 정리 표지가 없다. 연결한 정의 전용 노드와 생성된 Challenge가 Blueprint에 대응하는 명제를 담는다. 원문 대장은 일차 문헌의 식과 그로부터 추가한 허용량을 명시한다.'),
        _source_links(link, source, refs, t),
    ]
    out += [
        h('One witness also gives an asymptotic population curve', '하나의 증인에서 나오는 점근적 소수 개수 곡선'),
        p('The same objective bound is supplied to the CMS population input. For every nonnegative requested density and every positive width allowance, Lean proves a positive eventual count margin. This is stronger than merely producing one prime, and the positive width allowance is retained instead of claiming that an infimum is attained.',
          '같은 목적함수 경계를 CMS 소수 개수 입력에도 공급한다. 임의의 음이 아닌 요구 밀도와 양의 너비 허용량에 대해, Lean은 충분히 큰 곳에서 양의 개수 여유가 존재함을 증명한다. 이는 소수 하나의 존재만 보이는 것보다 강한 결론이며, 계수 집합의 하한이 실제로 달성된다고 주장하지 않고 양의 너비 허용량을 유지한다.'),
        m('GF_population_curve'), m('GF_population_count'),
        p('A separate Lean theorem proves the pointwise comparison with the older CPJ coefficient curve. This does not dominate all newer population bounds. For ordinary primes, the 2026 paper’s two printed affine alternatives below can be stronger in part of the density range; its ordinary-RH specialization is stated at the end of Section 3.',
          '별도의 Lean 정리로 이전 CPJ 계수 곡선과의 점별 비교도 증명한다. 그렇다고 더 최근의 모든 소수 개수 경계를 지배하는 것은 아니다. 일반 소수에 대해서는 2026년 논문에 인쇄된 두 아핀 경계가 밀도 범위 일부에서 더 강할 수 있다. 일반 RH만을 사용하는 특수화는 그 논문 3절 끝에 명시되어 있다.'),
        m('GF_population_old_comparison'), m('GF_population_2026'),
        refs(link('Solutions/RHOnePrimeEvolution.v1/gaussian_gap/GaussianAsymptoticConsumers.lean', 'Population margin, actual counts and old-curve comparison'),
             source('https://arxiv.org/pdf/2005.02393v3#page=2', 'CPJ–de Laat, Section 1.3: printed older population curve'),
             source('https://zenodo.org/records/24429650/files/prime-gaps-v2.pdf#page=2', 'Blanquer Robles Theorem 2, equation (2), page 2'),
             source('https://zenodo.org/records/24429650/files/prime-gaps-v2.pdf#page=10', 'Ordinary-RH specialization, end of Section 3')),
        h('The closed result and the still external sharper candidates', '완성된 결과와 여전히 외부 계산인 더 날카로운 후보'),
        p('The columns show the Laguerre search degree, an inverse-functional value or bound and its evidence class. The approximation symbol in the middle row is a search estimate, not a directed enclosure. Search degree twelve uses thirteen rational coefficients and gives the degree-twenty-four polynomials above. The first row now includes the true Fourier identity and the conditional ANT consumer; D denotes a kernel-proved derivation and E external computational evidence.',
          '열은 라게르 탐색 차수, 역목적함수의 값 또는 경계, 증거 분류를 나타낸다. 가운데 행의 근사 기호는 탐색 추정치이며 방향성 구간 포함 경계가 아니다. 탐색 차수 12는 유리수 계수 13개를 사용하며 위의 24차 다항식을 만든다. 첫 행에는 실제 푸리에 항등식과 조건부 정수론 소비 정리까지 연결되어 있다. D는 커널로 증명한 유도 결과, E는 외부 계산 증거이다.'),
        m('GF_evidence_status'),
        p('The completed kernel theorem deliberately uses a looser enclosure than the external numerical search estimate for the same degree-twelve candidate. The tighter numerical value has not been substituted into the verified theorem. The degree-forty candidate and the other external search outputs retain their separate E status.',
          '완료된 커널 정리는 같은 12차 후보의 외부 수치 탐색 추정치보다 여유 있는 경계를 사용한다. 별도로 일치시킨 방향성 Arb 출력도 불완전한 실행 기록을 명시하여 E로 보관한다. 더 날카로운 수치를 검증된 정리에 대신 넣지 않았다. 40차 후보와 다른 외부 탐색 출력은 별도의 E 상태로 유지한다.'),
    ]
    return section('gaussian-frontier', 'A new Gaussian witness reaches actual prime-gap and population theorems', '새 가우스 증인에서 실제 소수 간격·개수 정리까지', ''.join(out))


def render_gaussian_network(lang, m, link, source):
    """Typed-network consequence of the same proved Gaussian witness."""
    t, p, h, refs, section = _writers(lang, link, source)
    out = [
        p('A second network path now starts from a new, fully proved polynomial-Gaussian Fourier witness. Its numerical argument is passed to actual theorem consumers for asymptotic prime gaps and a whole population-width curve. The earlier explicit octic population, power, index and Goldbach paths remain preserved.',
          '네트워크의 두 번째 경로는 완전히 증명된 새 다항식·가우스 푸리에 증인에서 출발한다. 그 수치 증명을 실제 정리 소비자에게 전달하여 점근적 소수 간격과 소수 개수·너비 곡선 전체를 얻는다. 기존의 명시적 옥틱 개수, 거듭제곱, 인덱스, 골드바흐 경로도 보존한다.'),
        h('The proved mathematical input', '증명된 수학 입력'),
        p('Two explicit even rational polynomials specify the physical function and its transform. Thirteen fixed rational coefficients select this degree-twenty-four pair. The actual Fourier identity and all three raw integral/value bounds below are proved; the linear-programming search and certificate generation are untrusted ways to suggest the input.',
          '명시적인 짝 유리수 다항식 두 개가 물리 공간 함수와 그 변환을 정한다. 고정된 유리수 계수 13개로 이 24차 다항식 쌍을 선택한다. 실제 푸리에 항등식과 아래의 세 가지 원시 적분·값 경계를 모두 증명했다. 선형계획 탐색과 인증서 생성은 입력을 제안하는 신뢰하지 않는 방법이다.'),
        m('GF_functions'), m('GF_integral_definitions'), m('GF_integral_bounds'), m('GF_denominator_steps'),
        p('This numerical result is derived by the kernel. Its proof checks every one of the five hundred sixty-four cells in eight modules, proves the actual polynomial-to-Fourier correspondence, and closes the infinite tails, integrability, symmetry and pi scaling. It is D, not source-first PV; no C, C++ or CUDA source-to-execution correspondence is claimed.',
          '이 수치 결과는 커널이 확인한 유도 결과이다. 모듈 8개의 셀 564개를 모두 검사하고, 실제 다항식에서 푸리에 변환으로의 대응을 증명하며, 무한 꼬리, 적분 가능성, 대칭성, 원주율 스케일 변환을 완성했다. 이는 D이며 소스 우선 PV는 아니다. C, C++, CUDA 소스와 실행 사이의 대응을 증명했다고 주장하지 않는다.'),
        refs(link('Solutions/RHOnePrimeEvolution.v1/gaussian_kernel/GaussianCertificate.lean', 'General actual-integral checker theorem'),
             link('Solutions/RHOnePrimeEvolution.v1/gaussian_fourier/GaussianActualFourier.lean', 'True Fourier identity of the actual functions'),
             link('Solutions/RHOnePrimeEvolution.v1/gaussian_kernel/GaussianWings.lean', 'Full actual-integral functional bounds')),
        h('Three canonical nodes, with actual proof arguments', '실제 증명 인자를 사용하는 정식 노드 세 개'),
        '<div class="table-scroll" style="overflow-x:auto;max-width:100%" tabindex="0" role="group" aria-label="'+escape(t('Canonical node contracts','정식 노드 계약'))+'"><table style="min-width:640px;width:100%;border-collapse:collapse"><thead><tr><th>' + escape(t('Node', '노드')) + '</th><th>' + escape(t('Mathematical role', '수학적 역할')) + '</th><th>' + escape(t('Proof boundary', '증명 경계')) + '</th></tr></thead><tbody>',
        '<tr><td><code>CMSFunctionalInput.v1</code></td><td>' + escape(t('Two universal source clauses: gap reduction and population reduction.', '일반 원문 절 두 개: 간격 환원과 소수 개수 환원.')) + '</td><td>' + escape(t('Explicit literature-backed B inputs; no candidate coefficient or new numerical conclusion is assumed.', '문헌에 근거한 명시적 B 입력이다. 후보 계수나 새 수치 결론을 가정하지 않는다.')) + '</td></tr>',
        '<tr><td><code>GaussianFourierWitness.v1</code></td><td>' + escape(t('An eligible actual Fourier pair with raw norm/leakage/value bounds, then a derived positive-denominator objective witness.', '실제 푸리에 쌍의 사용 조건과 원시 노름·꼬리·원점 값 경계, 그로부터 유도한 양의 분모 목적함수 증인.')) + '</td><td>' + escape(t('The supplied raw witness is destructured and all three bounds are consumed by exact arithmetic.', '전달받은 원시 증인을 분해하고 세 경계를 모두 정확한 산술에 사용한다.')) + '</td></tr>',
        '<tr><td><code>RHAsymptoticGaussian.v1</code></td><td>' + escape(t('Four conclusions: normalized gaps, strict printed-benchmark comparison, population curve, actual population count.', '결론 네 개: 정규화 간격, 원문 기준과의 엄격 비교, 소수 개수 곡선, 실제 소수 개수.')) + '</td><td>' + escape(t('Gap and population consumers use their respective CMS clause, RH and the passed objective witness.', '간격과 개수 소비자는 각각 해당 CMS 절, RH, 전달된 목적함수 증인을 사용한다.')) + '</td></tr>',
        '</tbody></table></div>',
        m('GF_typed_edges'),
        p('A Conclusion is a proposition with an exact mathematical type. Metadata names its imported propositions; the generated Challenge exposes the required proof arguments; a Solution proves the conditional function. Here the raw-to-objective Solution uses its supplied witness, and the asymptotic consumers use the objective witness they are passed. The new numerical proof is therefore a consumed mathematical dependency.',
          'Conclusion은 정확한 수학적 타입을 갖는 명제이다. 메타데이터는 가져올 명제를 지정하고, 생성된 Challenge는 필요한 증명 인자를 드러내며, Solution은 그 조건부 함수를 증명한다. 여기서는 원시 증인을 목적함수 증인으로 바꾸는 Solution이 전달된 증인을 실제로 사용하며, 점근 소비자도 전달받은 목적함수 증인을 사용한다. 따라서 새 수치 증명은 실제로 소비되는 수학적 의존성이다.'),
        refs(link('IEANTN/Nodes/CMSFunctionalInput/v1/Conclusions.lean', 'Both general source clauses'),
             link('IEANTN/Nodes/GaussianFourierWitness/v1/Conclusions.lean', 'Raw and objective witness propositions'),
             link('IEANTN/Nodes/RHAsymptoticGaussian/v1/Conclusions.lean', 'Four canonical asymptotic outputs'),
             link('Solutions/RHOnePrimeEvolution.v1/gaussian_gap/GaussianNumericalWitness.lean', 'Raw input is consumed in the objective proof'),
             link('Solutions/RHOnePrimeEvolution.v1/gaussian_gap/GaussianCanonicalConsumers.lean', 'The passed objective is consumed by actual ANT proofs')),
    ]
    out += [
        h('The resulting prime-gap and count branches', '그 결과 얻는 소수 간격과 개수 분기'),
        p('For this branch the primes are indexed from zero and ordinary prime counting includes the upper endpoint. Under RH and the corresponding CMS source clause, the one certified witness yields the following eventual gap and population statements. No explicit onset is asserted.',
          '이 분기에서는 소수 인덱스가 0부터 시작하며 보통의 소수계수함수는 오른쪽 끝점을 포함한다. RH와 해당 CMS 원문 절 아래에서 인증된 증인 하나로 다음 점근적 간격 및 개수 명제를 얻는다. 명시적 시작점을 주장하지 않는다.'),
        m('GF_prime_objects'), m('GF_population_objects'), m('GF_input_names'), m('GF_gap'), m('GF_gap_strict'), m('GF_population_curve'), m('GF_population_count'),
        p('The positive eventual margin in the curve gives the strict count statement. A separate proved comparison improves the older CPJ coefficient curve. Newer 2026 affine population bounds can be stronger for some densities; this branch is not declared an optimal population frontier.',
          '곡선 정리의 양의 점근적 여유로부터 엄격한 개수 명제를 얻는다. 별도의 증명된 비교로 이전 CPJ 계수 곡선도 개선한다. 그러나 더 최근의 2026년 아핀 개수 경계가 일부 밀도에서 더 강할 수 있으므로, 이 분기를 최적 소수 개수 경계라고 선언하지 않는다.'),
        m('GF_population_old_comparison'), m('GF_population_2026'),
        p('The new count is half-open, while the preserved explicit octic count is strictly open. Its asymptotic curve has no numerical onset. It therefore does not silently replace the earlier finite-onset inputs for the cube, prime-index or Goldbach theorems. The newly completed typed fanout is the gap/population family stated here.',
          '새 개수는 반열린 구간을 사용하지만 기존의 명시적 옥틱 개수는 열린 구간을 사용한다. 또한 새 점근 곡선에는 수치 시작점이 없다. 따라서 세제곱, 소수 인덱스, 골드바흐 정리의 명시적 시작점 입력을 조용히 대체하지 않는다. 이번에 완성한 타입 기반 분기는 여기 명시한 간격·개수 정리 계열이다.'),
        refs(link('Solutions/RHOnePrimeEvolution.v1/gaussian_gap/GaussianAsymptoticConsumers.lean', 'Actual family and strict-count proofs'),
             source('https://arxiv.org/pdf/2005.02393v3#page=2', 'CPJ–de Laat, Section 1.3: printed older population curve'),
             source('https://zenodo.org/records/24429650/files/prime-gaps-v2.pdf#page=2', '2026 Theorem 2, equation (2): competing printed population curves'),
             source('https://zenodo.org/records/24429650/files/prime-gaps-v2.pdf#page=10', 'Ordinary-RH specialization, end of Section 3')),
        h('The source assumptions stay visible', '원문 가정은 드러나 있게 유지한다'),
        p('The generic CMS source input comes from its extremal definition and its gap/population theorems, using the published Brun–Titchmarsh allowance. The primary statements and the reciprocal transfer are displayed below. The actual Gaussian eligibility and numerical estimates are discharged locally; the general analytic reduction remains B rather than an RH-only theorem proved inside Mathlib.',
          '일반 CMS 원문 입력은 극값 정의와 간격·개수 정리, 그리고 문헌의 브룬–티치마시 허용량에서 온다. 일차 문헌의 명제와 역수 변환을 아래에 표시한다. 실제 가우스 증인의 조건과 수치 경계는 이 작업에서 해결했지만, 일반 해석학 환원은 Mathlib 안에서 RH만으로 증명한 정리가 아니라 B로 남는다.'),
        m('GF_CMS_extremal'), m('GF_CMS_B'), m('GF_CMS_conclusions'), m('GF_source_allowance'),
        _source_links(link, source, refs, t),
        p('The new node contracts and Challenges are the precise Blueprint-facing correspondence; there is no separate Blueprint theorem label for these new interfaces. Their local kernel proofs and actual source/value audits are complete. The repository’s official Comparator receipt remains a separate workflow status.',
          '새 노드 계약과 Challenge가 Blueprint에 대응하는 정확한 명제를 담으며, 이 새 인터페이스에는 별도의 Blueprint 정리 표지가 없다. 로컬 커널 증명과 실제 소스·증명 값 감사는 완료했다. 저장소의 공식 Comparator 확인서는 별도의 워크플로 상태이다.'),
        h('What this demonstrates, and what remains external', '이 시연이 보인 것과 외부 계산으로 남은 것'),
        p('The columns show the Laguerre search degree, an inverse-functional value or bound and its evidence class. The approximation symbol in the middle row is a search estimate, not a directed enclosure. Search degree twelve uses thirteen rational coefficients and gives the degree-twenty-four polynomials above. The first row now includes the true Fourier identity and the conditional ANT consumer; D denotes a kernel-proved derivation and E external computational evidence.',
          '열은 라게르 탐색 차수, 역목적함수의 값 또는 경계, 증거 분류를 나타낸다. 가운데 행의 근사 기호는 탐색 추정치이며 방향성 구간 포함 경계가 아니다. 탐색 차수 12는 유리수 계수 13개를 사용하며 위의 24차 다항식을 만든다. 첫 행에는 실제 푸리에 항등식과 조건부 정수론 소비 정리까지 연결되어 있다. D는 커널로 증명한 유도 결과, E는 외부 계산 증거이다.'),
        m('GF_evidence_status'),
        p('The looser degree-twelve functional bound is now part of a proved Fourier-to-ANT chain. The sharper external numerical estimate for that candidate and the degree-forty search result remain E. No unverified numerical value is promoted into the canonical node. This is a concrete theorem-reuse and numerical-to-analytic propagation demonstration; it is not a randomized exposure experiment or evidence of a causal advantage from network exposure.',
          '여유 있는 12차 목적함수 경계는 이제 푸리에 증인에서 정수론까지 이어지는 증명 경로의 일부이다. 같은 후보의 더 날카로운 외부 수치 추정치와 40차 탐색 결과는 E로 남는다. 검증하지 않은 수치를 정식 노드로 올리지 않는다. 이는 구체적인 정리 재사용과 수치에서 해석학으로의 전달 시연이며, 무작위 노출 실험이나 네트워크 노출의 인과적 이점을 입증한 결과는 아니다.'),
    ]
    return section('gaussian-network', 'One proved Fourier witness supplies four downstream conclusions', '증명된 푸리에 증인 하나에서 후속 결론 네 개까지', ''.join(out))
