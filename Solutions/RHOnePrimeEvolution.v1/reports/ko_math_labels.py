"""Translate display labels; preserve every mathematical token and source name."""
import re
LABELS={
' and ':' 및 ', ' consecutive primes':' 연속 소수', ' continuous':' 연속', ' even':' 짝수', ' fixed':' 고정', ' is prime':' 는 소수', ' odd':' 홀수', ' prime':' 소수', ' real here':' 여기서는 실수값',
' the same eventual count requires only RH.':' 같은 극한 개수에는 RH만 필요하다.',
'(literature bound, not a new Lean theorem).':'(문헌의 하한이며 새 Lean 정리가 아님).',
'Assume binary Goldbach through ':'다음 범위까지 두 소수 골드바흐를 가정: ',
'Blanquer Robles, Theorem 3: RH':'Blanquer Robles, 정리 3: RH',
'Blanquer Robles, Thm.1':'Blanquer Robles, 정리 1', 'Blanquer Robles, Thm.3':'Blanquer Robles, 정리 3',
'CMS (6.16)':'CMS (6.16)', 'CMS source (6.16)':'CMS 원문 가정 (6.16)', 'CMS, Thm.5':'CMS, 정리 5', 'CPJ--de Laat':'CPJ--de Laat',
'Coefficient':'계수', 'Domain of real ':'실수 영역 ', 'Gaussian, degree ':'가우스, 차수 ',
'Journal, Theorem 3.2/Table 4, first row:':'출판본, 정리 3.2 및 표 4의 첫 행:',
'Lee 2026, Thm.1.1: ':'Lee 2026, 정리 1.1: ',
'Octic inherited leading count: ':'기존 옥틱 정리의 개수 주항: ', 'Quantifiers':'범위 및 양화', 'RH':'RH',
'Ratio enclosure (upper, rounded up)':'비율 포함구간의 상한 (올림)', 'Objective value / bound':'목적함수 값 또는 경계', 'numerical search estimate':'수치 탐색 추정치', 'Section 3: for ':'3절: 다음 경우 ',
'Source':'원문', 'Status':'검증 상태', 'Strictly open prime window':'엄격한 열린 소수 구간',
'Theorem 2, (2): GRH and ':'정리 2, 식 (2): GRH 및 ',
'Thus this theorem does not directly permit ':'따라서 이 정리가 직접 허용하지 않는 경우: ', 'Witness':'증인',
'arXiv v2, Theorem 3.2/Table 4, first row:':'arXiv v2, 정리 3.2 및 표 4의 첫 행:',
'asymptotic gap route (CMS Theorem 3/Corollary 4)':'점근적 간격 경로 (CMS 정리 3 및 따름정리 4)',
'asymptotic normalized gaps':'점근적 정규화 간격', 'closed endpoints':'닫힌 양 끝점',
'explicit finite-range route (CMS section 6.3).':'명시적 유한 범위 경로 (CMS 6.3절).',
'external certificate computation':'외부 인증서 계산', 'external interval verification':'외부 구간산술 검증',
'first prime strictly above ':'다음 값보다 엄격히 큰 첫 소수: ',
'rational hats, ':'유리수 해트, ', 'reported gap table':'보고된 간격 표', 'screened ratio: ':'탐색한 비율: '
}
def translate(tex):
    def replace(match):
        text=match.group(1)
        if text not in LABELS:raise ValueError('Untranslated mathematical display label: '+text)
        return r'\text{'+LABELS[text]+'}'
    return re.sub(r'\\text\{([^{}]*)\}',replace,tex)
