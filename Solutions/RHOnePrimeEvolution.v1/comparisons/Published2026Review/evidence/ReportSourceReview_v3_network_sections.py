"""Bilingual network mathematics; the caller supplies static math and links.

No JavaScript, remote fonts, runtime mathematics, or verification claims are
inserted here. The complete artifact and its verification section belong to
the campaign report builder.
"""

from html import escape


def render_network(lang, m, link, source):
    """Return a self-contained mathematical body in English or Korean."""
    if lang not in ("EN", "KO", "en", "ko"):
        raise ValueError("Supported network-report languages: EN, KO")
    ko = lang.lower() == "ko"

    def t(en, kr):
        return kr if ko else en

    def p(en, kr):
        return "<p>" + escape(t(en, kr)) + "</p>"

    def h(en, kr):
        return "<h2>" + escape(t(en, kr)) + "</h2>"

    def refs(*items):
        return '<p class="source-links">' + " · ".join(items) + "</p>"

    def section(identifier, title_en, title_ko, body):
        return '<section id="' + identifier + '">' + h(title_en, title_ko) + body + "</section>"

    pieces = [
        '<div class="lead">',
        p(
            "The completed network changes strengthen three mathematical uses of the preserved octic prime-count family: populations between powers, the location of consecutive prime indices, and the range/count tradeoff for sorted ternary Goldbach representations. The strongest cube result has the natural square-over-logarithm scale. These are actual theorem consumers; no new Fourier kernel is claimed for these consequences.",
            "이번 네트워크 확장은 기존 옥틱 커널의 소수 개수 정리를 세 방향으로 강화한다. 거듭제곱 사이의 소수 개수, 연속된 소수 인덱스의 위치, 그리고 정렬된 세 소수 골드바흐 표현의 범위와 개수 사이의 절충이다. 가장 강한 세제곱 결과는 제곱을 로그로 나눈 규모의 소수 개수를 보장한다. 실제 정리의 소비 경로를 구현한 결과이며, 이 귀결들을 위해 새로운 푸리에 커널을 만들었다는 주장은 하지 않는다.",
        ),
        "</div>",
        '<div class="grid">',
        '<article class="card"><h3>' + escape(t("Cube populations", "세제곱 사이의 소수 개수")) + "</h3>" + m("NET_cube_density") + m("NET_cube_natural") + "</article>",
        '<article class="card"><h3>' + escape(t("A shorter prime-rich window", "더 짧은 소수 밀집 구간")) + "</h3>" + m("NET_rich_shifted") + "</article>",
        '<article class="card"><h3>' + escape(t("A genuinely newly covered Goldbach band", "실제로 새롭게 포함된 골드바흐 범위")) + "</h3>" + m("NET_goldbach_numeric") + p("The finite binary-Goldbach hypothesis displayed below is required.", "아래에 명시한 유한 범위의 두 소수 골드바흐 가정이 필요하다.") + "</article>",
        "</div>",
    ]

    pieces.append(section("objects", "The mathematical objects and conventions", "수학적 대상과 표기 규약", "".join([
        p(
            "The open-window count is the cardinality of the finite set of natural primes with both real endpoints excluded. Ordinary prime counting includes its right endpoint. These are different objects, and the strict-open count is the one used for the new population and index statements.",
            "열린 구간의 개수는 양쪽 실수 끝점을 모두 제외하는 자연수 소수의 유한집합 크기이다. 보통의 소수계수함수는 오른쪽 끝점을 포함한다. 두 대상은 서로 다르며, 이번 소수 개수 및 인덱스 정리에는 엄격한 열린 구간 개수를 사용한다.",
        ),
        m("NET_objects"),
        p(
            "The prime sequence used by Lean is indexed from zero. Adding offset zero to the number of primes at or below the starting point therefore selects the first prime strictly above that point. An offset equal to a real lower count is permitted only when the actual integer cardinality is strictly larger.",
            "Lean에서 사용하는 소수열의 인덱스는 0부터 시작한다. 따라서 시작점 이하의 소수 개수에 오프셋 0을 더한 인덱스는 그 시작점보다 엄격히 큰 첫 번째 소수를 가리킨다. 실수 하한과 같은 오프셋도 허용하려면 실제 정수 집합 크기가 그 값보다 엄격히 커야 한다.",
        ),
        m("NET_prime_index"),
        refs(link("IEANTN/Vocabulary/PrimeWindows.lean", "PrimeWindows definitions"), link("IEANTN/Nodes/PrimeQuantile/v4/Conclusions.lean", "PrimeQuantile.v4")),
    ])))

    pieces.append(section("preserved", "What is inherited, and what changed", "물려받은 결과와 새로 달라진 점", "".join([
        p(
            "The starting snapshot is commit 3539bbba83db8345db1c43f37a9ddb6d8baf3ab0. Its mathematical statements, moment certificates and numerical source files are preserved. In particular, the entire octic family and all three stronger fixed population branches remain available. They are prior results, not discoveries attributed to this campaign.",
            "출발 스냅샷은 커밋 3539bbba83db8345db1c43f37a9ddb6d8baf3ab0이다. 기존 수학적 명제, 모멘트 인증서, 수치 소스 파일을 보존한다. 특히 옥틱 커널의 전체 매개변수 정리와 세 가지 강한 고정 구간 개수 결과를 모두 유지한다. 이는 이전 결과이며 이번 연구의 새 발견으로 돌리지 않는다.",
        ),
        m("NET_inherited_family"),
        m("NET_preserved_fixed"),
        p(
            "The general family is proved in Lean conditional on RH and the preserved general Green explicit-formula, Nicolas spectral, and BPT zero-counting predicates. Its numerical moment facts were checked by Lean's kernel. Downstream solutions may consume the single typed family statement instead of repeating those analytic arguments; the original source assumptions remain upstream.",
            "일반 매개변수 정리는 RH와 기존의 일반 Green 명시공식, Nicolas 스펙트럴 입력, BPT 영점 계수 입력을 가정한 Lean 정리이다. 필요한 수치 모멘트 사실은 Lean 커널이 확인했다. 후속 해법은 이 하나의 타입이 있는 매개변수 명제를 받아 해석적 논증을 반복하지 않고 사용할 수 있다. 원래의 원문 가정은 상위 노드에 그대로 남는다.",
        ),
        p(
            "The earlier parabolic population branch has a separate parameterization and source contract. It is retained separately rather than silently identified with the octic theorem. This campaign adds new consumers of the whole octic family; it does not rewrite the parabolic result or the completed Box and PNT results.",
            "이전 포물선 커널의 소수 개수 결과는 별도의 매개변수와 원문 조건을 갖는다. 이를 옥틱 정리와 같은 명제로 취급하지 않고 따로 보존한다. 이번에는 옥틱 매개변수 정리 전체를 사용하는 새 소비 정리를 추가한다. 포물선 결과나 이미 완료된 Box 및 PNT 결과를 다시 쓰지 않는다.",
        ),
        refs(link("Solutions/RHOcticPush.v1/octic/OcticOptimizedCertified.lean", "Frozen octic theorem"), link("IEANTN/Nodes/PrimeInterval/v4/Conclusions.lean", "PrimeInterval.v4 contracts"), link("Solutions/RHOcticPush.v1/comparisons/NLParabolicConsumer.lean", "Separate parabolic consumer")),
    ])))

    pieces.append(section("powers", "Quantitative primes between powers", "거듭제곱 사이의 정량적 소수 개수", "".join([
        p(
            "The old cube consumer guaranteed existence at the exponential onset below. The first new consumer chooses a wider admissible octic window that still fits strictly between successive cubes. A whole-ray logarithmic inequality proves the fit, so the argument covers every real base in its domain rather than a tested integer grid.",
            "이전 세제곱 소비 정리는 아래의 지수함수 문턱 이상에서 소수의 존재를 보장했다. 첫 번째 새 소비 정리는 허용된 옥틱 구간 중 더 넓은 것을 골라도 연속된 세제곱 사이에 엄격히 들어감을 보인다. 전체 실수 구간에서 성립하는 로그 부등식으로 포함 관계를 증명하므로, 검사를 수행한 정수 격자만 다루는 논증이 아니다.",
        ),
        m("NET_single_cube"),
        m("NET_single_fit"),
        p(
            "A single short window has only the three-halves power scale. The stronger construction partitions most of the entire cube interval and adds the prime populations of disjoint cells. It proves the density result in the opening card, including the concrete natural-number onset. The natural conversion uses a proved exponential bound, not a finite prime search.",
            "짧은 구간 하나만 사용하면 소수 개수는 밑과 그 제곱근의 곱 규모에 머문다. 더 강한 구성은 세제곱 사이 전체 구간의 대부분을 여러 셀로 나누고, 서로 겹치지 않는 셀의 소수 개수를 합한다. 이 방법으로 첫 카드의 밀도 결과와 구체적인 자연수 문턱을 증명했다. 자연수 문턱으로의 변환은 증명된 지수함수 경계를 사용하며 유한 소수 탐색에 의존하지 않는다.",
        ),
        m("NET_exp_conversion"),
        p(
            "The same argument also gives a quantitative population between successive integer powers. Here the exponent is a natural number at least three; this is not a theorem for arbitrary real exponents or for consecutive squares. Bernoulli's inequality and a square-root comparison prove the interval geometry, retaining the full positive logarithmic allowance.",
            "같은 입력으로 연속된 정수 거듭제곱 사이의 정량적 소수 개수도 얻는다. 여기서 지수는 3 이상인 자연수이다. 임의의 실수 지수나 연속된 제곱 사이에 관한 정리가 아니다. 베르누이 부등식과 제곱근 비교로 구간의 기하를 증명하고, 양의 로그 보정항도 모두 유지한다.",
        ),
        m("NET_higher_powers"),
        p(
            "The published consumer keeps the maximum of the density and single-window lower counts. Thus introducing the stronger large-base density never discards the better small-base branch. The earlier density proofs remain preserved, and their strict whole-ray numerical improvement is itself a proved comparison.",
            "공개 소비 정리는 밀도 하한과 단일 구간 하한의 최댓값을 유지한다. 따라서 큰 밑에서 강한 밀도 결과를 추가하면서 작은 밑에서 더 좋은 분기를 버리지 않는다. 앞선 밀도 증명들도 보존하며, 같은 전체 실수 범위에서 하한이 엄격히 개선되었다는 비교도 정리로 증명한다.",
        ),
        m("NET_cube_max"),
        m("NET_density_gain"),
        refs(link("Solutions/RHOnePrimeEvolution.v1/powers/PowerPopulation.lean", "Single-window cube proof"), link("Solutions/RHOnePrimeEvolution.v1/powers/HigherPowerPopulation.lean", "Integer-exponent proof"), link("Solutions/RHOnePrimeEvolution.v1/powers/CubeNatural070.lean", "Natural onset"), link("IEANTN/Nodes/PrimePowerPopulation/v1/Conclusions.lean", "Canonical exact statements")),
    ])))

    pieces.append(section("partition", "Why the adaptive partition improves the count", "가변 분할이 소수 개수를 개선하는 이유", "".join([
        p(
            "The partition has four concrete objects: a dimensionless width ratio, the number of cells, a kernel width shared by those cells, and their common length. They depend on the real cube base as follows. The ceiling makes the number of cells an actual positive integer.",
            "분할에는 네 가지 구체적인 대상이 있다. 무차원 너비 비율, 셀의 개수, 각 셀에 공통으로 사용하는 커널 너비, 그리고 셀의 길이이다. 이들은 실수 밑으로부터 다음과 같이 정의한다. 올림을 취하므로 셀 개수는 실제 양의 정수가 된다.",
        ),
        m("NET_partition_parameters"),
        p(
            "A proved common bound dominates every octic short-window length whose start lies in the cube interval. The chosen width is within the original admissible kernel domain and its bounded length is exactly one cell. The cells cover the initial cubic-difference term; leaving the remaining positive tail unused only weakens the lower bound.",
            "증명된 공통 경계는 세제곱 구간 안에서 시작하는 모든 옥틱 짧은 구간의 길이를 지배한다. 선택한 너비는 원래 커널의 허용 범위 안에 있으며, 그 길이 경계는 셀 하나의 길이와 정확히 일치한다. 셀들은 세제곱 차이의 주항에 해당하는 부분을 덮는다. 나머지 양의 꼬리 구간을 사용하지 않는 것은 하한을 약하게 만들 뿐이다.",
        ),
        m("NET_partition_geometry"),
        p(
            "Every cell receives a genuine prime-count theorem from the same family. Open cell boundaries prevent double counting. A prime exactly on a cell boundary may be omitted, which is harmless for a lower bound. The finite disjoint-union theorem adds the cardinalities before the residual costs are estimated.",
            "각 셀에는 같은 매개변수 정리의 실제 소수 개수 명제를 적용한다. 셀 경계를 열어 두므로 중복 계산이 없다. 셀 경계에 정확히 놓인 소수를 세지 않을 수는 있지만, 하한에는 문제가 없다. 유한한 서로소 합집합 정리로 먼저 집합 크기를 합한 뒤 잔여 비용을 평가한다.",
        ),
        m("NET_partition_sum"),
        p(
            "The first implementation paid for a full extra cell at every ratio and obtained the earlier density. Independent mathematical criticism noticed that a small ratio forces exactly one cell. For larger ratios a simpler relative ceiling bound suffices. Splitting these two cases recovers enough of the same mathematical budget to prove the stronger coefficient without changing a kernel or a certificate.",
            "첫 구현은 모든 너비 비율에서 추가 셀 하나의 비용을 지불하여 앞선 밀도를 얻었다. 독립적인 수학 검토에서 비율이 작으면 셀 개수가 정확히 하나라는 점을 찾아냈다. 비율이 크면 더 간단한 상대적 올림 경계로 충분하다. 두 경우를 나누어 같은 수학적 비용의 여유를 회수했고, 커널이나 인증서를 바꾸지 않고 더 강한 계수를 증명했다.",
        ),
        m("NET_ceiling_cases"),
        m("NET_partition_final"),
        p(
            "This is an identifiable reuse mechanism: the consumer needs the full variable-width count family, not merely a single fixed-width existence result. The improvement arose in independent proof review. No controlled experiment here establishes that network exposure uniquely caused it.",
            "재사용의 작동 방식이 구체적이다. 이 소비 정리에는 고정 너비 하나의 존재 결과가 아니라 너비를 바꿀 수 있는 개수 정리 전체가 필요하다. 개선은 독립적인 증명 검토에서 나왔다. 여기서 네트워크 노출이 유일한 원인임을 입증하는 통제 실험을 수행한 것은 아니다.",
        ),
        refs(link("Solutions/RHOnePrimeEvolution.v1/powers/PowerPartition.lean", "Disjoint cardinality proof"), link("Solutions/RHOnePrimeEvolution.v1/powers/CubeDensityUniform.lean", "Preserved initial density"), link("Solutions/RHOnePrimeEvolution.v1/powers/CubeDensity070.lean", "Stronger ceiling split"), link("Solutions/RHOnePrimeEvolution.v1/frontier/reviews/powers-070-v1/REVIEW.json", "Independent mathematical review")),
    ])))

    pieces.append(section("alpha-frontier", "The inherited population-versus-width curve", "기존 매개변수 정리의 소수 개수와 너비 곡선", "".join([
        p(
            "Fix a nonnegative normalized population target. Solving the inherited affine count inequality for the width produces the following exact curve. A positive reserve is needed if the limiting lower count must remain strictly above the target. The admissible-domain condition is retained rather than extending the formula outside the proved kernel range.",
            "음이 아닌 정규화 소수 개수 목표를 정한다. 기존의 일차 개수 부등식을 너비에 대해 풀면 다음의 정확한 곡선을 얻는다. 극한에서의 하한도 목표보다 엄격히 커야 한다면 양의 여유가 필요하다. 증명된 커널 범위를 벗어나 공식을 사용하는 대신, 허용 영역 조건을 그대로 유지한다.",
        ),
        m("NET_alpha_width"),
        m("NET_alpha_finite"),
        m("NET_alpha_domain"),
        p(
            "The finite inequality is an actual Lean theorem. Its usual limiting deduction is displayed separately: with positive reserve, the limit inferior is at least the target plus that reserve. With zero reserve the finite count remains strict, but a vanishing logarithmic margin alone gives only a non-strict limit-inferior bound. No separately compiled Lean limit-inferior theorem is claimed for this deduction.",
            "유한한 시작점부터의 부등식은 실제 Lean 정리이다. 표준적인 극한 귀결은 따로 표시한다. 여유가 양수이면 하극한은 목표와 그 여유의 합 이상이다. 여유를 0으로 두어도 유한 구간의 부등식은 엄격하지만, 사라지는 로그 보정항만으로는 하극한에 대해 비엄격한 하한만 얻는다. 이 극한 귀결 자체를 별도의 Lean 하극한 정리로 컴파일했다는 주장은 하지 않는다.",
        ),
        m("NET_alpha_limit"),
        p(
            "The historical benchmark is the ordinary-RH statement in Chirre, Pereira Júnior and de Laat, section 1.3 of arXiv:2005.02393v3. Its actual formulation is an upper bound on the infimum of admissible width coefficients, shown here; it has no explicit onset. This is distinct from their arithmetic-progression theorem, which assumes GRH.",
            "역사적 비교 원문은 arXiv:2005.02393v3의 Chirre, Pereira Júnior, de Laat 논문 1.3절에 있는 일반 RH 명제이다. 원문은 아래에 표시한 허용 너비 계수 집합의 하한에 대한 상계이며 명시적인 시작점은 주지 않는다. 이는 GRH를 가정하는 같은 논문의 등차수열 정리와 구별해야 한다.",
        ),
        m("NET_chirre_source"),
        p(
            "A newer comparison is essential. Rafael Blanquer Robles, version 2 dated 21 November 2026, states a two-line population envelope in Theorem 2, equation (2). Although that theorem is stated for progressions on GRH, the final paragraph of section 3 explicitly states that its ordinary-prime cases require only RH. The ordinary-prime specialization is therefore a valid current comparator and is not excluded as a GRH result.",
            "더 최신 결과와의 비교도 필요하다. Rafael Blanquer Robles의 2026년 11월 21일 버전 2 논문은 정리 2의 식 (2)에서 두 직선의 최솟값으로 소수 개수 경계를 서술한다. 정리 자체는 GRH 아래의 등차수열로 서술하지만, 3절 마지막 문단은 일반 소수에 해당하는 경우에는 RH만 필요하다고 명시한다. 따라서 이 일반 소수 특수화는 유효한 최신 비교 대상이며, GRH 결과라는 이유로 제외하지 않는다.",
        ),
        m("NET_br_ordinary"),
        "<details><summary>" + escape(t("Exact current primary statement and its ordinary-RH specialization", "최신 원문의 정확한 명제와 일반 RH 특수화")) + "</summary>",
        p(
            "In the source, the modulus set is nonempty, the totient is Euler's function, and progression prime counting counts primes in a reduced residue class. The source definitions and small-modulus condition are these; the theorem is then the displayed minimum below. Taking the singleton modulus one recovers ordinary prime counting, and the section 3 proof permits RH alone for that case.",
            "원문에서 법의 집합은 공집합이 아니며, 토션트는 오일러 함수이고, 등차수열 소수계수함수는 기약 잉여류 안의 소수를 센다. 원문의 정의와 작은 법 조건은 다음과 같고, 그 아래의 최솟값이 정리의 내용이다. 법이 1인 단원소 집합을 취하면 일반 소수계수함수가 되며, 3절의 증명은 이 경우 RH만으로 성립함을 명시한다.",
        ),
        m("NET_br_source_definitions"),
        m("NET_br_source_statement"),
        refs(source("https://zenodo.org/records/24429650", "Blanquer Robles v2: Theorem 2, equation (2), page 2; section 3 final paragraph, page 10"), link("Solutions/RHOnePrimeEvolution.v1/sources/Blanquer_Robles_2026.txt", "Pinned primary text")),
        "</details>",
        p(
            "The old and current crossings are both shown below. To beat the whole newer printed minimum, the population target must exceed the larger, current crossing. A sufficiently small positive reserve then retains a strict limiting target and a width below both new lines, provided the original kernel domain holds. This compares published upper-bound curves, not an unknown optimum. Near the zero-population endpoint the octic intercept is worse.",
            "과거 및 최신 경계와의 교점을 모두 아래에 표시한다. 최신 원문의 최솟값 전체보다 작아지려면 소수 개수 목표가 더 큰 최신 교점을 넘어야 한다. 원래 커널 영역 안에서 충분히 작은 양의 여유를 택하면 엄격한 극한 목표를 유지하면서 새 두 직선보다 모두 작은 너비를 얻는다. 이는 발표된 상계 곡선끼리의 비교이지 미지의 최적값과의 비교가 아니다. 목표가 0에 가까우면 옥틱 곡선의 절편이 더 나쁘다.",
        ),
        m("NET_alpha_crossing"),
        m("NET_epsilon_choice"),
        p(
            "For the unit population target, the preserved slightly wider branch already has a fixed positive leading excess. This gives a concrete strict limiting target below the current displayed benchmark without assuming that the limiting affine width itself is attained.",
            "소수 개수 목표가 1일 때는 보존된 약간 더 넓은 분기에 이미 고정된 양의 주항 여유가 있다. 따라서 극한의 일차 너비 자체가 달성된다고 가정하지 않고도, 최신 원문의 표시된 경계보다 작은 구체적인 너비에서 엄격한 극한 목표를 얻는다.",
        ),
        m("NET_alpha_one_strict"),
        p(
            "The same 2026 source also states an explicit one-prime theorem on RH from the much earlier starting point below. It is stronger than the separate uniform CMS refinement in this campaign, so that refinement is not a current best explicit existence bound. The finite lower-coefficient slabs and the population consequences must be assessed on their own exact targets and domains.",
            "같은 2026년 원문에는 아래의 훨씬 이른 시작점부터 성립하는 RH 아래의 명시적 한 소수 정리도 있다. 이는 이번 연구의 별도 균일 CMS 개선보다 강하므로, 그 CMS 개선을 현재 최선의 명시적 존재 경계로 제시하지 않는다. 유한 범위의 더 작은 계수 결과와 소수 개수 귀결은 각각의 정확한 목표 및 영역에서 평가해야 한다.",
        ),
        m("NET_br_explicit"),
        refs(source("https://arxiv.org/html/2005.02393v3#S1.SS3", "Primary source: section 1.3, first display"), source("https://arxiv.org/html/2005.02393v3#S1.SS1", "Primary source: section 1.1, equation (1.3)"), link("Solutions/RHOnePrimeEvolution.v1/frontier/PopulationFrontier.lean", "Exact curve and finite Lean consumer"), link("Solutions/RHOnePrimeEvolution.v1/comparisons/Published2026Review/WholePopulationComparison2026.lean", "Current printed-envelope comparison")),
        p(
            "These crossings compare the CPJ curve and the two printed 2026 Blanquer Robles lines; they do not exhaust RH population frontiers. Lee's Theorem 1.1, equation (4), in arXiv:2403.11814v4 supplies another explicit count route through a short-interval theta estimate. At larger admissible widths its limiting count expression can improve on the octic expression, including within the original kernel width range. A complete pointwise Lee comparison and its crossovers have not been compiled here, so the affine octic curve is not presented as globally optimal or best known.",
            "이 교점들은 CPJ 곡선과 2026년 Blanquer Robles 원문에 표시된 두 직선을 비교한 것이며, RH 아래의 모든 소수 개수 경계를 망라하지 않는다. arXiv:2403.11814v4의 Lee 정리 1.1, 식 (4)는 짧은 구간의 세타 추정을 통해 다른 명시적 소수 개수 경로를 준다. 허용 너비가 클 때에는 그 극한 개수 식이 원래 커널의 너비 범위 안에서도 옥틱 식보다 좋아질 수 있다. Lee와의 전체 점별 비교 및 교점을 여기서 컴파일한 것은 아니므로, 옥틱 일차 곡선을 전역 최적 또는 알려진 최선의 경계로 제시하지 않는다.",
        ),
        "<details><summary>" + escape(t("Lee's exact source estimate and the open-endpoint cost", "Lee 원문의 정확한 추정과 열린 끝점의 비용")) + "</summary>",
        p(
            "The source constant is defined by equation (2), rather than left as an unexplained decimal. Under RH the theta estimate below holds on its stated start and length domain. Theta denotes the sum of logarithms of primes at or below its argument.",
            "원문의 상수는 설명 없는 소수로 두지 않고 식 (2)의 정의를 그대로 표시한다. RH 아래에서 다음 세타 추정은 명시한 시작점과 길이 영역에서 성립한다. 세타 함수는 그 인자 이하의 소수들의 로그 합을 뜻한다.",
        ),
        m("NET_lee_constant"),
        m("NET_lee_source"),
        p(
            "For an open prime count the source theta difference may include a prime exactly at the upper endpoint. Bounding every logarithmic weight by the endpoint logarithm and allowing that one extra prime gives the two displayed steps. The subtracted one is an endpoint allowance, not an unexplained change in the source constant. The last line is the resulting limiting expression after substituting a fixed width coefficient. This source-derived comparison is not a newly verified network theorem.",
            "열린 구간의 소수 개수와 달리, 원문의 세타 차이는 오른쪽 끝점에 정확히 놓인 소수를 포함할 수 있다. 각 로그 가중치를 끝점의 로그로 제한하고 그 추가 소수 하나를 허용하면 표시한 두 단계를 얻는다. 마지막에 빼는 1은 끝점 보정이며, 설명 없이 원문 상수를 바꾼 것이 아니다. 마지막 줄은 고정된 너비 계수를 대입했을 때의 극한 식이다. 이 원문에서 유도한 비교를 새롭게 검증한 네트워크 정리로 제시하지 않는다.",
        ),
        m("NET_lee_open_derivation"),
        m("NET_lee_limiting"),
        refs(source("https://arxiv.org/pdf/2403.11814v4#page=2", "Primary source: Lee, Theorem 1.1, equations (2) and (4), page 2"), link("Solutions/RHOnePrimeEvolution.v1/sources/Lee2403.11814v4.txt", "Pinned primary text")),
        "</details>",
    ])))

    pieces.append(section("indices", "Recovering logarithmic slack for prime indices", "로그 여유를 회수한 소수 인덱스 경계", "".join([
        p(
            "The positive logarithmic population allowance can be spent on a shorter interval instead of discarded. At normalized population one, exact algebra subtracts an additive square-root term from the old width. Both the retained target and the new endpoint are proved on the whole real ray.",
            "양의 로그 개수 보정항은 버리는 대신 구간을 줄이는 데 사용할 수 있다. 정규화 소수 개수 목표를 1로 놓으면, 정확한 대수 계산으로 기존 너비에서 제곱근 규모의 항을 뺀다. 유지되는 목표와 새로운 끝점은 전체 실수 구간에서 증명된다.",
        ),
        m("NET_shifted_derivation"),
        m("NET_rich_shifted"),
        p(
            "The old fixed-window theorem retained a larger positive count margin; it remains available. The new theorem is a count/width tradeoff for the same chosen normalized target. The strict-open count then places every eligible consecutive prime index strictly inside the shorter interval, improving the old closed upper endpoint as well.",
            "기존의 고정 구간 정리는 더 큰 양의 소수 개수 여유를 갖고 있었으며 그대로 사용할 수 있다. 새 정리는 선택한 정규화 목표를 유지하면서 소수 개수와 너비를 교환한 결과이다. 엄격한 열린 구간 개수를 이용하면 허용되는 모든 연속 소수 인덱스를 더 짧은 구간 안에 엄격히 넣을 수 있어, 이전의 닫힌 오른쪽 끝점도 개선한다.",
        ),
        m("NET_shifted_indices"),
        p(
            "For a requested index offset, the actual pointwise inversion uses the entire count allowance. Small targets are clamped to the proved minimum width; the upper-domain guard remains necessary. A separate effective choice retains the specialized fixed-width branch, whose logarithmic margin is stronger than the generic family. It is an actual minimum of available theorem routes, not an unproved extrapolation.",
            "원하는 인덱스 오프셋에 대한 점별 역산은 개수 여유 전체를 사용한다. 작은 목표의 너비는 증명된 최소 너비로 올려 제한하며, 최대 너비 조건도 필요하다. 별도의 유효 선택은 일반 정리보다 로그 여유가 큰 특수 고정 너비 분기도 유지한다. 이는 사용할 수 있는 정리 경로들의 실제 최솟값이며 증명되지 않은 외삽이 아니다.",
        ),
        m("NET_index_inversion"),
        refs(link("Solutions/RHOnePrimeEvolution.v1/frontier/PopulationFrontier.lean", "Population and index proofs"), link("IEANTN/Nodes/PrimeQuantile/v4/Conclusions.lean", "Strict indexed-prime contracts"), link("Solutions/PrimeQuantile.v4/Solution.lean", "Typed canonical adapters")),
    ])))

    pieces.append(section("goldbach", "Goldbach multiplicity: exchange count for range", "골드바흐 표현 수: 개수와 범위의 교환", "".join([
        p(
            "A sorted representation is an unordered prime triple recorded in nondecreasing order; repeated primes are allowed. The finite binary hypothesis supplies a prime pair for every even residual in its stated range. It is an explicit mathematical assumption, not a computation newly verified in this campaign.",
            "정렬된 표현은 순서를 구별하지 않는 세 소수의 합을 비내림차순으로 기록한 것이다. 같은 소수를 반복해도 된다. 유한한 두 소수 가정은 지정한 범위의 모든 짝수 잔여값을 두 소수의 합으로 나타내 준다. 이는 명시적인 수학적 가정이며, 이번 연구에서 새롭게 검증한 계산이 아니다.",
        ),
        m("NET_goldbach_objects"),
        p(
            "The old injection selected a prime larger than half the target, making it the unique largest component. The new transfer permits primes above one third of the target: such a prime can be the middle or largest component, but not the smallest. Counting the union of those two component images loses a factor of at most two and expands the valid range. With no component-size restriction the analogous union has three images.",
            "이전의 단사 대응은 목표의 절반보다 큰 소수를 골라 그것이 유일하게 가장 큰 성분이 되도록 했다. 새 전달은 목표의 3분의 1보다 큰 소수를 허용한다. 이 소수는 중간 성분이나 가장 큰 성분일 수 있지만 가장 작은 성분일 수는 없다. 두 성분상들의 합집합을 세면 최대 두 배의 손실로 범위를 넓힐 수 있다. 성분 크기를 제한하지 않으면 같은 논증에서 세 개의 상을 사용한다.",
        ),
        m("NET_goldbach_factors"),
        p(
            "Write the real interval start as the target minus the finite binary height. The analytic onset and width budget below remain explicit. The divisor chooses the strongest available cardinality transfer, retaining the old full-count branch rather than replacing it by the weaker half-count bound.",
            "실수 구간의 시작점은 목표에서 유한한 두 소수 가정의 높이를 뺀 값으로 둔다. 아래의 해석적 시작점 및 너비 예산은 그대로 필요하다. 나눗수는 사용할 수 있는 집합 크기 전달 중 가장 강한 것을 선택하므로, 이전의 전체 개수 분기를 더 약한 절반 개수 결과로 대체하지 않는다.",
        ),
        m("NET_goldbach_domain"),
        m("NET_goldbach_divisor"),
        m("NET_goldbach_frontier"),
        p(
            "For odd targets the equality in the full-count condition cannot occur, because twice a natural height is even. It therefore adds no new odd cases. The genuine range improvements are the factor-two and factor-three branches, demonstrated by the explicit odd band in the opening card.",
            "홀수 목표에서는 전체 개수 조건의 등호가 성립할 수 없다. 자연수 높이의 두 배는 짝수이기 때문이다. 따라서 그 등호는 새 홀수 경우를 추가하지 않는다. 실제 범위 개선은 두 배 및 세 배 손실 분기이며, 첫 카드의 구체적인 홀수 범위가 이를 보여 준다.",
        ),
        m("NET_goldbach_numeric_detail"),
        p(
            "The shifted rich-prime window also saves the exact additive width term in the finite binary budget while retaining its selected representation target. This is a proved saving at a fixed interval start. A separately optimized smaller finite height for a fixed odd target has not been established, because changing the height also changes that start.",
            "이동한 소수 밀집 구간은 선택한 표현 수 목표를 유지하면서 유한한 두 소수 예산에서도 정확한 가법적 너비 항을 절약한다. 이는 구간 시작점을 고정했을 때의 증명된 절약이다. 유한 높이를 바꾸면 시작점도 바뀌므로, 홀수 목표를 고정한 채 필요한 유한 높이를 따로 최적화한 결과까지 얻었다는 주장은 하지 않는다.",
        ),
        m("NET_goldbach_shift"),
        refs(link("IEANTN/Vocabulary/Goldbach.lean", "Exact finite binary hypothesis"), link("IEANTN/Vocabulary/GoldbachCounts.lean", "Actual sorted triples"), link("Solutions/RHOnePrimeEvolution.v1/frontier/GoldbachExtendedRange.lean", "Component-image proofs"), link("Solutions/RHOnePrimeEvolution.v1/frontier/GoldbachNumericalBand.lean", "Numerical band proof"), link("IEANTN/Nodes/Goldbach/v3/Conclusions.lean", "Goldbach.v3 contracts")),
    ])))

    edge_rows = [
        ("PrimeInterval.v4.optimized_strict_family", "PrimePowerPopulation.v1", t("All-real cube density, natural onset, integer powers and effective maximum", "전체 실수 세제곱 밀도, 자연수 문턱, 정수 지수 및 유효 최댓값")),
        ("PrimeInterval.v4.optimized_strict_family", "PrimeQuantile.v4", t("Strict prime-index blocks and the exact additive shortening", "엄격한 소수 인덱스 블록과 정확한 가법적 단축")),
        ("PrimeInterval.v4.optimized_strict_family + GoldbachEvenUpTo", "Goldbach.v3", t("Broader representation-count ranges and the explicit numerical band", "표현 수 범위의 확장과 구체적인 수치 범위")),
    ]
    table = '<table><thead><tr><th>' + escape(t("Typed input", "타입이 있는 입력")) + '</th><th>' + escape(t("New conclusion family", "새 결론 계열")) + '</th><th>' + escape(t("Mathematical effect", "수학적 효과")) + '</th></tr></thead><tbody>'
    for a, b, c in edge_rows:
        table += "<tr><td><code>" + escape(a) + "</code></td><td><code>" + escape(b) + "</code></td><td>" + escape(c) + "</td></tr>"
    table += "</tbody></table>"
    pieces.append(section("network-mechanism", "What the IEANTN structure actually enables", "IEANTN 구조가 실제로 가능하게 한 것", "".join([
        p(
            "A conclusion is a proposition with an exact formula and quantified domain. A version preserves that contract. A solution is a typed proof function taking its declared input propositions to that conclusion; evidence metadata records how the implication was checked. Statements and proof status are separate, so an imported literature claim does not become a proved Lean source theorem merely because a consumer compiles.",
            "결론은 정확한 공식과 양화된 영역을 갖는 명제이다. 버전은 그 조건을 보존한다. 해법은 선언된 입력 명제들로부터 해당 결론을 만드는 타입이 있는 증명 함수이며, 근거 메타데이터는 이 함의를 어떻게 확인했는지 기록한다. 명제와 증명 상태는 별개이다. 소비 정리가 컴파일된다고 해서 가져온 문헌 명제의 원문 증명까지 Lean으로 증명되는 것은 아니다.",
        ),
        table,
        p(
            "The power solution really passes the imported family to the adaptive partition theorem. The index adapters really pass it to the strict finite-set/prime-index argument. The Goldbach adapters really pass it to the component-cardinality transfers together with the finite binary hypothesis. Proof-value audits check these consumed terms, not only the presence of matching names in a graph file.",
            "거듭제곱 해법은 가져온 매개변수 정리를 실제로 가변 분할 정리에 전달한다. 인덱스 어댑터는 이를 엄격한 유한집합과 소수 인덱스 논증에 전달한다. 골드바흐 어댑터는 이를 유한한 두 소수 가정과 함께 성분 집합 크기 전달에 사용한다. 증명 값 감사는 그래프 파일에 같은 이름이 있는지만 보는 것이 아니라 실제로 사용된 항을 확인한다.",
        ),
        p(
            "The new conclusions depend on the whole family, preserving information about width, count and the positive logarithmic allowance. That information enables adaptive cell sizes and index inversion which a single fixed-width endpoint would not supply to these proof constructions. The inherited numerical moment theorem is reused, and no new external analytic premise is added to these three downstream families.",
            "새 결론들은 전체 매개변수 정리에 의존하며 너비, 개수, 양의 로그 보정항 정보를 보존한다. 그 정보가 있어야 이 증명 구성에서 셀 크기를 바꾸고 인덱스 관계를 역산할 수 있다. 고정 너비 하나의 최종 결과만으로는 이 구성에 필요한 입력이 주어지지 않는다. 기존 수치 모멘트 정리를 재사용하며, 이 세 후속 계열에는 새 외부 해석적 가정을 추가하지 않는다.",
        ),
        p(
            "Generated Challenges are statement interfaces, not proof evidence. The supplied Solutions prove the new interfaces and local audits check their types and permitted axioms. Official Comparator workflow receipts remain distinct from these local kernel checks; no receipt or verified status is manufactured.",
            "생성된 Challenge는 명제 인터페이스이지 증명 근거가 아니다. 제공된 Solution이 새 인터페이스를 증명하고, 로컬 감사가 타입과 허용 공리를 확인한다. 공식 Comparator 워크플로의 영수증은 이러한 로컬 커널 검사와 구별한다. 영수증이나 검증 상태를 임의로 만들어 넣지 않는다.",
        ),
        refs(link("Solutions/PrimePowerPopulation.v1/Solution.lean", "Power solution adapters"), link("Solutions/PrimePowerPopulation.v1/Audit.lean", "Actual power proof-value audit"), link("Solutions/RHOnePrimeEvolution.v1/frontier/CanonicalFrontierTransport.lean", "Index and Goldbach adapters"), link("docs/ARCHITECTURE.md", "Repository architecture")),
    ])))

    pieces.append(section("limits", "Proof boundaries and honest negative results", "증명의 경계와 얻지 못한 결과", "".join([
        p(
            "These downstream claims are source-conditional mathematical Lean results with kernel-checked numerical support, classified B+D in the campaign. The mathematical source predicates remain explicit hypotheses. They are not a proof of RH, a derivation of every literature theorem from Mathlib, or source-first program verification. No new numerical C, C++ or CUDA program was needed for the power and cardinality arguments.",
            "이 후속 결과들은 원문 수학 명제를 조건으로 둔 Lean 정리와 커널이 확인한 수치 근거이며, 연구의 분류로는 B+D이다. 수학적 원문 술어는 명시적인 가정으로 남는다. RH 자체의 증명도, 모든 문헌 정리를 Mathlib에서 유도한 결과도, 소스 우선 프로그램 검증도 아니다. 거듭제곱 및 집합 크기 논증에는 새로운 수치 C, C++, CUDA 프로그램이 필요하지 않았다.",
        ),
        p(
            "The audited mathematical consumers use only propext, Classical.choice and Quot.sound; their selected final proof closures contain no native execution axiom. Compiler, core-runtime, operating-system and hardware correctness retain the stated platform trust boundary. The separate historical finite-gap source used by the one-prime hybrid and the finite binary-Goldbach hypothesis are not newly source-verified computations.",
            "감사한 수학 소비 정리는 propext, Classical.choice, Quot.sound만 사용하며, 선택한 최종 증명 의존성에는 네이티브 실행 공리가 없다. 컴파일러, 핵심 런타임, 운영체제, 하드웨어의 정확성은 명시된 플랫폼 신뢰 경계에 남는다. 한 소수 하이브리드가 사용하는 별도의 과거 유한 소수 간격 자료와 유한 두 소수 골드바흐 가정은 새롭게 소스 검증한 계산이 아니다.",
        ),
        p(
            "The separate one-prime branch introduces a new explicit source input, SourceCMS616; the three downstream families above still consume the old octic family. In CMS, Lemma 7 on page 21 excludes a zero ordinate at its parameter, while page 22 after equation (6.3) notes removable kernel singularities. The source obstruction is interpreted through the entire cosine kernel with the following values at its apparent poles. Extending the source formula to all required parameters by Guinand–Weil or continuity is part of that disclosed B input, not a Lean adapter proved from a literal totalized zero-over-zero expression.",
            "별도의 한 소수 분기는 새 명시적 원문 입력인 SourceCMS616을 도입한다. 위의 세 후속 계열은 여전히 기존 옥틱 매개변수 정리를 사용한다. CMS 원문의 21쪽 보조정리 7은 매개변수가 영점의 허수부와 같은 경우를 제외하며, 22쪽 식 (6.3) 뒤에서는 커널의 제거 가능한 특이점을 언급한다. 원문 장애 부등식은 겉보기 극점에서 다음 값을 갖는 전해석적 코사인 커널을 통해 해석한다. Guinand–Weil 공식이나 연속성으로 필요한 모든 매개변수에 확장하는 부분은 명시된 B 입력에 포함되며, 전역적으로 정의한 0 나누기 0 식에서 출발해 Lean으로 증명한 어댑터가 아니다.",
        ),
        m("NET_cms_entire_extension"),
        refs(source("https://arxiv.org/pdf/1708.04122v2#page=21", "CMS Lemma 7, page 21; equation (6.3), page 22"), link("Solutions/RHOnePrimeEvolution.v1/analytic/CMSPrimeFrontier.lean", "Explicit SourceCMS616 input")),
        p(
            "This work does not establish a new PNT, LCM/divisor-sum, primorial, signed Mertens, or Möbius bound. The earlier completed results are preserved. In particular, the Box/PNT route has a different integrated-Perron input and may yield stronger cube consequences on that larger premise package; the present count is not asserted to dominate it. Proposed spectral-product and Möbius routes did not acquire the additional weighted-moment or reciprocal-zeta information needed for new numeric conclusions.",
            "이번 결과는 새로운 PNT, LCM/약수합, 프리모리얼, 부호를 살린 Mertens 합, Möbius 합의 경계를 증명하지 않는다. 앞서 완료한 결과는 보존한다. 특히 Box/PNT 경로에는 다른 일반 적분 Perron 입력이 있으며, 그 더 큰 가정 묶음에서는 세제곱에 관한 더 강한 귀결이 나올 수 있다. 여기의 개수 경계가 그 경로를 지배한다고 주장하지 않는다. 제안된 스펙트럴 곱 및 Möbius 경로에서는 새 수치 결론에 필요한 추가 가중 모멘트나 역제타 정보를 얻지 못했다.",
        ),
        p(
            "The strengthened cube theorem is a same-input improvement over the inherited existence consumer and the preserved earlier density. Its mathematical mechanism and actual consumers are explicit. No global best-known, optimality, or overall causal exposure-advantage claim is made. Ramanujan's inequality is excluded from this campaign.",
            "강화된 세제곱 정리는 동일한 입력 아래 기존의 존재 소비 정리와 보존된 앞선 밀도를 개선한다. 작동하는 수학적 방식과 실제 소비 경로를 명시했다. 전역 최선 기록, 최적성, 또는 노출 실험 전체의 인과적 우위를 주장하지 않는다. Ramanujan 부등식은 이번 연구 범위에서 제외한다.",
        ),
        refs(link("Solutions/RHOnePrimeEvolution.v1/powers/THEOREMS.json", "Exact power theorem inventory"), link("Solutions/RHOnePrimeEvolution.v1/powers/GOLDBACH_FINITE_INDEPENDENT_REVIEW.json", "Independent Goldbach/source review"), link("Solutions/PrimePowerPopulation.v1/REPRODUCE.md", "Reproduction commands")),
    ])))
    return "\n".join(pieces)
