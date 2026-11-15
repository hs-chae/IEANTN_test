#!/usr/bin/env python3
"""Bounded independent review checks; not a replacement for Lean proof checking."""
from pathlib import Path
from fractions import Fraction as F
import argparse, hashlib, html, json, re

ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parent
BASE='research/analytic/lean/SynergyAnalytic/'
OLD='scoped/kernel-overlay-v1/lean/'

def require(condition,message):
    if not condition: raise RuntimeError(message)
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def source(relative): return (ROOT/relative).read_text()
def anchor(relative,fragment):
    text=source(relative)
    require(fragment in text,f'missing reviewed declaration: {relative}: {fragment}')
    line=text[:text.index(fragment)].count('\n')+1
    return {'file':relative,'line':line,'sha256':digest(ROOT/relative)}

ANCHORS=[
 ('network/IEANTN/Vocabulary/ErrorTerms.lean','noncomputable def Eπ'),
 ('network/IEANTN/Vocabulary/PrimeCounting.lean','noncomputable def Li'),
 ('network/IEANTN/Vocabulary/PowerError.lean','def HasPowerLogBound'),
 ('network/IEANTN/Nodes/ZeroCount/v1/Conclusions.lean','def rvm_error_bound'),
 ('network/IEANTN/Nodes/LowZeroes/v1/Conclusions.lean','noncomputable def no_zeroes_below_first_ordinate'),
 ('network/IEANTN/Vocabulary/Zeta.lean','def RiemannHypothesisUpTo'),
 ('network/IEANTN/Vocabulary/ZeroFreeHalfPlane.lean','def ZetaZeroFreeHalfPlane'),
 (OLD+'WinnerDensityA/HeightPrimary.lean','structure PrimaryInputs'),
 (OLD+'WinnerDensityA/DirectCHJPairing.lean','def OriginalCHJSource'),
 (OLD+'WinnerDensityA/DirectRayParameters.lean','theorem direct_height_domains'),
 (OLD+'WinnerDensityA/DirectRHPiKernel.lean','theorem actual_pi_from_CHJ_kernel'),
 (OLD+'WinnerDensityA/DirectRHSplitNormalized.lean','theorem rh_pi_ray_of_budgets'),
 (OLD+'ScopedWinnerA/Result.lean','theorem pi_refined_exact'),
 (BASE+'TangentCertifiedBasis.lean','theorem tangent256_universal_basis_caps'),
 (BASE+'HeightPointGeometry.lean','theorem heightEndpoint_last'),
 (BASE+'HeightGenericAll.lean','theorem kernel_generic_height_all'),
 (BASE+'HeightPointResultBounds.lean','theorem checked_point_bounds'),
 (BASE+'EndpointAnyWidth.lean','theorem count_endpoint_any_width'),
 (BASE+'HeightBudgetSound.lean','theorem cValue_eq'),
 (BASE+'ActualReciprocal.lean','theorem actual_reciprocal_from_count_caps'),
 (BASE+'ReciprocalBoundary.lean','theorem finite_reciprocal_cells_tail_boundary'),
 (BASE+'TailFour.lean','theorem'),
 (BASE+'CountBoundary.lean','theorem count_boundary_affine'),
 (BASE+'ActualSpectral.lean','theorem actual_spectral_from_continuous_envelope'),
 (BASE+'ProfileCoefficient.lean','theorem ordinate_paired_coefficient'),
 (BASE+'PNTTransfer.lean','theorem pi_from_continuous_ordinate_envelope'),
 (BASE+'HeightTightBudget.lean','theorem final_height_budget_tight'),
 (BASE+'HeightPNTInstance.lean','theorem source_pi_008441646'),
 (BASE+'HeightPrimeRichInstance.lean','theorem source_prime_rich_017'),
 (BASE+'HeightComparison.lean','theorem height_bound_strict_on_original_interval'),
]

def run(out):
    anchors=[anchor(*a) for a in ANCHORS]
    # These are the eight fields of the actual original source package, not a new hypothesis.
    primary=source(OLD+'WinnerDensityA/HeightPrimary.lean').split('theorem selected_lower_contour_param')[0]
    fields=re.findall(r'^  (\w+)\s*:',primary,re.M)
    require(fields==['lowZeta','reversZeta','mollifierMeanSquare','sourceSmoothing','sourceRightMoment','sourceRectangle','sourceUnsmoothing','sourceInterpolation'],'source input package changed')
    generic=source(BASE+'HeightGenericAll.lean')
    imports=re.findall(r'^import SynergyAnalytic\.Height768GenericV4\.Chunk(\d+)$',generic,re.M)
    require([int(x) for x in imports]==list(range(96)),'height chunk import coverage/order')
    height_indices=[]
    for b in range(96):
        relative=BASE+f'Height768GenericV4/Chunk{b:02d}.lean'
        text=source(relative)
        require(f'(logCell (j+{8*b}+1))' in text and f'(cWords[j+{8*b}]?)' in text and f'(DWords[j+{8*b}]?)' in text,'point/cap offset mismatch')
        height_indices.extend(range(8*b,8*b+8))
        anchors.append(anchor(relative,f'theorem kernel_height_generic_v4_chunk{b:02d}'))
    require(height_indices==list(range(768)),'actual height point coverage')
    budget_indices=[]
    for b in range(6):
        relative=BASE+f'HeightBudgetChunk{b:02d}.lean'
        text=source(relative)
        require(f'(sumBudget 32 (32*(j+{4*b})) zero)' in text and f'(blockWords[j+{4*b}]?)' in text,'budget block/cap offset mismatch')
        budget_indices.extend(range(4*b,4*b+4))
        anchors.append(anchor(relative,f'theorem kernel_budget_chunk{b}'))
    require(budget_indices==list(range(24)),'actual budget block coverage')
    text=source(BASE+'HeightBudgetBlocks.lean')
    words_match=re.search(r'def blockWords : List Int := \[([^]]*)\]',text)
    require(words_match is not None,'block words not found')
    words=[int(v.strip()) for v in words_match.group(1).split(',')]
    require(len(words)==24 and all(v>0 for v in words),'actual block words count/sign')
    finite=F(sum(words),2**128)
    finite_cap=F(8433850764,10**12)
    require(finite<=finite_cap,'tight finite-word total')
    # Exactly the rational relaxations consumed by final_height_budget_tight.
    profile=finite_cap+F(1,250000)*F(330,170)+F(1,50000000)+F(1,10**12)*9+F(1,10**12)
    final=(1+F(1,10**9))*(F(1,10**12)+profile)+F(1,10**12)+F(1,10**8)
    cap=F(8441646,10**9)
    require(final<cap,'final analytic allowance/rounding')
    prime=F(17,1000)/F(1000001,1000000)-F(4221,500000)*(F(5001,5000)+1)
    require(prime>=F(57,500000),'prime-rich transfer coefficient')
    old_prime=F(17,1000)/F(1000001,1000000)-F(43,5000)*(F(5001,5000)+1)
    require(old_prime<0,'old coefficient comparison')
    receipt_rows=[]
    for suffix,module,roots in [('heightpntinstance','HeightPNTInstance',['actual_height_cells','source_pi_008442','source_pi_008441646']),('heightprimerichinstance','HeightPrimeRichInstance',['source_prime_rich_017'])]:
        relative=f'research/analytic/work/height-nf-closure-v1-{suffix}/RECEIPT.json'
        p=ROOT/relative;j=json.loads(p.read_text())
        require(j['exit_code']==0 and j['source_unchanged'],'actual accepted Lean receipt')
        require(j['source_sha256']==digest(ROOT/(BASE+module+'.lean')),'receipt/source identity')
        stdout=(p.parent/'stdout.txt').read_text()
        for root in roots:
            needle=f"'SynergyAnalytic.HeightPoint.{root}' depends on axioms: [propext, Classical.choice, Quot.sound]"
            require(needle in stdout,f'full Std3 closure absent: {root}')
        receipt_rows.append({'file':relative,'sha256':digest(p),'module':module,'selected_roots':roots,'seconds':j['seconds'],'tier':j['tier'],'source_sha256':j['source_sha256']})
    result={'status':'BOUNDED_INDEPENDENT_REVIEW_NO_MATHEMATICAL_DEFECT_FOUND','scope':'Named conditional Lean mathematical proof path; not an exhaustive original-paper source audit, fresh source-cold replay, or source-first PV. Manual proof review is described in REPORT.html; this script only repeats finite structural/hash/rational checks.', 'original_primary_fields':fields,'separate_original_assumptions':['OriginalCHJSource','rvm_error_bound','rvm_error_small','no_zeroes_below_first_ordinate','RH up to 3e12','open zero-free half-plane Re(s)>7/8'],'height_cells':768,'budget_blocks':24,'budget_cells_per_block':32,'finite_words_sum':str(finite),'finite_words_sum_decimal':float(finite),'finite_cap':str(finite_cap),'final_rational_upper':str(final),'final_rational_upper_decimal':float(final),'claimed_tight_cap':str(cap),'cap_margin':str(cap-final),'prime_rich_transfer_lower':str(prime),'prime_rich_claimed_lower':str(F(57,500000)),'old_0086_same_transfer':str(old_prime),'reviewed_sources':anchors,'accepted_warm_kernel_receipts':receipt_rows,'remaining_trust':['ordinary Lean kernel and standard propext/Classical.choice/Quot.sound','the displayed original analytic/source hypotheses remain assumptions','warm imports and pinned toolchain; no new independent full-source replay in this review','actual C producer/helper/evaluate/I/O/source-linked numerical outputs remain separate unfinished source-first PV obligations']}
    out.mkdir(parents=True,exist_ok=True)
    payload=json.dumps(result,indent=2,sort_keys=True)+'\n'
    tmp=out/'REVIEW.json.tmp';tmp.write_text(payload);tmp.replace(out/'REVIEW.json')
    print(json.dumps({k:result[k] for k in ['status','height_cells','budget_blocks','final_rational_upper_decimal']}))

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,default=HERE);a=parser.parse_args();run(a.out)
