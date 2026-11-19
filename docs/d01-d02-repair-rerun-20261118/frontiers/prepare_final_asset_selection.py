"""Explicit final public evidence selection; no draft trees or generated caches."""
from pathlib import Path
import json,hashlib
F=Path(__file__).resolve().parent;old=F.parent/'twenty-normalized-frontiers-v1'
rows={}
def add(p,archive,role):
    p=Path(p)
    if not p.is_file():raise ValueError('MISSING_FINAL_SELECTED_ASSET '+str(p))
    item={'path':str(p),'archive_path':archive,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size,'role':role}
    if archive in rows and rows[archive]!=item:raise ValueError('CONFLICTING_ARCHIVE_IDENTITY '+archive)
    rows[archive]=item
names='''REPORT.html REPORT.md REPORT_BASE_WITHOUT_FONT.html README_REPRODUCE_FINAL24.md
ALL24_SOURCE_BOUND_OBJECTS.json NORMALIZED_OBJECTS.json FINITE_EXPLICIT_FUNCTIONS.json MATCHED_R_COEFFICIENT_VECTOR_TABLE.json WHOLE_SYMBOLIC_OPERATOR_FRONTIERS.json SAME_ONSET_DIAGNOSTIC_FUNCTION_VALUES.json EXACT_SOURCE_PAIRED_M_FUNCTION_RATIO_CHECKS.json EXACT_COMPARISON_ALGEBRA_AND_SOURCE_EXAMPLES.json PLOT_DOMAIN_CASE_AND_REPRESENTATION_COVERAGE.json QUANTITATIVE_LITERAL_CLAUSE_COVERAGE.json
FROZEN_FINALIZATION_SELECTION.json ALL100_ASSUMPTION_FORMS_SOURCE_KEYS.json NEW_EXACT_ASSUMPTION_FORMS.json EXACT_ASSUMPTION_FORM_POLICY.json EXACT_BARE_INTERVAL_SOURCE_AXIS_POLICY.json HISTORICAL48_DOMAIN_REPRESENTATION_RECHECK.json CURRENT_C022_FINALIZATION_METADATA_V2.json REVIEWED_M_LITERAL_RECEIVER_INTERFACES_V1.json REVIEWED_R_LITERAL_RECEIVER_INTERFACES_V1.json
ACTUAL_ALL24_INTERFACE_NORMAL_O_OO_CONTROLS.json ACTUAL_PORTABLE_SOURCE_NORMAL_O_OO_READ_DENIAL_CONTROLS.json ACTUAL_CLEAN_PORTABLE_ANALYSIS_REGENERATION.json ACTUAL_ALL53415_PLOT_POINTS_SOURCE_DOMAIN_AND_ORDINATE_RECHECK.json ACTUAL_FINAL24_PLOT_COMMAND_1_RECEIPT.json ACTUAL_FINAL24_PLOT_COMMAND_2_RECEIPT.json ACTUAL_FINAL24_PLOT_METADATA_PREFLIGHT.json ACTUAL_PLOT_REGENERATION_RECEIPT.json ACTUAL_PLOT_RECEIPT.json PLOT_EXECUTION_PLAN_FINAL24_UNSIGNED.json FINAL_SOURCE_LITERAL_EXTRACTION_DELTA_AND_DOMAIN_QUERIES.json
ROOT_UNEXPANDED2252_EXACT_SOURCE_SCOPE_REVIEW.json ROOT_UNEXPANDED2252_EXACT_GROUP_INDEX.json ROOT_EXACT2252_INDEPENDENT_COVERAGE_PARTITION.json ROOT_REMAINDER_READ_ROOT.json ROOT_NONFOUNDATION536_LITERAL_SCOPE_READBACK_PENDING_BINDINGS.json ROOT_NONFOUNDATION32_M_LITERAL_BINDINGS_V1.json CONCRETE_FOUNDATION_M_BINDING_WORKLIST.json M_LITERAL_RECEIVER_SCOPE_DISPOSITIONS_V1.json FINISH_REPRO_FOUNDATION_LITERAL_SOURCE_DISPOSITIONS_V1.json FINISH_REPRO_CONCRETE_FOUNDATION_RECEIVER_BINDING_FLAGS_V1.json FINISH_REPRO_M_COMPLETE_LITERAL_SCOPE_CLOSURE_V3.json FINISH_REPRO_M_ROOT_AND_COMPOSITE_SOURCE_PEER_V4.json FINISH_REPRO_R_SCOPE_CLOSURE_AFTER_EXTRACTION_V3.json FINISH_REPRO_R_EXACT_RECEIVER_MAPPING_V3.json FINISH_REPRO_R_ADDITIVE_EXACT_SOURCE_BRANCHES_V3.json FINISH_REPRO_R_C004_FULL_VECTOR_DEFINITION_SOURCE.json FINISH_REPRO_C021420000_WEIGHTED_INTERFACE_SOURCE_CORRECTION.json
THROUGH_PHYSICAL_LF_EXACT_SOURCE_RANGE_CORRIGENDUM.json C011_OLD_DIRECT_EXPLICIT_SOURCE_CASE_CORRIGENDUM.json LEGACY_PARSER_SOURCE_COPY_RECEIPT.json REQUIRED_ADDITIONAL_ANALYSIS_SOURCE_ASSETS_V1.json REQUIRED_ADDITIONAL_COLLECTOR_SOURCE_ASSETS_V1.json LATEST_OFFLINE_FONT_EMBEDDING.json
RAMANUJAN_EARLY_FRONTIERS.svg MERTENS_FOUR_ERROR_FRONTIERS.svg RAMANUJAN_MATCHED_VECTOR_ONSETS.svg MERTENS_FOUR_ERROR_PREVIEW.png PLOT_VALUES_AND_CHOSEN_SOURCE_FUNCTIONS.csv plot-requirements.lock plot-requirements-with-hashes.lock'''.split()
for name in names:add(F/name,'frontiers/'+name,'final source-bound comparison, exact accepted inputs/output or source-scope evidence')
for p in sorted(F.glob('*.py')):
    if p.name not in ['validate.py','coordinate_gate.py']:add(p,'frontiers/'+p.name,'analysis/reproduction/source-scope validator source; historical host controller paths are not the portable recipe')
for name in ['ALL24_SOURCE_BOUND_OBJECTS.json','NORMALIZED_OBJECTS.json','MATCHED_R_COEFFICIENT_VECTOR_TABLE.json']:
    add(F/(name+'.gz'),'frontiers/'+name+'.gz','deterministic gzip for GitHub-sized download; raw JSON restored and verified on bundle reconstruction')
add(F/'evidence-inputs/PORTABLE_SOURCE_MAP_V8.json','frontiers/evidence-inputs/PORTABLE_SOURCE_MAP_V8.json','exact historical source-map bytes consumed by accepted12 source-CLI controls')
for name in ['ACTUAL_CLEAN_SOURCE_MAP_V1.json','CLEAN_ORIGINAL_WORKSPACE_OPEN_DENIAL_SITECUSTOMIZE.py','PORTABLE12_ORIGINAL_WORKSPACE_OPEN_DENIAL_SITECUSTOMIZE.py']:
    add(F/'evidence-inputs'/name,'frontiers/evidence-inputs/'+name,'exact accepted source-map or original-workspace read-denial helper consumed by completed portable controls')
for p in (old/'plot-wheels').iterdir():add(p,'frontiers/plot-wheels/'+p.name,'exact pinned offline binary plotting wheel')
for name in ['plot-dependencies-INSTALLED_SOURCE_MANIFEST_V4.json','plot-regeneration-dependencies-INSTALLED_SOURCE_MANIFEST_V4.json']:
    add(old/name,'frontiers/evidence-inputs/'+name,'full installed environment identity used by both actual final plot commands')
for rec in json.loads((F/'ACTUAL_ALL24_INTERFACE_NORMAL_O_OO_CONTROLS.json').read_text())['records']:
    for k in ['stdout','stderr']:
        p=Path(rec[k]['path']);add(p,'frontiers/'+str(p.relative_to(F)),'actual final72 CLI output; invalid fixture datasets are regenerable and not selected')
for rec in json.loads((F/'ACTUAL_PORTABLE_SOURCE_NORMAL_O_OO_READ_DENIAL_CONTROLS.json').read_text())['records']:
    for k in ['stdout','stderr']:
        p=Path(rec[k]['path']);add(p,'frontiers/'+str(p.relative_to(F)),'actual final12 mapped-source CLI stdout/stderr')
font=json.loads((F/'LATEST_OFFLINE_FONT_EMBEDDING.json').read_text())
# Preserve the actual latest renderer receipt and its locally copied licensed sources.
for p in sorted((F/'font-embedding-runs').rglob('*')):
    if p.is_file():add(p,'frontiers/'+str(p.relative_to(F)),'actual offline MathML/font rendering evidence or unchanged licensed renderer/font source')
for name in ['PLOT_PREFLIGHT.stdout.log','PLOT_PREFLIGHT.stderr.log','FINAL_PLOT_EXECUTION.stdout.log','FINAL_PLOT_EXECUTION.stderr.log','REPORT_FINAL.stdout.log','REPORT_FINAL.stderr.log','FINAL_COVERAGE_CURRENT.stdout.log','FINAL_COVERAGE_CURRENT.stderr.log','LINEAGE_CURRENT.stdout.log','LINEAGE_CURRENT.stderr.log']:
    add(F/name,'frontiers/'+name,'actual completed final metadata/plot output')
clean=json.loads((F/'ACTUAL_CLEAN_PORTABLE_ANALYSIS_REGENERATION.json').read_text());work=Path(clean['root'])/'reproduction-work/frontiers'
for p in (work/'analysis-regeneration-runs').rglob('*'):
    if p.is_file():add(p,'frontiers/clean-analysis-evidence/'+str(p.relative_to(work)),'actual seven-step clean portable metadata run, original workspace reads denied')
add(work/'ACTUAL_SEQUENTIAL_ANALYSIS_REGENERATION.json','frontiers/clean-analysis-evidence/ACTUAL_SEQUENTIAL_ANALYSIS_REGENERATION.json','actual relocated seven-step success pointer')
for dirname in ['clean-analysis-reproduction-v1','clean-analysis-reproduction-v2']:
    for p in (F/dirname).glob('*'):
        if p.is_file():add(p,'frontiers/'+str(p.relative_to(F)),'preserved failedclosed first source-map attempt or completed retry; filenames distinguish historical evidence')
# The source-extraction audit re-reads the immutable original15441-row snapshot.
add(F/'pre-literal-receiver-expansion-v1/FINITE_EXPLICIT_FUNCTIONS.json','frontiers/pre-literal-receiver-expansion-v1/FINITE_EXPLICIT_FUNCTIONS.json','original15441-row comparison preserved, explicitly historical')
add(F/'pre-literal-receiver-expansion-v1/normalize.py','frontiers/pre-literal-receiver-expansion-v1/normalize.py','historical flawed C021 generic four-target source attribution, explicitly not active')
out={'schema':'EXPLICIT_PUBLIC_FRONTIER_ASSET_SELECTION_V1','status':'FINAL_SELECTED_MATHEMATICAL_SOURCE_COMPARISON_AND_REPRODUCTION_ASSETS','files':sorted(rows.values(),key=lambda r:r['archive_path']),'retained_generated_large_raw_JSON_restored_from_gzip':True,'not_selected':'Draft triage and pending-status ledgers; regenerable invalid fixture data; bytecode/cache directories; broad private context; unused historical plot environments.'}
p=F/'FINAL_PUBLIC_FRONTIER_ASSET_SELECTION_V1.json';p.write_text(json.dumps(out,indent=2)+'\n');print('FINAL_SELECTION',len(rows),p.stat().st_size,hashlib.sha256(p.read_bytes()).hexdigest())
