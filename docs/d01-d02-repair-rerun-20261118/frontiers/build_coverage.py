"""Lossless all-source coverage ledger, independent of the scalar parser predicate.
Does not declare an unexpanded literal nonnumerical or prove full-operator dominance.
"""
from collect import *

def main():
    source=load(O/'ALL24_SOURCE_BOUND_OBJECTS.json');norm=load(O/'NORMALIZED_OBJECTS.json');finite=load(O/'FINITE_EXPLICIT_FUNCTIONS.json');by={tuple(r['key']):r for r in norm['objects']};bm={r['bound_id']:r for r in finite['bounds']}
    independent=N/'coordinator-private/independent-final24-quantitative-coverage-v1';ip=independent/'ALL24_ACCEPTED_INDEPENDENT_LITERAL_CLAUSE_SOURCE_CENSUS_V3.json';census=load(ip);ib={tuple(r['key']):r for r in census['objects']}
    need(len(ib)==11411 and set(by)==set(ib),'EXACT_ALL11411_INDEPENDENT_SOURCE_UNIVERSE_JOIN')
    mappings=load(independent/'CONFIRMED_LITERAL_TO_BOUND_MAPS_V2.json');mapped={}
    for m in mappings['maps']:
        key=tuple(m['source_key']);need(key in by,'independent literal mapping actual source key')
        checked=[]
        for b in m['actual_target_bound_records']:
            actual=bm[b['bound_id']];audit=__import__('copy').deepcopy(actual)
            for field in ['source_interval_axis','source_axis_basis','source_axis_context']:
                if field not in b['domain']:audit['domain'].pop(field,None)
            need(audit==b,'independent alias mathematical parameters/domain/source remain exact; only explicit axis provenance may be additive')
            checked.append(b['bound_id'])
        mapped[key]={'independent_relation':m['relation'],'exact_literal_clause':m['literal_quantitative_clause'],'target_bound_ids':checked,'source':m['original_written_identity']}
    rclose=load(O/'FINISH_REPRO_R_SCOPE_CLOSURE_AFTER_EXTRACTION_V3.json');mclose=load(O/'FINISH_REPRO_M_COMPLETE_LITERAL_SCOPE_CLOSURE_V3.json');need(rclose['unmapped_scalar_clauses']==0 and mclose['pending_fixed_numeric_clauses']==0,'ALL_FIXED_LITERAL_RECEIVER_CLAUSES_HAVE_CLOSED_INDEPENDENT_SCOPE')
    need(rclose['assigned_R_groups']==171 and rclose['assigned_R_exact_keys']==197 and mclose['foundation_groups']==100 and mclose['foundation_exact_source_keys']==119 and mclose['Root_nonfoundation_exact_keys']==32,'EXACT_REVIEWED_LITERAL_SCOPE_POPULATIONS')
    frozen_functions=load(verified(rclose['actual_current_function_snapshot']));need(frozen_functions['bounds']==finite['bounds'],'CURRENT_ALL_FUNCTION_MATHEMATICAL_BODIES_EQUAL_INDEPENDENT_REVIEW_SNAPSHOT')
    for ref in mclose['source_snapshots']:
        actual_ref=dict(ref)
        if not Path(actual_ref['path']).is_absolute():actual_ref['path']=str(N/actual_ref['path'])
        verified(actual_ref)
    rmap=load(verified(rclose['exact_checked_mapping']));rreview={tuple(x['key']):{'kind':'INDEPENDENT_EXACT_R_FUNCTION_OR_VECTOR_MAPPING','source':pin(O/'FINISH_REPRO_R_EXACT_RECEIVER_MAPPING_V3.json'),'key':x['key']}for x in rmap['fixed_receiving_entries']}
    for item in rmap['native_exact_predicates']:
        for key in item['exact_keys']:rreview[tuple(key)]={'kind':item['status'],'source':pin(O/'FINISH_REPRO_R_EXACT_RECEIVER_MAPPING_V3.json'),'key':key}
    mreview={}
    for group in mclose['foundation_source_dispositions']:
        for item in group['source_dispositions']:mreview[tuple(item['key'])]={'kind':item['status'],'source':pin(O/'FINISH_REPRO_M_COMPLETE_LITERAL_SCOPE_CLOSURE_V3.json'),'key':item['key'],'pending_fixed_numeric_clause':item['pending_fixed_numeric_clause']}
    for item in mclose['Root_nonfoundation_independent_checks']:mreview[tuple(item['key'])]={'kind':item['status'],'source':pin(O/'FINISH_REPRO_M_COMPLETE_LITERAL_SCOPE_CLOSURE_V3.json'),'key':item['key'],'pending_fixed_numeric_clause':item['pending_fixed_numeric_clause']}
    foundation=load(O/'FINISH_REPRO_FOUNDATION_LITERAL_SOURCE_DISPOSITIONS_V1.json');foundation_keys={tuple(key):{'kind':'INDEPENDENT_ACTUAL_SOURCE_STATEMENT_SCOPE_DISPOSITION','source':pin(O/'FINISH_REPRO_FOUNDATION_LITERAL_SOURCE_DISPOSITIONS_V1.json'),'group':group['group'],'actual_source_dispositions':group['dispositions']}for group in foundation['groups']for key in group['exact_keys']}
    rootgroups=load(O/'ROOT_REMAINDER_READ_ROOT.json');rootread=load(O/'ROOT_NONFOUNDATION536_LITERAL_SCOPE_READBACK_PENDING_BINDINGS.json');need(len(rootgroups)==rootread['exact_groups_represented']==536,'ALL_ROOT_ASSIGNED_NONFOUNDATION_SOURCE_GROUPS_READ')
    rootkeys={tuple(key):{'kind':'ROOT_ACTUAL_FULL_STATEMENT_SOURCE_SCOPE_READ_WITH_CONCRETE_CLAUSES_SEPARATELY_BOUND','source':pin(O/'ROOT_REMAINDER_READ_ROOT.json'),'group':group['group'],'scope_read_receipt':pin(O/'ROOT_NONFOUNDATION536_LITERAL_SCOPE_READBACK_PENDING_BINDINGS.json')}for group in rootgroups for key in group['keys']}
    need(len(foundation_keys)==1643 and len(rootkeys)==609 and not(set(foundation_keys)&set(rootkeys)),'EXACT2252_ORIGINAL_UNEXPANDED_SOURCE_POPULATION_PARTITION_NO_COLLAPSE')
    original_remainder=load(O/'ROOT_UNEXPANDED2252_EXACT_SOURCE_SCOPE_REVIEW.json');need(set(foundation_keys)|set(rootkeys)=={tuple(x['key'])for x in original_remainder['rows']},'EXACT_ENTIRE2252_SOURCE_SCOPE_AUDIT_JOIN')
    root32=load(O/'ROOT_NONFOUNDATION32_M_LITERAL_BINDINGS_V1.json');need(len(root32['records'])==32 and root32['all32_exact_source_keys_checked']is True,'ALL_ROOT_CONCRETE_M_CLAUSES_EXACTLY_BOUND')
    for item in root32['records']:
        for target in item['actual_current_target_records']:need(bm[target['bound_id']]==target,'CURRENT_EXACT_ROOT_M_ALIAS_TARGET_PARAMETERS_SOURCE_DOMAIN_PREMISES')
    normalized_pin=pin(O/'NORMALIZED_OBJECTS.json');independent_pin=pin(ip)

    rows=[];counts=collections.Counter()
    for key,r in by.items():
        ii=ib[key];ss=r['source'];isrc=ii['source'];need((ss['sha256'],ss['physical_LF'],ss['physical_LF_end'])==(isrc['sha256'],isrc['physical_LF'],isrc['physical_LF_end']),'EXACT_INDEPENDENT_WRITTEN_SHA_LF_IDENTITY')
        status='EXPANDED_SOURCE_RECEIVING_FUNCTIONS'if r['finite_bound_ids']else'EXPLICIT_INDEPENDENT_EQUAL_OR_STRONGER_FUNCTION_MAPPING'if key in mapped else'EXACT_SOURCE_DEFINED_INTERFACE_RETAINED_NOT_AUTOMATICALLY_NONNUMERICAL'
        evidence=mreview.get(key)or rreview.get(key)or foundation_keys.get(key)or rootkeys.get(key)
        need(r['finite_bound_ids']or key in mapped or evidence is not None,'NO_UNREVIEWED_UNEXPANDED_SOURCE_SCOPE_ROW')
        counts[status]+=1
        rows.append({'key':r['key'],'family':r['family'],'written_identity':{k:ss[k]for k in ['file','physical_LF','physical_LF_end','sha256']},'representation_status':status,'actual_source_scope_evidence':evidence,'source_claim_scope_class':r['object_role'],'direct_function_ids':r['finite_bound_ids'],'independent_literal_to_function_map':mapped.get(key),'exact_expression_and_all_domain_parameter_guards':{'normalized_source':normalized_pin,'key':r['key']},'Root_qualified_statement_distinguished_from_raw':r.get('current_qualified_statement')is not None,'independent_literal_numeric_and_receiver_annotations_preserved_in':{'source':independent_pin,'key':r['key']},'an_unexpanded_scalar_is_not_declared_nonnumerical':True})
    save('QUANTITATIVE_LITERAL_CLAUSE_COVERAGE.json',{'status':'PASS_ALL11411_SOURCE_SCOPE_AND_LITERAL_RECEIVER_COVERAGE','created_by':'informed coordinator; independent all-floor source census supplied separately','requested_universe':'Every one of the24 Root-finalized current qualified portfolios, all11411 exact written-source identities; no parser or language heuristic decides inclusion.','all11411_rows':rows,'representation_counts':dict(counts),'expanded_function_count':len(bm),'complete_source_universe_independent_join':pin(independent/'FINAL24_SOURCE_COLLECTION_INDEPENDENT_JOIN.json'),'independent_census':pin(ip),'independent_confirmed_literal_mappings':pin(independent/'CONFIRMED_LITERAL_TO_BOUND_MAPS_V2.json'),'independent_units_case_onset_readback':pin(independent/'EXACT_ADDITIONAL_LITERAL_UNITS_AND_DOMAINS_READBACK_V1.json'),'historical48_literal_domains':pin(O/'HISTORICAL48_DOMAIN_REPRESENTATION_RECHECK.json'),'all248_bare_interval_source_axis_policy':pin(O/'EXACT_BARE_INTERVAL_SOURCE_AXIS_POLICY.json'),'independent_R_literal_scope_closure':pin(O/'FINISH_REPRO_R_SCOPE_CLOSURE_AFTER_EXTRACTION_V3.json'),'independent_M_literal_scope_closure':pin(O/'FINISH_REPRO_M_COMPLETE_LITERAL_SCOPE_CLOSURE_V3.json'),'original2252_source_scope_read_complete':True,'pending_fixed_literal_receiver_clauses':0,'native_exact_lower_sign_root_or_operator_predicates_are_not_silently_nonnumerical':True,'numeric_plot_inclusion':'Every accepted expanded source receiving bound in G/ES/EP/EQ/EW, with its complete real source interval and resolved exact B0/D02 case. Root-defined rays retain exact boundaries; only their separate conservative projection is evaluated. No quality selection.','numeric_plot_exclusion':'Other native observables and proof providers, diagnostics/refutations, counterfactual/full-RH cases, quantified/integral/signed-intersection operators and other exact source-defined compound expressions have no numerical contribution unless separately converted to a justified receiving bound. They remain in the complete source operator closure.','canonical_target_family_field_is_not_a_provider_to_receiver_cast':True,'all_operators_numerically_optimized':False,'new_mathematics_or_premises_from_parser_repairs':False})
    print('PASS_ALL11411_LOSSLESS_INTERFACE_AND12_INDEPENDENT_LITERAL_MAPPING_JOINS')
if __name__=='__main__':main()
