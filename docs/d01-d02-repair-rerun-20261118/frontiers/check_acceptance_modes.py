"""Actual normal/-O/-OO metadata CLIs; no models, mathematical execution or builds."""
import json,subprocess,sys,time,hashlib
from pathlib import Path
from collect import O,save,pin,need

def main():
    out=O/'actual-all24-interface-cli-controls-v7';out.mkdir(exist_ok=False)
    def rat(v):return {'numerator':str(v),'denominator':'1'}
    # Every altered input lives only in this new owned fixture directory.
    fixtures={
      'weighted_log_degree':('branch',{'object_key':['FOLLOWUP-C019','M.power47'],'quantity':'EW','replace':{'log_denominator_degree':1}}),
      'wrong_power_rate':('branch',{'object_key':['FOLLOWUP-C017','M-power-prefix-1-2'],'quantity':'ES','replace':{'x_decay_exponent':{'numerator':'1','denominator':'8'}}}),
      'source_order_as_degree':('branch',{'object_key':['FOLLOWUP-C016','R-repair-69'],'quantity':'G','replace':{'degree':69}}),
      'unknown_assumptions':('branch',{'object_key':['FOLLOWUP-C019','M.power47'],'quantity':'ES','replace':{'assumptions':'UNREVIEWED_UNKNOWN_INPUT'}}),
      'missing_finite_integral':('object',{'object_key':['FOLLOWUP-C022','D02.M.general-kernel'],'replace':{'current_qualified_statement':'Unrestricted decreasing f only'}}),
      'full_RH_promoted':('object',{'object_key':['FOLLOWUP-C024','R-DP-RH'],'replace':{'scope':'B0_OR_WEAKER_AS_DECLARED'}}),
    }
    finite=json.loads((O/'FINITE_EXPLICIT_FUNCTIONS.json').read_text())['bounds'];by={b['bound_id']:b for b in finite}
    c20=next(b for b in finite if b['object_key']==['FOLLOWUP-C020','R-stronger-constant-3']);d=json.loads(json.dumps(c20['domain']));d['numeric_intervals'][0]['upper']=None
    fixtures['finite_to_false_global_ray']=('branch',{'object_key':c20['object_key'],'quantity':'G','replace':{'domain':d}})
    c23=next(b for b in finite if b['object_key']==['FOLLOWUP-C023','R02-global-scope-correction']);d=json.loads(json.dumps(c23['domain']));d['numeric_intervals'][0]['upper']=None
    fixtures['refuted_bound_promoted']=('branch',{'object_key':c23['object_key'],'quantity':'G','replace':{'domain':d}})
    root=next(b for b in finite if b['object_key']==['FOLLOWUP-C009','M-small-root-.29446-D1']);d=json.loads(json.dumps(root['domain']));d.pop('exact_symbolic_intervals')
    fixtures['root_replaced_by_upper_bracket']=('branch',{'object_key':root['object_key'],'quantity':'ES','replace':{'domain':d}})
    fixtures['duplicate_json']=('branch','{"object_key":[],"object_key":[],"quantity":"EW","replace":{}}')
    fixtures['nonfinite_json']=('branch','{"object_key":[],"quantity":"EW","replace":{"x":NaN}}')
    axis=next(b for b in finite if b['object_key']==['FOLLOWUP-C022','M.band.finite100m.txt.3']and b['quantity']=='EW');d=json.loads(json.dumps(axis['domain']));d['numeric_intervals'][0]['lower']['coordinate']='L';d['numeric_intervals'][0]['upper']['coordinate']='L'
    fixtures['prime_tape_as_log_axis']=('branch',{'object_key':axis['object_key'],'quantity':'EW','replace':{'domain':d}})
    es=next(b for b in finite if b['object_key']==['FOLLOWUP-C023','M-step-11']and b['quantity']=='ES');d=json.loads(json.dumps(es['domain']));d['numeric_intervals'][0]['lower']['rational']=rat(2278382)
    fixtures['copied_ES_guard']=('branch',{'object_key':es['object_key'],'quantity':'ES','replace':{'domain':d}})
    fixtures['domain_clause_as_error']=('object',{'object_key':['FOLLOWUP-C003','M-finite-pointwise'],'replace':{'finite_bound_ids':['FABRICATED_DOMAIN_ERROR_CAP']}})
    fixtures['diagnostic_as_suffix']=('object',{'object_key':['FOLLOWUP-C022','M.threshold.finite100m.txt.1.P,Q'],'replace':{'finite_bound_ids':['FABRICATED_POSITIVE_SUFFIX']}})
    fixtures['unlicensed_weaker_B0']=('branch',{'object_key':['FOLLOWUP-C022','D02.M.fast.168'],'quantity':'ES','replace':{'case':'B0'}})
    fixtures['G_M_as_log_units']=('branch',{'object_key':['FOLLOWUP-C018','M-targets'],'quantity':'ES','replace':{'log_denominator_degree':3}})
    fixtures['density_free_wrong_log_sign']=('branch',{'object_key':['FOLLOWUP-C010','M-fallback'],'quantity':'EW','replace':{'log_denominator_degree':2}})
    witness=next(b for b in finite if b['object_key']==['FOLLOWUP-C018','M-witness-0-200']);domain=json.loads(json.dumps(witness['domain']));domain['numeric_intervals'][0]['upper']=None
    fixtures['witness_as_global_ray']=('branch',{'object_key':witness['object_key'],'quantity':'ES','replace':{'domain':domain}})
    fixtures['literal_source_coefficient']=('branch',{'object_key':['FOLLOWUP-C007','M-basic-uniform-0'],'quantity':'ES','replace':{'coefficient':rat(0)}})
    fixtures['unlicensed_weighted420000']=('branch',{'object_key':['FOLLOWUP-C021','M-power-420000'],'quantity':'ES','replace':{'quantity':'EW'}})
    newroot=next(b for b in finite if b['object_key']==['FOLLOWUP-C024','M-new-root-16']and b['quantity']=='EP');domain=json.loads(json.dumps(newroot['domain']));domain['exact_symbolic_intervals']=[]
    fixtures['new_exact_root_as_endpoint']=('branch',{'object_key':newroot['object_key'],'quantity':'EP','replace':{'domain':domain}})
    paths={}
    for name,(kind,data)in fixtures.items():
        p=out/(name+'.json');p.write_text(data if isinstance(data,str)else json.dumps(data,sort_keys=True));paths[name]=(kind,p)
    inputs=[pin(O/n)for n in ['reviewed_literal_interfaces.py','REVIEWED_M_LITERAL_RECEIVER_INTERFACES_V1.json','REVIEWED_R_LITERAL_RECEIVER_INTERFACES_V1.json','source_resolver.py','collect.py','normalize.py','compare.py','check_acceptance_modes.py','premises.py','legacy_coordinate_parser_v1.py','check_interfaces.py','EXACT_ASSUMPTION_FORM_POLICY.json','EXACT_BARE_INTERVAL_SOURCE_AXIS_POLICY.json','ALL24_SOURCE_BOUND_OBJECTS.json','NORMALIZED_OBJECTS.json','FINITE_EXPLICIT_FUNCTIONS.json']]
    records=[]
    for mode in [[],['-O'],['-OO']]:
        for name in ['positive']+list(paths):
            argv=[sys.executable,*mode,'-B',str(O/'check_interfaces.py'),'--check']
            if name!='positive':kind,p=paths[name];argv += ['--'+kind+'-fixture',str(p)]
            st=time.monotonic();r=subprocess.run(argv,capture_output=True,text=True);tag=('normal'if not mode else mode[0][1:])+'-'+name
            (out/(tag+'.stdout')).write_text(r.stdout);(out/(tag+'.stderr')).write_text(r.stderr)
            expected=0 if name=='positive'else 1
            need(r.returncode==expected,'ACTUAL_CLI_EXPECTED_STATUS '+tag+':'+str(r.returncode))
            if name!='positive':
                need('ValueError' in r.stderr,'EXPLICIT_REJECTION '+tag)
                markers={'new_exact_root_as_endpoint':'SOURCE_LITERAL_EXACT_ROOT_DOMAIN','unlicensed_weighted420000':'SOURCE_LITERAL_COORDINATE_EXTRACTION_CORRESPONDENCE','witness_as_global_ray':'SOURCE_LITERAL_FINITE_INTERVAL_NEVER_A_RAY','literal_source_coefficient':'SOURCE_LITERAL_COORDINATE_EXTRACTION_CORRESPONDENCE','weighted_log_degree':'SOURCE_COEFFICIENT_RATE_LOG_DEGREE','wrong_power_rate':'SOURCE_COEFFICIENT_RATE_LOG_DEGREE','source_order_as_degree':'SOURCE_ORDER_TO_CANONICAL_DEGREE','unknown_assumptions':'EXACT_SOURCE_ASSUMPTIONS','missing_finite_integral':'FINITE_INTEGRAL_ROOT_QUALIFICATION','full_RH_promoted':'FULL_RH_NOT_CURRENT','finite_to_false_global_ray':'SOURCE_UPPER_ENDPOINT_NOT_A_RAY','refuted_bound_promoted':'SOURCE_UPPER_ENDPOINT_NOT_A_RAY','root_replaced_by_upper_bracket':'EXACT_ROOT_NOT_REPLACED','duplicate_json':'duplicate','nonfinite_json':'nonfinite','prime_tape_as_log_axis':'SOURCE_AXIS_X_VS_LOG_NOT_DEFAULT','copied_ES_guard':'COPIED_SOURCE_ES_EXTRA_ONSET_GUARD','domain_clause_as_error':'DOMAIN_INEQUALITY_IS_NOT_ERROR_BOUND','diagnostic_as_suffix':'DIAGNOSTIC_NO_POSITIVE_SUFFIX','unlicensed_weaker_B0':'D02-only source cannot acquire B0','G_M_as_log_units':'G_M_IS_NOT_LOG_POWER_UNITS','density_free_wrong_log_sign':'DENSITY_FREE_SOURCE_POSITIVE_LOG_FACTOR'}
                need(markers[name].lower() in r.stderr.lower(),'SPECIFIC_INTENDED_REJECTION '+tag)
            for source0 in inputs:need(pin(source0['path'])==source0,'ACTUALLY_TESTED_IMMUTABLE_INTERFACE_INPUT_VERSION')
            records.append({'case':tag,'argv':argv,'returncode':r.returncode,'wall_seconds':time.monotonic()-st,'stdout':pin(out/(tag+'.stdout')),'stderr':pin(out/(tag+'.stderr'))})
    missing=out/'missing-literal-table-fixture';missing.mkdir()
    for name in ['reviewed_literal_interfaces.py','collect.py','source_resolver.py']:(missing/name).write_bytes((O/name).read_bytes())
    for mode in [[],['-O'],['-OO']]:
        argv=[sys.executable,*mode,'-B','-c','import reviewed_literal_interfaces as x; x.entries()'];st=time.monotonic();r=subprocess.run(argv,cwd=missing,capture_output=True,text=True);tag=('normal'if not mode else mode[0][1:])+'-missing-required-literal-table';stdout=out/(tag+'.stdout');stderr=out/(tag+'.stderr');stdout.write_text(r.stdout);stderr.write_text(r.stderr);need(r.returncode==1 and'REQUIRED_LITERAL_INTERFACE_TABLE_MISSING'in r.stderr,'ACTUAL_MISSING_SOURCE_TABLE_FAILS_CLOSED '+tag);records.append({'case':tag,'argv':argv,'cwd':str(missing),'returncode':r.returncode,'wall_seconds':time.monotonic()-st,'stdout':pin(stdout),'stderr':pin(stderr)})
        for source0 in inputs:need(pin(source0['path'])==source0,'ACTUALLY_TESTED_IMMUTABLE_INTERFACE_INPUT_VERSION')
    save('ACTUAL_ALL24_INTERFACE_NORMAL_O_OO_CONTROLS.json',{'status':'PASS_ALL'+str(len(records))+'_ACTUAL_FULL_SOURCE_AND_SEMANTIC_METADATA_CONTROLS','input_pins':inputs,'source':pin(O/'check_interfaces.py'),'controller':pin(__file__),'records':records,'actual_math_or_model_execution':False,'original_source_mutation':False})
    print('PASS'+str(len(records))+'_ACTUAL_NORMAL_O_OO_SOURCE_AND_SEMANTIC_CONTROLS')
if __name__=='__main__':main()
