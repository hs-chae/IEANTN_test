#!/usr/bin/env python3
"""Actual normal/-O/-OO acceptance controls; does not mutate source evidence."""
from pathlib import Path
import argparse,copy,json,subprocess,sys
from execute_full_scalar_certificate import read,need,sha
S=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--result',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();baseline=read(a.result);need(not a.out.exists(),'fresh control directory');a.out.mkdir(parents=True);tests=[];modes=[[],['-O'],['-OO']];script=S/'scripts/execute_full_source_rows.py'
 def run(mode,label,path,success):
  result=subprocess.run([sys.executable,*mode,str(script),'--check',str(path)],capture_output=True,text=True);need((result.returncode==0)==success,'actual CLI control '+label+' '+str(mode));tests.append(dict(mode=mode,label=label,returncode=result.returncode,expected_success=success,stdout=result.stdout,stderr=result.stderr))
 def changed(name,edit):
  d=copy.deepcopy(baseline);edit(d);path=a.out/(name+'.json');path.write_text(json.dumps(d,indent=2)+'\n');return name,path
 cases=[changed('wrong_rows',lambda d:d.update(rows=d['rows']-1)),changed('wrong_margin',lambda d:d.update(retained_integer_margin=9006)),changed('promoted_counts',lambda d:d.update(prime_counts_formally_proved_here=True)),changed('omitted_source_PV',lambda d:d.update(source_first_scalar_PV=False)),changed('promoted_ANT',lambda d:d.update(complete_ANT_result=True)),changed('omitted_record',lambda d:d['records'].pop()),changed('omitted_axiom_population',lambda d:d['records'][0].update(required_constants=[])),changed('wrong_object',lambda d:d['records'][0].update(object=str(a.result))),changed('wrong_memory_cap',lambda d:d['records'][0].update(memory_limit_bytes=123)),changed('wrong_affinity',lambda d:d['records'][0].update(affinity=[9999])),changed('wrong_compiler',lambda d:d.update(compiler_sha256='0'*64)),changed('wrong_original_type_target',lambda d:d['independent_audit'].update(expected_rows='[]')),changed('over_budget',lambda d:d.update(combined_worker_limit_bytes=301*1024**3)),changed('wrong_full_scope',lambda d:d.update(full_locked_prefix=not d['full_locked_prefix']))]
 duplicate=a.out/'duplicate.json';duplicate.write_text(a.result.read_text().replace('{','{"rows":1,',1));cases.append(('duplicate_key',duplicate));nonfinite=a.out/'nonfinite.json';nonfinite.write_text(a.result.read_text().replace('{','{"extra":NaN,',1));cases.append(('nonfinite',nonfinite))
 for mode in modes:
  run(mode,'positive',a.result,True)
  for label,path in cases:run(mode,label,path,False)
 result=dict(status='ALL_ACTUAL_SOURCE_SCALAR_CLI_CONTROLS_PASS',tests=tests,script=str(script),script_sha256=sha(script),baseline_result_sha256=sha(a.result));tmp=a.out/'RESULT.pending';tmp.write_text(json.dumps(result,indent=2)+'\n');tmp.replace(a.out/'RESULT.json');print(json.dumps({'status':result['status'],'positive':3,'negative':3*len(cases)}))
if __name__=='__main__':main()
