#!/usr/bin/env python3
"""Exercise the real fresh-v3 resource reader on explicitly synthetic control evidence.

No resource fixture is a production run, mathematical proof or acceptance receipt.
The CLI runs identically under normal Python, -O and -OO.
"""
import argparse,copy,json,subprocess,sys
from pathlib import Path
from types import SimpleNamespace
from reproduce_dual import need,publish,sha,load
import verify_fft_dag_fresh_v3 as gate

HERE=Path(__file__).resolve().parent


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--template',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    a=ap.parse_args();need(not a.out.exists(),'Fresh fixture directory required');a.out.mkdir()
    command=load(a.template);argv=command['command']
    def value(flag):return argv[argv.index(flag)+1]
    root=Path(value('--run'));context=Path(value('--context'));candidate=Path(value('--candidate'))
    p=dict(workers=12)
    r=dict(stages=24,N=16777216,norm_numerator=7813568381279800,
           phase_counts=dict(ORIGINAL_SOURCE_COLD=992,VALIDATED_CONTINUATION_1=4,VALIDATED_NESTED_CONTINUATION_2=35),
           modules=1033,reused_original_source_cold_modules=992,
           reused_prior_continuation_modules=39,freshly_compiled_modules=2)
    cases=['positive','argv-order','argv-duplicate','AS-numeric','worker-count','physical-cap',
           'swap','wrong-unit','OOM-counter','missing-OOM-counter','admission-RAM','admission-disk',
           'admission-scratch','sample-host','sample-scratch','missing-telemetry','source-pin',
           'changed-log','boolean-exitcode']
    rows=[]
    for case in cases:
        work=a.out/case;work.mkdir();cmd=copy.deepcopy(command);plan=copy.deepcopy(p)
        out=work/'stdout';err=work/'stderr';out.write_text('PASS_INTEGER_FFT_NOT_C_PV\n');err.write_text('')
        observation=dict(path='/sys/fs/cgroup/SYNTHETIC_CONTROL_ONLY/fixture.service',
                         **{'memory.max':str(300*2**30),'memory.swap.max':'0',
                            'memory.events':'low 0\nhigh 0\nmax 0\noom 0\noom_kill 0\n'})
        supervisor=dict(status='COMPLETE_CHILD_NOT_MATHEMATICAL_ACCEPTANCE',returncode=0,failure=None,
                        seconds=1.,command=cmd['command'],supervisor_sha256=sha(HERE.parent/'pv/supervise_resource_run.py'),
                        stdout_sha256=sha(out),stderr_sha256=sha(err),before=copy.deepcopy(observation),
                        final=copy.deepcopy(observation),admission=dict(available_RAM_bytes=2**40,
                        free_disk_bytes=2**40,owned_scratch_bytes=1),
                        samples=[dict(available_RAM_bytes=2**40,owned_scratch_bytes=1,
                                      cgroup=dict(observation,**{'memory.current':'1'}))])
        if case=='argv-order':
            i=cmd['command'].index('--candidate');pair=cmd['command'][i:i+2];del cmd['command'][i:i+2];cmd['command'].extend(pair)
        elif case=='argv-duplicate':cmd['command']+=['--workers','12']
        elif case=='AS-numeric':cmd['command'][-1]='300'
        elif case=='worker-count':plan['workers']=11
        elif case=='physical-cap':supervisor['final']['memory.max']=str(301*2**30)
        elif case=='swap':supervisor['final']['memory.swap.max']='1'
        elif case=='wrong-unit':supervisor['final']['path']+='.wrong'
        elif case=='OOM-counter':supervisor['final']['memory.events']=observation['memory.events'].replace('oom 0','oom 1')
        elif case=='missing-OOM-counter':supervisor['final']['memory.events']='low 0\n'
        elif case=='admission-RAM':supervisor['admission']['available_RAM_bytes']=2**40-1
        elif case=='admission-disk':supervisor['admission']['free_disk_bytes']=2**40-1
        elif case=='admission-scratch':supervisor['admission']['owned_scratch_bytes']=270*2**30
        elif case=='sample-host':supervisor['samples'][0]['available_RAM_bytes']=256*2**30-1
        elif case=='sample-scratch':supervisor['samples'][0]['owned_scratch_bytes']=290*2**30
        elif case=='missing-telemetry':supervisor['samples']=[]
        elif case=='source-pin':cmd['source_pins'][0]['sha256']='0'*64
        elif case=='changed-log':out.write_text('arbitrary successful output\n')
        elif case=='boolean-exitcode':supervisor['returncode']=False
        command_file=work/'command.json';command_file.write_text(json.dumps(cmd));supervisor['command_file_sha256']=sha(command_file)
        supervisor_file=work/'supervisor.json';supervisor_file.write_text(json.dumps(supervisor))
        args=SimpleNamespace(run=root,context=context,candidate=candidate,supervisor=supervisor_file,
             command_plan=command_file,stdout=out,stderr=err,unit='fixture.service')
        error=None
        try:gate.verify_resources(args,plan,r)
        except BaseException as e:error=type(e).__name__+': '+str(e)
        need((error is None)==(case=='positive'),'Wrong real-reader outcome for '+case+': '+str(error))
        rows.append(dict(case=case,rejected=error is not None,error=error))
    publish(a.out/'RESULT.json',dict(status='PASS_SYNTHETIC_FRESH_V3_RESOURCE_READER_1_POSITIVE_18_REJECTIONS',
           synthetic_control_evidence_only=True,production_or_mathematical_acceptance=False,
           cases=rows,gate_sha256=sha(Path(gate.__file__)),harness_sha256=sha(Path(__file__)),
           command_template_sha256=sha(a.template)))
    print('PASS synthetic fresh-v3 resource reader: canonical argv and18 negative cases')

if __name__=='__main__':main()
