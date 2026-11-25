#!/usr/bin/env python3
"""Source-only kernel proof of the new three-formula scalar comparison."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

PINS = {
    'mathlib':'71a80585ee495fc24472fd0eaffc89d94e4fd8d6',
    'plausible':'d9598f07b1bc701f1e3aae163d2681c1fd978793',
    'LeanSearchClient':'ba67e212be1197b84c1f1f6299488a10a3002713',
    'importGraph':'1681d78dd6e65e38b143f9740d829c826673807c',
    'proofwidgets':'a8acbfd87375ff4abe14ce09db5b7664d383bc7f',
    'aesop':'18889deb9e83ea7420ef51c160d6f88552e744e3',
    'Qq':'507746ab8f4b643ccdacb2ec4cdb5853fa9f8ab3',
    'batteries':'4cac2177c37f5530c4da76aa8e4307f3fc9e4dcb',
}
COMPILER = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
VERSION = 'Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release)'
ROOTS = ['crossing_order','G_le_P₁','P₁_le_P₂','P₂_le_Oline','G_le_Oline',
    'envelope_G','envelope_P₁','envelope_P₂','envelope_O',
    'paper_strictly_smaller_at_old_crossing','continuous_envelope']


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def unique(items):
    result = {}
    for key, value in items:
        need(key not in result, 'Duplicate context key')
        result[key] = value
    return result


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--context', type=Path, required=True)
    parser.add_argument('--run', type=Path, required=True)
    args = parser.parse_args()
    controller = Path(__file__).resolve()
    controller_hash = sha(controller)
    context = json.loads(args.context.read_bytes(), object_pairs_hook=unique,
        parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))
    paths = context['generic_lean_path']
    if isinstance(paths, str):
        paths = paths.split(':')
    need(isinstance(paths, list) and len(paths)==len(PINS) and
        all(isinstance(x,str) and Path(x).is_dir() for x in paths), 'Invalid generic libraries')
    dependencies = context['generic_dependencies']
    need(isinstance(dependencies,list) and len(dependencies)==len(PINS), 'Invalid generic dependency count')
    need(all(isinstance(x,dict) and set(x)=={'name','revision'} for x in dependencies), 'Invalid generic dependency rows')
    names = [x['name'] for x in dependencies]
    need(len(set(names))==len(PINS) and {x['name']:x['revision'] for x in dependencies}==PINS,
        'Generic dependency revisions changed')
    compiler = Path(context['compiler'])
    need(context['compiler_sha256']==COMPILER and sha(compiler)==COMPILER, 'Pinned compiler changed')
    version = subprocess.check_output([str(compiler),'--version'],text=True).strip()
    need(version==VERSION and context['compiler_version'].strip()==VERSION, 'Pinned compiler version changed')
    need(not os.path.lexists(args.run), 'Fresh source-only run required')
    args.run.mkdir(parents=True)
    original = controller.parent/'PopulationCompetitionComparison.lean'
    source = args.run/original.name
    source.write_bytes(original.read_bytes())
    object_path = args.run/'PopulationCompetitionComparison.olean'
    command = ['/usr/bin/time','-v','-o',str(args.run/'run.time'),'prlimit',
        '--as='+str(32*2**30),'--',str(compiler),'-j2','-R',str(args.run),'-o',str(object_path),str(source)]
    plan = {'source_sha256':sha(source),'compiler_sha256':COMPILER,'compiler_version':VERSION,
        'command':command,'context_sha256':sha(args.context),'generic_libraries':paths,
        'generic_dependencies':dependencies,'controller_sha256':controller_hash,
        'application_objects_supplied':False,'source_first_PV':False}
    (args.run/'PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
    start = time.monotonic()
    with (args.run/'stdout').open('wb') as out, (args.run/'stderr').open('wb') as err:
        proc = subprocess.run(command,env=dict(os.environ,LEAN_PATH=':'.join(paths)),stdout=out,stderr=err)
    need(proc.returncode==0, 'Lean failed; exact snapshot/logs retained')
    output = (args.run/'stdout').read_text()
    audits = {}
    for name in ROOTS:
        match = re.search("'RH080.PopulationCompetition."+re.escape(name)+"' depends on axioms: \\[(.*?)\\]", output, re.S)
        need(match is not None, 'Missing theorem axiom audit: '+name)
        axioms = {x.strip() for x in match.group(1).split(',') if x.strip()}
        need(axioms <= {'propext','Classical.choice','Quot.sound'}, 'Unaccepted theorem axiom: '+name)
        audits[name] = sorted(axioms)
    need(sha(original)==sha(source)==plan['source_sha256'], 'Source changed during run')
    need(sha(compiler)==COMPILER and sha(controller)==controller_hash, 'Compiler/controller changed during run')
    times = (args.run/'run.time').read_text()
    rss = re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',times)
    need(rss is not None, 'Missing actual peak RAM')
    result = {'status':'PASS_KERNEL_THREE_FORMULA_COMPARISON','seconds':time.monotonic()-start,
        'maximum_rss_kib':int(rss.group(1)),'exit_code':proc.returncode,'signal_kill':False,
        'source_sha256':sha(source),'object_sha256':sha(object_path),'stdout_sha256':sha(args.run/'stdout'),
        'stderr_sha256':sha(args.run/'stderr'),'time_sha256':sha(args.run/'run.time'),
        'plan_sha256':sha(args.run/'PLAN.json'),'axiom_audits':audits,'source_first_PV':False,
        'scope':'Exact scalar formulas, continuous envelope and original-crossing ordering only. No ANT transfer, onset claim, PV or optimality.'}
    temporary = args.run/'RESULT.json.tmp'
    temporary.write_text(json.dumps(result,indent=2)+'\n')
    os.link(temporary,args.run/'RESULT.json');temporary.unlink()
    print(json.dumps({k:result[k] for k in ['status','seconds','maximum_rss_kib']}))


if __name__=='__main__':
    main()
