#!/usr/bin/env python3
"""Validate fixed_add cold evidence and execute wrong-source numerical controls."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def atomic(path, value):
    need(not path.exists(), 'fresh final receipt required')
    tmp = path.with_name('.'+path.name+'.tmp')
    with tmp.open('x') as f:
        json.dump(value, f, indent=2, allow_nan=False)
        f.write('\n')
        f.flush()
        os.fsync(f.fileno())
    try:
        os.link(tmp, path)
    finally:
        tmp.unlink()


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False, description=__doc__)
    parser.add_argument('--context', type=Path, required=True)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--cc', default='cc')
    args = parser.parse_args()
    need(not args.out.exists(), 'fresh experiment-owned validation directory required')
    run = args.run.resolve(strict=True)
    candidate_path = run/'RESULT.json'
    candidate_hash = sha(candidate_path)
    candidate = json.loads(candidate_path.read_text())
    need(candidate['status']=='PASS_FIXED_ADD_SOURCE_EXECUTION_INTEGER_CONTRACT_ONLY', 'candidate did not finish')
    need(candidate['source_first_PV_complete'] is False and candidate['final_ANT_connection_pending'] is True,
         'helper contract must remain distinct from the final ANT connection')
    bank = run/'lean'
    plan = json.loads((bank/'PLAN.json').read_text())
    need(plan['context_sha256']==sha(args.context), 'different pinned dependency context')
    need(plan['application_object_fallback'] is False, 'application-object fallback forbidden')
    need(plan['roots']==['ExplicitFFTAddAudit'], 'different selected theorem/audit roots')
    proof_receipt = bank/'RESULT.json'
    need(sha(proof_receipt)==candidate['proof_receipt_sha256'], 'changed source-cold root receipt')
    proof = json.loads(proof_receipt.read_text())
    need(proof['status']=='PASS_SOURCE_COLD_SELECTED_MODULE_COMPILATION_ONLY' and
         proof['roots']==['ExplicitFFTAddAudit'] and proof['modules']==109,
         'source-cold root does not match selected complete closure')
    need(plan['controller_sha256']==candidate['proof_controller_sha256'], 'different proof controller identity')
    rows = plan['source_rows']
    need(len(rows)==109 and candidate['modules']==109, 'different pinned source closure')
    need(len({row['module'] for row in rows})==len(rows), 'collapsed compiler identities')
    need(len({(row['origin'],row['module']) for row in rows})==len(rows), 'collapsed written source identities')
    context = json.loads(args.context.read_text())
    need(sha(Path(context['compiler']))==context['compiler_sha256'], 'pinned Lean compiler changed')
    module_receipts = []
    peak = 0
    for row in rows:
        name = row['module']
        receipt_path = bank/(name+'.COMPILED.json')
        receipt = json.loads(receipt_path.read_text())
        need(receipt['module']==name and receipt['exitcode']==0, 'failed child compiler '+name)
        command = receipt['command']
        expected_obj = bank/'objects'/(name.replace('.','/')+'.olean')
        compiler_position = command.index(context['compiler']) if context['compiler'] in command else -1
        need(command.count(context['compiler'])==1 and compiler_position>=0 and
             command[compiler_position:]==[context['compiler'],'-j2','--root='+str(bank/'source'),
                 '-o',str(expected_obj),row['snapshot']],
             'child compiler command/source/object route changed '+name)
        need(sha(Path(row['origin']))==row['source_sha256'] and
             sha(Path(row['snapshot']))==row['source_sha256'], 'source snapshot changed '+name)
        obj = bank/'objects'/(name.replace('.','/')+'.olean')
        need(obj.is_file() and sha(obj)==receipt['object_sha256'], 'missing or changed proof object '+name)
        output = bank/'logs'/(name+'.stdout')
        error = bank/'logs'/(name+'.stderr')
        timing = bank/'logs'/(name+'.time')
        need(sha(output)==receipt['stdout_sha256'] and sha(error)==receipt['stderr_sha256'] and
             sha(timing)==receipt['time_sha256'], 'changed compiler evidence '+name)
        diagnostics = output.read_text()+error.read_text()
        need(not any(marker in diagnostics for marker in ['PANIC','error:','sorryAx']),
             'unclean compiler output even if exit code was zero '+name)
        rss = re.findall(r'Maximum resident set size \(kbytes\): (\d+)', timing.read_text())
        need(len(rss)==1, 'missing exact resource usage '+name)
        peak = max(peak, int(rss[0]))
        module_receipts.append(dict(module=name,receipt_sha256=sha(receipt_path),
                                    source_sha256=row['source_sha256'],object_sha256=sha(obj)))
    audit = (bank/'logs/ExplicitFFTAddAudit.stdout').read_text()
    marker = ('FFT_ADD_SOURCE_AUDIT_PASS four-actual-C-files independently-parsed full-Call all-executions '
              'all-argument-orders signed-integer-add-sub alias-safe no-wrap temporary-lifetimes caller-frame '
              'Std3 final-ANT-connection-pending')
    need(audit.count(marker)==1 and audit.count('FFT_ADD_SOURCE_AXIOMS ')==4, 'incomplete source/signed-math audit')
    compiler = shutil.which(args.cc)
    need(compiler is not None and sha(Path(compiler))==candidate['C_compiler_sha256'], 'native compiler differs')
    associations = candidate['associations']
    native = candidate['native_smoke_tests']
    need(len(associations)==4 and len(native)==4 and all(item['cases']==264 for item in native), 'native routes missing')
    need(len({item['C_origin'] for item in associations})==4, 'duplicate concrete source route')
    need(candidate['random_seed']==0x080A55, 'different locked native seed')
    concrete_names = ['w4_fft.c','fap_fft.c','w4_fft_recursive.c','fap_fft_recursive.c']
    need([Path(item['C_snapshot']).name for item in associations]==concrete_names and
         [item['source'] for item in native]==concrete_names, 'native source routes reordered or replaced')
    native_rechecks = []
    for item, observation in zip(associations,native):
        concrete = Path(item['C_snapshot']).name
        need(sha(run/'native'/(concrete+'.harness.c'))==observation['harness_sha256'] and
             sha(run/'native'/(concrete+'.test'))==observation['executable_sha256'] and
             sha(run/'native'/(concrete+'.run.stdout'))==observation['output_sha256'],
             'native baseline/harness/executable changed '+concrete)
        need((run/'native'/(concrete+'.run.stderr')).read_text()=='', 'native baseline stderr '+concrete)
        replay = subprocess.run([str(run/'native'/(concrete+'.test'))],capture_output=True,text=True)
        need(replay.returncode==0 and replay.stderr=='' and
             hashlib.sha256(replay.stdout.encode()).hexdigest()==observation['output_sha256'],
             'native baseline actual rerun changed '+concrete)
        native_rechecks.append(dict(source=concrete,command=[str(run/'native'/(concrete+'.test'))],returncode=replay.returncode,
            executable_sha256=observation['executable_sha256'],output_sha256=observation['output_sha256']))
        formal_text = Path(item['formal_origin']).read_text()
        encoded = re.search(r'^def sourceChars[^\n]*\[(.*?)\]\s*$',formal_text,re.M)
        need(encoded is not None, 'formal sourceChars absent '+concrete)
        chars = encoded.group(1).split(', ')
        need(all(re.fullmatch(r'Char\.ofNat \d+', c) for c in chars), 'unsupported sourceChars '+concrete)
        need(''.join(chr(int(c[11:])) for c in chars).encode()==Path(item['C_snapshot']).read_bytes(),
             'formal-string/concrete-source association changed '+concrete)
        need(sha(Path(item['C_origin']))==item['C_sha256'] and sha(Path(item['C_snapshot']))==item['C_sha256'] and
             sha(Path(item['formal_origin']))==item['formal_sha256'], 'source association changed')
    args.out.mkdir(parents=True)
    mutation_root = args.out/'mutations'
    mutation_root.mkdir()
    began = time.monotonic()
    controls = []
    replacements = [
        ('wrong_add_modulus','out[j]=(t%1000000000ULL);','out[j]=(t%999999999ULL);'),
        ('reversed_comparison','magnitude_compare(a,b)','magnitude_compare(b,a)'),
        ('skipped_canonical_zero','canonical_sign(out);','/* deliberate numerical mutation: omitted canonicalization */'),
        ('inverted_subtract_flag','if(subtract>0ULL)','if(subtract==0ULL)'),
    ]
    for association in associations:
        concrete = Path(association['C_snapshot']).name
        original = Path(association['C_snapshot']).read_text()
        expected = (run/'native'/(concrete+'.run.stdout')).read_text()
        harness_source = (run/'native'/(concrete+'.harness.c')).read_text()
        need(len(expected.splitlines())==264, 'incomplete baseline native observations')
        start = original.index('uint64_t fixed_add(')
        finish = original.index('\nuint64_t ', start+10)
        body = original[start:finish]
        for label, old, new in replacements:
            need(old in body, 'mutation target absent '+concrete+'/'+label)
            changed_body = body.replace(old,new,1)
            changed = original[:start]+changed_body+original[finish:]
            fixture = mutation_root/(concrete+'-'+label)
            fixture.mkdir()
            source = fixture/concrete
            source.write_text(changed)
            harness = fixture/'harness.c'
            harness.write_text(harness_source)
            exe = fixture/'test'
            command = [compiler,'-std=c11','-O2','-Wall','-Wextra',str(harness),'-o',str(exe)]
            built = subprocess.run(command,capture_output=True,text=True)
            (fixture/'compile.stdout').write_text(built.stdout)
            (fixture/'compile.stderr').write_text(built.stderr)
            need(built.returncode==0, 'wrong-source control did not compile '+label)
            observed = subprocess.run([str(exe)],capture_output=True,text=True)
            (fixture/'run.stdout').write_text(observed.stdout)
            (fixture/'run.stderr').write_text(observed.stderr)
            need(observed.returncode==0 and observed.stderr=='', 'control failed as an execution/resource event '+label)
            need(observed.stdout!=expected, 'deliberately wrong numerical source was not distinguished '+label)
            expected_lines = expected.splitlines()
            actual_lines = observed.stdout.splitlines()
            need(len(actual_lines)==len(expected_lines), 'wrong-source control changed output protocol '+label)
            mismatches = [i for i,(a,b) in enumerate(zip(expected_lines,actual_lines)) if a!=b]
            need(mismatches, 'no numerical mismatch '+label)
            controls.append(dict(source=concrete,mutation=label,old_fragment=old,new_fragment=new,
                original_source_sha256=association['C_sha256'],mutated_source_sha256=sha(source),
                byte_source_association_distinguishes=sha(source)!=association['C_sha256'],
                command=command,executable_sha256=sha(exe),harness_sha256=sha(harness),exitcode=observed.returncode,
                output_sha256=hashlib.sha256(observed.stdout.encode()).hexdigest(),
                mismatch_cases=len(mismatches),first_mismatch_case=mismatches[0],
                expected_first=expected_lines[mismatches[0]],observed_first=actual_lines[mismatches[0]]))
            # These fixture copies/executables are deterministically regenerated
            # from the preserved original source and the exact recipe above.
            for temporary in [source,harness,exe]:
                need(temporary.resolve().is_relative_to(mutation_root.resolve()) and not temporary.is_symlink(),
                     'cleanup escaped experiment-owned temporary directory')
                temporary.unlink()
    need(len(controls)==16 and all(item['byte_source_association_distinguishes'] for item in controls),
         'not all concrete mutation routes completed')
    need(sha(candidate_path)==candidate_hash, 'primary receipt changed during independent validation')
    atomic(args.out/'RESULT.json',dict(status='PASS_FIXED_ADD_SOURCE_CONTRACT_AND_NATIVE_MUTATION_CONTROLS',
        source_to_AST_execution_correctness_contract_complete=True,source_first_PV_complete=False,
        final_ANT_connection_pending=True,primary_receipt=str(candidate_path),primary_receipt_sha256=candidate_hash,
        validator_sha256=sha(Path(__file__)),context_sha256=sha(args.context),modules=module_receipts,
        mutation_controls=controls,mutations=16,native_actual_rechecks=native_rechecks,peak_Lean_rss_kib=peak,oom_events=0,
        seconds=time.monotonic()-began,scope='Standalone source contract, not the final ANT connection; wrong-source native tests supplement the consumed general Lean proof.',
        cleanup='Removed only generated mutant C copies, harness copies and executables after observing numerical mismatches. Original sources, source-cold snapshots, accepted proof artifacts, hashes and concise control observations retained.'))
    print('PASS fixed_add source contract, strict compiler evidence and 16 native mutation controls; final ANT connection pending')


if __name__=='__main__':
    main()
