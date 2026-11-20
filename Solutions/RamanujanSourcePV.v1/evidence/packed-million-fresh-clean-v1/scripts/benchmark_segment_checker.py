#!/usr/bin/env python3
"""Execute the actual segmented C checker against independent native data.

This is ordinary numerical differential evidence, not an accepted Lean source
execution proof. Input words are streamed through stdout and hashed in memory;
large prime lists/flag arrays are not left on disk. The untrusted primesieve
proposal and two separately source-proved quotient-counter calls are compared.
"""
from pathlib import Path
import argparse
import hashlib
import json
import math
import os
import re
import shutil
import struct
import subprocess
import sys
import time

S = Path(__file__).resolve().parents[1]
PIN = '9eb78bc0d1c98129f464db287699532376f52950'
DRIVER = r'''#include <primesieve.hpp>
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <iostream>
#include <stdexcept>
#include <vector>
extern "C" uint64_t rpc_check_segment(uint64_t,uint64_t,uint64_t,uint64_t*,uint64_t*);
extern "C" uint64_t rpc_quotient_count(uint64_t,uint64_t,uint64_t*,uint64_t*);
static uint64_t small[1500000],large[1500000];
int main(int argc,char**argv){try{
 if(argc!=3)throw std::runtime_error("lo hi required");
 const uint64_t lo=std::stoull(argv[1]),hi=std::stoull(argv[2]);
 if(lo<2||hi<lo||hi>2000000000000ULL||hi-lo>16777216ULL)throw std::runtime_error("domain");
 const uint64_t length=hi-lo+1;
 std::vector<uint64_t> primes,claims(length,0),flags(length,19);
 primesieve::generate_primes(lo,hi,&primes);
 for(uint64_t p:primes)claims[p-lo]=1;
 auto begin=std::chrono::steady_clock::now();
 const uint64_t result=rpc_check_segment(lo,hi,length,claims.data(),flags.data());
 const double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count();
 if(result!=primes.size()+1)throw std::runtime_error("checker count mismatch");
 const uint64_t before=rpc_quotient_count(lo-1,1500000,small,large);
 const uint64_t after=rpc_quotient_count(hi,1500000,small,large);
 if(after<before||after-before!=result-1)throw std::runtime_error("independent quotient difference mismatch");
 claims[length/2]=1-claims[length/2];
 if(rpc_check_segment(lo,hi,length,claims.data(),flags.data())!=0)throw std::runtime_error("mutation accepted");
 claims[length/2]=1-claims[length/2];
 if(rpc_check_segment(lo,hi,length-1,claims.data(),flags.data())!=0)throw std::runtime_error("capacity accepted");
 if(std::fwrite(&length,8,1,stdout)!=1||std::fwrite(claims.data(),8,length,stdout)!=length)throw std::runtime_error("input byte stream");
 std::cout<<"{\"lo\":"<<lo<<",\"hi\":"<<hi<<",\"length\":"<<length
  <<",\"prime_count\":"<<result-1<<",\"counter_before\":"<<before<<",\"counter_after\":"<<after
  <<",\"native_checker_seconds\":"<<seconds<<",\"mutation_rejected\":true,\"capacity_rejected\":true}\n";
 if(std::fflush(stdout)!=0)throw std::runtime_error("flush");
 return 0;
}catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}
'''


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def strict_json(data):
    def pairs(values):
        result = {}
        for key, value in values:
            need(key not in result, 'duplicate native summary key')
            result[key] = value
        return result
    def finite(value):
        result = float(value)
        need(math.isfinite(result), 'nonfinite native summary number')
        return result
    def constant(value):
        raise ValueError('invalid native summary constant ' + value)
    return json.loads(data, object_pairs_hook=pairs, parse_float=finite, parse_constant=constant)


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--scratch', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--cpu', type=int, default=9)
    parser.add_argument('--case', type=int, nargs=2, action='append', metavar=('LO', 'HI'))
    args = parser.parse_args()
    out = args.out.resolve()
    need(not out.exists(), 'fresh experiment output required')
    need(sys.byteorder == 'little', 'explicit little-endian native ABI')
    need(args.cpu in os.sched_getaffinity(0), 'actual selected CPU')
    vendor = args.scratch / 'vendor' / 'primecount'
    library = args.scratch / 'primecount-build' / 'lib' / 'primesieve' / 'libprimesieve.a'
    need(subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=vendor, text=True).strip() == PIN,
         'pinned untrusted numerical proposal dependency')
    need(not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'],
         cwd=vendor, text=True), 'tracked numerical dependency changed')
    need(library.is_file(), 'build pinned native dependency using reproduce_numerics.py')
    cc = Path(shutil.which('cc')).resolve()
    cxx = Path(shutil.which('g++')).resolve()
    out.mkdir(parents=True)
    source = out / 'driver.cpp'
    source.write_text(DRIVER)
    commands = []
    for name in ['verified_segment_checker', 'verified_quotient_count']:
        command = [str(cc), '-std=c11', '-O3', '-c', str(S / 'c' / (name + '.c')),
                   '-o', str(out / (name + '.o'))]
        run = subprocess.run(command, capture_output=True, check=False)
        (out / (name + '.compile-stdout')).write_bytes(run.stdout)
        (out / (name + '.compile-stderr')).write_bytes(run.stderr)
        need(run.returncode == 0, 'actual C source failed compilation')
        commands.append(command)
    executable = out / 'segment-checker'
    command = [str(cxx), '-std=c++17', '-O3', '-I' + str(vendor / 'lib/primesieve/include'),
               str(source), str(out / 'verified_segment_checker.o'), str(out / 'verified_quotient_count.o'),
               str(library), '-lpthread', '-o', str(executable)]
    build = subprocess.run(command, capture_output=True, check=False)
    (out / 'link-stdout').write_bytes(build.stdout)
    (out / 'link-stderr').write_bytes(build.stderr)
    need(build.returncode == 0, 'native link failed')
    commands.append(command)
    cases = args.case or [(2, 1000001), (38358837683, 38358837683 + 1048575),
                          (1490000000000 - 1048575, 1490000000000)]
    for lo, hi in cases:
        need(2 <= lo <= hi <= 2000000000000 and hi-lo <= 16777216,
             'exact native driver domain and bounded input stream')
    records = []
    for index, (lo, hi) in enumerate(cases):
        case = out / str(index)
        case.mkdir()
        command = ['/usr/bin/time', '-v', '-o', str(case / 'rusage'),
                   '/usr/bin/prlimit', '--as=' + str(24 << 30), '--',
                   '/usr/bin/taskset', '-c', str(args.cpu), str(executable), str(lo), str(hi)]
        started = time.monotonic()
        run = subprocess.run(command, capture_output=True, check=False)
        (case / 'stderr').write_bytes(run.stderr)
        need(run.returncode == 0, 'native differential check failed; evidence preserved')
        need(len(run.stdout) >= 8, 'missing binary input framing')
        length = struct.unpack('<Q', run.stdout[:8])[0]
        need(length == hi-lo+1, 'exact input word count')
        end = 8 + 8*length
        need(len(run.stdout) > end, 'missing exact binary input or summary')
        data = run.stdout[8:end]
        result = strict_json(run.stdout[end:].decode('ascii'))
        for field in ['lo', 'hi', 'length', 'prime_count', 'counter_before', 'counter_after']:
            need(type(result[field]) is int and result[field] >= 0, 'strict native integer ' + field)
        need(type(result['native_checker_seconds']) in [int, float]
             and math.isfinite(result['native_checker_seconds'])
             and result['native_checker_seconds'] >= 0, 'finite nonnegative execution time')
        need(result['lo'] == lo and result['hi'] == hi and result['length'] == length, 'case identity')
        need(result['mutation_rejected'] is True and result['capacity_rejected'] is True, 'negative checks')
        need(result['counter_after']-result['counter_before'] == result['prime_count'], 'independent exact difference')
        peak = re.search(r'Maximum resident set size \(kbytes\): (\d+)', (case / 'rusage').read_text())
        need(peak is not None, 'actual peak RAM receipt')
        result.update(command=command, elapsed_seconds=time.monotonic()-started,
                      peak_rss_bytes=int(peak.group(1))*1024,
                      input_word_bytes=len(data), input_sha256=hashlib.sha256(data).hexdigest(),
                      complete_stdout_sha256=hashlib.sha256(run.stdout).hexdigest(),
                      rusage_sha256=sha(case / 'rusage'))
        (case / 'RESULT.json').write_text(json.dumps(result, indent=2) + '\n')
        records.append(result)
    receipt = {'status': 'ORDINARY_NATIVE_SEGMENT_CHECKER_DIFFERENTIAL_RUNS_PASS',
               'source_first_PV_complete': False,
               'remaining': 'This numerical receipt alone does not prove source execution, caller initialization, or physical source/build/run association; those are separate obligations.',
               'parameters': cases, 'random_seed': None, 'records': records,
               'c_checker_source_sha256': sha(S / 'c/verified_segment_checker.c'),
               'quotient_source_sha256': sha(S / 'c/verified_quotient_count.c'),
               'driver_source_sha256': sha(source), 'script_sha256': sha(Path(__file__)),
               'compiler_sha256': sha(cc), 'cxx_sha256': sha(cxx),
               'executable_sha256': sha(executable), 'build_commands': commands,
               'untrusted_proposal_dependency_commit': PIN,
               'untrusted_primesieve_library_sha256': sha(library),
               'large_generated_input_files_stored': False}
    (out / 'RESULT.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'status': receipt['status'], 'counts': [r['prime_count'] for r in records],
                      'checker_seconds': [r['native_checker_seconds'] for r in records]}))


if __name__ == '__main__':
    main()
