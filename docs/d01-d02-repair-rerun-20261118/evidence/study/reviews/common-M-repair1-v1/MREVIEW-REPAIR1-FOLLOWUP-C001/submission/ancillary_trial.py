from pathlib import Path
import subprocess as sp, hashlib, json
s=Path('/task/CANDIDATE_011.cpp').read_text()
a=s.index('Test ts[]=')
b=s.index('I log1000i',a)
src=Path('/work/review_weighted_trial.cpp')
src.write_text(s[:a]+'Test ts[]={{16000000000,0,100}};\n'+s[b:])
print('original sha256',hashlib.sha256(Path('/task/CANDIDATE_011.cpp').read_bytes()).hexdigest())
print('trial sha256',hashlib.sha256(src.read_bytes()).hexdigest())
for argv in [['/usr/bin/g++','-std=c++17','-O3',str(src),'-o','/work/review_weighted_trial'],['/work/review_weighted_trial']]:
    r=sp.run(argv,capture_output=True)
    print(json.dumps(dict(argv=argv,status=r.returncode,stdout=r.stdout.decode(),stderr=r.stderr.decode(),stdout_sha256=hashlib.sha256(r.stdout).hexdigest())))
    r.check_returncode()
