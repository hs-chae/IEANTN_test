from pathlib import Path
import tempfile, hashlib, json, subprocess as sp
c=Path("/work/c")
src=c/"prior_check.py"
for args,receipt in [([], "gap_evidence.txt"),(["--basic"],"gap_basic_evidence.txt")]:
    argv=["/usr/bin/python3.10",str(src),*args]
    r=sp.run(argv,cwd=c,capture_output=True)
    print(json.dumps(dict(argv=argv,status=r.returncode,stdout=r.stdout.decode(),stderr=r.stderr.decode(),sha256=hashlib.sha256(r.stdout).hexdigest(),match=r.stdout==(c/receipt).read_bytes())))
    r.check_returncode()
