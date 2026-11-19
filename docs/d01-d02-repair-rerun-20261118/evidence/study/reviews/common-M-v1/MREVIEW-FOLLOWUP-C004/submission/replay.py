from pathlib import Path
import subprocess,sys,time,hashlib
D=Path("/work/c004"); O=Path("/work/submission")
group=sys.argv[1]; P="/usr/bin/python3.10"
jobs={
"prime":[("tables",[P,"-B","tables.py"],None),("compile",["/usr/bin/g++","-O3","-std=c++17","-Wall","-Wextra","sieve.cpp","-o","/work/primes-cert"],None),("sieve",["/work/primes-cert"],"tables.stdout")],
"ram":[("root",[P,"-B","-u","verify.py","root"],None),("gap",[P,"-B","-u","verify.py","gap"],None),("trade",[P,"-B","-u","verify.py","trade"],None)],
"other":[("mcheck",[P,"-B","mcheck.py"],None),("orders",[P,"-B","orders.py","0","6","12","19","25","50"],None)]}
with (O/(group+".receipt")).open("w",encoding="utf8") as rec:
 for name,args,inp in jobs[group]:
  start=time.monotonic()
  print(name,args,"cwd",D,"stdin",inp,file=rec,flush=True)
  src=(O/inp).open("rb") if inp else subprocess.DEVNULL
  with (O/(name+".stdout")).open("wb") as out,(O/(name+".stderr")).open("wb") as err:
   p=subprocess.run(args,cwd=D,stdin=src,stdout=out,stderr=err)
  if inp: src.close()
  print("exit",p.returncode,"seconds",round(time.monotonic()-start,3),file=rec,flush=True)
  for q in [O/(name+".stdout"),O/(name+".stderr")]+([Path("/work/primes-cert")] if name=="compile" and not p.returncode else []):
   print(q.name,hashlib.sha256(q.read_bytes()).hexdigest(),file=rec,flush=True)
  if p.returncode: sys.exit(p.returncode)
