import os, sys, re, subprocess
from pathlib import Path
roots = [Path(s) for s in os.environ["LEAN_PATH"].split(":")]
out=roots[0]
srcs=[Path("/ieantn")]+[Path(x) for x in sys.argv[2:]]
def deps(p):
 return re.findall(r"^(?:(?:public|meta|private) )?import ([^\s]+)",p.read_text(),re.M)
def build(m):
 stem=m.replace(".","/")
 if any((d/(stem+".olean")).is_file() for d in roots): return
 matches=[(src,src/(stem+".lean")) for src in srcs if (src/(stem+".lean")).is_file()]
 if not matches: raise FileNotFoundError(m)
 src,p=matches[0]
 for dep in deps(p): build(dep)
 o=out/(stem+".olean");o.parent.mkdir(parents=True,exist_ok=True)
 print(m,flush=True)
 subprocess.run(["/opt/lean/bin/lean","--root=/ieantn","-o",str(o),str(p)],check=True)
for mod in deps(Path(sys.argv[1])): build(mod)
