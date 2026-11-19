"""Build and replay the integer bridge in /work, after verify.py --endpoint."""
import subprocess
from pathlib import Path
from verify import I
from decimal import ROUND_CEILING
def main():
    path=Path(__file__).resolve().parent
    start,end,step=38358837683,100000000000,1000000
    scale=10**16
    el=27182818284590452
    e=I(1).exp()
    assert (I(el)/scale).b<e.a and e.b<(I(el+1)/scale).a
    assert int((I(start)/e).a)==int((I(start)/e).b)==14111427770
    subprocess.run(['/usr/bin/gcc','-std=c11','-O3',str(path/'bridge.c'),'-o','/work/bridge'],check=True)
    with open('/work/bridge.logs','w') as f:
        for n in range(start,end+1,step):
            f.write(str((I(n).log()*scale).b.to_integral_value(rounding=ROUND_CEILING))+'\n')
    with open('/work/bridge.logs','r') as f:
        subprocess.run(['/work/bridge'],stdin=f,check=True)
if __name__=='__main__': main()
