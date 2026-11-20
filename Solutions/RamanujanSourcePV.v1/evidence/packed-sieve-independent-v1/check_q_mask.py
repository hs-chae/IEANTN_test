from pathlib import Path
import hashlib,json,math,re,sys,time
D=Path('/data/ivy-ramanujan-source-pv-20261119/packed-sieve-independent-audit-v1');p=Path('/data/ivy-ramanujan-source-pv-20261119/packed-sieve-primitive-v1/source/RamanujanPV/PackedSievePrimitiveQWindow.lean');text=p.read_text();literal=re.search(r'def bits : Nat := 0x([0-9a-fA-F]+)',text)
if literal is None:raise ValueError('exactgroundbitliteral')
lo=14111427771;count=367880;hi=lo+count-1;t=time.monotonic();r=math.isqrt(hi);base=bytearray(b'\1')*(r+1);base[:2]=b'\0\0'
for d in range(2,math.isqrt(r)+1):
 if base[d]:base[d*d:r+1:d]=b'\0'*((r-d*d)//d+1)
flags=bytearray(b'\1')*count
for d in range(2,r+1):
 if base[d]:
  first=max(d*d,((lo+d-1)//d)*d)
  if first<=hi:flags[first-lo:count:d]=b'\0'*((hi-first)//d+1)
packed=bytearray((count+7)//8)
for i,v in enumerate(flags):
 if v:packed[i//8]|=1<<(i%8)
actual=int.from_bytes(packed,'little');expected=int(literal[1],16)
if actual!=expected or sum(flags)!=15972:raise ValueError('fullQevery-bit/countmismatch')
result=dict(status='PASS_SUPPLEMENTAL_INDEPENDENT_EVERY_Q_BIT_NATIVE_SIEVE_NOT_FORMAL_PV',lo=lo,count=count,hi=hi,prime_count_increment=sum(flags),all_bits_match=True,source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),packed_bytes_sha256=hashlib.sha256(packed).hexdigest(),seconds=time.monotonic()-t,python=sys.version,qualification='IndependentordinaryPythonEratosthenesreadbackonly; theacceptedLeanmasktheoremandgenericsourceproofareseparate. NoP-millionornativepackedCverificationclaim.')
(D/'Q_NATIVE_EVERY_BIT_READBACK.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
