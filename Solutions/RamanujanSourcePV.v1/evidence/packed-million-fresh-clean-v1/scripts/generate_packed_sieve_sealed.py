#!/usr/bin/env python3
"""Regenerate untrusted packed-sieve proposals; Lean kernel proofs accept them.
No generated literal is mathematical evidence until packed_bits compiles.
"""
from pathlib import Path
import argparse, hashlib, json, math, platform, sys, time

def sha(data):
    return hashlib.sha256(data).hexdigest()

def generate(out):
    if out.exists():
        raise ValueError("Output must be a fresh experiment-owned directory")
    source = out / "source" / "RamanujanPV"
    source.mkdir(parents=True)
    records = []
    started = time.monotonic()
    for tag, lo, width in [("Million",38358837684,1000000),("QWindow",14111427771,367880)]:
        hi = lo + width - 1
        r = math.isqrt(hi)
        base = bytearray(b"\1") * (r+1)
        base[:2] = b"\0\0"
        for p in range(2,math.isqrt(r)+1):
            if base[p]:
                base[p*p:r+1:p] = b"\0" * (((r-p*p)//p)+1)
        flags = bytearray(b"\1") * width
        for p in range(2,r+1):
            if not base[p]:
                continue
            first = max(p*p,((lo+p-1)//p)*p)
            if first <= hi:
                flags[first-lo:width:p] = b"\0" * (((hi-first)//p)+1)
        packed = bytearray((width+7)//8)
        for i, flag in enumerate(flags):
            if flag:
                packed[i//8] |= 1 << (i%8)
        literal = hex(int.from_bytes(packed,"little"))
        expected = sum(flags)
        module = "RamanujanPV.PackedSieveSealed" + tag
        body = f"""import RamanujanPV.PackedSieveByteTail
namespace RamanujanPV.PackedSieveSealed{tag}
open PackedSieveKernel PackedSieveByteCount PackedSieveByteTail
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def bits : Nat := {literal}
theorem packed_bits : primeBits {lo} {width} = bits := by decide +kernel
theorem raw_byte_result : byteCount {((width+7)//8)} (primeBits {lo} {width}) = {expected} := by
  rw [packed_bits, ←byteCountFast_eq]
  decide +kernel
#print axioms packed_bits
#print axioms raw_byte_result
end RamanujanPV.PackedSieveSealed{tag}
"""
        path = source / (module.split(".")[-1]+".lean")
        path.write_text(body)
        records.append(dict(module=module,lo=lo,width=width,expected_count=expected,
            flags_sha256=sha(flags),packed_bytes_sha256=sha(packed),
            source_sha256=sha(path.read_bytes()),source_bytes=len(path.read_bytes())))
    receipt = dict(status="UNTRUSTED_PROPOSAL_UNTIL_BOTH_KERNEL_THEOREMS_COMPILE",
        algorithm="exactsameprimeBits;onekernelbitmaskidentitythenprovedtailbytecount",
        records=records,generator_sha256=sha(Path(__file__).read_bytes()),
        python=platform.python_version(),python_executable=sys.executable,
        random_seed=None,seconds=time.monotonic()-started)
    (out/"PROPOSAL.json").write_text(json.dumps(receipt,indent=2)+"\n")
    return receipt

if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out",type=Path,required=True)
    args=parser.parse_args()
    result=generate(args.out.resolve())
    print(json.dumps(dict(status=result["status"],records=result["records"])))
