#!/usr/bin/env python3
"""Generate the proved primitive-equivalent variant of the fixed packed masks."""
from pathlib import Path
import argparse, hashlib, json, re
from generate_packed_sieve_sealed import generate

def sha(data):
    return hashlib.sha256(data).hexdigest()

def primitive_proposal(out, mask_only=False):
    original=generate(out)
    records=[]
    for row in original["records"]:
        old_module=row["module"]
        new_module=old_module.replace("PackedSieveSealed","PackedSievePrimitive")
        source=out/"source"/Path(*old_module.split(".")).with_suffix(".lean")
        body=source.read_text().replace(
            "import RamanujanPV.PackedSieveByteTail",
            "import RamanujanPV.PackedSieveByteTail\nimport RamanujanPV.PackedSievePrimitiveBits").replace(
            old_module.split(".")[-1],new_module.split(".")[-1])
        pattern=r"theorem packed_bits : primeBits (\d+) (\d+) = bits := by decide \+kernel"
        match=re.search(pattern,body)
        if match is None:
            raise ValueError("Exact original theorem template absent")
        lo,count=map(int,match.groups())
        replacement=f"""theorem primitive_bits : PackedSievePrimitiveBits.primitiveBits {lo} {count} = bits := by decide +kernel
theorem packed_bits : primeBits {lo} {count} = bits :=
  (PackedSievePrimitiveBits.primitiveBits_eq {lo} {count}).symm.trans primitive_bits"""
        body=re.sub(pattern,lambda _:replacement,body)
        body=body.replace("#print axioms packed_bits","#print axioms primitive_bits\n#print axioms packed_bits")
        if mask_only and new_module.endswith("Million"):
            masked_module=new_module.replace("PackedSievePrimitiveMillion","PackedSievePrimitiveMaskMillion")
            body=body.replace(new_module.split(".")[-1],masked_module.split(".")[-1])
            begin=body.index("theorem raw_byte_result")
            end=body.index("#print axioms primitive_bits",begin)
            body=body[:begin]+body[end:]
            body=body.replace("#print axioms raw_byte_result\n","")
            new_module=masked_module
        target=out/"source"/Path(*new_module.split(".")).with_suffix(".lean")
        target.write_text(body)
        records.append(dict(module=new_module,lo=lo,width=count,source_sha256=sha(target.read_bytes()),
            original_proofsource_sha256=sha(source.read_bytes())))
    original.update(status="UNTRUSTED_PROPOSAL_REQUIRES_PRIMITIVE_KERNEL_EQUALITY_AND_GENERIC_REWRITE",
        primitive_records=records,primitive_generator_sha256=sha(Path(__file__).read_bytes()))
    (out/"PRIMITIVE_PROPOSAL.json").write_text(json.dumps(original,indent=2)+"\n")
    return records

if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out",type=Path,required=True)
    parser.add_argument("--mask-only",action="store_true",help="SealPmaskwithoutredundantwholepopcount;285prefixconsumerprovesthecounts")
    args=parser.parse_args()
    print(json.dumps(primitive_proposal(args.out.resolve(),args.mask_only)))
