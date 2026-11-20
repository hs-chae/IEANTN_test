# Reproduce the bounded certificate representation experiment

This is **kernel-certificate representation work**, separate from source-first
PV. The original324-bit records, twelve decoded fields, `unpack`, `checkEntry`,
arithmetic and proposed prime-count values are unchanged. The generic
`PackedCertificateArray.get_tabulate` proves exact absolute-index lookup for the
lazy balanced tree. Its axioms are `propext` and `Quot.sound`; all closed word
identity and numerical-check facts in this experiment are axiom-free.

The complete118-payload packet is
`evidence/packed-certificate-scout-v1/PACKET.json`, SHA-256
`b8d232e7be89459f13459149e2912f8d9d75dd91fbeadf64176d566b320e5496`.
It contains exact compressed accepted Lean source snapshots, manifests,
source/object/compiler/resource receipts, axiom output, both deterministic
proposal generators, the generic proof and independent control review. Large
original datasets are unnecessary to replay this bounded experiment: the
compressed snapshots preserve every numerical input used here.

## Exact scope and results

| Workload | Explicit table | Packed table | Numeric check |
|---|---:|---:|---|
| All11,523 control records,16/128/512 packing |5,260,064B|778,096 /516,664 /488,352B|All pass;44.71s versus40.76 /42.00 /41.75s|
| Original high first131,072 words,128 packing |59,256,048B|5,741,600B|Same first32,768 predicates pass;77.38s versus80.77s|

These are **raw-table objects**, excluding identical shared gap definitions and
other common dependencies. Shared gap objects are110,632B for the control and
70,488,112B for the high page. Every original word was additionally checked
kernel-equal: all11,523 words for EACH control variant, and all131,072 high-page
words. This experiment does not verify the remaining90,670,946-record high
certificate, its GapCheck, its final prime count, or the full finite Ramanujan
range. The original692-data-module pipeline is unchanged.

There is no supported RAM/speed improvement claim. The high partial explicit
check peaked at11.42GB RSS; packed at12.92GB. The separate original full-table
first check passed at14.20GB RSS:41GB of object files can be mapped lazily.
The measured improvement is storage, with potential address-space benefit.
Timings are single shared-host profiles. Padding outside the original control
index interval is unused; every in-scope word is formally identical.

## Clean replay from the accepted self-contained input packet

Start in an isolated copy of this solution with the exact pinned Lean4.34.0-rc2
compiler and Mathlib commit71a80585ee495fc24472fd0eaffc89d94e4fd8d6;
follow the main README/bootstrap to obtain CLEAN_CONTEXT using only pinned
generic libraries. Rebuild the numerical core and generic lookup proof into a
fresh application object bank:

```bash
python3 scripts/reproduce_numerical_core.py --context CLEAN_CONTEXT \
  --out FRESH_CORE --root RamanujanPV.QuotientCertificateCode \
  --root RamanujanPV.PackedCertificateArray --cpus CPU --memory-gib 48
```

Use absolute paths. The following extraction checks every packet payload hash,
restores the exact numerical source data, and creates a context pointing to that
fresh core's object bank. Run it from the solution directory:

```bash
python3 - CLEAN_CONTEXT FRESH_CORE <<'PY'
from pathlib import Path
import gzip,hashlib,json,sys
packet=Path('evidence/packed-certificate-scout-v1').resolve()
context=Path(sys.argv[1]);core=Path(sys.argv[2]).resolve()
metadata=json.loads((packet/'PACKET.json').read_text())
for item in metadata['payloads']:
    p=packet/item['path']
    if hashlib.sha256(p.read_bytes()).hexdigest()!=item['sha256']:
        raise ValueError('packet payload changed: '+item['path'])
for label in ['control','high-page']:
    manifest=json.loads((packet/label/'PROPOSAL.json').read_text())
    for item in manifest['modules']:
        packed=packet/label/'accepted'/item['module']/'source.lean.gz'
        source=gzip.decompress(packed.read_bytes())
        if hashlib.sha256(source).hexdigest()!=item['sha256']:
            raise ValueError('accepted source changed')
        out=core/'scout-source'/Path(*item['module'].split('.')).with_suffix('.lean')
        out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(source)
c=json.loads(context.read_text());c['new_application_object_root']=str(core/'lean')
(core/'SCOUT_CONTEXT.json').write_text(json.dumps(c,indent=2)+'\n')
PY
```

Compile each module in each packet PROPOSAL's listed order, first `control`,
then `high-page`, using the actual `module` field as MODULE:

```bash
python3 scripts/compile_lean_context.py MODULE \
  --context FRESH_CORE/SCOUT_CONTEXT.json --source-root FRESH_CORE/scout-source \
  --audit-root FRESH_CORE/scout-audit --cpus CPU --memory-gib 48
```

There are14 control and7 high-page modules. Require every compile to succeed;
require each `all_numeric`, `original_first32768`, `every_original_word` and
`every_original_page_word` print to report no axioms. The new receipt records
source/object hashes, exact commands, elapsed time and actual peak RSS. Object
hashes may change with source locations; mathematical statements and restored
source bytes remain exact. The original accepted executions and Primary's
independent data/pivot/field review are in the packet. This documented combined
clean extraction/core replay has not itself been executed; the constituent
accepted21 modules and source extraction identities have been checked.

The optional generators `generate_packed_representation.py` and
`generate_packed_high_page.py` regenerate the same source proposals from the
original canonical manifests/packed files. They are untrusted producers;
source generation or native extraction agreement never replaces the kernel
checks. The high generator is deliberately bounded to Data0000 and the original
first32,768 predicates; it starts no90-million-record rebuild. No random seed
is used. Preserve accepted sources/receipts and only remove verified-regenerable
experiment-owned temporary data after a checked reproduction.
