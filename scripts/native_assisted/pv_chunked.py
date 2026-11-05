#!/usr/bin/env python3
"""Write chunked selected C files for `PVCore.ChunkedProgram` (local research tool).

    python scripts/native_assisted/pv_chunked.py table4 <k>   # Table 4 QRH, its 30 cells in k chunks
    python scripts/native_assisted/pv_chunked.py demo         # 100 upward literals of 1/(j+2)^2

The frozen `sum` function is copied byte for byte from the existing selected file; each chunk is
an array `inputs<j>` and the wrapper adds the chunk sums in order, then scales and applies the
signed constants, exactly in the token shape `PVCore.renderChunked` prints. The literals are not
recomputed for Table 4: the chunked file holds the same 30 cell literals and the same constants as
`Solutions/FKS2Numerics.v5/c/fks2_table4_transport.c`.
"""
from __future__ import annotations

import pathlib
import re
import sys
from fractions import Fraction as F

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
TABLE4 = ROOT / "Solutions" / "FKS2Numerics.v5" / "c" / "fks2_table4_transport.c"
OUTDIR = ROOT / "pilots" / "pv-replay" / "c"

sys.path.insert(0, str(HERE))
import pv_update  # noqa: E402  (frozen generator's `upward` and `literal`)


def frozen_sum_text() -> str:
    text = TABLE4.read_text()
    end = text.index("}\n", text.index("return s;")) + 2
    return text[:end]


def render(fn: str, chunks: list[list[str]], scale: str, ops: list[tuple[str, str]]) -> str:
    out = [frozen_sum_text()]
    for j, c in enumerate(chunks):
        out.append(f"\nstatic const double inputs{j}[{len(c)}] = {{\n    " + ",\n    ".join(c) + "\n};")
    body = [f"    double s = sum(inputs0, {len(chunks[0])});"]
    body += [f"    s = (s + sum(inputs{j}, {len(c)}));" for j, c in enumerate(chunks) if j > 0]
    body.append(f"    double r = (s * {scale});")
    body += [f"    r = (r {sign} {c});" for sign, c in ops]
    body.append("    return r;")
    return "\n".join(out) + f"\ndouble {fn}(void) {{\n" + "\n".join(body) + "\n}\n"


def table4(k: int) -> pathlib.Path:
    text = TABLE4.read_text()
    arr = re.search(r"static const double inputs\[(\d+)\] = \{(.*?)\};", text, re.S)
    lits = [x.strip() for x in arr.group(2).split(",") if x.strip()]
    assert len(lits) == int(arr.group(1))
    scale = re.search(r"double r = \(s \* ([0-9.]+)\);", text).group(1)
    ops = re.findall(r"r = \(r ([+-]) ([0-9.]+)\);", text)
    size = -(-len(lits) // k)
    chunks = [lits[i:i + size] for i in range(0, len(lits), size)]
    out = OUTDIR / "fks2_table4_transport_chunked.c"
    out.write_text(render("fks2_table4_transport", chunks, scale, ops))
    return out


def demo() -> pathlib.Path:
    g = pv_update.frozen_generator()
    lits = [g.literal(g.upward(F(1, (j + 2) ** 2))) for j in range(100)]
    out = OUTDIR / "inverse_squares_100.c"
    out.write_text(render("inverse_squares", [lits[:64], lits[64:]], "1.0", []))
    return out


def main(argv: list[str]) -> int:
    OUTDIR.mkdir(parents=True, exist_ok=True)
    if argv[:1] == ["table4"]:
        print(table4(int(argv[1]) if len(argv) > 1 else 2))
    elif argv[:1] == ["demo"]:
        print(demo())
    else:
        print(__doc__)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
