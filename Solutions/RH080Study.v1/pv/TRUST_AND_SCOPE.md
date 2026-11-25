# Compact dual-grid source-first verification scope

The complete fixed-input source-first chain has passed a fresh 45-module replay,
followed by an eight-file canonical integration append. Exact receipts, theorem
paths, resource measurements and controls are in `receipts/` and `HANDOFF.json`.
An ordinary compiled run or a separate Arb enclosure is not source-first PV.

`dual_grid.c` computes a bound from the fixed rational twenty-step dual witness.
Its numerical function visits all 257 grid points; each nonzero point visits all
twenty coefficient jumps and evaluates a nine-term fixed-point sine polynomial.
The maximum is computed by the source loop. The returned maximum is not copied
into that loop as a constant. The zero-grid branch is the exact, separately
justified limit ceiling of `625/512` at scale one million, not an assumption about
the computed maximum. Rational input coefficients and fixed algorithm parameters
are recorded in `PARAMETERS.json`.

The independent Goldbach character-level lexical, precedence/parentheses,
declaration/statement/function and physical-preprocessing grammar is reused
unchanged. Its general acceptance-implies-syntax theorem does not follow from
testing or from equality of two token lists. `parse_source.py` is an untrusted
candidate AST producer: the formal checker validates its output against the
actual source, so correctness of Python parsing is not a premise. The restricted
source fragment is unsigned scalar C, explicit blocks, declarations/assignment,
arithmetic/comparison, direct function calls, if/while, returns and the one
standard printf format in the host harness. No CUDA, pointers, dynamic allocation,
concurrency, unspecified evaluation side effects or arbitrary C preprocessing is
used by this program.

`DualExecution.lean` specifies evaluation structurally over the actual parsed AST.
Own function calls resolve the program's function list. There is no primitive for
the whole sine, point or maximum routine and no desired numerical answer in the
execution rules. Environments preserve lexical block scope. Successful addition
and multiplication require values below `2^64`; subtraction requires a
nonnegative difference; division and remainder reject zero divisors. Thus a
successful closed modeled run does not assume absence of these application
errors: those guards must actually evaluate successfully. This is a safe partial
model of the used unsigned arithmetic, not a semantics for all legal wrapping C
programs. The checked arithmetic operation lemmas state the exact natural-number
result and applicability conditions.

The finite correctness domain is this fixed twenty-step witness and grid,
including sine arguments zero through128. No verified global optimizer,
unbounded-input sine implementation or general-C frontend is claimed. The
high-level recurrence `Model.sineFixed` and `sampleBound` is separate from the
source-AST interpreter. Their correspondence and actual execution require
separate proved claims. The finite sine accuracy claims must use actual real
sine and pi; the final real dual bound also needs periodic/reflection identities,
the interpolation remainder, and the source-accurate weak-duality theorem.

The precise remaining platform interpretation is conventional C11 unsigned
integer and function-call behavior; `uint64_t` is an available exact64-bit
unsigned integer type; decimal ULL constants have their standard values; the
chosen compiler preserves the program's behavior; libc printf with `%llu\n`
serializes the actual unsigned-long-long argument in decimal followed by newline;
the loader, OS, runtime and hardware execute that binary correctly. The source,
compiled binary, command, compiler version and actual stdout bytes are hashed.
The application casts a value below `2^64` to unsigned long long, whose standard
range contains that value. This is not a compiler, libc, OS or hardware
formalization. Main-call structure and decimal output association remain explicit
application obligations, not an assumption that the reported answer is correct.

The V0 comparison must receive identical rational coefficients and numerical
information. If both routes establish the same mathematical bound, V1 adds
verified source execution coverage; it does not by itself establish greater
mathematical strength or a causal advantage for PV.

A successful stdout operation is not a generic trusted platform fact. ISO C
`printf` can fail, and this application does not inspect its return code. The host
semantics therefore takes the primitive's actual capture relation as a parameter.
The proved application main theorem says that an actual such operation is called
with the source-verified integer and the exact format, then returns zero; exact
bytes follow only under an explicitly supplied successful-format contract. The
pure numerical function and its mathematical cap do not depend on I/O success.
The recorded compiled runs separately demonstrate the actual captured eight bytes
`31 32 32 31 31 36 31 0a`; these receipts are not transformed into a theorem that
all possible platform executions emit that line.

The conventional arithmetic and printf interpretation above is the selected
model's adequacy boundary with ISO C11, rather than a formalization of every C11
rule or the optimizing compiler. The independent syntax theorem is a proved
character-level correspondence; it does not by itself prove semantic adequacy.
The relevant primary standard locators are WG14 N1570 §6.2.5 paragraph9 (unsigned
arithmetic), §7.20.1.1 (exact-width integer types), and §7.21.6.3 paragraphs2–3
(`printf`, including a negative result on output/encoding failure):
https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf .
