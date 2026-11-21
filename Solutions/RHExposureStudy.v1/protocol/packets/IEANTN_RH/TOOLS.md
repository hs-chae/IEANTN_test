# Generic tools

Use /opt/lean/bin/lean for pinned Lean4.34rc2, /usr/bin/gcc or /usr/bin/g++ for ordinary C/C++, /usr/bin/python3.10 for Python with mpmath1.3.0 and sympy1.12. Shell /bin/bash must be non-login. The LEAN_PATH environment lists your assigned pinned library roots; add /work or your own object root when compiling local modules. No shared host cache or HOME is available.

Compile example: /opt/lean/bin/lean -o /work/Example.olean /work/Example.lean . You may inspect generic source under /generic/source/PACKAGE. The toolchain includes Lake, but network downloads inside worker are blocked; dependency sources/objects are already provided identically. Generic caches are read-only. Source requests do not block research; save otherwork and inspect admissions after a technical snapshot.
