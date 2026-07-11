#!/usr/bin/env python3
"""
Dependency graph + non-circularity audit for the StructuralBertrand Lean project.

Scans `StructuralBertrand/*.lean`, extracts `import` edges among the project modules,
and renders a module dependency graph. The single external dependency of interest,
`Mathlib.NumberTheory.Bertrand`, is drawn as a highlighted node so that the
non-circularity property is visible: it is imported only by `Erdos.lean` (instance A,
off the main path), and the main theorem `bertrand_chebyshev` does not depend on it.

Usage:
    python3 scripts/dependency_graph.py

Requires Graphviz (`dot`) and the `graphviz` Python package. Outputs
`docs/dependency_graph.svg` (and `.pdf`). The audit is printed to stdout.
"""

import os
import re
from graphviz import Digraph

# Repository root = parent of this script's directory.
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "StructuralBertrand")
OUT_DIR = os.path.join(ROOT, "docs")

import_re = re.compile(r"^\s*import\s+(\S+)")

# Modules that make up the main theorem's dependency closure (for colouring).
# Erdos is instance A, off the main path; it is the only importer of Mathlib's Bertrand.
BERTRAND_IMPORT = "Mathlib.NumberTheory.Bertrand"


def module_name(path: str) -> str:
    """`StructuralBertrand/BinomialBound.lean` -> `StructuralBertrand.BinomialBound`."""
    rel = os.path.relpath(path, ROOT)
    return rel[:-len(".lean")].replace(os.sep, ".")


def scan():
    files = {}          # module name -> path
    imports = {}        # module name -> list of imported module names
    for name in sorted(os.listdir(SRC)):
        if not name.endswith(".lean"):
            continue
        path = os.path.join(SRC, name)
        mod = module_name(path)
        files[mod] = path
        imps = []
        with open(path, encoding="utf8") as f:
            for line in f:
                m = import_re.match(line)
                if m:
                    imps.append(m.group(1))
        imports[mod] = imps
    return files, imports


def audit(files, imports):
    print("=" * 70)
    print("NON-CIRCULARITY AUDIT")
    print("=" * 70)
    importers = [m for m, imps in imports.items() if BERTRAND_IMPORT in imps]
    print(f"\nModules importing {BERTRAND_IMPORT}:")
    for m in importers:
        print(f"    {m}")
    if importers == ["StructuralBertrand.Erdos"]:
        print("  OK: only Erdos.lean (instance A, off the main path).")
    # grep for forbidden *uses* of Mathlib's Bertrand theorem
    pat = re.compile(r"Nat\.bertrand[^_]|exists_prime_lt_and_le_two_mul")
    hits = []
    for m, path in files.items():
        with open(path, encoding="utf8") as f:
            for i, line in enumerate(f, 1):
                if pat.search(line):
                    hits.append((m, i, line.strip()))
    print("\nUses of Nat.bertrand / exists_prime_lt_and_le_two_mul:")
    if not hits:
        print("    none")
    else:
        for m, i, line in hits:
            tag = "comment" if line.lstrip().startswith("--") or "`" in line else "CODE"
            print(f"    [{tag}] {m}:{i}: {line}")


def build(files, imports):
    dot = Digraph("StructuralBertrand")
    dot.attr(rankdir="LR", ranksep="0.6", nodesep="0.25", splines="spline")
    dot.attr("node", shape="box", style="rounded,filled", fillcolor="#eef3f8",
             color="#1a5f7a", fontname="Helvetica", fontsize="10", margin="0.10,0.05")
    dot.attr("edge", arrowsize="0.6", color="#7a8a99")

    def label(mod):
        return mod.split(".")[-1]

    for mod in files:
        fill, col = "#eef3f8", "#1a5f7a"
        if mod == "StructuralBertrand.Main":
            fill, col = "#d7f0d7", "#2e7d32"      # main theorem
        elif mod == "StructuralBertrand.Erdos":
            fill, col = "#fde9d0", "#b5651d"      # instance A, off the main path
        elif mod == "StructuralBertrand.Certificate":
            fill, col = "#e6e0f0", "#5b3fa0"      # modular interface
        dot.node(mod, label(mod), fillcolor=fill, color=col)

    # External Bertrand node (highlighted) — the non-circularity focus.
    dot.node(BERTRAND_IMPORT, "Mathlib.NumberTheory\n.Bertrand", shape="box",
             style="rounded,filled,dashed", fillcolor="#ffdddd", color="#b00020",
             fontsize="9")

    for mod, imps in imports.items():
        for imp in imps:
            if imp in files:
                dot.edge(mod, imp)
            elif imp == BERTRAND_IMPORT:
                dot.edge(mod, imp, color="#b00020", penwidth="1.4")

    os.makedirs(OUT_DIR, exist_ok=True)
    # Render via pipe() and write the bytes ourselves — avoids leaving/removing
    # intermediate .gv files (deletion can fail on synced drives).
    for fmt in ("svg", "pdf"):
        data = dot.pipe(format=fmt)
        out = os.path.join(OUT_DIR, f"dependency_graph.{fmt}")
        with open(out, "wb") as f:
            f.write(data)
        print(f"Wrote {out}")


if __name__ == "__main__":
    files, imports = scan()
    audit(files, imports)
    build(files, imports)
