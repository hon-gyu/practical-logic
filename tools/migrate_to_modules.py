#!/usr/bin/env python3
"""One-shot migration: Harrison's concatenated sources -> real dune modules.

Run once from the repo root.  For each source file this:
  * lifts the START_INTERACTIVE blocks out into examples/<name>.ml
  * lifts the #install_printer directives out into toplevel/printers.ml
  * rewrites {%fml|..|} to the explicit {%expr|..|} / {%prop|..|} / {%fol|..|}
    according to which default_parser was in scope at that point
  * prepends the "open" preamble the concatenation used to provide implicitly
and writes the result to lib/<module>.ml.

The preamble starts as every predecessor module; tools/trim_opens.sh then
removes the ones the compiler reports as unused (warning 33).
"""

import os
import re

# The concatenation order from the old lib/dune.  It is also the dependency
# order: nothing here can refer to anything below it.
ORDER = [
    "initialization", "lib", "intro", "formulas", "prop", "propexamples",
    "defcnf", "dp", "stal", "bdd", "fol", "skolem", "herbrand", "unif",
    "tableaux", "resolution", "prolog", "meson", "skolems", "equal", "cong",
    "rewrite", "order", "completion", "eqelim", "paramodulation", "decidable",
    "qelim", "cooper", "complex", "real", "grobner", "geom", "interpolation",
    "combining", "lcf", "lcfprop", "folderived", "lcffol", "tactics",
    "print_fpf", "limitations",
]

# On disk print-fpf.ml has a dash, which is not a legal module name.
SOURCE_NAME = {"print_fpf": "print-fpf.ml"}

# Which parser {%fml|..|} meant, by position in the chain.
def quotation_for(mod):
    i = ORDER.index(mod)
    if i < ORDER.index("prop"):
        return "expr"
    if i < ORDER.index("fol"):
        return "prop"
    return "fol"

START = "START_INTERACTIVE;;"
END = "END_INTERACTIVE;;"

def split_interactive(lines):
    """Return (code_lines, example_blocks)."""
    code, blocks, current = [], [], None
    for line in lines:
        if line.strip() == START:
            current = []
        elif line.strip() == END:
            if current is not None:
                blocks.append(current)
            current = None
        elif current is not None:
            current.append(line)
        else:
            code.append(line)
    assert current is None, "unterminated START_INTERACTIVE"
    return code, blocks

INSTALL = re.compile(r"^\s*#install_printer\s+([A-Za-z0-9_']+)\s*;;")

def split_printers(lines):
    code, printers = [], []
    for line in lines:
        m = INSTALL.match(line)
        if m:
            printers.append(m.group(1))
        else:
            code.append(line)
    return code, printers

def main():
    os.makedirs("lib", exist_ok=True)
    os.makedirs("examples", exist_ok=True)
    os.makedirs("toplevel", exist_ok=True)
    all_printers = []

    for pos, mod in enumerate(ORDER):
        src = SOURCE_NAME.get(mod, mod + ".ml")
        lines = open(src).read().split("\n")

        code, blocks = split_interactive(lines)
        code, printers = split_printers(code)
        all_printers += [(mod, p) for p in printers]

        kind = quotation_for(mod)
        code = [l.replace("{%fml|", "{%" + kind + "|") for l in code]
        blocks = [[l.replace("{%fml|", "{%" + kind + "|") for l in b] for b in blocks]

        opens = "".join("open %s\n" % m.capitalize() for m in ORDER[:pos])
        body = "\n".join(code).rstrip() + "\n"
        with open("lib/%s.ml" % mod, "w") as f:
            f.write(opens + ("\n" if opens else "") + body)

        if blocks:
            with open("examples/%s.ml" % mod, "w") as f:
                f.write(
                    "(* Interactive examples from %s, lifted out of the source by\n"
                    "   tools/migrate_to_modules.py.  Not compiled: these are meant to be\n"
                    "   pasted into a toplevel that has opened Atp.All. *)\n\n" % src)
                f.write("\n(* ---- *)\n\n".join(
                    "\n".join(b).strip() + "\n" for b in blocks))

    with open("toplevel/printers.ml", "w") as f:
        f.write(
            "(* Optional: toplevel printers, so the REPL shows a formula as\n"
            "   <<p ==> q>> rather than its constructor tree.  #install_printer is a\n"
            "   toplevel directive, so these cannot live in the compiled library.\n"
            "   Loaded by toplevel/loadall.ml. *)\n\n")
        for mod, p in all_printers:
            f.write("#install_printer Atp.%s.%s;;\n" % (mod.capitalize(), p))

    print("modules: %d" % len(ORDER))
    print("printers: %d" % len(all_printers))
    print("example files: %d" % len(os.listdir("examples")))

main()
