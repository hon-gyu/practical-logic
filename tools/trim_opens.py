#!/usr/bin/env python3
"""Reduce each module's "open" preamble to the modules it actually uses.

migrate_to_modules.py gives every module an open for every predecessor, which
is correct but says nothing about real dependencies.  This asks the compiler
(warning 33, unused open) which ones are dead and drops them, repeating until
the build is clean.  Removing an open that warning 33 reports is safe even
where modules shadow each other: the warning fires only when nothing at all
resolved through that open.
"""
import re, subprocess, sys

FLAGS = "(:standard -w -a+33 -warn-error -a -no-strict-sequence -open Format -open Num -open Str)"
DUNE = "lib/dune"

def build():
    return subprocess.run(["dune", "build", "@lib/all"],
                          capture_output=True, text=True).stderr

def main():
    original = open(DUNE).read()
    open(DUNE, "w").write(re.sub(r"\(:standard[^)]*\)", FLAGS, original))
    try:
        total = 0
        for _ in range(60):
            err = build()
            # File "lib/foo.ml", line N, characters ...:  Warning 33: unused open Bar.
            hits = {}
            for m in re.finditer(
                    r'File "([^"]+)", line (\d+),[^\n]*\n(?:[^\n]*\n)*?'
                    r'(?:Error \(warning 33[^)]*\)|Warning 33[^:]*):[^\n]*unused open', err):
                hits.setdefault(m.group(1), set()).add(int(m.group(2)))
            if not hits:
                break
            for path, lines in hits.items():
                src = open(path).read().split("\n")
                for n in sorted(lines, reverse=True):
                    del src[n - 1]
                    total += 1
                open(path, "w").write("\n".join(src))
        else:
            print("did not converge", file=sys.stderr)
        print("removed %d open lines" % total)
    finally:
        open(DUNE, "w").write(original)
    err = build()
    print("final build clean" if not err.strip() else err[:2000])

main()
