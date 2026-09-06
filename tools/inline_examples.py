#!/usr/bin/env python3
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""Fold examples/<mod>.ml back into lib/<mod>.ml as inline expect tests.

The examples were lifted out of Harrison's sources by tools/migrate_to_modules.py
(deleted in 5c3e67c): each `START_INTERACTIVE;; ... END_INTERACTIVE;;` block
became one entry of examples/<mod>.ml, separated by `(* ---- *)`.  This puts
them back in the style of lib/skolem.ml:

    let%expect_test "eg" =
      print_fol_formula
        (simplify {%fol|...|});
      [%expect {| |}]
    ;;

Insertion points come from the pre-migration source (`git show 8f0bb00^:<mod>.ml`,
which still has the markers), mapped onto the current lib/<mod>.ml with difflib
so the added `open`s and trimmed directives do not matter.

This is a one-off: it gets the shape right, not the types.  Every echoed phrase
is wrapped in the same printer (--printer, default print_fol_formula); wherever
that is the wrong one the compiler will say so and it is a hand fix.  The
`[%expect {| |}]` bodies are left empty -- fill them in at the end with
`dune runtest --auto-promote`.

    uv run --script tools/inline_examples.py skolem          # print the result
    uv run --script tools/inline_examples.py --all --write   # rewrite lib/*.ml
"""

import argparse
import difflib
import os
import re
import subprocess
import sys

LEGACY_REV = "8f0bb00^"

# Which formula printer a module can reach, by position in the old
# concatenation order -- the same split that decided what {%fml|..|} meant.
BEFORE_PROP = ["initialization", "lib", "intro", "formulas"]
BEFORE_FOL = ["prop", "propexamples", "defcnf", "dp", "stal", "bdd"]


def default_printer(module):
    if module in BEFORE_PROP:
        return "print_exp"
    if module in BEFORE_FOL:
        return "print_prop_formula"
    return "print_fol_formula"
SOURCE_NAME = {"print_fpf": "print-fpf.ml"}  # had a dash on disk back then
START = "START_INTERACTIVE;;"
END = "END_INTERACTIVE;;"
SEPARATOR = "(* ---- *)"


# OCaml-aware scanning
# ====================

CHAR_LIT = re.compile(r"'(\\[\\'\"ntbr ]|\\[0-9]{3}|\\x[0-9a-fA-F]{2}|[^\\'])'")
QUOTED_OPEN = re.compile(r"\{(?P<pct>%)?(?P<id>[a-z_]*)\|")


def skip_string(s, i):
    """i points at the opening '"'; returns the index just past the closing one."""
    i += 1
    while i < len(s):
        if s[i] == "\\":
            i += 2
        elif s[i] == '"':
            return i + 1
        else:
            i += 1
    return len(s)  # unterminated: examples/ was split mid-construct


def skip_comment(s, i):
    """i points at '(*'; returns the index just past the matching '*)'."""
    depth = 0
    while i < len(s):
        if s.startswith("(*", i):
            depth += 1
            i += 2
        elif s.startswith("*)", i):
            depth -= 1
            i += 2
            if depth == 0:
                return i
        elif s[i] == '"':
            i = skip_string(s, i)
        else:
            i += 1
    return len(s)  # unterminated: a disabled (*** ... ***) region got split


def skip_quoted(s, i, ident):
    """i points just past the opener; returns the index past '|<ident>}'.

    `{%fol|..|}` is an extension with an empty delimiter, so it closes on `|}`;
    a plain `{tag|..|tag}` closes on its own tag.
    """
    j = s.find("|" + ident + "}", i)
    if j < 0:
        return len(s)
    return j + len(ident) + 2


def scan(src):
    """Yield (kind, start, end) over src; kind is code/comment/string/quoted/char."""
    i, n, code_start = 0, len(src), 0
    while i < n:
        if src.startswith("(*", i):
            j, kind = skip_comment(src, i), "comment"
        elif src[i] == '"':
            j, kind = skip_string(src, i), "string"
        elif src[i] == "{" and QUOTED_OPEN.match(src, i):
            m = QUOTED_OPEN.match(src, i)
            j = skip_quoted(src, m.end(), "" if m.group("pct") else m.group("id"))
            kind = "quoted"
        elif src[i] == "'" and CHAR_LIT.match(src, i):
            j, kind = CHAR_LIT.match(src, i).end(), "char"
        else:
            i += 1
            continue
        if code_start < i:
            yield ("code", code_start, i)
        yield (kind, i, j)
        i = code_start = j
    if code_start < n:
        yield ("code", code_start, n)


def code_only(src):
    """src with comments, strings and quotations blanked out, positions kept."""
    return "".join(src[a:b] if kind == "code" else " " * (b - a)
                   for kind, a, b in scan(src))


# Blocks -> expect tests
# ======================

def split_phrases(src):
    """Split on top-level `;;`, dropping the terminator."""
    blanked = code_only(src)
    out, start = [], 0
    for m in re.finditer(r";;", blanked):
        out.append(src[start:m.start()])
        start = m.end()
    if src[start:].strip():
        out.append(src[start:])
    return out


def split_leading_comments(phrase):
    """(comment lines, the rest): a comment above a phrase stays above it."""
    end = 0
    for kind, a, b in scan(phrase):
        if kind == "comment":
            if phrase[end:a].strip():
                break
            end = b
        elif phrase[a:b].strip():
            break
    return phrase[:end].strip("\n"), phrase[end:]


LET_DEF = re.compile(r"^\s*let\s+(rec\s+)?(?P<name>[A-Za-z_][A-Za-z0-9_\']*)")
STRUCTURE = re.compile(r"^\s*(let|type|module|exception|open)\b")


def classify(phrase):
    """('skip'|'comment'|'expr'|'def', bound name) for one phrase.

    A `let` phrase is a definition unless every `let` in it is matched by an
    `in`, which makes it an ordinary expression (`let x = e in f x`).  Only a
    value binding reports a name: `let f x = ...` has nothing worth printing.
    """
    code = code_only(phrase)
    if not code.strip():
        return ("skip", None)
    if code.lstrip().startswith("#"):
        return ("comment", None)
    if not STRUCTURE.match(code):
        return ("expr", None)
    words = re.findall(r"[A-Za-z_][A-Za-z0-9_\']*", code)
    if code.lstrip().startswith("let") and words.count("in") >= words.count("let"):
        return ("expr", None)
    m = LET_DEF.match(code)
    name = m.group("name") if m and code[m.end():].lstrip().startswith("=") else None
    return ("def", name)


def indent(text, prefix="  "):
    return "\n".join(prefix + l if l.strip() else l for l in text.split("\n"))


def dedent(text):
    lines = text.split("\n")
    body = [l for l in lines if l.strip()]
    if not body:
        return text
    pad = min(len(l) - len(l.lstrip()) for l in body)
    return "\n".join(l[pad:] if l.strip() else "" for l in lines)


def test_name(header):
    """Name the test after the section banner the block sat under."""
    if not header:
        return None
    text = header.strip().rstrip(".")
    if text.lower() == "example":
        return "eg"
    text = re.sub(r"(?i)^examples? (of|for) ", "", text)
    text = re.sub(r"(?i)^examples?[:,]?\s+", "", text).replace('"', "'")
    return "eg: " + text if text else "eg"


def render_block(block, name, printer):
    header = "let%%expect_test %s =" % ('"%s"' % name if name else "_")
    body = []
    for phrase in split_phrases(block):
        lead, rest = split_leading_comments(phrase)
        if lead.strip():
            body.append(("raw", dedent(lead)))
        kind, bound = classify(rest)
        text = dedent(rest.strip("\n").rstrip()).strip()
        if kind == "skip":
            continue
        if kind == "comment":
            body.append(("raw", "\n".join("(* %s *)" % l.strip()
                                          for l in text.split("\n"))))
        elif kind == "def":
            body.append(("raw", "%s in" % text))
            if bound:
                body.append(("print", bound))
        else:
            body.append(("print", text))
    if not any(what == "print" for what, _ in body):
        return []  # nothing the toplevel would have echoed (#install_printer &c)
    lines = [header]
    for what, text in body:
        if what == "raw":
            lines += indent(text).split("\n")
        else:
            lines.append("  " + printer)
            lines += ("    " + indent("(%s);" % text, "    ").lstrip()).split("\n")
    lines += indent("[%expect {| |}]").split("\n")
    lines.append(";;")
    return lines


# Where the blocks used to be
# ===========================

BANNER = re.compile(r"^\(\* -+ \*\)\s*$")


def legacy_source(module):
    src = SOURCE_NAME.get(module, module + ".ml")
    out = subprocess.run(["git", "show", "%s:%s" % (LEGACY_REV, src)],
                         capture_output=True, text=True)
    if out.returncode:
        raise SystemExit("cannot read %s:%s\n%s" % (LEGACY_REV, src, out.stderr))
    return out.stdout.split("\n")


def banner_text(code):
    """Text of the `(* --- *) (* Title. *) (* --- *)` banner just above, if any."""
    i = len(code) - 1
    while i >= 0 and not code[i].strip():
        i -= 1
    if i < 1 or not BANNER.match(code[i]):
        return None
    body, j = [], i - 1
    while j >= 0 and not BANNER.match(code[j]):
        m = re.match(r"^\(\*(.*)\*\)\s*$", code[j])
        if not m:
            return None
        body.append(m.group(1).strip())
        j -= 1
    return " ".join(reversed(body)).strip() or None


def split_interactive(lines):
    """(code lines, [(index into them, banner above)]) for the old source."""
    code, marks, inside = [], [], False
    for line in lines:
        if line.strip() == START:
            inside = True
            marks.append((len(code), banner_text(code)))
        elif line.strip() == END:
            inside = False
        elif not inside:
            code.append(line)
    return code, marks


def map_positions(old_code, current):
    """Map indices in the old code lines onto lines of the current file."""
    a = [l.strip() for l in old_code]
    b = [l.strip() for l in current]
    mapping = {}
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b).get_opcodes():
        if tag == "equal":
            for k in range(i2 - i1):
                mapping[i1 + k] = j1 + k
    return mapping


def insertion_point(old_idx, mapping, current):
    """Line of `current` to insert before, for a block at old_idx."""
    i = old_idx - 1
    while i >= 0 and i not in mapping:
        i -= 1
    if i < 0:
        return None
    j = mapping[i]
    while j + 1 < len(current) and not current[j + 1].strip():
        j += 1
    return j + 1


def strip_banner_above(lines, at, header):
    """Drop an `Example.` banner above the insertion point; return the new index.

    The test name says what the banner said, so keeping it would just repeat it.
    Banners that say anything else stay.
    """
    if not header or not header.lower().startswith("example"):
        return at
    i = min(at, len(lines)) - 1
    while i >= 0 and not lines[i].strip():
        i -= 1
    if i < 2 or not BANNER.match(lines[i]):
        return at
    j = i - 1
    while j >= 0 and not BANNER.match(lines[j]):
        j -= 1
    if j < 0:
        return at
    del lines[j:at]
    return j


# Driver
# ======

def read_example_blocks(path):
    with open(path) as f:
        text = f.read()
    text = re.sub(r"\A\(\*.*?\*\)\s*", "", text, count=1, flags=re.S)  # preamble
    return [b for b in (b.strip("\n") for b in text.split(SEPARATOR)) if b.strip()]


def lib_file(root, name):
    """lib/<name>.ml, or lib/<name>/<name>.ml for the modules with their own dir."""
    flat = os.path.join(root, "lib", name + ".ml")
    return flat if os.path.exists(flat) else os.path.join(
        root, "lib", name, name + ".ml")


def convert(name, root, printer):
    lib_path = lib_file(root, name)
    with open(lib_path) as f:
        current = f.read().split("\n")
    blocks = read_example_blocks(os.path.join(root, "examples", name + ".ml"))
    old_code, marks = split_interactive(legacy_source(name))
    if len(marks) != len(blocks):
        raise SystemExit("%s: %d blocks in examples/, %d in %s -- hand edited?"
                         % (name, len(blocks), len(marks), LEGACY_REV))
    mapping = map_positions(old_code, current)
    delta = 0
    for (old_idx, header), block in zip(marks, blocks):
        at = insertion_point(old_idx, mapping, current)
        if at is None:
            raise SystemExit("%s: cannot place a block" % name)
        at += delta
        body = render_block(block, test_name(header), printer)
        if not body:
            continue
        trimmed = strip_banner_above(current, at, header)
        delta -= at - trimmed
        current[trimmed:trimmed] = body + [""]
        delta += len(body) + 1
    return "\n".join(current), len(blocks)


def main():
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("modules", nargs="*")
    ap.add_argument("--all", action="store_true", help="every module with examples")
    ap.add_argument("--write", action="store_true", help="rewrite lib/<mod>.ml")
    ap.add_argument("--delete-examples", action="store_true",
                    help="also remove examples/<mod>.ml")
    ap.add_argument("--printer", help="printer to wrap phrases in "
                    "(default: per module, print_exp / print_prop_formula / "
                    "print_fol_formula)")
    ap.add_argument("--root", default=os.path.dirname(
        os.path.dirname(os.path.abspath(__file__))))
    args = ap.parse_args()

    names = args.modules
    if args.all:
        names = [f[:-3] for f in sorted(os.listdir(os.path.join(args.root, "examples")))
                 if f.endswith(".ml")]
    if not names:
        ap.error("give module names, or --all")

    for name in names:
        text, n = convert(name, args.root,
                          args.printer or default_printer(name))
        if not args.write:
            sys.stdout.write(text)
            continue
        with open(lib_file(args.root, name), "w") as f:
            f.write(text)
        print("%-16s %d block(s)" % (name, n))
        if args.delete_examples:
            os.remove(os.path.join(args.root, "examples", name + ".ml"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
