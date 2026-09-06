# Building the documentation under OxCaml 5.2

`dune build @doc @doc-private` needs an odoc that understands the compiler that
produced the `.cmt` files.  Under an OxCaml 5.2 switch, a stock odoc is not that
odoc, and the failure it reports is misleading:

```
File "lib/.atp.objs/byte/_unknown_", line 1, characters 0-0:
ERROR: File "atp.cmt":
not an implementation
```

Every `.cmt` fails this way, not just the two dune happens to name.  OxCaml's
typedtree and `Cmt_format` differ from upstream OCaml's, so stock odoc cannot
unmarshal the files at all, and it reports the read failure as "not an
implementation".

## What to install

OxCaml maintains an odoc fork at <https://github.com/oxcaml/odoc>, a linear
stack of adaptation commits.  Two things have to line up:

  - The fork commit must match the era of the switch's compiler.  The tip
    (`5.2.0minus-39`) targets a newer OxCaml snapshot and fails against an
    older one, for instance with `Types.Mty_functor expects 2 arguments, but is
    applied here to 3` once modal functors landed.  Compare the date of the
    compiler commit recorded in the switch's `ocaml-variants` package against
    the fork's history and pick a commit from the same period.  Commit
    `97e1daec` ("Sherlodoc", 2025-08-26) works for a mid-2025 5.2.0+ox
    snapshot.
  - `sherlodoc` must come from the same commit as `odoc`.  Dune's doc rules
    invoke whichever `sherlodoc` is on `PATH`, and one built against upstream
    odoc **segfaults** reading the fork's `.odocl` files:

    ```
    File "_doc/_html/atp@<hash>/_unknown_", line 1, characters 0-0:
    Command got signal SEGV.
    ```

    A stray `sherlodoc` from an unrelated switch left on `PATH` is enough to
    cause this even when `odoc` itself resolves correctly.

The opam package for the fork (`odoc.3.2.0+ox2`) targets the current OxCaml
packaging and will not solve against a 5.2 switch, so build from source and
install into the switch prefix:

```sh
git clone https://github.com/oxcaml/odoc.git
cd odoc && git checkout <commit>
git tag -f 3.1.0 HEAD && dune subst     # odoc's file magic is "odoc-%%VERSION%%"
dune build -p odoc @install
dune install odoc --prefix "$(opam var prefix)"
```

`dune subst` matters: without it the binary writes files with magic
`odoc-%%VER` and later rejects its own output.

Then the same for sherlodoc.  Its CLI embeds the search frontend through
`ppx_blob`, which pulls in `brr` and `js_of_ocaml-toplevel`; the latter does not
build under this compiler (`Error: Uninterpreted extension 'if'`).  The
frontend is plain JavaScript and does not depend on odoc, so a copy taken from
any sherlodoc of the same series can be substituted:

```sh
sherlodoc js sherlodoc.js.prebuilt        # from any existing sherlodoc
mv sherlodoc.js.prebuilt sherlodoc/jsoo/
cat > sherlodoc/jsoo/dune <<'DUNE'
(rule
 (action
  (copy sherlodoc.js.prebuilt sherlodoc.js)))
DUNE
dune build -p sherlodoc @install
dune install sherlodoc --prefix "$(opam var prefix)"
```

Build dependencies to have in the switch: `odoc-parser.3.1.0`, `fmt`, `crunch`,
`ptime`, `ppx_blob`, `decompress`, `base64`, `bigstringaf`.

## Keeping the switch solvable

The OxCaml opam repository tracks current OxCaml.  Updating it rewrites
`ocaml-variants.5.2.0+ox` to depend on `oxcaml-compiler` and a chain of patch
guards that require a newer dune than a 5.2 switch pins, after which opam can
install nothing at all in that switch — including reinstalling
`ocaml-lsp-server`.  Pin the repository to the commit the switch was built
from:

```sh
opam repository set-url ox 'git+https://github.com/oxcaml/opam-repository.git#<commit>'
```

## Notes

Both binaries are installed with `dune install`, outside opam's bookkeeping.
`opam upgrade` may overwrite or remove them, in which case rebuild from the
same checkout.

The alternative, if none of this is wanted, is to build the docs from an
ordinary (non-OxCaml) OCaml 5.x switch that has odoc: this project compiles
there unchanged, and `dune build --build-dir=_build.doc @doc @doc-private`
keeps those artifacts out of the way of the main build.
