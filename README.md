# Code from John Harrison's book

John Harrison's remarkable book, **"Handbook of Practical Logic and Automated Reasoning"**,
comes with OCaml code implementing and demonstrating many of the ideas presented there.
Unfortunately the web page and code distribution for them are considerably behind the
current OCaml language and tooling.

This repository was created to help people like myself, who are not very familiar with
OCaml or its toolset, to use Harrison's sample code with recent versions of OCaml
and tools.  It builds with OCaml 5 and dune, and no longer needs camlp5.

The material here started with exactly the tar file referenced on Harrison's resource page
https://www.cl.cam.ac.uk/~jrh13/atp/index.html.  It has been updated slightly to work with much
more recent versions of OCaml and OCaml tools, some of the supporting functionality
has been extended, and minor errors have been corrected.  The instructions here for
installing and setting up OCaml and tools are new.

## Installation

To set up OCaml for use with this repository, get a version of OCaml 5.x.  This has
been tested with 5.2.0, installed with OPAM in a Unix (Mac OS) environment using

```
sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
```

as described at https://opam.ocaml.org/doc/Install.html, followed by

```
opam init
eval (opam env)
```

I added the ```eval (opam env)``` line to my ~/.bashrc to ensure that appropriate
environment variables are set up each time I run bash.

You will need the opam packages "num" (arbitrary-precision arithmetic), "dune"
(the build system) and "ppxlib" (used by the quotation syntax extension).  The
"ocamlfind" package is used to load things into the toplevel, and many users find
the "utop" package very helpful for interactive development.  You can install all
of this with:

```
opam install num dune ppxlib ocamlfind utop
```

camlp5 is no longer required.

## Formula and term quotations

Harrison's book writes formulas and terms in a camlp5 quotation syntax that plain
OCaml cannot parse:

```
<<p ==> q <=> ~q ==> ~p>>          (* a formula *)
<<|x + y|>>                        (* a term *)
```

Rather than depend on camlp5, this repository uses an equivalent syntax built on
OCaml's own extension nodes and quoted string literals, expanded by a small ppx
rewriter in ```ppx/```:

```
{%fml|p ==> q <=> ~q ==> ~p|}      (* a formula *)
{%tm|x + y|}                       (* a term *)
```

```{%fml|...|}``` expands to ```default_parser "..."``` and ```{%tm|...|}``` to
```secondary_parser "..."```, which is exactly what the camlp5 expander did, so the
progressive redefinition of ```default_parser``` through intro.ml, prop.ml and fol.ml
still selects the right parser at each point.  Because ```{|...|}``` needs no escaping,
the ```/\``` and ```\/``` connectives are written just as in the book.

## Using Harrison's code

Build everything first:

```
dune build
```

(```make``` still works; it just calls dune.)  Then invoke the OCaml command line by
running ```ocaml``` or ```utop``` in the top directory of the repo.  Utop provides an
OCaml toplevel with many additional conveniences for interactive use compared with
plain ocaml.  In the top directory is a .ocamlinit file that loads most of Harrison's
code, including the quotation syntax.

The build puts each file's interactive examples in ```_build/default/lib/samples```,
which .ocamlinit adds to the toplevel search path, so you can run any file of examples
with

```
#use "x-<name>.ml";;
```

The files intro.ml, prop.ml, and limitations.ml are a little different.  To run one of
these enter:

```
#use "intro.ml";;
```
or
```
#use "prop.ml";;
```
or
```
#use "limitations.ml";;
```

on your OCaml command line.  In this case restart OCaml before attempting to run other
samples.

To run the batch examples in example.ml as a native executable:

```
dune exec bin/example.exe
```

The ```Makefile``` and ```lib/dune``` comments have more details on what is available.

## Customization

You can customize the OCaml top level further by modifying ```.ocamlinit```, or provide UTop-specific
customizations in ```utop-prefs.ml```, both in the repository top level directory.

## Layout

| path | what it is |
| --- | --- |
| ```*.ml``` (top level) | Harrison's sources, one per chapter topic |
| ```ppx/``` | the ```{%fml\|...\|}``` / ```{%tm\|...\|}``` quotation rewriter |
| ```ppx/driver/``` | standalone driver, so the quotations also work in the toplevel |
| ```lib/``` | dune rules concatenating the sources into the ```atp``` library |
| ```bin/``` | the example.ml executable |
| ```tools/modernize.py``` | the one-shot OCaml 4 to 5 source conversion, kept for reference |

