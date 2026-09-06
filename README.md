# Code from John Harrison's book

John Harrison's remarkable book, **"Handbook of Practical Logic and Automated Reasoning"**,
comes with OCaml code implementing and demonstrating many of the ideas presented there.
Unfortunately the web page and code distribution for them are considerably behind the
current OCaml language and tooling.

This repository was created to help people like myself, who are not very familiar with
OCaml or its toolset, to use Harrison's sample code with recent versions of OCaml
and tools.  It builds with OCaml 5 and dune, no longer needs camlp5, and the sources are
ordinary OCaml modules rather than one concatenated file.

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

```just``` is optional; it only runs the shortcuts in the ```justfile```.

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
rewriter in ```ppx/```.  camlp5 had a single ```<<...>>``` meaning "whichever
parser is currently in scope", so the book's sources redefine ```default_parser```
as they go; here the level is named explicitly instead:

```
{%expr|2 * x + y|}                 (* an arithmetic expression, chapter 1 *)
{%prop|p ==> q <=> ~q ==> ~p|}     (* a propositional formula *)
{%fol|forall x. P(x) ==> Q(x)|}    (* a first-order formula *)
{%tm|x + y|}                       (* a first-order term *)
```

Each expands to a plain function call -- ```parse_prop_formula "..."``` and so on
-- so a quotation means the same thing wherever it appears.  That is what lets
the sources be ordinary modules instead of one concatenated file.  Because
```{|...|}``` needs no escaping, the ```/\``` and ```\/``` connectives are written
just as in the book.

## Using Harrison's code

Build everything with

```
dune build
```

or ```just build```; ```just --list``` shows the other shortcuts (```just test```,
```just example```, ```just top```).

The code is the library ```atp```, one module per chapter topic: ```Atp.Prop```,
```Atp.Fol```, ```Atp.Resolution```, ```Atp.Meson``` and so on.  Open the modules
you need, or ```open Atp.All``` to get every name at once, which is what the
single concatenated module used to give you.

```ocaml
open Atp
open Fol
open Meson

let () =
  Initialization.init ();
  ignore (meson {%fol|exists y. forall x. P(y) ==> P(x)|})
```

```Atp.Initialization.init ()``` raises the stack limit and sets the print
margin.  Those used to happen as a side effect of loading the code; deep proof
search can overflow the default stack without it.

Goedel's theorem and relatives live in a separate library, ```atp_limitations```,
because that module runs a second or so of proof search when it loads.

To run the test suite:

```
dune test
```

To run the batch examples in bin/example.ml as a native executable:

```
dune exec bin/example.exe
```

### Toplevel

Optional, and not required to use the library.  Run ```ocaml``` or ```utop``` in
the top directory: ```.ocamlinit``` loads ```toplevel/loadall.ml```, which loads
the library, enables the quotation syntax and installs the printers that display
a formula as ```<<p ==> q>>``` rather than as its constructor tree.  The printers
are in ```toplevel/printers.ml``` and can simply be left out.

The worked examples from the book -- the blocks that used to be bracketed by
```START_INTERACTIVE``` in each source file -- are in ```examples/```, one file per
chapter topic, to be pasted into a toplevel that has done ```open Atp.All```.

## Customization

You can customize the OCaml top level further by modifying ```.ocamlinit``` in the
repository top level directory, or provide UTop-specific customizations in
```toplevel/utop-prefs.ml```.  Both are gitignored, so they stay local to you.

## Layout

| path | what it is |
| --- | --- |
| ```lib/``` | Harrison's sources, one module per chapter topic |
| ```lib/limitations/``` | Goedel's theorem, separate because it is slow to load |
| ```ppx/``` | the quotation rewriter |
| ```ppx/driver/``` | standalone driver, so the quotations also work in the toplevel |
| ```bin/``` | the example.ml executable |
| ```tests/``` | the test suite, run with ```dune test``` |
| ```examples/``` | the book's interactive example blocks, for pasting into a toplevel |
| ```toplevel/``` | optional toplevel setup: loader and printers |
| ```tools/``` | one-shot migration scripts, kept for reference |
