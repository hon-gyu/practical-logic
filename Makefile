# Thin wrapper over dune, kept so the commands in README.md and in muscle
# memory still work.  The real build description is in dune-project,
# lib/dune, ppx/dune and bin/dune.

# Build everything the toplevel needs: the atp library, the quotation ppx
# and its standalone driver, printers.ml and the samples/ directory.
.PHONY: TOP
TOP:
	dune build @lib/top

# Native and bytecode executables running the examples in example.ml.
.PHONY: example
example:
	dune build bin/example.exe

.PHONY: clean
clean:
	dune clean
