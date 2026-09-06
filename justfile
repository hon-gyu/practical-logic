# Convenience commands.  dune is the build system; these are just shortcuts.

# List the available recipes.
default:
    @just --list

# Build the library, the example executable and the tests.
build:
    dune build

# Run the test suite.
test:
    dune test

# Run the batch examples from bin/example.ml.
example:
    dune exec bin/example.exe

# Start a toplevel with the library, printers and quotation syntax loaded.
top: build
    utop

# Type-check without producing artifacts.
check:
    dune build @check

# Format the dune files (OCaml sources are left in the book's own style).
fmt:
    dune build @fmt --auto-promote || true

# Remove build artifacts.
clean:
    dune clean
