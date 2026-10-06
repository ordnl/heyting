# Formalised Heyting Arithmetic

Formalisation of the sequent calculus G3i+HA.

## Building

The current dependencies for the project are:

* [`Rocq-std++`](https://gitlab.mpi-sws.org/iris/stdpp) - An extended "Standard Library" for Rocq.
* [`autosubst-ocaml`](https://github.com/uds-psl/autosubst-ocaml) - Autosubst 2

To install these:

```sh
opam repo add rocq-released https://rocq-prover.github.io/opam/released/
opam install rocq-stdpp
opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev
opam install rocq-autosubst-ocaml
```

### Using Autosubst

Autosubst is used to generate tactics for De Bruijn indices:

```sh
autosubst ./theories/Autosubst/formulas.sig -o ./theories/Autosubst/Formulas.v -s urocq
```

### Generating the makefile

To make the project:

```sh
rocq makefile -f _CoqProject -o makefile
make
```