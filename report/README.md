# Report on Consistency of Heyting Arithmetic

This folder contains a report on the pen and paper proof of syntactic proofs of the consistency of Heyting arithmetic. Currently, the project discuesses:

* Gentzen's Consistency via Reduction Procedure
* Schütte's Infinitary Proof Theoretic Cut-Elimination

## Building

To build the PDF, run `latexmk`:

```
latexmk -pdf main.tex
```

## Cleaning

To clean auxiliary files:

```
latexmk -c
```