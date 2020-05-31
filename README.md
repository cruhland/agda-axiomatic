# agda-axiomatic

An "axiomatic" approach to defining math concepts in Agda: using
fields of record types to specify axioms, instead of algebraic data
types. The advantage of this approach is that theorems derived from
the axioms will apply to any concrete data type that satisfies them.

For example, both an unary and a binary representation of natural
numbers can be built with algebraic data types. By constructing an
instance of the `Peano` record supplied by this library for either
representation, we can make use of its associated theorems to draw
conclusions about the representation's behavior.

## Usage

Since this project is an Agda library, please see the [Library
Management](https://agda.readthedocs.io/en/latest/tools/package-system.html)
page of the Agda docs for instructions on how to use it.
