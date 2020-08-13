Functional Linear Algebra in Agda
=================================

![CI](https://github.com/ryanorendorff/functional-linear-algebra/workflows/Test/badge.svg)

This library attempts to formalize the matrix-free implementation of linear
algebra, where a matrix is represented as a linear map from one vector space to
another. Specifically, this is a formalization of the following two libraries.

- [PyOp](https://github.com/ryanorendorff/pyop), a Python library for composing
  matrix-free linear algebra. Has primary been used in Magnetic Particle Imaging
  (MPI) reconstruction techniques that involve convex optimization.
- [convex](https://github.com/ryanorendorff/convex), a Haskell implementation of
  PyOp that is an investigation into how dependent Haskell can be used to add
  compile time guarantees to the composition of matrix-free operators.
