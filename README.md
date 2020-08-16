Functional Linear Algebra in Agda
=================================

![CI](https://github.com/ryanorendorff/functional-linear-algebra/workflows/build/badge.svg)

This library attempts to formalize the matrix-free implementation of linear
algebra, where a matrix is represented as a linear map from one vector space
to another. Specifically, this is a formalization of the following two
libraries.

- [PyOp](https://github.com/ryanorendorff/pyop), a Python library for composing
  matrix-free linear algebra. Has primary been used in Magnetic Particle Imaging
  (MPI) reconstruction techniques that involve convex optimization.
- [convex](https://github.com/ryanorendorff/convex), a Haskell implementation of
  PyOp that is an investigation into how dependent Haskell can be used to add
  compile time guarantees to the composition of matrix-free operators.


How to use this library
-----------------------

All of these instructions assume that the [nix][nix] package manager is
installed.


### Use Nix to get Agda installed

This repository includes a shell file that will make the `agda` 2.6.1 binary
available. Simply type `nix-shell` to get started.

It is recommended that you use emacs to write Agda code, although any editor
with [agda-mode][agda-mode] support will work. If you have `spacemacs` you
can activate the `agda` configuration layer.


### How to include this library in other Agda libraries

This library can be included in other Agda packages using either the
`agdaPackages.mkDerivation` or `agdaPackages.callPackage` functions in
[nixpkgs][nixpkgs]. More details on how to package Agda with [nix][nix] can
be found in the [Agda section of the nixpkgs manual][nixpkgs-agda].

<!-- References -->
[agda-mode]: https://agda.readthedocs.io/en/v2.6.1/tools/emacs-mode.html
[nix]: https://nixos.org
[nixpkgs]: https://github.com/nixos/nixpkgs
[nixpkgs-agda]: https://github.com/NixOS/nixpkgs/blob/master/doc/languages-frameworks/agda.section.md
[spacemacs]: https://www.spacemacs.org/
