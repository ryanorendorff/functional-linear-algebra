Functional Linear Algebra in Agda
=================================

![CI](https://github.com/ryanorendorff/functional-linear-algebra/workflows/build/badge.svg)

This library attempts to formalize the matrix-free implementation of linear
algebra, where a matrix is represented as a linear map from one vector space
to another. This is accomplished by representing matrices as a pair of
functions (matrix vector multiply `M` and matrix transpose vector multiply
`Mᵀ`) that must have two properties

- Each function respects linearity and homogeneity. 
  - Linearity: `(u v : Vec A m) → f (u +ⱽ v) ≡ f u +ⱽ f v`
  - Homogeneity: `(c : A) → (v : Vec A m) → f (c ∘ⱽ v) ≡ c ∘ⱽ (f v)`
- The pair of functions must form a valid inner product:

  `(x : Vec A m) → (y : Vec A n) → ⟨ x , M ·ˡᵐ y ⟩ ≡ ⟨ y , Mᵀ ·ˡᵐ x ⟩`.

This library is based off the following previous implementations of the idea.

- [PyOp][PyOp], a Python library for composing matrix-free linear algebra.
  Has primary been used in Magnetic Particle Imaging (MPI) reconstruction
  techniques that involve convex optimization. Represents matrices as a pair
  of functions of type `numpy.ndarray -> numpy.ndarray`. No proofs or size
  checking is performed.
- [convex][convex], a Haskell implementation of PyOp that is an investigation
  into how dependent Haskell can be used to add compile time guarantees to
  the composition of matrix-free operators. Represents matrices as a pair of
  functions on dependent vector (`Vec A n`) types. Sizes are checked at
  compile time, but there are no proofs of linearity, homogeneity, or the
  inner product property.

A [presentation][presentation] comparing how these representations can be used
and what bugs can occur in each was presented for LambdaConf 2020.


How to use this library
-----------------------

All of these instructions assume that the [nix][nix] package manager is
installed.


### Use Nix to get Agda installed

This repository includes a shell file that will make the `agda` 2.6.4.1 binary
available. Simply type `nix-shell` to get started.

It is recommended that you use emacs to write Agda code, although any editor
with [agda-mode][agda-mode] support will work.


### How to include this library in other Agda libraries

This library can be included in other Agda packages using either the
`agdaPackages.mkDerivation` or `agdaPackages.callPackage` functions in
[nixpkgs][nixpkgs]. More details on how to package Agda with [nix][nix] can
be found in the [Agda section of the nixpkgs manual][nixpkgs-agda].


### Dependencies

The following Agda libraries are used:

- `standard-library` (version 2.0 only, does not work with the 1.x series)

You can override which specific version of the standard library is being used
through Nix by changing the `use-overlay-standard-library` boolean in
`agda-stardard-library.nix` and updating the git revision to the one you'd like
to use.


Want to contribute?
-------------------

If you want to learn more Agda (from a fellow Agda beginner) or have a new idea,
please submit a pull request! I would like to get to the following at some point:

1. Square root of a matrix. This should be finding a matrix A^(1/2) such that
   B = A^(1/2)A^(1/2) is held.
2. Proving that a matrix is positive semidefinite. This should be possible by
   using the inner product definition.
3. Prove a transformation of an optimization problem preserves the problem
   solution.


<!-- Other material related to this project on my github -->
[PyOp]: https://github.com/ryanorendorff/pyop
[convex]: https://github.com/ryanorendorff/convex
[presentation]: https://github.com/ryanorendorff/lc-2020-linear-algebra-agda

<!-- References -->
[agda-mode]: https://agda.readthedocs.io/en/v2.6.4.1/tools/emacs-mode.html
[nix]: https://nixos.org
[nixpkgs]: https://github.com/nixos/nixpkgs
[nixpkgs-agda]: https://github.com/NixOS/nixpkgs/blob/master/doc/languages-frameworks/agda.section.md
