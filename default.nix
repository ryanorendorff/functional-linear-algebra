# Since this package is already in nixpkgs, we just override the src.
{ agdaPackages, lib }:

agdaPackages.functional-linear-algebra.overrideAttrs (oldAttrs: rec {
  version = "0.5.0";

  src = lib.sourceFilesBySuffices (builtins.path {
    path = ./.;
    name = "functional-linear-algebra";
  }) [
    ".agda"
    ".lagda"
    ".lagda.md"
    ".lagda.rst"
    ".lagda.tex"
    ".agda-lib"
    "generate-everything.sh"
  ];

  preConfigure = ''
    # Find all .agda files in the src/ directory and put it in Everything.agda
    ./generate-everything.sh
  '';

  # Force the meta to be unbroken so that the package will always attempt to
  # build in CI, regardless of the upstream broken status.
  meta.broken = false;
})
