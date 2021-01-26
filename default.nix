# Since this package is already in nixpkgs, we just override the src.
{ pkgs }:

pkgs.agdaPackages.functional-linear-algebra.overrideAttrs (oldAttrs: rec {
  src = pkgs.lib.sourceFilesBySuffices ./. [
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
})
