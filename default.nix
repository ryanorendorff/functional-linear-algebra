# This package can be called with the nixpkg function
# `agdaPackages.callPackage`, which is where the `standard-library` input comes
# from.
{ lib, stdenv, mkDerivation, standard-library }:

mkDerivation {
  version = "0.1";
  pname = "functional-linear-algebra";

  buildInputs = [ standard-library ];

  src = lib.sourceFilesBySuffices ./. [
    ".agda"
    ".lagda"
    ".lagda.md"
    ".lagda.rst"
    ".lagda.tex"
    ".agda-lib"
  ];

  meta = with stdenv.lib; {
    homepage = "https://github.io/ryanorendorff/functional-linear-algebra";
    description = ''
      Formalizing linear algebra in Agda by representing matrices as functions
      from one vector space to another.
    '';
    license = licenses.bsd3;
    platforms = platforms.unix;
    maintainers = with maintainers; [ ryanorendorff ];
  };
}
