let

  pkgs = import (builtins.fetchTarball {
    url =
      "https://github.com/NixOS/nixpkgs-channels/archive/32b46dd897ab2143a609988a04d87452f0bbef59.tar.gz";
    sha256 = "1gzfrpjnr1bz9zljsyg3a4zrhk8r927sz761mrgcg56dwinkhpjk";
  }) { };

in pkgs.agdaPackages.mkDerivation {
  version = "0.1";
  pname = "functional-linear-algebra";

  buildInputs = [ pkgs.agdaPackages.standard-library ];

  src = pkgs.lib.sourceFilesBySuffices ./. [ ".agda" ".agda-lib" ".lagda" ".lagda.md" ".lagda.tex" ".lagda.rst" ];

  meta = with pkgs.stdenv.lib; {
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
