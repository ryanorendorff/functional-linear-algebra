let

  # nixpkgs unstable channel from Aug 10 2020, 11:11 AM GMT
  pkgs = import (builtins.fetchTarball {
    url =
      "https://github.com/NixOS/nixpkgs-channels/archive/32b46dd897ab2143a609988a04d87452f0bbef59.tar.gz";
    sha256 = "1gzfrpjnr1bz9zljsyg3a4zrhk8r927sz761mrgcg56dwinkhpjk";
  }) { };

in pkgs.agdaPackages.callPackage ./default.nix { }
