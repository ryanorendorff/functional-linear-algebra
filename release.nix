let

  # nixpkgs unstable channel from Aug 10 2020, 11:11 AM GMT
  pkgs = import ./nixpkgs.nix;
in import ./default.nix { inherit pkgs; }
