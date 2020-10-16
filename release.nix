let pkgs = import ./nixpkgs.nix; in import ./default.nix { inherit pkgs; }
