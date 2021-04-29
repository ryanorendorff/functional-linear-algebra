# nixpkgs unstable channel from April 16th, 2021

let

  # Temporary workaround while Agda standard library is an RC.
  agda-standard-library-overlay = (self: super: {
    agdaPackages = super.agdaPackages // {
      standard-library = super.agdaPackages.standard-library.overrideAttrs
        (old: import ./agda-stardard-library.nix super);

      functional-linear-algebra =
        super.agdaPackages.functional-linear-algebra.override ({
          standard-library = self.agdaPackages.standard-library;
        });
    };
  });

in import (builtins.fetchTarball {
  url =
    "https://github.com/NixOS/nixpkgs/archive/1c65a509fbbc17a2853a657ea1391de0aab9e793.tar.gz";
  sha256 = "16393rlq9zq8cs3hapd614bjchmxzkfzn9nawa81rxc7zb2khwqm";
}) { overlays = [ agda-standard-library-overlay ]; }
