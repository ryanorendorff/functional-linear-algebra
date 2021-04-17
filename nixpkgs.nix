# nixpkgs unstable channel from April 16th, 2021

let

  # Temporary workaround while Agda standard library is an RC.
  agda-standard-library-1-6-overlay = (self: super: {
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
    "https://github.com/NixOS/nixpkgs/archive/e5cc06a1e806070693add4f231060a62b962fc44.tar.gz";
  sha256 = "04543i332fx9m7jf6167ac825s4qb8is0d0x0pz39il979mlc87v";
}) { overlays = [ agda-standard-library-1-6-overlay ]; }
