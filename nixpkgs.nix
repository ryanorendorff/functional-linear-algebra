# nixpkgs 22.05 from 31st Aug 2022

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
    "https://github.com/NixOS/nixpkgs/archive/067d5d5b89133efcda060bba31f9941c6396e3ee.tar.gz";
  sha256 = "0wyrwrw5fr5b1ss2za37cgwk7hzydy184a49wbqrks5vhpjvfkg7";
}) { overlays = [ agda-standard-library-overlay ]; }
