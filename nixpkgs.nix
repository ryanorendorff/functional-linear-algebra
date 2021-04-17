# nixpkgs unstable channel from April 16th, 2021

let

  # Temporary workaround while Agda standard library is an RC.
  agda-standard-library-1-6-overlay = (self: super: {
    agdaPackages = super.agdaPackages // {
      standard-library = super.agdaPackages.standard-library.overrideAttrs
        (old: {
          version = "1.6";
          src = super.fetchFromGitHub {
            repo = "agda-stdlib";
            owner = "agda";

            # v1.6-rc1
            rev = "bfb790f8d07e96710cabf5915af4c51b2a1b9643";
            sha256 = "1vb84jqv3qpbd40ir1wj3rwj3wmzs8s57whwl4hssk5r8dimxng3";
          };
        });

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
