# nixpkgs unstable channel from July 24th, 2021
# specifically set to test the bump to the agda-stdlib 1.7

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
    "https://github.com/NixOS/nixpkgs/archive/703882fb577fc939ace7cdc3197440f306380b9b.tar.gz";
  sha256 = "0141ip3wfaj1pvh2681kdhhj4lwwwjdrchmgg5xnd9zmazvk2nsc";
}) { overlays = [ agda-standard-library-overlay ]; }
