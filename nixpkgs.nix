# nixpkgs unstable channel from April 16th, 2021
import (builtins.fetchTarball {
  url =
    "https://github.com/NixOS/nixpkgs/archive/e5cc06a1e806070693add4f231060a62b962fc44.tar.gz";
  sha256 = "04543i332fx9m7jf6167ac825s4qb8is0d0x0pz39il979mlc87v";
}) { }

