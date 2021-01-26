# nixpkgs unstable channel from November 25th, 2020
import (builtins.fetchTarball {
  url =
    "https://github.com/NixOS/nixpkgs/archive/9af5a55a1960fc31f2f671419a28d4a65ac18dfb.tar.gz";
  sha256 = "1hxdcggxkz2a8sc31hs7ka0fjbp4a90rkgfr8x629mm5w9pzniws";
}) { }

