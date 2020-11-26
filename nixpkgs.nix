# nixpkgs unstable channel from November 25th, 2020
import (builtins.fetchTarball {
  url =
    "https://github.com/NixOS/nixpkgs/archive/d47eb666b1eb9d43d2bb261d3d9cd2b5a3e147a2.tar.gz";
  sha256 = "0yirimlkifhrmsxxmqrjra7a99mfwkc5p09hamapday8svzdaycv";
}) { }

