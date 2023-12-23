{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/master";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        nixpkgs-patched = (import nixpkgs { inherit system; }).applyPatches {
          name = "patches";
          src = nixpkgs;
          patches = [ ./nix-patches/273765.patch ];
        };
        pkgs = import nixpkgs-patched { inherit system; };
      in { packages.default = pkgs.callPackage ./default.nix { }; });
}
