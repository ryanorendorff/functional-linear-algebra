let

  use-overlay-standard-library = true;

in pkgs:
if use-overlay-standard-library then {
  version = "1.6";
  src = pkgs.fetchFromGitHub {
    repo = "agda-stdlib";
    owner = "agda";

    # v1.6-rc1
    rev = "bfb790f8d07e96710cabf5915af4c51b2a1b9643";
    sha256 = "1vb84jqv3qpbd40ir1wj3rwj3wmzs8s57whwl4hssk5r8dimxng3";
  };
} else
  { }

