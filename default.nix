let
  pkgs = import <nixpkgs> {};
in
  pkgs.mkShell {
    packages = with pkgs; [
      python3
      rustup
    ];

    HACL_HOME = "/home/lucas/repos/hacl-star";
    HAX_PROOF_LIBS_HOME = "/home/lucas/repos/hax/latest-core/proof-libs/fstar";
    HAX_LIBS_HOME = "/home/lucas/repos/hax/latest-core/hax-lib/proofs/fstar/extraction";
    FSTAR_HOME = "/home/lucas/repos/hax/latest-core/proof-libs/fstar";
  }
