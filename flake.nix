{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    crane = {
      url = "github:ipetkov/crane";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    hax.url = "github:hacspec/hax";
  };
  outputs =
    inputs:
    let
      system = "x86_64-linux";
      hax = inputs.hax.packages.${system}.default;
      pkgs = import inputs.nixpkgs { inherit system; };
      craneLib = inputs.crane.mkLib pkgs;
      src = ./.;
      cargoArtifacts = craneLib.buildDepsOnly { inherit src; };
      bertie = craneLib.buildPackage {
        inherit src cargoArtifacts;
        buildInputs = [
          hax
          pkgs.python3
        ];
        buildPhase = "python hax-driver.py extract-fstar";
        installPhase = "cp -r . $out";
        doCheck = false;
      };
    in
    {
      packages.${system}.default = bertie;
    };
}
