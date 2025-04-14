{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    crane = {
      url = "github:ipetkov/crane";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    hax.url = "github:hacspec/hax";
  };
  outputs = inputs: inputs.flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import inputs.nixpkgs { inherit system; };
      # Make an overrideable package.
      t13 = { python3, craneLib, hax, runCommand, cargoLock }:
        let
          src = runCommand "t13-src" { } ''
            cp -r ${./.} $out
            chmod u+w $out
            rm -f $out/Cargo.lock
            cp ${cargoLock} $out/Cargo.lock
          '';
          cargoArtifacts = craneLib.buildDepsOnly { inherit src; };
        in
        craneLib.buildPackage {
          inherit src cargoArtifacts;
          buildInputs = [
            hax
            python3
          ];
          buildPhase = ''
            python hax-driver.py extract-fstar
            python hax-driver.py extract-proverif
          '';
          installPhase = "cp -r . $out";
          doCheck = false;
        };
      hax = inputs.hax.packages.${system}.default;
      craneLib = inputs.crane.mkLib pkgs;
    in
    {
      # Takes the lockfile as input.
      packages.default = cargoLock: pkgs.callPackage t13 { inherit hax craneLib cargoLock; };
      devShells.default = craneLib.devShell { };
    }
  );
}
