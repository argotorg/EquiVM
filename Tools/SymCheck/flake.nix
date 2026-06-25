{
  description = "EquiVM symbolic side-condition checker";

  inputs = {
    hevm = {
      url = "github:argotorg/hevm/408bf3100f1edbfc489b21b5218332e583e503a7";
      inputs.flake-utils.follows = "flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    foundry = {
      url = "github:shazow/foundry.nix/stable";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-utils.follows = "flake-utils";
    };
    solidity = {
      url = "github:argotorg/solidity/fd3a22656ebe9c91a96ebd846ab7699b5f2e053c";
      flake = false;
    };
    forge-std = {
      url = "github:foundry-rs/forge-std";
      flake = false;
    };
    empty-smt-solver = {
      url = "github:msooseth/empty-smt-solver/74bd120fdb730fde8e44243305e669e5e8a3e02a";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-utils.follows = "flake-utils";
    };
    solc-pkgs = {
      url = "github:hellwolf/solc.nix";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-utils.follows = "flake-utils";
    };
  };

  outputs = { flake-utils, hevm, nixpkgs, foundry, solidity, forge-std, empty-smt-solver, solc-pkgs, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ solc-pkgs.overlay ];
          config = { allowBroken = true; };
        };
        execution-spec-tests-fixtures = pkgs.stdenv.mkDerivation {
          name = "execution-spec-tests-fixtures";
          src = pkgs.fetchurl {
            url = "https://github.com/ethereum/execution-spec-tests/releases/download/v5.4.0/fixtures_develop.tar.gz";
            hash = "sha256-PisC1J/pA+2k/Yyspcvw0TnEcOl+HemoUpmxsDT5cJk=";
          };
          phases = [ "unpackPhase" ];
          unpackPhase = ''
            mkdir -p $out
            tar xf $src --strip-components=1 -C $out "fixtures/blockchain_tests"
            grep -rLZ '"network": "Osaka"' $out | xargs -0 rm
          '';
        };

        hspkgs = ps:
          let
            platformOverrides = hfinal: hprev: {
              with-utf8 =
                if (with ps.stdenv; hostPlatform.isDarwin && hostPlatform.isx86)
                then ps.haskell.lib.compose.overrideCabal (_ : { extraLibraries = [ ps.libiconv ]; }) hprev.with-utf8
                else hprev.with-utf8;
              witch = ps.haskell.lib.doJailbreak hprev.witch;
            };

            localOverrides = hfinal: hprev: {
              hevm =
                ps.lib.pipe
                  ((hfinal.callCabal2nix "hevm" hevm.outPath {
                    secp256k1 = ps.secp256k1;
                  }).overrideAttrs (_: {
                    HEVM_SOLIDITY_REPO = solidity;
                    HEVM_ETHEREUM_TESTS_REPO = "${execution-spec-tests-fixtures}/blockchain_tests";
                    HEVM_FORGE_STD_REPO = forge-std;
                    DAPP_SOLC = "${solc}/bin/solc";
                  }))
                  [
                    ps.haskell.lib.dontCheck
                    (ps.haskell.lib.compose.addTestToolDepends (testDeps ++ [ (hspkgs ps).cabal-install ]))
                  ];
              equivm-symcheck = hfinal.callCabal2nix "equivm-symcheck" ./. {};
            };
          in ps.haskellPackages.override {
            overrides = ps.lib.composeExtensions platformOverrides localOverrides;
          };
        hsPkgs = hspkgs pkgs;

        solc = solc-pkgs.mkDefault pkgs pkgs.solc_0_8_31;
        testDeps = [
          solc
          foundry.defaultPackage.${system}
          pkgs.go-ethereum
          pkgs.z3
          pkgs.cvc5
          pkgs.git
          pkgs.bitwuzla
        ];
        libraryPath = pkgs.lib.makeLibraryPath [ pkgs.libff pkgs.secp256k1 pkgs.gmp ];
        hevmPkg =
          pkgs.haskell.lib.compose.overrideCabal (old: {
            configureFlags = (old.configureFlags or []) ++ [ "-fci" "-O2" ];
          }) hsPkgs.hevm;
      in {
        packages.default = hsPkgs.equivm-symcheck;

        devShells.default = hsPkgs.shellFor {
          packages = ps: [
            hevmPkg
            ps.equivm-symcheck
          ];

          buildInputs = [
            pkgs.curl
            pkgs.mdbook
            pkgs.mdbook-mermaid
            pkgs.yarn
            hsPkgs.cabal-install
            hsPkgs.eventlog2html
            hsPkgs.haskell-language-server
            empty-smt-solver.packages.${system}.default
          ] ++ testDeps;

          HEVM_SOLIDITY_REPO = solidity;
          DAPP_SOLC = "${solc}/bin/solc";
          HEVM_FORGE_STD_REPO = forge-std;
          LD_LIBRARY_PATH = libraryPath;
          withHoogle = true;

          shellHook = pkgs.lib.optionalString pkgs.stdenv.isDarwin ''
            export DYLD_LIBRARY_PATH="${libraryPath}"
          '';
        };
      });
}
