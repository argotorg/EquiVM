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
        symcheckPkg = pkgs.haskell.lib.dontCheck hsPkgs.equivm-symcheck;
        portableBundle =
          let
            closure = pkgs.closureInfo { rootPaths = [ symcheckPkg ]; };
          in pkgs.stdenv.mkDerivation {
            pname = "equivm-symcheck-portable-bundle";
            version = "0.1.0.0";
            dontUnpack = true;
            dontPatchShebangs = true;
            nativeBuildInputs = [ pkgs.patchelf ];
            installPhase = ''
              set -euo pipefail

              bundleRoot="$out"
              mkdir -p "$bundleRoot/bin" "$bundleRoot/lib"

              cp ${symcheckPkg}/bin/equivm-symcheck "$bundleRoot/bin/equivm-symcheck-bin"
              chmod u+w "$bundleRoot/bin/equivm-symcheck-bin"

              interpreter="$(patchelf --print-interpreter "$bundleRoot/bin/equivm-symcheck-bin")"
              interpreterBase="$(basename "$interpreter")"
              cp "$interpreter" "$bundleRoot/lib/$interpreterBase"
              chmod u+w "$bundleRoot/lib/$interpreterBase"

              find_library() {
                local needed="$1"
                while IFS= read -r storePath; do
                  for candidate in \
                    "$storePath/lib/$needed" \
                    "$storePath/lib64/$needed" \
                    "$storePath/libexec/$needed" \
                    "$storePath/bin/$needed"
                  do
                    if [ -e "$candidate" ]; then
                      printf '%s\n' "$candidate"
                      return 0
                    fi
                  done
                  found="$(find "$storePath" -maxdepth 4 -type f -name "$needed" 2>/dev/null | head -n1 || true)"
                  if [ -n "$found" ]; then
                    printf '%s\n' "$found"
                    return 0
                  fi
                done < ${closure}/store-paths
                return 1
              }

              scan_elf() {
                local elf="$1"
                local needed src dest
                while IFS= read -r needed; do
                  [ -n "$needed" ] || continue
                  dest="$bundleRoot/lib/$needed"
                  if [ ! -e "$dest" ]; then
                    src="$(find_library "$needed")"
                    cp "$src" "$dest"
                    chmod u+w "$dest"
                    if patchelf --print-needed "$dest" >/dev/null 2>&1; then
                      scan_elf "$dest"
                    fi
                  fi
                done < <(patchelf --print-needed "$elf" || true)
              }

              scan_elf "$bundleRoot/bin/equivm-symcheck-bin"

              patchelf --set-rpath '$ORIGIN/../lib' "$bundleRoot/bin/equivm-symcheck-bin"
              for libFile in "$bundleRoot"/lib/*; do
                if [ "$(basename "$libFile")" = "$interpreterBase" ]; then
                  continue
                fi
                if patchelf --print-needed "$libFile" >/dev/null 2>&1; then
                  patchelf --set-rpath '$ORIGIN' "$libFile"
                fi
              done

              cat > "$bundleRoot/bin/equivm-symcheck" <<EOF
              #!/bin/sh
              set -eu
              script_dir="\$(CDPATH= cd -- "\$(dirname -- "\$0")" && pwd)"
              exec "\$script_dir/../lib/$interpreterBase" \
                --library-path "\$script_dir/../lib" \
                "\$script_dir/equivm-symcheck-bin" \
                "\$@"
              EOF
              chmod +x "$bundleRoot/bin/equivm-symcheck"

              cat > "$bundleRoot/README-portable.txt" <<EOF
              This is a standalone equivm-symcheck bundle.

              Run:

                ./bin/equivm-symcheck --help

              The launcher uses the bundled dynamic loader and shared libraries,
              so this bundle can run outside the originating Nix environment on
              a compatible Linux x86_64 host.
              EOF
            '';
          };
        portableTarball = pkgs.runCommand "equivm-symcheck-portable-${system}.tar.gz"
          { nativeBuildInputs = [ pkgs.gnutar pkgs.gzip ]; }
          ''
            mkdir -p "$out"
            tar -C ${portableBundle} -czf "$out/equivm-symcheck-portable-${system}.tar.gz" .
          '';
      in {
        packages.default = symcheckPkg;
        packages."portable-bundle" = portableBundle;
        packages."portable-tarball" = portableTarball;

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
