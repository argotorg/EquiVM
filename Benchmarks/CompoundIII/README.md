# Compound III Benchmarks

This directory contains two benchmark scaffolds from Compound III Comet:

- `CometRewards`: `contracts/CometRewards.sol`
- `Comet`: `contracts/CometWithExtendedAssetList.sol`

The sources are copied from the upstream `compound-finance/comet` main branch tarball resolved on
2026-07-03 to commit `f766f51583c23acc33b2a7824654ef2029a96804`.

The copied source closure is under `contracts/`, and `sources.sha256` records the exact file hashes.

Compound's `foundry.toml` on that branch pins:

- `solc_version = "0.8.15"`
- `optimizer = true`
- `optimizer_runs = 1`
- `via_ir = true`
- `evm_version = "cancun"`

The bytecode here was generated with the matching compiler version and optimization settings:

```bash
/tmp/solc-0.8.15 --via-ir --optimize --optimize-runs 1 --metadata-hash none \
  --bin --bin-runtime --abi --storage-layout --base-path . --overwrite \
  -o /tmp/equivm-compound-main/build-via-ir \
  contracts/CometRewards.sol contracts/CometWithExtendedAssetList.sol
```

Compiler:

```text
0.8.15+commit.e14f2714.Darwin.appleclang
```

Important note: solc `0.8.15` does not support `--evm-version cancun`, so these artifacts use the
compiler's default EVM target for `0.8.15`. Compiling without `--via-ir` fails with a stack-too-deep
compiler error, which is consistent with Compound's `via_ir = true` setting.

AST JSON files were generated with:

```bash
/tmp/solc-0.8.15 --base-path . --ast-compact-json --overwrite \
  -o /tmp/equivm-compound-main/ast \
  contracts/CometRewards.sol contracts/CometWithExtendedAssetList.sol
```

Compiler warnings observed during generation:

- `CometWithExtendedAssetList` has a payable fallback but no receive function.
- `CometWithExtendedAssetList` has an unused local variable `status` at source line 197.

Scaffold notes:

- The Lean files are benchmark scaffolds with constructor and runtime correctness targets left as
  `sorry`.
- `Spec.lean` files expose ABI-shaped transition declarations and solc storage layouts.
- `SpecSyntax.lean` files expose syntax-facing contract values checked by `rfl` against the AST
  specs.
- Selector bytes, if needed in downstream proofs, should follow the `Examples/*/Trusted.lean`
  convention: trust only opaque Keccak selector byte computations, then prove dispatch facts from
  those axioms.
- `CometRewards` has been handed off for proof and semantically audited for the current equivalence
  relation. Its 0.8.15 via-IR artifacts match the Lean byte arrays, its packed storage layout
  matches the spec, and its no-return `accrueAccount` calls include the solc `EXTCODESIZE` guards
  in the spec.
- The Comet runtime artifact is solc's unpatched `--bin-runtime` template. Its immutable template
  values are explicit in `Comet/Immutables.lean`, and its payable fallback is modeled in
  `Comet/Spec.lean`.
- Comet exposes a parameterized immutable-aware whole-contract wrapper using
  `constructorEquivalenceWith`, but it is still not ready for proof: the constructor spec contains
  placeholders for `numAssets`, asset-list creation, constructor validation, and external-call
  wiring, and several runtime protocol bodies remain source-level scaffolds.
