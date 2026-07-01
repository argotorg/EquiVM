# Gnosis MultiSigWallet Benchmark

This benchmark uses the upstream Gnosis `MultiSigWallet.sol` contract.

## Source

- Upstream repository: <https://github.com/gnosis/MultiSigWallet>
- Source file: `contracts/MultiSigWallet.sol`
- Pinned commit: `90639984c960d281bed3e0a5d56dd4adcb9407c4`
- Commit date: `2021-08-24T15:56:50Z`
- Checked-in source: `Benchmarks/GnosisMultiSig/MultiSigWallet.sol`
- Source SHA-256: `3af8e4f195a884097a8d3e7a4c2dffa59bf2659eeab4657840ff40667fa4a855`

## Compilation

The checked-in bytecode was produced from the checked-in Solidity file, not from a temporary path:

```bash
/tmp/solc-0.4.26 --optimize --optimize-runs 200 --bin --bin-runtime --abi \
  -o /tmp/multisig-build-repo Benchmarks/GnosisMultiSig/MultiSigWallet.sol
```

Compiler:

```text
solc, the solidity compiler commandline interface
Version: 0.4.26+commit.4563c3fc.Darwin.appleclang
```

Compiler binary SHA-256:

```text
bc956645b792dcbb8f820b8010a8d4ec1e188f7b40c6af951a436da4c13ae677
```

Expected Solidity warnings are the legacy 0.4.x warnings for constructor syntax, event invocation
without `emit`, and fallback visibility.

## Artifacts

- `creation.hex`: optimized `--bin`, 5845 bytes, SHA-256
  `2d40184ccd30210d1c2c3e5939a7d47d5bc14da5774d0123c7e3b27008aa3fee`
- `runtime.hex`: optimized `--bin-runtime`, 5315 bytes, SHA-256
  `31dddea3816759c59617f64a5eb25c99ba4f48ccdf9bbfd3568363b41b6ddbd3`
- `MultiSigWallet.abi.json`: solc ABI, SHA-256
  `39401071b306d13610235a62ad470c3b172220f0edf0e2d714caa5cdb2b92e98`

`Bytecode.lean` embeds the optimized runtime and creation bytecode with `valid_jumps` facts computed
from the byte arrays.

## Lean Files

- `Spec.lean`: Solm AST scaffold for the public ABI surface, storage declarations, constructor, and
  internal helpers.
- `SpecSyntax.lean`: syntax-frontend companion for the fragments currently supported by
  `Solm.Notation`.
- `Bytecode.lean`: optimized creation/runtime bytecode and jumpdest facts.
- `Constructor.lean`: top-level constructor-equivalence theorem, intentionally `sorry`.
- `Correct.lean`: top-level runtime-equivalence theorem plus whole-contract wrapper.

## Scaffold Notes

- Events are omitted, following the existing examples.
- The payable fallback `function() payable { ... }` is modeled as a storage no-op; its `Deposit`
  event is ignored by the current equivalence.
- `Transaction.data` is a dynamic `bytes` field in storage, represented with Solidity compact
  bytes layout at `transactions[transactionId].data`.
- The assembly `external_call` is represented by `lowLevelCall`; the exact solc gas subtraction
  `sub(gas, 34710)` is not modeled in the Solm surface yet.
