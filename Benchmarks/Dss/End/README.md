# MakerDAO/Sky DSS End Benchmark

This benchmark uses the unmodified upstream DSS `End` source from MakerDAO/Sky:

- Repository requested: `makerdao/dss`
- Canonical GitHub redirect: `sky-ecosystem/dss`
- Commit: `fa4f6630afb0624d04a003e920b0d71a00331d98`
- Commit date: `2022-05-18T14:07:24Z`
- Path: `src/end.sol`
- Source URL:
  `https://raw.githubusercontent.com/sky-ecosystem/dss/fa4f6630afb0624d04a003e920b0d71a00331d98/src/end.sol`
- Solidity pragma: see `contracts/end.sol`

Artifacts were generated locally with optimizer enabled and metadata hash disabled:

```bash
/tmp/solc-0.6.12 --optimize --optimize-runs 200 --metadata-hash none \
  --bin --bin-runtime --abi --ast-json --storage-layout \
  -o /tmp/equivm-dss-end-build --overwrite \
  Benchmarks/Dss/End/contracts/end.sol
```

Compiler:

```text
0.6.12+commit.27d51765.Darwin.appleclang
```

Generated artifacts and scaffold files:

- `contracts/end.sol`: exact fetched upstream Solidity source.
- `end.sol.ast.json`: Solidity AST JSON emitted by solc.
- `End.storage.json`: solc storage layout for this contract.
- `creation.hex`: optimized creation bytecode.
- `runtime.hex`: optimized deployed runtime bytecode/template.
- `End.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Spec.lean`: Solm benchmark spec entrypoint.
- `SpecSyntax.lean`: Solm notation companion wired to the AST spec.
- `Constructor.lean`: top-level constructor-equivalence theorem target.
- `Correct.lean`: top-level runtime-equivalence theorem target plus whole-contract wrapper.

Source and artifact hashes:

```text
contracts/end.sol        sha256 40eca7c82e6794a4dabfa9b6ae41f177dd3c0bafacefc14f060b88f52667adef
end.sol.ast.json         sha256 cd224334d666fa47fefcc3b4620fa0b273dd635fd33f8a058d0ea3e9a737571e
End.abi.json             sha256 309c3b43e4134aa916e91dc280c7f4928bce8462a44213ea376e1bd33b553094
End.storage.json         sha256 02329353c316fe497d6c6c83c37c7c6b17f75c5f4b18093eec262c4b8decaeab
creation.hex             sha256 cf92a4bb19e8bfea9d35ad01fc0980847ce2ae2ec98257de9981fcc87b7ebb65
runtime.hex              sha256 1b7d4c9cf21f0c8716e4725aa4202528b6c29c1b57efad3c179bb65b790da198
```

Scaffold notes:

- This file was generated as part of the DSS coverage expansion pass on 2026-07-06.
- Events are intentionally omitted from the Solm specs, matching the existing event-bearing DSS
  benchmarks whose equivalence relation ignores logs/substate.
- Proof status is tracked by `endContractCorrect` in `Correct.lean`.

## Dispatcher proof boundaries

The `endReachGroup…FirstArm` theorems in `Dispatch.lean` provide shared
selector-tree prefixes for per-entry reachability proofs. Keep these
opaque theorem boundaries: spelling out the selector-tree traversal inside
each consumer produces deeply nested proof terms that can overflow Lean's
default thread stack. The shared theorems hide the intermediate step and gas
counts behind existential witnesses without changing the reachability claims.

CI checks the five previously overflowing consumers (`Rely`, `Out`, `Bag`,
`Fix`, and `Art`) without increasing the stack size. To check the complete End
constructor and runtime equivalence proofs locally, run:

```bash
lake build Benchmarks.Dss.End.Correct
```
