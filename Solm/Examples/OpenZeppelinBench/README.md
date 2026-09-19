# OpenZeppelin Benchmarks

These benchmark inputs use OpenZeppelin Contracts sources from the `master` branch snapshot fetched
on 2026-06-23 and compile with:

```bash
solc --optimize --evm-version shanghai
```

Each benchmark folder contains:

- `*.sol`: the concrete benchmark target when the OpenZeppelin module is abstract or needs fixed
  constructor parameters.
- `creation.hex`: exact creation bytecode for the benchmark target.
- `runtime.hex`: exact deployed runtime bytecode for the benchmark target.
- `Spec.lean`: the Solm-level contract specification and Solidity storage layout.
- `Bytecode.lean`: the same deployed runtime bytecode as a Lean `ByteArray`, plus its `D_J`
  jump-destination theorem.

`VestingWallet` uses a concrete no-argument wrapper with `start = 0` and `duration = 365 days`.
Its runtime bytecode has Solidity immutable slots patched to those constructor values.
