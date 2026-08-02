# Ripemd160Deployed

Executable Solm behavioral specification and runtime-equivalence scaffold for the pure Solidity
RIPEMD-160 precompile replacement from `evmification/src/ripemd160`.

## Pinned build

- Compiler: `solc 0.8.35+commit.47b9dedd`
- EVM version: Osaka
- Via IR: enabled
- Optimizer: enabled, 10,000 runs

```bash
solc-0.8.35 --via-ir --optimize --optimize-runs 10000 --evm-version osaka \
  --bin --bin-runtime --abi --storage-layout --ast-compact-json \
  -o /tmp/ripemd160-build --overwrite \
  Examples/Ripemd160/contracts/Ripemd160Deployed.sol
```

`SpecSyntax.lean` expresses RIPEMD-160 directly in Solm: message padding, little-endian word
loading, both 80-round compression paths, chaining, and digest serialization. It does not use a
precompile call or a configured hashing primitive. The fallback hashes all raw calldata and returns
12 zero bytes followed by the 20-byte digest.

`Bytecode.lean` pins the compiled runtime used by the equivalence target. `Correct.lean` defines
`runtimeEquivalenceTarget` but deliberately contains no proof. Constructor equivalence is out of
scope.
