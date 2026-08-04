# Ripemd160Deployed

Executable Solm behavioral specification and runtime-equivalence proof for the pure Solidity
RIPEMD-160 precompile replacement from `evmification/src/ripemd160`.

The bytecode-to-pure-model proof, including its exact gas theorem, is factored into
`Examples/Precompiles/Ripemd160`. This directory now contains the Solm specification and the
bridges needed only for bytecode-to-Solm equivalence.

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

`Examples/Precompiles/Ripemd160/Bytecode.lean` pins the compiled runtime and
`Examples/Precompiles/Ripemd160/Correct.lean` exposes the direct bytecode theorem.
`Correct.lean` here proves `ripemd160Correct`, covering the successful raw fallback, nonpayable
rejection, allocator-size rejection, and out-of-gas alternative in `runtimeEquivalence`.
Constructor equivalence is out of scope.
