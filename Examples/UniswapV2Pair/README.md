# Uniswap V2 Pair Benchmark

This benchmark uses the unmodified upstream `UniswapV2Pair` contract from:

- Repository: `Uniswap/v2-core`
- Tag: `v1.0.1`
- Solidity pragma: `=0.5.16`

The upstream Solidity import tree is preserved under `contracts/`.
`UniswapV2Pair.sol` at this directory's top level is a byte-for-byte copy of the compiled
entrypoint `contracts/UniswapV2Pair.sol`, added so the benchmark's main Solidity source is visible
next to the Lean files.  The bytecode was generated from the `contracts/` path below so the original
relative imports are preserved exactly.

Artifacts were generated locally with optimizer enabled:

```bash
/tmp/solc-0.5.16 --optimize --optimize-runs 200 --bin --bin-runtime --abi \
  -o /tmp/uniswap-v2pair-build Examples/UniswapV2Pair/contracts/UniswapV2Pair.sol
```

Compiler: `0.5.16+commit.9c3226ce`.

Generated artifacts:

- `creation.hex`: optimized creation bytecode.
- `runtime.hex`: optimized deployed runtime bytecode.
- `UniswapV2Pair.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: runtime bytecode as a Lean `ByteArray` plus the verified `JUMPDEST` set.
- `Spec.lean`: full ABI/storage benchmark scaffold.
- `Correct.lean`: top-level runtime-equivalence theorem routed to the per-function proof files.

The current Solm source bodies are a proof scaffold.  Storage layout and ABI coverage are explicit,
but the largest AMM paths still need proof-ready elaboration for legacy-solc details such as
`ecrecover`, `Math.sqrt`, exact ABI-encoded low-level transfer calldata, and string return encoding.
