# UniswapV3Pool Benchmark

Source: [`Benchmarks/UniswapV3Pool/contracts/UniswapV3Pool.sol`](contracts/UniswapV3Pool.sol) from `Uniswap/v3-core` commit `d0831dc6b8a318df3872b6d68f6de135c9f3ec29` (2026-04-30, `ci: harden lint workflow (#1091)`).

Compiled with optimizer enabled:

```bash
/tmp/solc-0.7.6 --optimize --optimize-runs 800 --metadata-hash none --bin --bin-runtime --abi \
  --base-path . --overwrite -o /tmp/uniswap-v3pool-build Benchmarks/UniswapV3Pool/contracts/UniswapV3Pool.sol
```

Compiler: `0.7.6+commit.7338295f.Darwin.appleclang`.

Artifacts:

- `creation.hex`: optimized creation bytecode, 22728 bytes, sha256 `888deca479325b2bdfed6c48f6ced356271fcba13e09d864a2f6986d8097fe43`
- `runtime.hex`: optimized deployed runtime bytecode, 22142 bytes, sha256 `ecd7503ff9ba5cface57946e85117c0c07796c0a5f2d7fe7ec20a54ec254510f`
- `UniswapV3Pool.abi.json`: ABI emitted by solc, sha256 `ad35708734bf3131a452370efa32b747caaca88b3276e9711cfef4b0d7a67c1e`
- `sources.sha256`: sha256 manifest for the vendored Solidity source tree
- `Spec.lean`: Solm AST scaffold with ABI surface and solc storage layout
- `SpecSyntax.lean`: syntax-side wrapper checked definitionally against the AST scaffold
- `Bytecode.lean`: optimized bytecode embedded as `ByteArray`, with `valid_jumps` facts
- `Constructor.lean`: constructor equivalence target, currently `sorry`
- `Correct.lean`: runtime and top-level contract equivalence targets, currently `sorry`

Main source sha256: `d515775b7f3ffe921dd70aca86b8bad16280fa4c122425d82b4dbea4dc564a7a`.

Note: The pool uses constructor-set immutables and a runtime above the Spurious Dragon mainnet size limit; the bytecode artifact is still useful as a framework stress benchmark. Events are omitted, as in the other benchmarks.
