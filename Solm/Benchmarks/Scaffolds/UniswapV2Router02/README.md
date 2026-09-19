# Uniswap V2 Router02 Benchmark

This benchmark uses the unmodified upstream Uniswap V2 Router02 source and dependencies:

- Periphery repository: `Uniswap/v2-periphery`
- Periphery commit: `ed24991304291297c3b4a52818d02f46a17aa9a2`
- Periphery commit date: `2026-04-02T19:50:49Z`
- Main source path: `contracts/UniswapV2Router02.sol`
- Solidity pragma: `=0.6.6`
- Core dependency repository: `Uniswap/v2-core`
- Core dependency commit: `6a9e7c97860676e0992f22a49665760444c1cdf5`
- Library dependency repository: `Uniswap/solidity-lib`
- Library dependency commit: `c01640b0f0f1d8a85cba8de378cc48469fcfd9a6`

Artifacts were generated locally with optimizer enabled, optimizer runs `999999`, and metadata hash
disabled:

```bash
cd Benchmarks/UniswapV2Router02
/tmp/solc-0.6.6 --optimize --optimize-runs 999999 --metadata-hash none \
  --allow-paths . --bin --bin-runtime --abi --ast-json \
  -o /tmp/equivm-uniswap-v2router02-build --overwrite \
  contracts/UniswapV2Router02.sol
```

Compiler:

```text
0.6.6+commit.6c089d02.Darwin.appleclang
```

Generated artifacts and scaffold files:

- `contracts/UniswapV2Router02.sol`: exact fetched upstream Solidity source.
- `contracts/interfaces/*.sol`, `contracts/libraries/*.sol`, `@uniswap/.../*.sol`: exact fetched
  upstream dependencies used by solc.
- `UniswapV2Router02.sol.ast.json`: Solidity AST JSON emitted by solc.
- `creation.hex`: optimized creation bytecode, 22346 bytes.
- `runtime.hex`: optimized deployed runtime bytecode template, 21955 bytes.
- `UniswapV2Router02.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Immutables.lean`: explicit immutable values and solc immutable-reference offset table for
  `factory` and `WETH`.
- `Spec.lean`: Solm AST benchmark scaffold with full public ABI surface, exact external-call
  selectors, source-shaped router/library helper bodies, and empty storage layout.
- `SpecSyntax.lean`: syntax-side wrapper checked definitionally against the AST scaffold.
- `Constructor.lean`: top-level constructor-equivalence theorem, intentionally `sorry`.
- `Correct.lean`: top-level runtime-equivalence theorem plus whole-contract wrapper, intentionally
  `sorry` at the runtime target.
- `sources.sha256`: sha256 manifest for the vendored Solidity source tree.

Artifact hashes:

```text
creation.hex                    sha256 b5708d99cef982e68b1df296fa0e65b11838c39b52ac7fba0cb741557d188483
runtime.hex                     sha256 3e13bf6f8c31a7df9fb6ce6f1d74aa756e8d080e4d2991e0119b5313bc1e581f
UniswapV2Router02.abi.json      sha256 6e79ecda8373ea27fceeff14d4fd6c587524bf3241cd26919048d6572164cac5
UniswapV2Router02.sol.ast.json  sha256 d714c74cc38e1e58057e5184f32b605f80dd4b0abfdd6110f9dbae8a40ed2db8
```

Scaffold notes:

- The contract has no storage. Its only persistent constructor data are the immutable `factory` and
  `WETH` addresses.
- `runtime.hex` is solc's deployed runtime template with zeroed immutable references. Concrete
  runtime correctness is stated for `patchRuntime uniswapV2Router02Bytecode (patches v)`.
- The source uses dynamic calldata/memory arrays, `for` loops, `abi.encodePacked`, `keccak256`,
  raw TransferHelper calls, typed pair/factory/WETH/ERC20 calls, payable ETH paths, and a payable
  `receive` restricted to WETH.
- No change to `Reasoning/` or `Solm/` was needed for this scaffold to build. The likely proof
  hotspots are CREATE2 `pairFor`, the chained `getAmountsIn`/`getAmountsOut` loops, TransferHelper
  raw-call return decoding, and the optimized router dispatcher.
