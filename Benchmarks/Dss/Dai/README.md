# MakerDAO DSS Dai Benchmark

This benchmark uses the unmodified upstream DSS Dai source from MakerDAO/Sky:

- Repository requested: `makerdao/dss`
- Canonical GitHub redirect: `sky-ecosystem/dss`
- Commit: `fa4f6630afb0624d04a003e920b0d71a00331d98`
- Commit date: `2022-05-18T14:07:24Z`
- Path: `src/dai.sol`
- Source URL:
  `https://raw.githubusercontent.com/sky-ecosystem/dss/fa4f6630afb0624d04a003e920b0d71a00331d98/src/dai.sol`
- Solidity pragma: `^0.6.12`

Artifacts were generated locally with optimizer enabled and metadata hash disabled:

```bash
/tmp/solc-0.6.12 --optimize --optimize-runs 200 --metadata-hash none \
  --bin --bin-runtime --abi --ast-json -o /tmp/dss-dai-build \
  Benchmarks/Dss/Dai/contracts/dai.sol
```

Compiler:

```text
0.6.12+commit.27d51765.Darwin.appleclang
```

Generated artifacts and scaffold files:

- `contracts/dai.sol`: exact fetched upstream Solidity source.
- `dai.sol.ast.json`: Solidity AST JSON emitted by solc.
- `creation.hex`: optimized creation bytecode.
- `runtime.hex`: optimized deployed runtime bytecode.
- `Dai.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Spec.lean`: Solm AST benchmark scaffold.
- `SpecSyntax.lean`: Solm notation presentation, checked by `rfl` against the AST spec.
- `Constructor.lean`: top-level constructor-equivalence theorem, intentionally `sorry`.
- `Correct.lean`: top-level runtime-equivalence theorem plus whole-contract wrapper,
  intentionally `sorry` at the runtime target.

Source and artifact hashes:

```text
contracts/dai.sol sha256 d37e84405c5743b956ed14e46ecb7b0503b53f2454e14eb2235653eda89876db
creation.hex      sha256 9c11f72e62a36a3a6a502c2884c7bec52fec77baaec457b211087806931b1628
runtime.hex       sha256 22b89cfb5798cf6b1909e68a689e6347ae58afcc3fbd6324871b03e2bf314661
Dai.abi.json      sha256 f7d6a7572a14fbc3b6bf0fa87092ffcd6c41d3a0f75c1ca4efd5de08d5d67267
dai.sol.ast.json  sha256 68b45d43995fcbdda54b2666514620636c50d762354db234f2e687fbf4ec58d0
```

Scaffold notes:

- The named ABI surface is explicit, including constants, public storage getters, auth functions,
  ERC20 actions, aliases, and `permit`.
- Storage layout is transcribed from solc's `storage-layout`: `wards` slot 0, `totalSupply` slot 1,
  `balanceOf` slot 2, `allowance` slot 3, `nonces` slot 4, and `DOMAIN_SEPARATOR` slot 5.
- Maker's Solidity 0.6 checked `add`/`sub` helpers are modeled as explicit `require`s around
  uint256 range-cast arithmetic.
- The `permit` nonce post-increment is modeled as unchecked uint256 arithmetic, matching Solidity
  0.6 and the optimized bytecode.
- The config uses legacy solc ABI decoding for the 0.6 optimized wrappers.
- `DOMAIN_SEPARATOR` is modeled using static-word `abiEncodePacked` operands to represent the
  source `abi.encode(...)` over fixed-width values.
- `permit` is represented with its EIP-712 digest construction and an `ecrecover` precompile-shaped
  static call.  The reusable proof work here should isolate precompile-call, ABI-word encoding, and
  `ecrecover` return-data lemmas rather than baking them into one contract-specific proof.
- The legacy ABI decoder now masks narrow integer calldata words, matching the optimized solc 0.6
  wrapper for `permit`'s `uint8 v` argument.
- Selector bytes, if needed during proof development, should follow the `Examples/*/Trusted.lean`
  convention: trust only the opaque Keccak selector byte computations, then prove dispatch facts
  from those axioms.
