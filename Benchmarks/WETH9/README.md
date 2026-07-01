# WETH9 Benchmark

This benchmark uses the unmodified canonical WETH9 source from:

- Repository: `gnosis/canonical-weth`
- Path: `contracts/WETH9.sol`
- Source URL: `https://raw.githubusercontent.com/gnosis/canonical-weth/master/contracts/WETH9.sol`
- Solidity pragma: `>=0.4.22 <0.6`

The checked-in `WETH9.sol` is the exact fetched upstream file, including the GPL text after the
contract.

Artifacts were generated locally with optimizer enabled:

```bash
/tmp/solc-0.5.16 --optimize --optimize-runs 200 --bin --bin-runtime --abi \
  -o /tmp/weth9-build Benchmarks/WETH9/WETH9.sol
```

Compiler:

```text
0.5.16+commit.9c3226ce
```

Generated artifacts:

- `creation.hex`: optimized creation bytecode.
- `runtime.hex`: optimized deployed runtime bytecode.
- `WETH9.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Spec.lean`: Solm AST benchmark scaffold.
- `SpecSyntax.lean`: Solm notation presentation, checked by `rfl` against the AST spec.
- `Constructor.lean`: top-level constructor-equivalence theorem, intentionally `sorry`.
- `Correct.lean`: top-level runtime-equivalence theorem plus whole-contract wrapper.

Source and bytecode hashes:

```text
WETH9.sol      sha256 097d1a4258c78e1062798419ecb9c4e60b7327de5213be4bedfa4c1fdd04aa95
creation.hex   sha256 db2920cfa07eab2950a09bc6b4ad7463998b4be5490a345778b6dc3a1c6eb96d
runtime.hex    sha256 f9305212a27f96e0334879d068df59d0fed30ab0afeabd9e5c5b7278ad9a3cbe
```

Current scaffold notes:

- The named ABI surface is explicit.
- The payable fallback `function() external payable { deposit(); }` is modeled as the same storage
  update as `deposit()`.
- `name` and `symbol` use Solidity compact dynamic-string storage: creation initializes slots 0 and
  1, and the runtime getters read those storage values.
- `withdraw` uses `lowLevelCall` plus `require(success)` to model `msg.sender.transfer(wad)`;
  the exact 2300-gas stipend is a later proof/detail refinement.
