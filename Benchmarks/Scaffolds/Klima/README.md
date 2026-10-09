# KlimaDAO KlimaToken Benchmark

This benchmark uses the unmodified upstream KlimaToken source from KlimaDAO:

- Repository: `KlimaDAO/klimadao-solidity`
- Commit: `0eb4770c1e9cbead8dd23ef0c23a9a27d761d029`
- Commit date: `2024-12-13T22:53:04Z`
- Path: `src/protocol/tokens/regular/KlimaToken.sol`
- Source URL:
  `https://raw.githubusercontent.com/KlimaDAO/klimadao-solidity/0eb4770c1e9cbead8dd23ef0c23a9a27d761d029/src/protocol/tokens/regular/KlimaToken.sol`
- Solidity pragma: `0.7.5`

Artifacts were generated locally with optimizer enabled and metadata hash disabled:

```bash
solc-0.7.5 --optimize --optimize-runs 200 --metadata-hash none \
  --bin --bin-runtime --abi --storage-layout \
  -o /tmp/klima-build --overwrite Benchmarks/Klima/contracts/KlimaToken.sol
```

Compiler:

```text
0.7.5+commit.eb77ed08.Darwin.appleclang
```

(`solc 0.7.5` fetched from `binaries.soliditylang.org/macosx-amd64`, sha256
`1c100ce86a3167fd4c194290aafec0d3d94fe86c7a1aa0837c1346cc93d8b6ce`.)

Generated artifacts and scaffold files:

- `contracts/KlimaToken.sol`: exact fetched upstream Solidity source (single self-contained file).
- `creation.hex`: optimized creation bytecode (7732 bytes).
- `runtime.hex`: optimized deployed runtime bytecode (6975 bytes).
- `KlimaToken.abi.json`: ABI emitted by solc (30 functions + implicit constructor).
- `KlimaToken.storage.json`: storage layout emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `StringLayout.lean`: per-contract pre-0.8 compact-string read/write hook for `_name`/`_symbol`.
- `Spec.lean`: Solm AST benchmark spec.
- `Constructor.lean`: top-level constructor-equivalence theorem (`sorry`).
- `Correct.lean`: top-level runtime-equivalence theorem plus whole-contract wrapper (`sorry`).

Source and artifact hashes are recorded in `sources.sha256`. Fresh solc output is byte-identical to
the checked-in `creation.hex`/`runtime.hex`, and the checked-in runtime is a verbatim substring of the
creation bytecode at byte offset 757 (there are no immutables, so creation returns the runtime
verbatim).

Target theorem: `Benchmarks.Klima.klimaContractCorrect`.

## Scaffold notes

`KlimaToken` is the full inherited contract: OpenZeppelin-style ERC20 with `SafeMath`, EIP-2612
`permit`, `Ownable`/`VaultOwned` access control, and a `TWAPOracleUpdater` layer with an
`EnumerableSet.AddressSet` of TWAP sources.

- Storage layout is transcribed from solc's `storage-layout`: `_balances` slot 0, `_allowances`
  slot 1, `_totalSupply` slot 2, `_name` slot 3, `_symbol` slot 4, `_decimals` slot 5, `_nonces`
  slot 6, `DOMAIN_SEPARATOR` slot 7, `_owner` slot 8, `_vault` slot 9, the `AddressSet` `_values`
  (`bytes32[]`) slot 10 and `_indexes` (`mapping(bytes32 => uint256)`) slot 11, `twapOracle` slot 12,
  `twapEpochPeriod` slot 13.
- `_name`/`_symbol` are mutable compact `string` storage read/written through the pre-0.8 **total**
  header decode in `StringLayout.lean` (the deployed getters do no ≥0.8 header validation). Both
  values are short (`"Klima DAO"` = 9 bytes, `"KLIMA"` = 5 bytes). `_decimals` is a `uint8` storage
  read.
- `_nonces` (`mapping(address => Counters.Counter)`) is modeled as `mapping(address => uint256)`: the
  single-word `Counter._value` at offset 0 has the identical slot `keccak(addr ‖ 6)`.
- The `EnumerableSet.AddressSet` is flattened to its two solc slots. `addTWAPSource`/`removeTWAPSource`
  model `_add`/`_remove` faithfully, including the `push`, the swap-and-pop `_remove` (dynamic-array
  `pop`, parallel `_indexes` update, `delete`), and the `bytes32(uint256(addr))` set-key form. Dynamic
  array element access is bounds-checked by the framework exactly as solc reverts on out-of-bounds.
- `SafeMath.add`/`sub` are the explicit `require`-guarded uint256 range-cast forms; the pre-0.8
  `Counter.increment` (permit nonce) is unchecked and wraps at 2^256.
- The `_beforeTokenTransfer` hook fires on every `transfer`/`transferFrom`/`mint`/`burn`/`_burnFrom`.
  When `from` (else `to`) is in the set, it makes an external `twapOracle.updateTWAP(...)` `CALL`,
  modeled with solc's high-level-call `EXTCODESIZE` guard (`runtime.hex` pc 6235) and its ignored
  `bool` return decoded through the legacy coder (a `returndatasize >= 32` size check, matching the
  discarded runtime decode). The `ITWAPOracle` selector is in `klimaExternalABI`.
- `permit` is represented with the EIP-712 digest construction (`abi.encode` over word-aligned
  operands, `uint16(0x1901)` prefix) and an `ecrecover` precompile static call to address `0x01`,
  reusing the Dai `permit` shape. `PERMIT_TYPEHASH` is the checked constant
  `keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)")`;
  `DOMAIN_SEPARATOR` is computed in the constructor from `chainid()` and the just-set name.
- The config uses legacy solc ABI decoding (`DecodeMode.legacySolc05`): 0.7.5 defaults to ABI coder
  v1 (no `pragma experimental ABIEncoderV2`).
- Events are omitted consistently with the framework's substate/log abstraction. `_burnFrom` is
  (accidentally) `public` in the source and is included in the ABI surface with the same body
  `burnFrom` delegates to.
