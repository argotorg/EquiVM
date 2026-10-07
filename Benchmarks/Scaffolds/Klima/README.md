# KlimaDAO KlimaToken Benchmark

Source: [`src/protocol/tokens/regular/KlimaToken.sol`](contracts/KlimaToken.sol) from
[`KlimaDAO/klimadao-solidity`](https://github.com/KlimaDAO/klimadao-solidity/tree/0eb4770c1e9cbead8dd23ef0c23a9a27d761d029)
commit `0eb4770c1e9cbead8dd23ef0c23a9a27d761d029`.

Artifacts reproduce the pinned upstream `forge build src/protocol/tokens/regular/KlimaToken.sol` build, including metadata.
The [`foundry.toml`](https://github.com/KlimaDAO/klimadao-solidity/blob/0eb4770c1e9cbead8dd23ef0c23a9a27d761d029/foundry.toml) build uses
Solidity 0.7.5, optimizer enabled with 800 runs, Istanbul EVM, default IPFS metadata,
and the complete remapping set, including mappings discovered from recursively installed
submodules at their pinned commits. This follows the README/CI Foundry build; the repository
also contains a separate Hardhat configuration with different optimizer settings.

Both creation and runtime bytecode were compared byte-for-byte with the actual upstream build.
The vendored Solidity source contents are unchanged.

Compiler: `0.7.5+commit.eb77ed08.Linux.g++`. Build tool versions, configuration/lockfile hashes,
canonical source paths, complete compiler settings, and expected bytecode hashes are in
[`build.json`](build.json). The compiler inputs retain upstream source names even where the
vendored directory layout differs.

Reproduce from the repository root with the matching solc binary:

```bash
python3 scripts/regenerate_scaffold_artifacts.py \
  Benchmarks/Scaffolds/Klima/build.json --solc /path/to/solc-0.7.5
```

Add `--check` to verify without writing. This replays the target's source closure through solc
standard JSON; its creation/runtime output is required to match the recorded upstream build.
Additional AST/storage output selection does not change the bytecode.

Artifacts:

- `creation.hex`: 7867 bytes, without constructor arguments.
- `runtime.hex`: 7110 bytes.
- `KlimaToken.abi.json`, `KlimaToken.storage.json`, and `KlimaToken.metadata.json`: compiler outputs.
- `Bytecode.lean`: matching creation/runtime arrays and verified jump-destination tables.
- `artifacts.sha256`: hashes of the generated files, checked from this directory with
  `sha256sum -c artifacts.sha256`. `build.json` separately records hashes of raw bytecode bytes.

`sources.sha256` records vendored Solidity checksums relative to this directory.

Block summaries are generated and type-checked with
[`check_all_benchmark_blocks.py`](../../../scripts/check_all_benchmark_blocks.py).
See the [benchmark build instructions](../../README.md#reproducing-upstream-scaffold-builds)
for the complete command. Generated summaries live outside the source tree.

The creation bytecode contains the runtime verbatim at byte offset 757.

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
  modeled with solc's high-level-call `EXTCODESIZE` guard (`runtime.hex` pc 6361) and its ignored
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
