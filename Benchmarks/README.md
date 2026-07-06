# Benchmark Status

Last updated: 2026-07-06.

This file tracks whether a benchmark is ready to give to a proving agent. "Completed" means the
proof task has been marked done. "Handed off" means the benchmark has been selected for agent proof
work and no current semantic blocker is recorded here. It does not mean the theorem is already
proved.

Sizes are byte counts from checked-in `runtime.hex` and `creation.hex`. ABI surface counts are from
the checked-in `.abi.json` files.

## Size and Readiness Table

| Benchmark | Runtime bytes | Creation bytes | ABI surface | Readiness level | Ready for proof |
| --- | ---: | ---: | --- | --- | --- |
| `Dss/Dai` | 4011 | 4312 | 22 fn + ctor | Completed | Yes |
| `Dss/Vow` | 5150 | 5410 | 24 fn + ctor | Completed | Yes |
| `Dss/Vat` | 6965 | 7021 | 28 fn + ctor | Handed off | Yes |
| `Dss/Pot` | 2595 | 2746 | 17 fn + ctor | Completed | Yes |
| `Dss/Jug` | 2440 | 2560 | 12 fn + ctor | Completed | Yes |
| `Dss/Spot` | 2178 | 2320 | 12 fn + ctor | Ready for proof | Yes |
| `Dss/LinearDecrease` | 1128 | 1217 | 6 fn + ctor | Ready for proof | Yes |
| `Dss/StairstepExponentialDecrease` | 1433 | 1522 | 7 fn + ctor | Ready for proof | Yes |
| `Dss/ExponentialDecrease` | 1321 | 1410 | 6 fn + ctor | Ready for proof | Yes |
| `Dss/GemJoin` | 2022 | 2326 | 11 fn + ctor | Ready for proof | Yes |
| `Dss/DaiJoin` | 1733 | 1876 | 9 fn + ctor | Ready for proof | Yes |
| `Dss/Cat` | 3873 | 3999 | 16 fn + ctor | Scaffolded | No |
| `Dss/Clipper` | 9360 | 9707 | 29 fn + ctor | Scaffolded | No |
| `Dss/Cure` | 3875 | 3971 | 20 fn + ctor | Scaffolded | No |
| `Dss/Dog` | 4745 | 4927 | 17 fn + ctor | Scaffolded | No |
| `Dss/End` | 10265 | 10359 | 32 fn + ctor | Scaffolded | No |
| `Dss/Flapper` | 5008 | 5216 | 20 fn + ctor | Scaffolded | No |
| `Dss/Flipper` | 6386 | 6596 | 19 fn + ctor | Scaffolded | No |
| `Dss/Flopper` | 4780 | 5000 | 20 fn + ctor | Scaffolded | No |
| `WETH9` | 1763 | 2055 | 11 fn + fallback/receive | Completed | Yes |
| `EAS/Attester` | 3186 | 3371 | 4 fn + ctor | Handed off | Yes |
| `ERC721` | 1482 | 1510 | 7 fn + empty ctor | Ready for proof | Yes |
| `OpenZeppelinBench/VestingWallet` | 2277 | 2485 | 14 fn + ctor + receive | Ready for proof | Yes |
| `OpenZeppelinBench/TimelockController` | 6509 | 7161 | 28 fn + ctor + receive | Handed off | Yes |
| `CompoundIII/CometRewards` | 4063 | 4207 | 11 fn + ctor | Handed off | Yes |
| `Safe` | 11874 | 11907 | 31 fn + ctor + fallback/receive | Handed off | Yes |
| `UniswapV2Router02` | 21955 | 22346 | 24 fn + ctor + fallback/receive | Prep needed | No |
| `UniswapV3Pool` | 22142 | 22728 | 26 fn + ctor | Handed off | Yes |
| `CompoundIII/Comet` | 18655 | 21528 | 68 fn + ctor + fallback/receive | Prep needed | No |
| `Auction` | 6150 | 6179 | 20 fn + empty ctor | Handed off | Yes |
| `Klima` | 6975 | 7732 | 30 fn + ctor | Ready for proof | Yes |

## Completed / ready for proof / handed off

- `Dss/Dai`: completed. Target theorem: `Benchmarks.Dss.Dai.daiContractCorrect`.
  Proof work has been marked done.

- `Dss/Vow`: completed. Target theorem: `Benchmarks.Dss.Vow.vowContractCorrect`.
  Proof work has been marked done.

- `Dss/Vat`: handed off. Target theorem:
  `Benchmarks.Dss.Vat.vatContractCorrect`. Fresh solc output exactly matches the checked-in Lean
  creation/runtime byte arrays, and the solc storage layout matches the spec. The runtime has no
  external call sites, contract creation, delegate calls, selfdestruct, or high-level-call
  `EXTCODESIZE` guards to model. No semantic blocker is currently known; expected proof work is
  arithmetic helper lemmas, storage-mapping layout lemmas, and the large state-update bodies.

- `Dss/Pot`: completed. Target theorem:
  `Benchmarks.Dss.Pot.potContractCorrect`. Fresh solc output exactly matches the checked-in Lean
  creation/runtime byte arrays, and the solc storage layout matches the spec. The runtime has two
  optimized external-call sites with two `EXTCODESIZE` guards; the spec now models those guards on
  all three source-level `VatLike` calls (`drip`, `join`, `exit`, with `join`/`exit` sharing a
  bytecode call path). Proof work has been marked done.

- `Dss/Jug`: completed. Target theorem:
  `Benchmarks.Dss.Jug.jugContractCorrect`. Fresh solc output exactly matches the checked-in Lean
  creation/runtime byte arrays, and the solc storage layout matches the spec. The runtime has two
  external-call sites with two `EXTCODESIZE` guards; the spec now models those guards on
  `VatLike.ilks` and `VatLike.fold`. Proof work has been marked done.

- `Dss/Spot`: ready for proof, not yet handed off. Target theorem:
  `Benchmarks.Dss.Spot.spotContractCorrect`. Fresh solc output exactly matches the checked-in Lean
  creation/runtime byte arrays, and the solc storage layout matches the spec. The runtime has two
  external-call sites with two `EXTCODESIZE` guards; the spec now models those guards on
  `PipLike.peek` and `VatLike.file`. The `Poke` event is omitted consistently with the framework's
  substate/log abstraction. No semantic blocker is currently known; expected proof work is oracle
  return decoding, conditional arithmetic, and `bytes32` to `uint256` casting.

- `Dss/LinearDecrease`, `Dss/StairstepExponentialDecrease`, and `Dss/ExponentialDecrease`: ready
  for proof, not yet handed off. Target theorems:
  `Benchmarks.Dss.LinearDecrease.linearDecreaseContractCorrect`,
  `Benchmarks.Dss.StairstepExponentialDecrease.stairstepExponentialDecreaseContractCorrect`, and
  `Benchmarks.Dss.ExponentialDecrease.exponentialDecreaseContractCorrect`. Fresh solc output is
  checked in for all three deployable contracts from `src/abaci.sol`; the specs model auth,
  storage layout, `file`, public getters, checked arithmetic, and the source-level price functions
  including the `rpow` loop for the exponential variants.

- `Dss/GemJoin` and `Dss/DaiJoin`: ready for proof, not yet handed off. Target theorems:
  `Benchmarks.Dss.GemJoin.gemJoinContractCorrect` and
  `Benchmarks.Dss.DaiJoin.daiJoinContractCorrect`. Fresh solc output is checked in for both
  deployable contracts from `src/join.sol`; the specs model auth, constructor initialization,
  public getters, cage, join/exit flows, high-level external-call `EXTCODESIZE` guards, and typed
  external ABI hooks for `VatLike`, `GemLike`, and `DSTokenLike`.

- `Dss/Cat`, `Dss/Clipper`, `Dss/Cure`, `Dss/Dog`, `Dss/End`, `Dss/Flapper`, `Dss/Flipper`, and
  `Dss/Flopper`: scaffolded, not ready for proof. Fresh upstream sources, ABI/AST/storage-layout
  artifacts, optimized creation/runtime bytecode, Lean `ByteArray`s, verified `JUMPDEST` sets, and
  top-level theorem targets are checked in and compile. Their current `Spec.lean` files are
  intentionally minimal entrypoints; they still need full source-body transcription before they
  should be handed to a proof agent.

- `WETH9`: completed. Target theorem:
  `Benchmarks.WETH9.weth9ContractCorrect`. Fresh solc output exactly matches the checked-in Lean
  creation/runtime byte arrays. The payable fallback is modeled as `deposit`, and `withdraw` is
  modeled as a value-sending low-level call followed by `require(success)`, matching the single
  runtime `CALL` site. No benchmark-local semantic blocker is currently known under Solm's current
  message-call abstraction; exact 2300-gas stipend precision would be framework-level refinement,
  not missing local scaffold work. Proof work has been marked done.

- `EAS/Attester`: handed off. Target theorem:
  `Benchmarks.EAS.Attester.attesterContractCorrect`. Fresh solc 0.8.26 output exactly matches the
  checked-in Lean creation/runtime byte arrays, and the solc storage layout is empty because `_eas`
  is immutable. The runtime template has four `_eas` immutable patch sites and four typed EAS
  `CALL`s; the spec models the two no-return calls (`revoke`, `multiRevoke`) with their explicit
  `EXTCODESIZE` guards, while `attest` and `multiAttest` rely on return decoding as the bytecode
  does. No semantic blocker is currently known; expected proof work is immutable patching, dynamic
  calldata arrays, tuple ABI encoding, loop bodies, and external-call return decoding.

- `ERC721`: ready for proof, not yet handed off. Target theorem:
  `ERC721.erc721ContractCorrect`. Fresh solc 0.8.35 output with `--metadata-hash none` exactly
  matches the checked-in Lean creation/runtime byte arrays, and the solc storage layout matches the
  four mapping slots in the spec. The source is intentionally the compact ERC721 core only
  (`approve`, `balanceOf`, `getApproved`, `isApprovedForAll`, `ownerOf`, `setApprovalForAll`,
  `transferFrom`); metadata, ERC165, and safe-transfer extensions are not in this benchmark source.
  The spec models the `unchecked` balance decrement/increment with modulo-2^256 wrapping. No
  benchmark-local semantic blocker is currently known; expected proof work is binary-search
  dispatcher routing, mapping slot lemmas, authorization/revert paths, and unchecked arithmetic.

- `OpenZeppelinBench/VestingWallet`: ready for proof, not yet handed off. Target theorem:
  `OpenZeppelinBench.VestingWallet.vestingWalletBenchContractCorrect`. Fresh solc 0.8.35 output
  with `--metadata-hash none` exactly matches the checked-in Lean creation/runtime byte arrays. A
  benchmark-local OpenZeppelin source closure is checked in with only the 14 files needed by
  `VestingWalletBench.sol`. The spec models the payable `receive`, concrete immutable values
  (`start = 0`, `duration = 365 days`), checked arithmetic, `uint64(block.timestamp)` truncation,
  ERC20 `balanceOf` as a static typed call, and `SafeERC20.safeTransfer` as a raw call with optional
  bool return checking plus the empty-return `EXTCODESIZE` guard. No benchmark-local semantic
  blocker is currently known; expected proof work is overloaded ABI dispatch, immutable creation
  patching, checked arithmetic paths, receive/fallback routing, and external-call reasoning.

- `OpenZeppelinBench/TimelockController`: handed off. Target theorem:
  `OpenZeppelinBench.TimelockController.timelockControllerBenchContractCorrect`. Fresh solc 0.8.35
  output with optimizer runs 200, Shanghai EVM, and `--metadata-hash none` is checked in with the
  emitted ABI and storage layout. A benchmark-local OpenZeppelin source closure is checked in with
  the 14 files needed by `TimelockControllerBench.sol`. The spec models the constructor's concrete
  role grants (`msg.sender` admin/proposer/canceller and `address(0)` executor), `_roles`,
  `_timestamps`, `_minDelay`, operation-state predicates, standard `abi.encode(...)` operation-id
  hashing through a benchmark-local ABI hook, batch length checks, payable execution/receive,
  low-level target calls, the reentrancy-sensitive `_afterCall` readiness check, and ERC721/ERC1155
  receiver hooks. Events, custom-error payloads, and bubbled revert bytes are omitted consistently
  with the framework's current log/revert-data abstraction; the event-only loop in `scheduleBatch`
  is omitted for that reason. No benchmark-local semantic blocker is currently known; expected
  proof work is dispatcher routing, nested-role mapping layout, dynamic ABI encoding for
  operation ids, checked timestamp arithmetic, batch call loops, and low-level call reasoning.

- `CompoundIII/CometRewards`: handed off. Target theorem:
  `Benchmarks.CompoundIII.CometRewards.cometRewardsContractCorrect`. Fresh solc 0.8.15 via-IR
  output exactly matches the checked-in Lean creation/runtime byte arrays and ABI; the solc storage
  layout matches the spec, including packed `RewardConfig` fields. The runtime has six
  `STATICCALL` sites, three `CALL` sites, and two `EXTCODESIZE` guards; the spec models the view
  calls as `perm := false` and the two guarded `accrueAccount` calls with explicit code-size
  checks. Events and custom-error payloads are omitted consistently with the framework's
  substate/revert-data abstraction. No semantic blocker is currently known; expected proof work is
  via-IR dispatch, packed storage writes, dynamic calldata arrays, `pow10`/overflow paths, and typed
  external-call return decoding.

- `Safe`: handed off. Target theorem:
  `Benchmarks.Safe.safeContractCorrect`. Fresh solc 0.8.35 output with optimizer runs 200,
  Shanghai EVM, and `--metadata-hash none` exactly matches the checked-in Lean creation/runtime byte
  arrays. The solc storage layout matches the spec, including the singleton, owners/modules
  mappings, nonce/threshold counters, approved-hash mappings, and fixed assembly slots for fallback
  handler, guard, and module guard. The spec models receive/fallback behavior, modern ABI decoding,
  checked arithmetic, high-level-call `EXTCODESIZE` guards where solc emits them, ecrecover's
  zero-address empty-return behavior, module/guard calls, and Safe's storage-access helper via raw
  EVM slots. Events and revert payloads are omitted consistently with the framework's current
  abstraction. No benchmark-local semantic blocker is currently known; expected proof work is
  dispatcher routing, storage-layout/raw-slot lemmas, signature-check paths, module/guard external
  calls, checked arithmetic, and low-level call reasoning.

- `Auction`: handed off. Target theorem:
  `auctionContractCorrect`. Fresh solc 0.8.23 output with optimizer runs 200, Shanghai EVM, and
  `--metadata-hash none` exactly matches the checked-in Lean creation/runtime byte arrays. The
  benchmark-local source closure contains the Nouns interfaces, OpenZeppelin upgradeable v4.4.0
  bases, and OpenZeppelin contracts v4.9.6 interfaces needed to reproduce the artifacts. The solc
  storage layout matches the spec, including OZ gap slots and packed `auction.settled` at slot 211
  offset 20. The spec models the OZ `initializer` top-level/nested flag behavior, checked
  arithmetic, the `mint` try/catch with `Error(string)` ABI-payload validation, high-level-call
  `EXTCODESIZE` guards on `deposit`, `burn`, and `transferFrom`, and the ignored-but-decoded WETH
  `transfer` bool return. No benchmark-local semantic blocker is currently known; expected proof
  work is binary-search dispatcher routing, OZ initializer/reentrancy modifier traces, try/catch
  return/revert decoding, packed storage updates, checked arithmetic, and external-call reasoning.

- `UniswapV3Pool`: handed off. Target theorem:
  `Benchmarks.UniswapV3Pool.uniswapV3PoolContractCorrect`. Large stress benchmark with
  constructor-set immutables and complex pool paths; proof work should expect substantial selector,
  immutable-code, external-call, and body-trace engineering.

- `Klima`: ready for proof, not yet handed off. Target theorem:
  `Benchmarks.Klima.klimaContractCorrect`. Fresh solc 0.7.5 output with optimizer runs 200 and
  `--metadata-hash none` exactly matches the checked-in Lean creation/runtime byte arrays, and the
  solc storage layout matches the spec. There are no immutables, so the creation bytecode returns the
  runtime verbatim (byte offset 757). The KlimaDAO `KlimaToken` is the full inherited ERC20 +
  EIP-2612 permit + `Ownable`/`VaultOwned` + `TWAPOracleUpdater` contract. The spec models the
  compact-string `_name`/`_symbol` storage (pre-0.8 total decode), the `EnumerableSet.AddressSet`
  `_values`/`_indexes` slots with `push`/swap-and-pop `remove`, `SafeMath` checked arithmetic, the
  `_beforeTokenTransfer` hook's `EXTCODESIZE`-guarded `twapOracle.updateTWAP` external call on every
  balance-moving path, and the `ecrecover`/EIP-712 `permit`. Events are omitted consistently with the
  framework's log abstraction. No benchmark-local semantic blocker is currently known; expected proof
  work is binary-search dispatcher routing, mapping/dynamic-array slot lemmas, compact-string layout,
  `SafeMath` checked arithmetic, the guarded external call on transfer/mint/burn, and the
  precompile/ABI `permit` lemmas.

## Scaffolded, not yet handed off

- None currently.

## Needs prep before handoff

- `UniswapV2Router02`: not ready for unsupervised handoff. Large scaffold with immutables, payable
  receive, dynamic arrays, loops, `CREATE2` address derivation, raw TransferHelper calls, and many
  typed external calls. Needs a focused semantic audit before agent assignment.

- `CompoundIII/Comet`: not ready for unsupervised handoff. A parameterized immutable-aware wrapper
  exists, but the constructor spec still has placeholders for `numAssets`, asset-list creation,
  constructor validation, and constructor external-call wiring. Several runtime protocol bodies
  also remain source-level scaffolds or placeholders rather than proof-ready specs.
