# Benchmark Status

Last updated: 2026-07-04.

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
| `Dss/Vow` | 5150 | 5410 | 24 fn + ctor | Handed off | Yes |
| `Dss/Vat` | 6965 | 7021 | 28 fn + ctor | Ready for proof | Yes |
| `Dss/Pot` | 2595 | 2746 | 17 fn + ctor | Ready for proof | Yes |
| `Dss/Jug` | 2440 | 2560 | 12 fn + ctor | Ready for proof | Yes |
| `Dss/Spot` | 2178 | 2320 | 12 fn + ctor | Ready for proof | Yes |
| `WETH9` | 1763 | 2055 | 11 fn + fallback/receive | Ready for proof | Yes |
| `CompoundIII/CometRewards` | 4063 | 4207 | 11 fn + ctor | Ready for proof | Yes |
| `Safe` | 12547 | 12584 | 31 fn + ctor + fallback/receive | Prep needed | No |
| `UniswapV2Router02` | 21955 | 22346 | 24 fn + ctor + fallback/receive | Prep needed | No |
| `UniswapV3Pool` | 22142 | 22728 | 26 fn + ctor | Handed off | Yes |
| `CompoundIII/Comet` | 18655 | 21528 | 68 fn + ctor + fallback/receive | Prep needed | No |

## Completed / ready for proof / handed off

- `Dss/Dai`: completed. Target theorem: `Benchmarks.Dss.Dai.daiContractCorrect`.
  Proof work has been marked done.

- `Dss/Vow`: handed off. Target theorem: `Benchmarks.Dss.Vow.vowContractCorrect`.
  The scaffold builds with the intended constructor/runtime `sorry`s. The external-call
  `EXTCODESIZE` guards have been audited against the bytecode. No semantic blocker is currently
  known; remaining work is proof engineering around selectors, checked external calls, constructor,
  and function bodies.

- `Dss/Vat`: ready for proof, not yet handed off. Target theorem:
  `Benchmarks.Dss.Vat.vatContractCorrect`. Fresh solc output exactly matches the checked-in Lean
  creation/runtime byte arrays, and the solc storage layout matches the spec. The runtime has no
  external call sites, contract creation, delegate calls, selfdestruct, or high-level-call
  `EXTCODESIZE` guards to model. No semantic blocker is currently known; expected proof work is
  arithmetic helper lemmas, storage-mapping layout lemmas, and the large state-update bodies.

- `Dss/Pot`: ready for proof, not yet handed off. Target theorem:
  `Benchmarks.Dss.Pot.potContractCorrect`. Fresh solc output exactly matches the checked-in Lean
  creation/runtime byte arrays, and the solc storage layout matches the spec. The runtime has two
  optimized external-call sites with two `EXTCODESIZE` guards; the spec now models those guards on
  all three source-level `VatLike` calls (`drip`, `join`, `exit`, with `join`/`exit` sharing a
  bytecode call path). No semantic blocker is currently known; expected proof work is `_rpow`,
  checked arithmetic, and typed external-call reasoning.

- `Dss/Jug`: ready for proof, not yet handed off. Target theorem:
  `Benchmarks.Dss.Jug.jugContractCorrect`. Fresh solc output exactly matches the checked-in Lean
  creation/runtime byte arrays, and the solc storage layout matches the spec. The runtime has two
  external-call sites with two `EXTCODESIZE` guards; the spec now models those guards on
  `VatLike.ilks` and `VatLike.fold`. No semantic blocker is currently known; expected proof work is
  `_rpow`, `_rmul`, `_diff`, timestamp/rho arithmetic, and typed external-call return decoding.

- `Dss/Spot`: ready for proof, not yet handed off. Target theorem:
  `Benchmarks.Dss.Spot.spotContractCorrect`. Fresh solc output exactly matches the checked-in Lean
  creation/runtime byte arrays, and the solc storage layout matches the spec. The runtime has two
  external-call sites with two `EXTCODESIZE` guards; the spec now models those guards on
  `PipLike.peek` and `VatLike.file`. The `Poke` event is omitted consistently with the framework's
  substate/log abstraction. No semantic blocker is currently known; expected proof work is oracle
  return decoding, conditional arithmetic, and `bytes32` to `uint256` casting.

- `WETH9`: ready for proof, not yet handed off. Target theorem:
  `Benchmarks.WETH9.weth9ContractCorrect`. Fresh solc output exactly matches the checked-in Lean
  creation/runtime byte arrays. The payable fallback is modeled as `deposit`, and `withdraw` is
  modeled as a value-sending low-level call followed by `require(success)`, matching the single
  runtime `CALL` site. No benchmark-local semantic blocker is currently known under Solm's current
  message-call abstraction; exact 2300-gas stipend precision would be framework-level refinement,
  not missing local scaffold work.

- `CompoundIII/CometRewards`: ready for proof, not yet handed off. Target theorem:
  `Benchmarks.CompoundIII.CometRewards.cometRewardsContractCorrect`. Fresh solc 0.8.15 via-IR
  output exactly matches the checked-in Lean creation/runtime byte arrays and ABI; the solc storage
  layout matches the spec, including packed `RewardConfig` fields. The runtime has six
  `STATICCALL` sites, three `CALL` sites, and two `EXTCODESIZE` guards; the spec models the view
  calls as `perm := false` and the two guarded `accrueAccount` calls with explicit code-size
  checks. Events and custom-error payloads are omitted consistently with the framework's
  substate/revert-data abstraction. No semantic blocker is currently known; expected proof work is
  via-IR dispatch, packed storage writes, dynamic calldata arrays, `pow10`/overflow paths, and typed
  external-call return decoding.

- `UniswapV3Pool`: handed off. Target theorem:
  `Benchmarks.UniswapV3Pool.uniswapV3PoolContractCorrect`. Large stress benchmark with
  constructor-set immutables and complex pool paths; proof work should expect substantial selector,
  immutable-code, external-call, and body-trace engineering.

## Scaffolded, not yet handed off

- None currently.

## Needs prep before handoff

- `Safe`: not ready for unsupervised handoff. The Solidity runtime has receive/fallback behavior
  that is not fully represented by the current `ContractDecl` fallback dispatch.

- `UniswapV2Router02`: not ready for unsupervised handoff. Large scaffold with immutables, payable
  receive, dynamic arrays, loops, `CREATE2` address derivation, raw TransferHelper calls, and many
  typed external calls. Needs a focused semantic audit before agent assignment.

- `CompoundIII/Comet`: not ready for unsupervised handoff. A parameterized immutable-aware wrapper
  exists, but the constructor spec still has placeholders for `numAssets`, asset-list creation,
  constructor validation, and constructor external-call wiring. Several runtime protocol bodies
  also remain source-level scaffolds or placeholders rather than proof-ready specs.
