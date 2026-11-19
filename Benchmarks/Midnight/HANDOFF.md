# Midnight refinement proof

The constructor and all 57 runtime functions now have complete Lean proofs.
`Correct.lean` assembles `midnightContractCorrect` under the user-authorized
condition `g.toNat ≤ 2^24` and the Osaka fork requirement.
The scaffold provenance and earlier differential results below are historical;
the differential suite was not rerun during proof completion.

## 1. Compiler settings and provenance

Target: `src/Midnight.sol` and its complete 13-file import closure from
[morpho-org/midnight at a61b99fa1d10556bb2281fb8511a2b851ef4a9b2](https://github.com/morpho-org/midnight/tree/a61b99fa1d10556bb2281fb8511a2b851ef4a9b2).
The sources in `contracts/` were compared byte-for-byte with the Git blobs at
that commit in a clean local upstream checkout. `provenance/source.json` records
the commit, source paths, Git blob IDs, and SHA-256 hashes. No external library
sources or remappings are needed.

| Setting | Value |
| --- | --- |
| Compiler | `/usr/local/bin/solc-0.8.34`, `0.8.34+commit.80d5c536.Linux.g++` |
| Pipeline | via IR |
| Optimizer | enabled, 466 runs |
| EVM version | Osaka |
| Metadata hash | none (the compiler's 12-byte CBOR version trailer remains) |
| Runtime | 24,557 bytes |
| Creation code | 24,640 bytes |
| Selectors | 57 |
| Immutables | none |

`sources.sha256` pins the compiler artifacts as well as the Solidity sources;
`provenance/bytecode-sha256.json` hashes the decoded byte arrays. The upstream
license and Foundry settings are retained in `provenance/`.

Generation, from the repository root:

```sh
python3 -B scripts/scaffold.py all --dir Benchmarks/Midnight \
  --solc /usr/local/bin/solc-0.8.34 --main src/Midnight.sol --contract Midnight \
  --runs 466 --via-ir --evm-version osaka --metadata-hash none \
  --module Benchmarks.Midnight --no-register
python3 -B scripts/bytecode_report.py Benchmarks/Midnight --full-creation \
  --output Benchmarks/Midnight/Midnight.report.md
python3 -B Benchmarks/Midnight/generate_blocks.py
python3 -B Benchmarks/Midnight/generate.py --all
python3 -B scripts/scaffold.py check --dir Benchmarks/Midnight
lake build Benchmarks.Midnight.Correct
```

The initial `sol2stele.py` report is retained in `Midnight.spec.json`.
`SpecSyntax.lean` is now authored; rerunning the translator would overwrite it.
`generate.py` uses the shared proof generator and regenerates the ABI/config
assembly from the pinned interfaces. Its extra configuration supplies the
three-word transient hash and SSTORE2 creation code. No shared file is edited.

The local block adapter retains every artifact byte but generates summaries only
for executable regions. There are 1,807 runtime summary units in 90 shards and
five creation summary units in one shard. The full report's disassembler also
visits embedded data; those visits are not additional executable routines.

## 2. Differential runs and coverage

The local runner creates an ignored Lake package under `.difftest/` and runs the
repository CLI with only Midnight registered. It preserves the global registry:

```sh
python3 -B Benchmarks/Midnight/run_difftest.py --only Midnight --count 50 --seed 2026
lake env lean --run Benchmarks/Midnight/SuccessfulPaths.lean
lake env lean --run Benchmarks/Midnight/EdgeCases.lean
```

Final run, count 50 and seed 2026 (`provenance/difftest-final.log`):

```text
Midnight: 3075 cases: 3075 agree (1341 successful), 0 disagree, 0 stuck, 0 EVM out of gas, 0 spec out of fuel
```

<details>
<summary>Final per-transition coverage line</summary>

```text
successful/cases: constructor 17/25, liquidationLocked(bytes32,address) 39/51, setDefaultContinuousFee(address,uint256) 6/54, defaultContinuousFee(address) 37/50, settlementFeeCbps(bytes32) 45/53, claimSettlementFee(address,uint256,address) 0/51, configurator() 41/51, supplyCollateral((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),uint256,uint256,address) 0/50, setMarketContinuousFee(bytes32,uint256) 0/51, enableLltv(uint256) 7/50, flashLoan(address[],uint256[],address,bytes) 0/54, claimableSettlementFee(address) 43/52, totalUnits(bytes32) 46/52, updatePosition((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),address) 0/52, lossFactor(bytes32) 40/53, claimContinuousFee((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),uint256,address) 0/55, isHealthy((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),bytes32,address) 32/50, setDefaultSettlementFee(address,uint256,uint256) 1/50, isAuthorized(address,address) 41/50, take(((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),bool,address,uint256,uint256,uint256,bytes32,address,bytes,address,address,bool,uint128,uint128,uint256),bytes,uint256,address,address,address,bytes) 0/53, repay((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),uint256,address,address,bytes) 0/54, withdrawable(bytes32) 41/50, feeClaimer() 41/50, feeSetter() 42/52, lastLossFactor(bytes32,address) 41/51, isLiquidationCursorEnabled(uint256) 47/53, enableLiquidationCursor(uint256) 4/50, debt(bytes32,address) 42/52, position(bytes32,address) 35/51, tickSpacingSetter() 45/50, setMarketSettlementFee(bytes32,uint256,uint256) 0/56, liquidate((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),uint256,uint256,uint256,address,bool,address,address,bytes) 0/50, setConfigurator(address) 8/51, withdrawCollateral((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),uint256,uint256,address,address) 0/52, touchMarket((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address)) 0/52, withdraw((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),uint256,address,address) 0/53, settlementFee(bytes32,uint256) 29/52, multicall(bytes[]) 17/51, setFeeSetter(address) 15/53, isLltvEnabled(uint256) 40/51, collateralBitmap(bytes32,address) 43/53, setIsAuthorized(address,bool,address) 22/51, continuousFee(bytes32) 44/53, defaultSettlementFeeCbp(address,uint256) 14/54, setFeeClaimer(address) 15/51, pendingFee(bytes32,address) 44/52, credit(bytes32,address) 39/51, updatePositionView((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),bytes32,address) 37/51, tickSpacing(bytes32) 36/50, lastAccrual(bytes32,address) 44/53, consumed(address,bytes32) 44/53, marketState(bytes32) 41/50, collateral(bytes32,address,uint256) 13/51, setConsumed(bytes32,uint128,address) 9/51, setMarketTickSpacing(bytes32,uint256) 1/52, setTickSpacingSetter(address) 7/53, toMarket(bytes32) 0/52, continuousFeeCredit(bytes32) 46/53, stray 0/100
```

</details>

`SuccessfulPaths.lean` threads the EVM post-state through a constructor, role
configuration, market creation, collateral supply, an offer, repayment,
withdrawal, fee claims, flash loan, post-maturity liquidation, and every getter.
Its final line is:

```text
Successful sequence: constructor and all 57 selectors succeeded.
```

`provenance/successful-coverage.json` independently compares those success lines
with the pinned ABI: 57/57 selectors and the constructor have a successful case.
Random inputs rarely construct a mutually consistent market, authorization,
position, and callback state. This explains their zero successful counts for
complex market operations; the directed sequence supplies those cases. Specifically:

- `touchMarket`, `supplyCollateral`, `withdrawCollateral`, `updatePosition`,
  `claimContinuousFee`, `take`, `repay`, `withdraw`, and `liquidate` need the
  matching market/position/authorization state established by the sequence.
- `setMarketContinuousFee` and `setMarketSettlementFee` need both a matching
  fee-setter role and an initialized market ID.
- `claimSettlementFee` needs the fee-claimer role, a permitted amount, and a
  token with an accepted reply. The directed and return-edge tests supply them.
- `flashLoan` needs matching array lengths, acceptable token calls, and a magic
  callback. The directed case uses two tokens and the pinned magic fixture.
- `toMarket` needs code at the ID address containing a valid encoded Market.
  The directed case uses the address just produced by CREATE2.

`EdgeCases.lean` checks 18 wrapped nested-offset cases for `multicall`, plus
16 token-return/permission cases: empty, true with 32 or 64 bytes, false, dirty
bool, short return, reverting callee, and codeless callee, in both permission modes.
All 34 agree. Logs are `provenance/successful-paths.log` and `provenance/edge-cases.log`.
These are execution evidence, not a proof or a replacement for the block audit.

## 3. Specification changes and semantic audit

The manual walk covers all 1,232 executable runtime basic blocks, the terminal
INVALID, all 57 selector arms, all 63 non-inlined compiler helper entries, and
the constructor. `provenance/block-audit.json` indexes every block exactly once
by physical range, lists each range's storage/call/event PCs, and records the
corresponding specification behavior. `provenance/runtime-blocks.txt` retains
the compact instruction listing used in the walk. `index_audit.py` reproduces
this index; it checks coverage, not semantic correctness.

Physical ranges are not exclusive call graphs: shared return labels and panic
paths inside an arm are also reached by other arms. Every such target is covered
by the containing range and by the calling statement's guard/return behavior.
The source report and the byte-identical compiler IR in
`provenance/Midnight.ir.yul` were read alongside the instruction blocks.

The constructor has three executable blocks: 0–9 checks call value, 10–77 writes
the low 160 bits of slot 9, emits `Constructor(msg.sender)`, and returns exactly
the 24,557 runtime bytes at creation offset 83; 78–81 reverts. Offset 82 is
INVALID. There are no constructor arguments or immutables. Runtime 0–657 checks
short calldata and dispatches; unmatched selectors revert. There is no fallback
or receive transition. All matched arms are nonpayable.

Runtime pc 24512 is INVALID, bytes 24513–24544 are the callback-success constant,
and bytes 24545–24556 are CBOR metadata. CREATE2 at pc 21667 is labelled
`UNSUPPORTED_F5` by the RD generator. This is a summary boundary; Stele's `.new`
and the underlying EVM model support the instruction.

Audit findings repaired in the authored inputs:

- All 22 draft holes now have value-level effects: ABI values, calls and revert
  propagation, MSB/popcount arithmetic, transient operations, and SSTORE2.
  Allocation buffers and copying have no standalone specification statements.
- `take`, `liquidate`, and position accrual restore the conditional calls and
  arithmetic that the translator hoisted out of ternaries and short circuits.
  The public and internal position-view entry points share one helper.
- SSTORE2 uses the exact 11 bytes `600b380380600b5f395ff3`, followed by
  `abi.encode(market)`. ID derivation hashes `ff`, the market's Midnight address,
  a zero salt, and that initcode hash. Creation uses CREATE2, zero value and salt,
  and requires a nonzero returned address. The prefix's fixed-bytes conversion
  was corrected after the first differential run exposed an interpreter error.
- Transient locks use one hash of the ABI words `(id, user, baseSlot)`, with base
  `keccak256("morpho.midnight.liquidationLocked")`. The layout is not a nested
  Solidity mapping hash. TLOAD tests the entire word for zero; TSTORE writes 0
  or 1. The custom backend preserves this behavior on arbitrary transient state.
- `multicall` uses signed tail checks and wrapping offsets at pcs 3590–3652.
  A negative nested offset can alias an empty byte string and succeed. The
  custom selector plan uses the existing `solc08Calldata` mode with direct
  calldata references, fixing a reproduced mismatch with the modern decoder.
- Typed external calls copy at most the first 32 return bytes. Their named ABI
  decoders receive that prefix. Raw token calls retain the whole result,
  accept empty bytes or a canonical true ABI bool, and reject other results.
  The compiler's uint64 raw return-size guard is explicit before the success
  check, including for delegatecall results.
- Entry argument allocation checks are closed predicates on decoded lengths:
  `1120 + 160*n < 2^64` for a Market, and
  `1696 + 160*n + pad(callbackData) + pad(ratifierData) + pad(takerCallbackData)
  < 2^64` for an Offer call. The Offer includes its Market. These checks reject
  inputs that cannot finish decoding before any observable effect.
- `toMarket` retains the external-code length guard `code.length <= 2^64-1152`
  and the decoded-length guard `pad(code.length) + 160*n + 1408 < 2^64`.
  They express the compiler's observable capacity checks using value lengths.
  No free pointer, memory state, or copying is represented in the specification.

Storage audit: slots 0–8 are, in order, position, market state, consumed,
authorization, default settlement fees, default continuous fee, claimable
settlement fees, enabled LLTVs, and enabled liquidation cursors. Slots 9–12 are
the four roles. Position slots pack two uint128 fields each in the first three
words; its 128 collateral amounts occupy 64 further words. Market slots pack
two uint128 fields each in the first two words; the third has seven uint16 fees,
a uint32 continuous fee at byte 14, and uint8 tick spacing at byte 18.

All writes preserve unrelated packed bits. Reads that can observe a preceding
write remain after it. In particular, market initialization writes tick spacing,
snapshots the default-fee word, writes the fee fields, then reads and writes
the default continuous fee. The compiler combines the first two fee writes;
the spec's consecutive writes have the same already-captured values and no
intervening observation. Accrual writes credit before re-reading market loss,
then updates last loss, pending fee, last accrual, and continuous fee credit.
`take` and `liquidate` retain their packed update order, including bad-debt
re-reads. Repeated getter reads and cached reads across STATICCALLs require
read stability, not a storage-slot noncollision assumption.

Arithmetic audit covers checked uint128/uint256 add/subtract/multiply,
zero divisors, ceil rounding, saturating minimum/subtraction, signed unchecked
`wExp`, the seven fee knots/caps, bitmap MSB and popcount, and masks on casts.
All five CLZ sites are represented by the value-level MSB calculation and
require the Osaka environment condition. Guards precede calls and writes in
the bytecode's order. Token code-presence checks, optional callbacks, gate
STATICCALLs, callback magic, oracle scaling, events and their arguments, and
the sender/value/address/chain/time environment reads are accounted for.

## 4. Proof-session configuration and validation

`Model.lean` supplies tuple/struct representation adapters, the transient layout,
input length guards, and SSTORE2 creation encoding. The generated `Spec.lean`
call table is checked against the pinned interfaces in
`provenance/interfaces.abi.json`: `transfer`, `transferFrom`, `price`,
`isRatified`, `canIncreaseCredit`, `canIncreaseDebt`, `canLiquidate`, `onBuy`,
`onSell`, `onRepay`, `onLiquidate`, and `onFlashLoan`. `encodeMarket` and
`encodeOffer` are pure ABI encoders without selectors.

Calldata mode is `.solc08Calldata` with a direct-reference plan only for
`multicall` (`0xac9650d8`); other selectors use fully materialized validation.
`liquidate` initially exposes a calldata Market but materializes it for
`touchMarket` before its first effect. Flash-loan address elements are validated
while encoding the event, before LOG or token calls. Eager validation therefore
preserves their observable failure order, including static permission mode.
Explicit `abi.decode` uses the modern decoder. Named call returns use strict
single-word decoding of the copied prefix. Representation conversion follows
validation and does not weaken scalar canonicality checks.

`Conditions.lean` defines `midnightWF σ I := I.fork >= .osaka` and the gas cutoff
below. There is no storage-shape, valid-market, or slot-noncollision assumption.
The runtime proofs receive these two hypotheses. The capstone exports
`runtimeRefinementWithWF midnightWF midnightGasBound` and
`contractRefinementWF midnightWF midnightGasBound`. The constructor theorem is
the ordinary typed constructor refinement, with an empty immutable valuation.
`generate.py` originally installed these signatures through the shared generator.
The function bodies now contain completed proofs; do not regenerate them.
The executable block summaries were preserved unchanged.

The completion build is recorded in `provenance/proof-final-build.log`; the
capstone dependency audit is recorded in `provenance/proof-final-axioms.log`.
The build passed all 4,643 jobs. The dependency audit contains only `propext`,
`Classical.choice`, `Quot.sound`, and 26,285 native-evaluation axioms; it contains
no proof-hole axiom or custom assumption. `provenance/proof-final-audit.json`
records the counts and authorized gas condition.
The original scaffold build and artifact checks remain in
`provenance/correct-build.log.gz` and `provenance/artifact-check.log`.

The proof covers dynamic decoders, packed writes in arbitrary storage, external
calls and reentrancy, transient locks, CREATE2/SSTORE2, the liquidation oracle
loop, signed price arithmetic, and compiler memory capacity checks. External
call proofs retain the EVM's actual forwarded gas and call substate.

For reproducibility, build shards and function modules in small batches before
`lake build Benchmarks.Midnight.Correct` on a memory-constrained machine. The
checked-in `provenance/` logs record the required gates; `.difftest/` and Python
caches are ignored. Nothing outside this directory is changed or registered.

## 5. Gas bound

The current, user-authorized runtime condition is `g.toNat ≤ 2^24`.
The earlier capacity cutoff below is retained as historical analysis. It is not
the current condition: `TakeCapacityAudit.lean` and `TakeCapacityWitness.lean`
record a cheaper token implementation and an arithmetic witness two gas below
that former cutoff. The new condition excludes that witness.

The former proposed runtime condition was the strict bound

```text
g.toNat < 327073817860464196263953616796569
```

That proposed cutoff included every starting gas through `2^24`, but its
claimed minimal counterexample cost was invalidated by the cheaper token
recorded above. The following arithmetic and path classification document the
former argument; they are not premises of the completed refinement proof.

Let `C(w) = 3*w + floor(w*w/512)` be cumulative EVM memory cost, and let
`J(q) = q + floor((q-1)/63)` for positive `q`. The latter is the least gas after
the call's extra charge that can forward `q` under the 63/64 cap. The binding
site is the second `safeTransferFrom` in `take`: CALL at pc 23522, raw extraction
at 22728–22774, and the capacity check at 18444–18476.

With an already initialized market, no collaterals, zero units, a buy offer
capped by units, no gates/callbacks, and maturity at least one year away, let
`N` be the padded length of unused `takerCallbackData`. Both authorizations
and all storage/account accesses can be warm. The ratifier returns magic in
32 bytes; the first token call returns true in 64 bytes. At the second token
call the compiler has reached exactly `4064 + N` active bytes and its next
allocation starts there. The transient event buffer's extra zero word is
included in this count. Set `p = (4064+N)/32` and `r = ceil(replyBytes/32)`.
The first aggregate capacity failure is

```text
p + r = S, where S = 2^59 - 1
32*p + 32 + 32*r = 2^64
```

The parent has spent `C(p) + 3*p + 26667` gas immediately before CALL.
The 3*p term includes the linear copy cost after substituting `N=32*(p-127)`;
the constant includes dispatch, decode, hashing, guards, warm reads/no-op
persistent writes, transient operations, the ratifier, the event, and the
first token call. CALL costs a further 100 for a warm ordinary callee.
`GasTrace.lean` measures the exact pinned EVM path at N = 0, 32, 64, and 1024;
all four agree with this formula. It also checks the alternative cap/direction
branches: assets-capped buys add 35 gas, units-capped sells add 197, and
assets-capped sells add 233 before this call.

A token producing the two replies can use these eight opcodes:

```text
TIMESTAMP PUSH0 MSTORE PUSH1 0x24 CALLDATALOAD PUSH0 RETURN
42 5f 52 60 24 35 5f f3
```

Set the timestamp to 1 and Midnight's address to 64. The first transfer's
destination is Midnight, so the first reply is 64 bytes with a true first word.
Set the second receiver to `32*r`; the second reply is that many bytes with
the same true first word. Its cost is exactly `C(r)+15`. The ratifier can use
`44 5f 52 59 5f f3`, with PREVRANDAO set to the callback magic (14 gas).
These are ordinary non-precompile callees; storage need only have initialized
tick spacing and maker authorization. An empty collateral array is allowed
in this arbitrary runtime pre-state because initialization checks are skipped.

Consequently the first reachable capacity failure on this path needs

```text
B = min over integer p: C(p) + 3*p + 26767 + J(C(S-p)+15)
  = 327073817860464196263953616796569.
```

Removing the floors gives a quadratic minimized at `(64*S-47616)/127`.
The floor error is below 4, so inspecting the 129 integers centered on its
floor includes every minimizer. `audit_gas.py` recomputes this minimum and
checks the seven ordinary-size traces; `provenance/gas-bound.json` retains
the minimizers and a witness. One minimizer is `p=290499906672590983`, with
`r=285960845630832504`, `N=9295997013522907392`, and reply size
`9150747060186640128`. At starting gas B, the callee can finish and the parent
retains more than `2*10^30` gas, so it reaches allocation panic rather than
running out of gas. Thus this upper interval cannot be enlarged while
abstracting that capacity guard.

The other paths do not give a lower cutoff:

- Consider the first failed aggregate guard. Entry Market/Offer and `toMarket`
  capacity failures are already represented by closed value-length guards.
  Fixed-size allocations elsewhere follow fully written objects; failure
  requires active memory within a fixed small distance of `2^64` bytes.
  Its single-frame cost is greater than B. Encoding/copying near that limit
  also pays this cost before any omitted pointer check can matter.
- The remaining early guard is raw return allocation, before RETURNDATACOPY.
  Before each such call the active memory covers the current allocation start.
  A crossing therefore requires `p+r >= S`. A fresh EVM child pays at least its
  own return-memory cost, subject to the forwarding cap. Fixed-size precompile
  replies cannot cross; identity requires the parent to supply the large input
  at its current buffer end; modexp's large-output charge exceeds the EVM-child
  bound. Nested callees still pay for the returning frame's memory.
- Outside `take`, large prior allocation comes from Market materialization and
  encoding, or previous raw replies in the flash-loan/multicall loops. Market
  validation/indexing adds positive gas per allocated word beyond copying;
  previous replies pay both their producing frame and their copy/loop costs.
  Counting these families gives at least one extra gas per allocated word
  beyond `3*p`, even after a fixed startup allowance of `10^6` gas. For p in
  `[S/4,3*S/4]` this already exceeds the fixed-cost advantage needed to beat B;
  outside that interval the quadratic memory/forwarding term itself exceeds B.
- Within `take`, unused taker data is the cheapest source of large prior
  allocation. Additional collateral entries require validation and repeated
  encoding; callback data is encoded/hashed again; ratifier data is encoded and
  logged. Their incremental costs exceed the saved taker-data copy cost.
  Accrual, gates, or a buyer callback add work. A buyer callback's 32-byte
  allocation saves at most one copied word and one first-reply word, less than
  its call cost. The checked zero-position path is therefore the minimum.
- Before the first token call, the event buffer leaves eight active words
  beyond the free-pointer position; after an empty or 32-byte first reply it
  still leaves excess active memory at the second call. Those cases require
  a larger `p+r`, which costs much more than their saved fixed gas. A 64-byte
  first reply is the smallest one eliminating that excess. Larger first
  replies replace taker-data words but add producer memory cost. The displayed
  branch-free token attains the minimum needed to distinguish the two reply
  sizes while producing a true first word; conditional/stateful token code
  adds work.

The former conclusion that every capacity violation below B exhausts gas was
invalidated by `TakeCapacityWitness.lean`. The completed proof instead uses the
authorized `2^24` limit. `midnightMemoryPaid_small` proves that a funded runtime
state either already exhausts gas or has fewer than 100,000 active memory
words. This supplies the needed allocation bounds and closes the take transfer
funding argument. Observable size checks remain explicit, and external calls
use their actual EVM witnesses.
