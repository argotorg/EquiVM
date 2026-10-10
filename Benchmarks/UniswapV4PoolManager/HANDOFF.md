# PoolManager refinement proof

All 33 public ABI refinements and the constructor are proved against the pinned
bytecode. `Correct.lean` assembles the runtime and deployment theorems under the
existing `poolManagerWF` and `poolManagerGasBound` hypotheses. The dependency
notes below retain the chronological history of the proving session.

## Refinement proof progress (2026-10-10)

The proving session reran the differential suite and both focused fixtures above:
all completed comparisons agreed. All 33 ABI entry proofs are now complete and built:
`owner`, `protocolFeeController`, scalar `extsload`, scalar `exttload`,
`supportsInterface`, `protocolFeesAccrued`, `balanceOf`, `isOperator`, `allowance`,
`approve`, `setOperator`, `transferOwnership`, `setProtocolFeeController`, `transfer`,
`transferFrom`, `clear`, `mint`, `burn`, `exttload(bytes32[])`, `extsload(bytes32[])`,
`extsload(bytes32,uint256)`, `updateDynamicLPFee`, `setProtocolFee`, `sync`, `settle`, `settleFor`, `take`, `collectProtocolFees`, `unlock`, `initialize`, `modifyLiquidity`, `swap`, and `donate`.
Their proofs cover malformed calldata and applicable nonpayable guards.
The mutating entries additionally cover storage updates and static violations.
`restrictImmutables_of_fit` is also proved. The capstone build passed all 4,638
jobs; the final trusted-dependency audit passed with only the accepted axioms.
The constructor is proved, including argument decoding, the owner store, immutable
patching, runtime-code return, and its nonpayable revert.

### Final verification (2026-10-10)

The required capstone build completed successfully:

```text
lake build Benchmarks.UniswapV4PoolManager.Correct
Build completed successfully (4638 jobs).
```

`AxiomAudit.lean` is a reproducible audit of the runtime, deployment, constructor,
and final Donate theorem. It fails if any dependency is outside the three
standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) and concrete
native evaluation facts. Its final output was:

```text
Benchmarks.UniswapV4PoolManager.poolManagerDonateBody: 3 standard axioms, 1596 native_decide axioms, 0 unexpected axioms
Benchmarks.UniswapV4PoolManager.poolManagerCorrect: 3 standard axioms, 17404 native_decide axioms, 0 unexpected axioms
Benchmarks.UniswapV4PoolManager.poolManagerRuntimeCorrect: 3 standard axioms, 17404 native_decide axioms, 0 unexpected axioms
Benchmarks.UniswapV4PoolManager.poolManagerConstructorCorrect: 3 standard axioms, 348 native_decide axioms, 0 unexpected axioms
Benchmarks.UniswapV4PoolManager.poolManagerContractCorrect: 3 standard axioms, 17751 native_decide axioms, 0 unexpected axioms
Build completed successfully (4639 jobs).
```

The Lean source searches for incomplete proofs and authored axioms returned no
matches. The directory-wide keyword search only matches historical prose in this
file. `git diff --check` passes. The generated block summaries, bytecode, and pinned
Solidity files have no changes. The specification correction and differential
results are documented below; all subsequent work only added or refactored proofs.
The temporary `Scratch.lean` audit has been replaced by `AxiomAudit.lean`.

The final commands and their verbatim outputs are captured in
`/tmp/uniswap-v4-final-verification.txt`; the complete capstone axiom list is
`/tmp/uniswap-v4-capstone-axioms.log`. Build logs are
`/tmp/uniswap-v4-correct-final-build.log` and
`/tmp/uniswap-v4-final-audit-build.log`.

The proved deployment statement is
`contractRefinementWF Syntax.poolManagerWF Syntax.poolManagerGasBound config
poolManagerCreationBytecode contract`. It retains the authorized range-return
span precondition and starting-gas bound `g < 324518553658429321982441292826060`.
No extra contract-specific assumption is used.

Shared helpers are in `EntrySource`, `EntryTrace`, `Values`, `Bytes4`, `Storage`,
`MappingMemory`, `Routines`, `Authorization`, `Arithmetic`, `BalanceTransfer`, and
`ConstructorSupport`. `transferFrom` covers caller/operator authorization, unlimited
and finite allowances, and all arithmetic/static failures while preserving storage
read/write order even for aliased slots. Source dispatch facts were split into
`DispatchSource` to keep each proof file below 2,000 lines. Function modules import
only the bytecode-summary shards they use. When normalizing nested mapping memory,
prove slot/output equalities separately and transport `RDret` with `congrArg`;
simplifying the full reachability proposition causes expensive elaboration.

`clear` is complete, including zero-amount success in static mode. Its shared source
and trace dependencies cover the lock read, currency-slot hashing, checked int128
casts, signed-256 addition, delta writes, and wrapping counter increments/decrements.
These are in `TransientSource`, `TransientTrace`, `SignedWords`, `SignedArithmetic`,
`Signed128`, `SignedAddTrace`, `SafeCast`, `DeltaCount`, `DeltaCountTrace`, `ApplyDelta`,
`AccountDeltaSource`, and `AccountDeltaTrace`. Counter reads follow the delta write,
including when slots alias. A new generic `tstoreStatic` lemma handles static halts.
For conditional trace propositions involving decoded signed values, abstract the
computed integer with `generalize` before eliminating existentials or splitting
cases; otherwise elaboration may attempt a very deep reduction of integer residues.

`mint` is complete. `CurrencyId` proves the low-160-bit id conversion;
`BalanceMint`/`BalanceMintTrace` prove the internal balance credit and event tail.
The public proof composes these after transient accounting, including zero amount,
signed-delta overflow, balance overflow, and static halts. `SourceComposition`
provides a generic function-body prefix lemma. Conditional trace definitions whose
guards hash storage may need `@[irreducible]` and explicit unfolding to prevent
Lean from trying to compute symbolic hashes while checking proof arguments.

`burn` is complete. Its helpers are `BalanceBurn`, `BalanceBurnTrace`,
`BurnAuthorization`, `BurnAuthorizationTrace`, `BurnAllowanceStatic`,
`BurnFromSource`, `BurnFromTrace`, `BurnSource`, and `BurnTrace`. Accounting precedes
authorization, then finite allowances are written before the balance is read.
`CallComposition` adds generic result maps and internal-call composition. Use its
specific `resumeCallResult_ite`/`finishBlockResult_ite` lemmas rather than broadly
simplifying with `apply_ite`, which also distributes enclosing proof propositions.

`exttload(bytes32[])` is complete, including malformed ABI, arbitrary unaligned
dynamic offsets, static reads, positive-length iteration, and the mandatory single
read on the empty-array path. Shared array helpers are in `WordArrayDecode`,
`WordArrayDecodeTrace`, `LocalArray`, `WordArrayMemory`, `WordArrayABI`, and
`WordArrayReturn`. The two array entries share `WordArrayLoop`, `WordArraySource`,
`WordArrayTraceLoop`, and `WordArrayTraceReturn`. Its source/trace helpers are `CalldataWordSource`,
`ExttloadArrayLoop`, `ExttloadArraySource`, `ExttloadArrayTrace`, and
`ExttloadArrayReturn`. The bytewise source helper is proved modularly and returns
a bounded word after exactly 32 iterations. The empty-array extra store is outside
the 64-byte return window. `wordArrayStepWord` avoids expensive definitional
reduction when proving pointer increments containing calldata words.

`extsload(bytes32[])` is also complete. Its storage-read steps compose with the
same decoded values, loop invariant, and return-buffer proofs as transient reads.
`ExtsloadArraySource`, `ExtsloadArrayTrace`, and `ExtsloadArrayReturn` contain the
specialization. Storage reads cover both warm and cold cases through the generated
summaries. The full `Correct` build was rerun after the specification correction;
the remaining runtime placeholders still prevent a final capstone axiom audit.

`extsload(bytes32,uint256)` is complete in `WordRangeABI`, `WordRangeSourceStep`,
`WordRangeSource`, and `WordRangeTrace`. The source and bytecode both read the first
slot even for an empty result. The storage cursor wraps modulo 2^256; only the
return buffer uses the existing `poolManagerWF` no-overflow assumption.
`WordArrayFillLoop` shares the source induction across all three array entries.
`WordReadTraceLoop` and `WordReadTraceReturn` generalize the bytecode loop over its
cursor and stride. Their step domain is `i < max 1 n`, covering the empty read
without requiring an additional memory step after a positive-length array ends.

`updateDynamicLPFee` is complete. `NarrowWords` proves uint24/int24 ABI cleanup;
`PoolKeyABI`, `PoolKeyMemory`, `PoolKeyDecodeTrace`, and `PoolKeySource` share the
five-word pool-key decoder and hash, including signed tick spacing. `LPFeeSource`
and `LPFeeTrace` cover dynamic-fee identification and the one-million fee limit.
`PoolStorage` proves storage aliases and the slot-6 pool mapping. `Slot0Source`,
`PoolLPFeeSource`, `PoolCheckTrace`, and `PoolLPFeeTrace` cover initialization checks,
the packed 24-bit field update, and its static halt. The public composition is in
`UpdateFeeSource` and `UpdateFeeTrace`. The proof requires no added storage or gas
assumptions. For computed calldata guards, an explicit success/revert disjunction
can avoid expensive reduction of a dependent `if` during elaboration.
Its axiom audit reports 565 dependencies, all standard Lean axioms or concrete
`native_decide` facts.

`setProtocolFee` is complete. `ProtocolFeeSource` proves both directional fee
limits and the controller guard; `PoolProtocolFeeSource` proves `_getPool` and the
internal setter. Both fee setters share `PoolCheckSource`, `PoolSetSlot0Source`,
and the packed-word update and shifted-mask lemmas in `Slot0Source`.
`PoolProtocolFeeTrace` handles the initialized-pool check, packed write, static
halt, and event tail; `SetProtocolFeeSource` and `SetProtocolFeeTrace` compose the
public function. Its audit reports 578 dependencies with no unexpected axioms.

`sync` is complete. `CurrencyReservesSource` proves the ordered transient stores;
`CurrencyBalanceSource`, `CurrencyBalanceABI`, `CurrencyBalanceTrace`, and
`CurrencyBalanceReturnTrace` prove the token balance call and its return decoder.
`StaticCallBridge` connects the EVM and source through the same opaque call,
including the depth limit. The return-data bound follows from the proved EVM
bound for a 36-byte input. `SingleWordCallMemory` and `AllocationTrace` provide
shared request-memory and allocation facts. `SyncSource` and `SyncStoreTrace`
compose the source branches and their final stores. Its audit reports 463
dependencies with no unexpected axioms. The capstone rebuild succeeds (3653 jobs)
with 9 runtime placeholders.

`settle` is complete. `CurrencyReservesRead` proves the transient reserve getters;
`SettlePaidSource`/`SettlePaidTrace` share the int128 cast and positive delta credit.
`SettleSource`, `SettleResetTrace`, and `SettleTrace` compose native and token
payments, including nonzero native value rejection, reserve subtraction underflow,
currency reset, delta overflow, and static halts. `SettleEntrySource` shares the
payable lock/call prefix. `CurrencyBalanceWordTrace` and `accountDeltaWordTrace`
accept raw currency words and prove their low-160-bit cleanup; canonical wrappers
preserve existing callers. Balance-call traces now retain memory bounds for later
returns. `WordReturnTrace`, `ReturnCall`, and `Uint256ResultTrace` provide shared
return-memory and source/trace composition. Its audit reports 584 dependencies,
all accepted. `settleFor` is also complete, reusing the same source and EVM helper
after the address decoder. Its audit reports 660 accepted dependencies. The
capstone rebuild succeeds (3664 jobs), including regression builds of the earlier
callers of the generalized accounting helpers. Seven runtime placeholders remain.
`take` is complete. `CurrencyTransferABI`, `CurrencyTransferSource`,
`CurrencyTransferReturnTrace`, and `CurrencyTransferTrace` prove the shared native
and ERC20 transfer helper, including call failures, optional return data, and static
halts. `RawCallBridge` also handles zero-value calls in static mode. `TwoWordCallMemory`,
`LocalBytes`, and `UnitResultTrace` add shared payload, source decoding, and result
composition facts. `TakeTrace` preserves accounting before the external call. Its
audit reports 672 dependencies, all accepted. Explicit `I`, `evm`, and `s0` arguments
at the `takeBodyTrace` application avoid expensive inference of calldata-bearing
states; the public proof builds in four seconds with the default heartbeat limit.
The checked negation expression is now shared with `mint` in `SignedWords`.
`collectProtocolFees` is complete. `ProtocolFeesSource` shares its mapping read/write
facts with the getter. `CollectProtocolFeesSource`, `CollectProtocolFeesTail`, and
`CollectProtocolFeesTrace` cover controller authorization, the synced-currency guard,
amount selection, checked subtraction, storage update, external transfer, and return.
The transfer trace now retains a configurable memory invariant through both native
and token calls; `CurrencyTransferMemory` proves the free-pointer preservation needed
by the uint256 return. `StorageStaticTrace` shares the JUMPDEST/SWAP1/SSTORE static
halt with the mint/burn proofs. Its axiom audit reports 725 accepted dependencies.

The capstone rebuild succeeds (3679 jobs), including the affected accounting,
mint/burn, settlement, transfer, and fee callers. No unexpected assumptions were introduced.
The next function in progress is `initialize`.

### Initialize dependency progress

The public `Initialize.lean` placeholder remains. Its TickMath dependencies are
now fully proved: `MostSignificantBitSource`/`MostSignificantBitTrace`,
`TickLogSource`/`TickLogStagesSource`, `TickSqrtSource`/`TickSqrtTrace`, and
`TickPriceSource`/`TickPriceTrace`. `TickPriceCanonical` proves successful ticks
are canonical int24 words. The price-to-tick trace starts at pc 17916 and covers
range rejection, MSB failure, all fourteen logarithm stages, signed casts,
the inverse-price fallback and its failure, and return selection. The pure
`tickPriceResult` model keeps the exact source and bytecode behavior.

`TickSqrtBounds` checks the fixed 887273 absolute tick inputs with a concrete
`List.range.all` native computation, proving nonzero ratios and uint160 results.
The other new arithmetic bridges are proved symbolically. These include signed
word representation, SAR, int24 sign extension, unsigned wrapping subtraction,
shift composition, and extraction of the top bit into another position.

The logarithm trace is split into fourteen small block lemmas and a composition
lemma. `TickLogUnroll` names intermediate values before joining the trace.
`signedWordResult` keeps source outcomes abstract during composition; unfolding
the computed option inside dependent source judgments caused kernel recursion
limits. Concrete constant rewrites must match the block syntax, and repeated
occurrences require `simp only` rather than a single `rw`.

The TickMath source, trace, and canonicality modules build successfully. The
packed setters (`Slot0InitializeSource`) and `Pool_initialize` are also complete.
`PoolInitializeSource` covers the existing-pool guard, tick computation, all
three setters, storage assignment, return value, and static violations.
`WordFieldPacking` and `PoolInitializePacking` prove that the compiler's combined
word equals the source setters. `PoolInitializeTrace` handles pc 4341 through
the store and event at pc 4555; `PoolInitializeGuardTrace` composes the entire
segment starting at pc 4292, including the pool-id hash and existing-pool revert.
The trace is parameterized by the current memory and source state, so it applies
after arbitrary hook callbacks. Its stack allowance is `R.length + 35 ≤ 1024`.

The pool source body and call each use 1 concrete native fact plus the three
standard Lean axioms. `poolInitializeTrace` uses 1202 native facts plus the
three standard axioms. The audit found no `sorryAx` or unexpected axioms.
`InitialLPFee` and hook-address validation are also complete on source and
bytecode. `HookValidationSource`, `HookPairTrace`, and `HookValidationTrace`
cover the four dependent flag pairs, zero/nonzero hook addresses, and dynamic
fees. `HookCallSource` and `HookCallTrace` prove the shared callback helper:
the same opaque call witness is used on both sides, failed calls revert,
replies shorter than 32 bytes revert, and the first four reply bytes must match
the request selector. `HookFailureTrace` covers the wrapped-error path.
`ReturnDataMemory` extends the existing return-data model to sparse writes;
`SelectorMemory` proves the exact relationship between high-byte masks and
byte prefixes. `HookReplyMemory` and `HookReplyTrace` join these facts to the
compiled reply checks. The call trace requires a request at least 32 bytes long;
both initialize callback payloads satisfy this.

The callback body uses only the three standard Lean axioms; its trace uses
262 concrete native facts plus those axioms. Hook-address validation uses
217 native facts, and the initial-fee trace uses 69. All six source/trace audits
found no `sorryAx` or unexpected axioms (`/tmp/initialize-hook-axioms.log`).
`InitializeHookABI` now proves both callback payload encoders (228 and 260
bytes). Both source wrappers and their complete bytecode traces are now proved.
`InitializeFinishSource`, `InitializePoolSource`, and `InitializePoolCorrect`
connect the pool update, event, after-initialize callback, and signed tick return.
`InitializeHooksCorrect` proves the source/bytecode correspondence from pc 4257
through the entire remaining public body (source statements 12 through 19).
Its hypotheses include the decoded pool key, current fee, small initial memory,
and the existing gas bound. It handles both callbacks, reverts, and static halts.
The public entry, decoding, and initial guards are now composed in `Initialize.lean`.

The capacity issue is discharged before the first hook reply is copied:
`HookReplyGas.hookLargeReply_outOfGas` proves that a reply with
`out.size + 4096 > solcMaxU64` exhausts the existing permitted gas when the
initial active memory is at most 2048 words and the free pointer at most 2048.
`HookCallBoundTrace` combines that result with the ordinary callback trace.
`BeforeInitializeEncodeTrace` preserves the active-memory bound, and
`BeforeInitializeHookTrace` returns either out of gas or a bounded successful
reply. `BeforeInitializeMemory` then proves the next allocation fits, using
`ReturnDataAllocation`. The gas-bound value and specification are unchanged.

`MemorySlice`, `PoolKeyView`, and `PoolKeyPreservation` preserve pool-key data
through callback buffers and mapping scratch stores. `InitializeEventMemory`
preserves the key and free pointer across event encoding. `SignedResultTrace`
provides the final ABI refinement bridge for a signed return value.
`AllocationTrace.allocateTraceWords` exposes the allocator's exact active-word
expression; the existing `allocateTrace` remains a compatible wrapper.
The shared CALL prefix is factored into `HookCallPrefixTrace`.

`InitializeHooksCorrect` builds successfully (`/tmp/initialize-hooks-correct2.log`).
Its axiom audit has 1786 concrete native facts and the three standard axioms;
the large-reply gas lemma has 42 native facts plus the three standard axioms,
and `initializePoolSource` has 3 native facts plus the three standard axioms
(`/tmp/initialize-core-axioms.log`). No unexpected axioms occur.
`NoDelegateCall` proves both the source and bytecode of the immutable-address guard.
`PoolKeyDecodeBounds` retains the decoder's active-word bound; `PoolKeyDecodeTrace`
keeps the earlier API as a wrapper. `PoolKeyABI` now shares its unsigned-width
decoder between uint24 and uint160, including malformed, short, and huge calldata.
`InitializeDecodeTrace` reaches pc 4081 with the bounded decoded memory.
`InitializeValidationSource` and `InitializeValidationTrace` prove all tick-spacing,
currency-order, hook-address, and initial-fee checks. `InitializePreludeSource`
and `InitializeBodyCorrect` compose these into the public entry proof.

`poolManagerInitializeBody` builds successfully (`/tmp/initialize-public3.log`).
Its audit contains 2677 concrete native facts plus `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx` or other axioms
(`/tmp/initialize-public-axioms.log`). The shared unsigned decoder has 2 native
facts plus those three standard axioms; the delegate-call source body has only
the standard three. The capstone build passed with all 3848 jobs (`/tmp/initialize-correct-build.log`).
The subsequent `modifyLiquidity` proof is recorded below; `swap` and `donate` remain.
No new `sorry`, axiom, semantic assumption, or source change was introduced.

### Swap completed (2026-10-10; development history)

`swap` is the active public ABI. Dependency work has completed the checked
uint160 cast and amount-1 next-price calculation, including both amount-size
branches, addition overflow, subtraction bounds, full-precision quotient failure,
rounding, and preservation of memory/active words and the incoming gas-cost floor.

- `SafeCast160Source` / `SafeCast160Trace`: source function 118 and bytecode
  pc 23963, with successful dynamic return and overflow reversion.
- `FullMathShift96Trace`: the specialized multiplication-by-2^96 routine at
  pc 22666, sharing the existing full-precision word model.
- `NextAmount1Words`, `NextAmount1QuotientSource`, `NextAmount1TailSource`, and
  `NextAmount1Source`: source function 117, its call wrapper, exact branch results,
  and the canonical-uint160 result bound.
- `NextAmount1AddQuotientTrace`, `NextAmount1AddTailTrace`,
  `NextAmount1SubQuotientTrace`, `NextAmount1SubGuardTrace`, and `NextAmount1Trace`:
  the inlined add path pc 20476→20464 and remove path pc 20749→20872.

These modules build (`/tmp/swap-next-price-deps-build.log`, 3561 jobs). The audit
`/tmp/swap-next-amount1-audit.log` found only standard Lean axioms and concrete
native facts: cast source/call 0, cast trace 36, shifted multiplication trace 160,
amount-1 source/call 0, add trace 301, remove trace 286.
Amount-0 next-price calculation is also complete: `NextAmount0Words`,
`NextAmount0RoundSource`, `NextAmount0FallbackSource`, `NextAmount0SubSource`,
`NextAmount0AddSource`, and `NextAmount0Source` prove source function 116 and its
call wrapper. `NextAmount0RoundTrace`, `NextAmount0FallbackTrace`,
`NextAmount0AddCoreTrace`, `NextAmount0SubTrace`, and `NextAmount0Trace` prove the
remove-token pc 23697 and add-token pc 23815 routines, including zero amount,
product overflow, fallback checked addition, rounded division, checked uint160
conversion, exact memory/active words, and the incoming cost floor. Canonical
uint160 result bounds are proved. The build passed all 3559 jobs
(`/tmp/swap-next-amount0-trace-build.log`). Its audit
(`/tmp/swap-next-amount0-audit.log`) has 0 native facts for the source call and
canonical bound, 414 for the add trace, and 352 for the remove trace; only the
standard three axioms and concrete evaluation facts appear.

The subtraction trace uses a separate generic arithmetic tail and supplies the
fit condition before simplifying its final conditional. This avoids reducing
symbolic shifted-word arithmetic during elaboration; no heartbeat increase is
needed. No specification or semantics changed during these dependencies.

The input/output next-price wrappers are complete. `NextPriceWords`,
`NextPriceCalcSource`, and `NextPriceSource` prove functions 114/115 and their
call wrapper, including price/liquidity guards and the uint160 result bound.
`NextPriceInputCoreTrace`, `NextPriceOutputCoreTrace`, `NextPriceGuardWords`,
`NextPriceInputTrace`, and `NextPriceOutputTrace` compose the token routines and
guard reverts. The compiled input segment is pc 20402→20464, the output segment
pc 20727→20872; both retain exact memory/active words and the cost floor.
The build passed 3582 jobs (`/tmp/swap-next-price-wrapper-build.log`). The audit
`/tmp/swap-next-price-wrapper-audit.log` found 0 native facts for the source call
and canonical bound, 704 for the input trace, and 546 for the output trace, with
no unexpected axioms.

Swap-step assembly is active. Its specialized FullMath denominator 1,000,000
routine at pc 22405 is complete (`FullMathPPMWords` / `FullMathPPMTrace`), with
the compiler's constant odd-factor inverse checked by concrete evaluation and
the shifts related to the general FullMath word model. Build:
`/tmp/swap-fullmath-ppm-build.log` (3507 jobs); audit:
`/tmp/swap-fullmath-ppm-audit.log` (trace 106 native facts, wide identity 0,
inverse 1; no unexpected axioms).

`SwapStepDeltaWords` / `SwapStepDeltaSource` prove the shared source statement
that selects and assigns the input or output delta. `AmountDeltaTrace` adds a
common cost-preserving interface to the existing delta routines.
`SwapStepInputDeltaTrace` proves pc 19615→19635;
`SwapStepOutputDeltaTrace` proves pc 20607→20631;
`SwapStepTailDeltaTrace` proves pc 19697→19714 and pc 20667→20684.
The source build passed 3547 jobs and the trace build 3537 jobs
(`/tmp/swap-step-delta-source-build.log`, `/tmp/swap-step-delta-trace-build.log`).
The audit `/tmp/swap-step-delta-audit.log` has 0 native facts for the source,
551 for the delta interface, and 594/602/622 for the three composed traces;
only the accepted standard/concrete axioms appear.

The fee dependencies are complete. `SwapStepFeeWords` / `SwapStepFeeSource`
cover rounded fees and the special 100% fee branch; `SwapStepFeeTrace` /
`SwapStepTargetFeeTrace` prove the input/output fee paths. `WordSubAdd` proves
the wrapping subtraction identity used by the compiler. `SwapStepRemainingWords`,
`SwapStepRemainingSource`, and `SwapStepRemainingTrace` cover signed remaining
amount conversion, available input after fees, and the non-target fee remainder.
Builds passed (`/tmp/swap-step-fee-trace-build.log`,
`/tmp/swap-step-remaining-build.log`, 3539 jobs). The audit
`/tmp/swap-step-fee-audit.log` is clean: source/arithmetic declarations have
0 native facts, target fee trace 279, output fee trace 234, available-input trace
121, and remainder trace 17. Conditional arithmetic trace interfaces use pairs
of success/failure implications to avoid evaluating symbolic word arithmetic.

The complete swap-step dependency is now proved. `SwapStepSelectWords`,
`SwapStepPriceSource`, `SwapStepInputPartialSource`, `SwapStepInputSelectSource`,
`SwapStepOutputSelectSource`, and `SwapStepSelectFrame` prove price selection and
its local values. The selection traces preserve the original caller stack,
including the duplicated step pointer and fee. `SwapStepWords` gives the four
result words and all arithmetic failure conditions. `SwapStepInputSource` /
`SwapStepOutputSource` compose each source branch; `SwapStepResultSource`,
`SwapStepPreludeSource`, and `SwapStepSource` prove function 104 and its internal
call. `SwapStepInputTrace` / `SwapStepOutputTrace` / `SwapStepTrace` reach pc 19714
from the inlined input/output entries, with unchanged memory/active words and
the incoming gas-cost floor. Successful prices are proved canonical uint160s.
The combined build passed all 3639 jobs (`/tmp/swap-step-complete-build.log`).
The audit `/tmp/swap-step-complete-audit.log` is clean: source call and canonical
bound 0 native facts, combined trace 1731, input trace 1349, output trace 1054.
Only the standard three Lean axioms and concrete evaluation facts appear.

`ValueLocals` supplies generic local-update projection lemmas. Using the current
frame for each boolean update, and rewriting the contract projection explicitly,
avoids elaboration expanding nested symbolic stores. No heartbeat increases,
source changes, new placeholders, or semantic assumptions were needed.

`SwapTargetWords` and `SwapTargetSource` prove function 105 and its internal
call. `WordXorSelect` proves the compiler's XOR/MUL selection identity.
`SwapStepStartTrace` proves pc 19479 through the exact-input/output branch,
including the preceding price store and the target selector. `SwapTargetStepTrace`
composes this with the complete step trace through pc 19714, retaining exact
memory, active words, and the cost floor. The combined build passed 3622 jobs
(`/tmp/swap-target-complete-build.log`). Audit `/tmp/swap-target-audit.log`:
source call and selection identity 0 native facts, entry trace 110, composed
trace 1836; only accepted axioms appear.

`BitMath_leastSignificantBit` (function 113) is complete. `WordLowBitPower`
proves the general isolated-bit power characterization. `LeastSignificantBit`
checks the concrete lookup tables over all 256 bit values, including the
nonzero division denominator and compiled shift/mask formula.
`LeastSignificantBitSource` proves the body and call, and
`LeastSignificantBitTrace` proves the inlined pc 21213→21435 calculation,
including its next-tick expression. Build `/tmp/swap-lsb-complete-build.log`
passed 3528 jobs. Audit `/tmp/swap-lsb-audit.log`: general bit characterization
0 native facts, source call and compiled identity 1 each, trace 65; no
unexpected axioms. Matching the generated constants as `UInt256.ofNat`
keeps the trace elaboration below three seconds.

The scan's `compress` and `position` functions (111/112) are complete.
`TickCompressWords` / `TickCompressSource` cover negative-remainder correction,
zero spacing, and the final int24 cast. `TickCompressTrace` proves pc
19221→19234/21109, including the explicit SMOD boundary. The source/word
audit has 0 native facts, the trace 29 (`/tmp/swap-tick-compress-audit.log`).
`SignedQuotientSource` also replaces the duplicate quotient proof in
`TickSpacingSource`. `TickPositionWords` / `TickPositionSource` cover both the
signed word position and unsigned low byte. `WordSignedField` proves signed
normalization for every valid width; the existing int24/int128 proofs and the
new int16 proof use it. Combined helper build: 3527 jobs
(`/tmp/swap-tick-helpers-build.log`); position/generic-field audit:
`/tmp/swap-tick-position-audit.log`, 0 native facts and no unexpected axioms.

Bitmap scanning (function 103) is complete. `WordNarrowCast` and
`WordNarrowArithmeticSource` relate deferred int24 casts to the compiler's
arithmetic, including low-byte preservation. `TickScanMask`,
`TickScanNextWords` / `TickScanNextSource`, and `TickScanWords` supply the
common word model. The source proof is split into syntax, storage-read
prelude, initialized-bit selection, and branch composition; `TickScanSource`
proves the whole body and its internal call. `TickScanStorageTrace`, the two
read traces, and the two next-tick traces compose in `TickScanTrace` from
pc 19221 through the common join at pc 19401. Both directions retain exact
scratch memory, active words, and the incoming cost floor. The caller's
duplicated stack words match block 19169; the combined stack bound is R+33.

Build `/tmp/swap-scan-complete-build.log` passed 3584 jobs. Audit
`/tmp/swap-scan-complete-audit.log`: source call 1 native fact (the least-bit
table), combined trace 458; left/right read traces 102/114, left/right next
traces 112/121. All arithmetic, cast, mask, and storage-read bridges have
0 native facts. No unexpected axioms or added placeholders. For expensive
word expressions, simplifying the selected `if` branch before composing its
identity avoids kernel recursion; raising heartbeat limits was unnecessary.

Tick crossing (function 106) is complete. `TickCrossWords` models both
outside-fee writes and the subsequent packed-liquidity read in bytecode order.
`TickCrossSource` proves the body and internal call, including a static
violation at the first write. `TickCrossStorageTrace` connects scratch-memory
hashing and the successive account maps without a slot noncollision premise.
`TickCrossTrace` covers pc 20029→20104/20082 with exact memory, active words,
post-state, and a retained cost floor; `TickCrossStatic` proves the first
SSTORE halt. Build `/tmp/swap-tick-cross-trace-build.log` passed 3533 jobs.
Audit `/tmp/swap-tick-cross-audit.log`: source and storage bridges 0 native
facts, normal trace 96, static trace 28; no unexpected axioms or placeholders.

Tick clamping and the scan/price trace connection are complete.
`TickClampWords` proves the signed bounds, int24 canonicality, and absolute
tick bound. `PoolSwapSyntax` exposes function 76's loop body; the clamp syntax
is checked against its actual statements. `PoolSwapStepWords`,
`TickClampSource`, and `TickClampPriceSource` prove the two source checks and
the modular price call. `TickClampMemory` retains the ordered stores.
`TickClampLowerTrace` / `TickClampUpperTrace` compose in `TickClampTrace`;
`tickClampPriceTrace` includes the bounded TickMath call. `TickScanPriceTrace`
now spans pc 19221→19479, with exact scratch/step memory, active words, and
cost floor (R+33). Build `/tmp/swap-scan-price-build.log`: 3596 jobs passed.
Audit `/tmp/swap-scan-price-audit.log`: arithmetic/memory bridges 0 native
facts, clamp+price source 1 (existing TickMath table), clamp trace 91,
clamp+price trace 690, scan+clamp+price trace 1143; no unexpected axioms.
For list tails expressed as `List.append`, explicit `change R.length+n ≤
1024; omega` avoids a simplifier mismatch at the composition boundaries.

The first eight source statements of the pool loop are assembled in
`PoolSwapScanSource`: initial price store, bitmap storage alias, modular scan
call, tuple assignments, both clamps, and the modular price call.
`PoolSwapValues` models the parameter and result structs; `PoolSwapScanSyntax`
extracts the generated storage-alias identifier from the checked AST.
`PoolSwapScanStartTrace` covers pc 19169→19221 and composes with the scan/price
trace in `PoolSwapScanPriceTrace` (pc 19169→19479). Build
`/tmp/swap-loop-scan-build.log` passed 3621 jobs. Audit
`/tmp/swap-loop-scan-audit.log`: combined source 2 native table facts, start
trace 31, combined trace 1172; no unexpected axioms.

`UnsafeMath_simpleMulDiv` (78) is complete. `SimpleMulDivSource` covers the
zero-denominator branch, wrapped multiplication, division, and internal call.
`SimpleMulDivTrace` covers its inlined Q128 use and fee-growth store at
pc 20222→19833, with exact memory and a cost floor. The shift identity reuses
`wordMulPow2`. Build `/tmp/swap-simple-muldiv-build.log`: 3519 jobs passed;
audit `/tmp/swap-simple-muldiv-audit.log`: source 0 native facts, trace 27,
no unexpected axioms.

LP-fee override helpers (98/99/110) are complete in `LPFeeOverrideSource` and
`LPFeeOverrideTrace`. The latter covers flag removal and both validation
outcomes at pc 18928→18941. Build `/tmp/swap-lp-override-build.log`: 3505 jobs
passed; audit `/tmp/swap-lp-override-audit.log`: all three source calls 0 native
facts, trace 44, no unexpected axioms.

Protocol-fee selection/calculation (95/97/101) and packed fee getters (96/100)
are complete in `Slot0FeeSource`, `ProtocolSwapFeeWords`,
`ProtocolSwapFeeSource`, and `ProtocolSwapFeeTrace`. The arithmetic proof
shows the combined fee is canonical uint24 for all canonical LP fees, and
the traces cover both packed directional extractions, stored LP fee, and
the inlined combination at pc 22219→18951. Build
`/tmp/swap-protocol-fee-build.log`: 3513 jobs passed; audit
`/tmp/swap-protocol-fee-audit.log`: all five source calls and arithmetic
bounds 0 native facts; direction trace 23, stored LP trace 16, combination
trace 24; no unexpected axioms. Shared right-shift lemmas are now in
`WordOperationsSource` (including the lemma moved from `TickPriceWords`),
and `WordBoundedArithmeticSource` supplies uncast bounded add/multiply.

The next loop segment is complete: `PoolSwapComputeSource` assigns the tick
price, calls target selection and computeSwapStep, then assigns all four
returned fields (loop statements 8–14). `PoolSwapScanComputeSource` joins it
to the first eight statements, with exact success/revert outcomes.
`PoolSwapComputeStoreTrace` handles the four memory writes and mode branch;
`PoolSwapComputeTrace` composes pc 19479 through computeSwapStep to
19740/20320, preserving the exact memory and a cost floor. Builds
`/tmp/swap-loop-compute-build.log` (3654 jobs) and
`/tmp/swap-loop-scan-compute-build.log` (3643 jobs) passed. Audit
`/tmp/swap-loop-compute-audit.log`: compute source 0 native facts, combined
first-15 source 2 table facts, store trace 52, combined compute trace 1883;
no unexpected axioms. `TickPriceWords` also rebuilt after moving its shared
right-shift lemma.

Statement 15, amount accounting, is complete in `PoolSwapAmountSource` and
`PoolSwapAmountTrace`, with separate input/output modules. The proof covers
checked SafeCast calls and amountCalculated arithmetic, with wrapping
amountSpecifiedRemaining. The exact-output branch also checks
amountIn+feeAmount for uint256 overflow; the exact-input branch wraps that
sum. `SignedSubSource` and `SignedSubGuard` supply shared checked-subtraction
facts. The trace joins both entries (19740/20320) at pc 19794 with unchanged
memory and a cost floor. Build `/tmp/swap-loop-amount-wrapper-build.log`
passed 3541 jobs. Audit `/tmp/swap-loop-amount-audit.log`: all source and
arithmetic lemmas 0 native facts; input trace 147, output trace 124,
combined trace 249; no unexpected axioms. AST evidence is in
`/tmp/swap-amount-syntax.log`.

Statements 16–17 are complete in `PoolSwapProtocolSource`/`Trace` and
`PoolSwapGrowthSource`/`Trace`, assembled in `PoolSwapFeeSource` and
`PoolSwapFeeTrace`. They cover zero/nonzero protocol fees, both share
formulas, wrapping fee/protocol-total updates, and zero/nonzero liquidity
for LP fee growth. The trace covers pc 19794→19833 with exact memory writes
and a cost floor. The combined trace leaves explicit post-write load
premises for the eventual allocation invariant. Build
`/tmp/swap-loop-fee-combined-build.log`: 3538 jobs passed. Audit
`/tmp/swap-loop-fee-audit.log`: all three source theorems 0 native facts;
protocol trace 90, growth trace 50, combined trace 135; no unexpected axioms.
The same audit log contains the checked AST of statement 18.

Statement 18 is complete in `PoolSwapTickSource` and `PoolSwapTickTrace`,
using separate boundary-tick, price-recomputation, and initialized-tick
crossing modules. The proof covers both directions, ordered fee-growth
storage writes, wrapping int128 negation, checked liquidity addition,
static violation, and TickMath failure. The trace covers pc 19833→19964,
with exact memory, active words, post-state, and a cost floor. Its explicit
post-write load premises will be supplied by the allocation invariant.
Build `/tmp/swap-loop-tick-trace-build.log`: 3616 jobs passed. Audit
`/tmp/swap-loop-tick-audit.log`: boundary/cross source and delta bounds 0
native facts; reprice and combined source 1 existing TickMath fact;
boundary trace 46, reprice 1101, cross prepare 56, cross liquidity 81,
cross combined 249, tick branch 44, tick combined 1442; no unexpected
axioms. No heartbeat increases were needed.

The complete loop body is now assembled in `PoolSwapIterationSource` and
`PoolSwapIterationTrace`. `PoolSwapAccountingSource`/`Trace` combine the
last four statements; `PoolSwapScanComputeTrace` combines the first fifteen.
The iteration trace covers pc 19169→19155, including the backedge, exact
stack updates, source-matched terminal outcomes, a memory invariant, and
a strict cost increase. `WordStructMemory` provides reusable indexed-field
and disjoint-write rules. `PoolSwapMemory`, `PoolSwapMemoryFields`,
`PoolSwapComputeMemory`, and `PoolSwapAccountingMemory` prove preservation
of the three allocated structs and discharge all intermediate load
premises. Memory-aware scan/compute wrappers keep the composition modular
and avoid kernel recursion from substituting large concrete memory terms.
Build `/tmp/swap-loop-iteration-trace-build.log`: 3839 jobs passed. Audit
`/tmp/swap-loop-iteration-audit.log`: all audited memory lemmas 0 native
facts; accounting source 1, iteration source 2; memory-aware scan trace
1172, compute 1883, scan+compute 3047, accounting 1816, iteration 4172;
no unexpected axioms or new placeholders.

The source-local and canonicality invariant is complete in
`PoolSwapTickFrame`, `PoolSwapTickPost`, `PoolSwapLoopLocals`,
`PoolSwapScanComputeLocals`, `PoolSwapAccountingPost`, and
`PoolSwapIterationPost`. `PoolSwapLoopInvariant` packages the source locals,
memory views, and price/tick/liquidity bounds. `PoolSwapIterationCorrect`
connects source execution and EVM reachability while preserving this
invariant. `Signed24Bounds` supplies the scan's signed absolute-value bound.
`PoolSwapLoopCondition`/`Trace` prove the short-circuit condition and both
exits. `PoolSwapLoopCorrect` proves the whole while statement by induction
on remaining gas, using strict body cost progress and `RD.oog_of_cost_gt`.
Build `/tmp/swap-loop-correct-build.log`: 3851 jobs passed. Audit
`/tmp/swap-loop-complete-audit.log`: signed bounds, tick-frame/canonical
facts, and source condition 0 native facts; iteration post 1, iteration
correctness 4172, condition trace 49, loop fuel/correctness 4216; no
unexpected axioms.

The loop interface now preserves caller memory from byte 64 up to the first
allocated step/result object, total memory size, and saved `slot0Start` and
`swapDelta` locals. `MemoryWindowEq`, `PoolSwapMemoryWindow`,
`PoolSwapComputeWindow`, `PoolSwapAccountingWindow`, and `PoolSwapSavedLocals`
provide the preservation facts carried through the traces and induction.
Build `/tmp/swap-loop-preserved-build.log`: 3856 jobs passed. Audit
`/tmp/swap-loop-preserved-audit.log`: the new preservation lemmas use 0 native
facts; iteration correctness 4172 and loop correctness 4216 remain unchanged;
no unexpected axioms. The active ABI remains `swap`; work continues on the
pool function's exit storage and return code. The enclosing pool function,
public hooks/accounting, and `donate` remain unfinished.

The pool exit is complete in `PoolSwapFinishStorage`, `PoolSwapStoreSource`,
`PoolSwapSlot0Packing`, `PoolSwapStoreStatic`, `PoolSwapSlot0StoreTrace`, and
`PoolSwapStoreTrace`. These prove ordered slot0/liquidity/fee-growth updates,
including unchanged liquidity and static failure at the first SSTORE.
`PoolSwapDeltaWords`, `PoolSwapDeltaSource`, `SafeCast128WordTrace`,
`PoolSwapDeltaBranchesTrace`, and `PoolSwapDeltaTrace` prove both checked
int128 conversion orders, overflow reverts, and BalanceDelta packing.
`PoolSwapFinishSource`/`Trace` cover source statements 29–35 and EVM
pc 21536 through the dynamic internal return. `PoolSwapLoopFinishCorrect`
joins the loop and exit, carrying canonical returned structs, caller-memory
preservation, and the accumulated cost floor. The loop's `tag` stack word
is saved `slot0Start`; its `x1` is the return PC.
Build `/tmp/swap-loop-finish-build.log`: 3882 jobs passed. Audit
`/tmp/swap-finish-audit.log`: storage/packing/delta/finish source lemmas 0
native facts; static trace 34, slot0/liquidity trace 125, full storage trace
194, delta trace 109, finish trace 298, loop+finish correctness 4502;
no unexpected axioms or new placeholders. Work continues on the pool setup
(source statements 0–27), before public swap hooks and accounting.

The complete internal `Pool_swap` body and call wrapper are now proved in
`PoolSwapBodyCorrect` and `PoolSwapCallCorrect`. `PoolSwapPreludeSource`
assembles source statements 0–27 from the input, protocol, result, LP-fee,
fee, mode, zero-amount, limit, and step source modules. It covers invalid
overrides, exact-output rejection at a full fee, zero-amount early return,
both price-limit directions, and loop initialization. Small frame projection
lemmas and `PoolSwapSetupLocals` keep elaboration within the default heartbeat
limit. `PoolSwapPreludeTrace` covers pc 18777→19155 or the early return/revert,
including both allocations, storage reads, all guards, exact memory and active
words, and a cost floor. `WordStructInitMemory`, `PoolSwapResultMemory`, and
`PoolSwapAllocatedMemory` establish the loop memory invariant and preserve the
caller parameter object. The result object starts at the incoming free pointer;
the step object starts 96 bytes later and occupies 256 bytes.

The body theorem accepts a params `WordStructView`, params ≥128, its 160-byte
span below the result pointer, result pointer+352 ≤ `solcMaxU64`, canonical
int24 spacing/uint160 limit/uint24 override, and stack tail+36 ≤1024.
The capacity premise still must be discharged by the public caller, including
the required out-of-gas cases. `PoolSwapBodyReturn` separates the zero-amount
return (exact allocated result memory) from the complete loop-return interface
(canonical result, params/step views, saved caller memory, and cost floor).
The call wrapper uses `internalCallFunctionExec`, with no caller inlining.
Next: normalize this return interface as needed by `_swap`, prove its protocol
fee update and Swap event, then the public swap hooks and accounting. The active
ABI remains `swap`; `donate` has not been started.

Build `/tmp/swap-call-correct-build.log`: 3935 jobs passed. Audit
`/tmp/swap-body-audit.log`: setup source and memory view 0 native facts; setup
trace 675; loop+finish 4502; full body and call wrapper 5172; no unexpected
axioms. Only the original `Swap.lean:27` and `Donate.lean:27` placeholders remain.
The setup fee helper is named `PoolSwapFeeInitTrace`; the existing loop
`PoolSwapFeeTrace` composes protocol and growth traces and retains its audited
135 native facts. An initial naming collision was corrected and the entire
dependent loop chain rebuilt successfully.

The complete internal `_swap` wrapper (function 20) is now proved in
`SwapWrapperBodyCorrect` and `SwapWrapperCallCorrect`, with no placeholders.
`ProtocolFeesUpdateSource` proves function 77 (`_updateProtocolFees`) and its
call wrapper; `ProtocolFeesUpdateTrace` covers its inlined mapping update at
pc 2003→1766, and `ProtocolFeesUpdateStatic` covers the SSTORE at 2041.
`SwapWrapperSource` unpacks the pool result and credits protocol fees;
`SwapWrapperEventSource` calls the balance-delta component helpers, emits Swap,
and returns delta. `SwapWrapperEventMemory`/`Trace`/`Static` cover pc 1766→1930,
including the LOG3 at 1905. `SwapWrapperTailTrace` covers the fee branch at
1755, both static failures, and the event. Mapping writes retain source order.

`PoolSwapReturnMemory` and `PoolSwapReturnView` normalize both pool return
paths. The result is canonical, the free pointer is incoming state+96 or
state+352, memory size is `max initial.size free.toNat`, and every caller
slice from byte 96 through the incoming state pointer is preserved.
`SwapWrapperReturn` carries the scalar result, RD1930, unchanged execution
environment and original account snapshot, and `SwapWrapperMemory`: free
pointer between state+96 and state+352, size `max initial.size (free+192)`,
and preserved caller slices. The event writes six words at the free pointer.

The wrapper entry is the Pool_swap entry pc 18777 with stack
`[poolSlot id, params, 1755, id, 16777215, callerParams, currency,
x8, x9, x10, x11, x12, x13, hookPtr, 32, junk] ++ R`.
It requires tail+49 ≤1024 and the same allocation/parameter premises as
Pool_swap. Its exit at 1930 retains the caller stack and loads hookPtr;
the following AND/jump to the after-swap hook remains caller work.

Composition exposed a missing original-account-snapshot invariant needed by
later hooks. `PoolSwapOriginalAccounts` now proves it through crossing and
finish stores. `PoolSwapIterationCorrect`, `PoolSwapLoopCorrect`,
`PoolSwapLoopFinishCorrect`, and the return interfaces carry it. The loop,
full-body, and call correctness theorems now require `evm.σ₀ = s0.σ₀` after
the execution-environment premise. All dependent modules were rebuilt.

Build `/tmp/swap-wrapper-call-build.log`: 3960 jobs passed. Audit
`/tmp/swap-wrapper-audit.log`: fee-update source, wrapper tail source,
original-account preservation, and pool return view use 0 native facts;
fee-update trace 28; Pool_swap body/call 5172; `_swap` body/call 5359.
No unexpected axioms.

`Hooks_beforeSwap` (function 37) is now complete. `SwapParams`, `SwapHookABI`,
and `SwapHookSource` provide the shared three-field parameter and hook payload
codecs. `BytesUintSlice` shares the unsigned return-word decoder.
`BeforeSwapAmountSource`, `BeforeSwapDeltaSource`, `BeforeSwapFeeSource`,
`BeforeSwapReplySource`, `BeforeSwapBranchSource`, `BeforeSwapSource`, and
`BeforeSwapCall` prove the complete source behavior, including reply-length,
checked signed-addition, and direction-preservation reverts.

`BeforeSwapKeyEncodeMemory` / `BeforeSwapKeyEncodeTrace` cover the interleaved
sender/key encoding at pc 15230→15382, reusing `PoolKeyEncodeMemory`.
`SwapParamsEncodeMemory` / `SwapParamsEncodeTrace` cover the three parameter
stores. `BeforeSwapEncodeTrace` and `BeforeSwapPrepareTrace` compose the full
payload and checked allocation. `BeforeSwapActiveTrace` invokes the existing
paid-memory hook-call proof. The encoder reaches pc 14575, whose allocator is
`wordBytesCallTailAllocationTrace` (not the pc 7990 variant).

`BeforeSwapReturnTrace`, `BeforeSwapAmountTrace`, `BeforeSwapDeltaTrace`,
`BeforeSwapFeeTrace`, `BeforeSwapParseTrace`, and `BeforeSwapReplyTrace` cover
all reply paths. The compiled function returns the raw fee word; the caller
masks it to 24 bits. `beforeSwapRawFee_clean` proves that the cleaned word is
the source's uint24 result. `BeforeSwapBranchTrace` connects callback and
parser; `BeforeSwapEntryTrace` handles self-call bypass and the disabled flag.
`BeforeSwapReplyMemory` proves reply allocation and caller-slice preservation.

`BeforeSwapBodyCorrect` / `BeforeSwapCallCorrect` connect the complete internal
function at pc 15172 to any valid return pc. Entry stack:
`[hook, keyPtr, paramsPtr, src, len, ret] ++ R`, with tail+24≤1024.
The normal return stack is `[rawFee, hookReturn, amount] ++ R`, and its source
tuple is `(amount, hookReturn, fee)`. `BeforeSwapReturn` retains cleaned-fee
equality and canonicality, source environment/original accounts, paid memory,
the new free pointer with 4,000 bytes of room, and every caller slice between
96 and the initial free pointer. The entry allows `Cₘ aw ≤ C+63` because its
first block pays 63 gas. Inputs include canonical key/price, source slices
before the free pointer, `free+len+480 < 2^256`, `free+4000 ≤ solcMaxU64`, and
the existing runtime gas bound.

Build `/tmp/before-swap-call-correct-build.log`: 3634 jobs passed. Audit
`/tmp/before-swap-complete-audit.log`: source body/call 4 concrete native facts,
entry trace 81, branch trace 708, return-memory connection 0, full body/call
781. No unexpected axioms. The new shared codec and BeforeSwap modules have
no `sorry`, `admit`, or authored axioms. No heartbeat increase was needed.
When rewriting generated memory, keep `UInt256.ofNat` constants in the same
form as the summaries. Local irreducibility on the reply/branch result models
prevents eager byte decoding during theorem application.

The source body and internal call for `Hooks_afterSwap` (38) are now proved.
`AfterSwapUpdateSource` checks the reply's signed-128 cast and addition;
`AfterSwapBranchSource` composes encoding and `Hooks_callHookWithReturnDelta`;
`AfterSwapPackSource` selects the token order; `AfterSwapFinishSource` performs
the checked packed-delta subtraction and returns both deltas.
`AfterSwapSelectionSource`, `AfterSwapSource`, and `AfterSwapCall` compose
active/disabled/self branches and preserve the required locals and range facts.
Build `/tmp/after-swap-call-build.log`: 3563 jobs passed. Audit
`/tmp/after-swap-source-audit.log`: update, packing, and finish 0 native facts;
callback branch, full body, and call 4. No unexpected axioms.

`Hooks_afterSwap` (38) is now complete through `AfterSwapBodyCorrect` and
`AfterSwapCallCorrect`. `AfterSwapKeyEncodeMemory` / `Trace`,
`AfterSwapEncodeTrace`, and `AfterSwapPrepareTrace` cover its eleven-word
payload and allocation at pc 15936→17823. `HookDeltaReplyTrace` now also exports
`hookDeltaReplyCostTrace`; its legacy interface is a projection of that proof.
`HookDeltaPaidTrace` preserves paid memory and the callback allocation bound.
`AfterSwapActiveTrace` and `AfterSwapBranchTrace` connect the callback to the
checked signed-128 cast and addition in `AfterSwapUpdateTrace`.

`AfterSwapPackTrace` selects token order from the parameter object;
`BalanceDeltaSubCostTrace` retains cost through the existing subtraction proof.
`AfterSwapFinishSelectTrace`, `AfterSwapFinishActiveTrace`, and
`AfterSwapFinishTrace` cover zero/nonzero deltas, checked subtraction, and return.
`AfterSwapEntryTrace` covers self bypass and the disabled hook flag.
`AfterSwapReplyMemory` preserves caller slices. `AfterSwapReturn` retains
environment/original accounts, paid memory, free pointer with 64 bytes of
room, and the same saved-slice predicate as `BeforeSwapReturnMemory`.
Both memory interfaces now specialize `HookReturnMemory room`; the before
hook retains its 4,000-byte margin while the after hook requires only 64.

Entry pc 15745 has stack `[hook, keyPtr, paramsPtr, delta, src, len, before, ret]
++ R`, with tail+26≤1024. Normal return is `[hookDelta, delta] ++ R`, while the
source tuple is `(delta, hookDelta)`. Premises include paramsPtr≥96, canonical
key/price, both objects below free, `free+len+512 < 2^256`,
`free+64 ≤ solcMaxU64`, and `Cₘ aw ≤ C+84`.

Build `/tmp/after-swap-call-correct-build.log`: 3659 jobs passed. Audit
`/tmp/after-swap-complete-audit.log`: source body/call 4 concrete native facts;
reply cost 50; paid hook delta 310; entry 80; prepare 229; branch 640; finish 217;
return-memory connection 0; full body/call 900. No unexpected axioms or new
placeholders. The call wrapper needed `dsimp only [cf, afterSwapCallFrame]`
before passing its contract equality; unrestricted definitional equality tried
to unfold the contract and hit the default heartbeat limit. No limit was raised.

The public swap proof is complete (2026-10-10). `SwapPreludeSource`, `SwapDecodeMemory`,
the generic `BoolWordDecode`, `SwapParamsDecode`, `SwapABI`, and
`SwapDecodeTrace` compile. The decoder starts at 1328 and ends at
1488 with `[len, src, 160, 384, 352, 320] ++ R`; free pointer is 416 and the
parameter object begins at 320. The public AST is `/tmp/public-swap-ast.log`;
hook ASTs remain in `/tmp/before-swap-ast.log`. Donate remains after Swap.
`SwapValidationSource` / `Trace`, `SwapAccountingCorrect`, and
`SwapAfterCorrect` compile. The latter composes source statements 25–31:
after-hook call, tuple assignments, both accounting calls, and ABI return.
The shared `assignTuplePair` also replaces the duplicate assignment proof in
`ModifyLiquidityAfterSource`.

The `Pool_swap` and `_swap` proofs now retain paid memory (`Cₘ aw ≤ C`) in
their call and return interfaces. `PoolSwapActiveWords` proves that the loop's
fixed allocation covers every access; `PoolSwapResultActiveWords` and
`PoolSwapPreludeActiveWords` establish it. `PoolSwapProtocolCostBlock` shares
the pc 18793 prefix and uses `RD.sloadMono` to retain costs across SLOAD.
`ProtocolFeesUpdatePaidTrace` and the event trace complete the wrapper proof.
Build `/tmp/swap-wrapper-paid-call-build.log` passed 3967 jobs. Audit
`/tmp/swap-public-infrastructure-audit.log` checked 16 declarations, including
both complete pool calls, hooks, decoder, validation, and accounting: only the
standard axioms and concrete native facts. No heartbeat increase was needed.

`SwapPoolSource` and `Allocate160Trace` compile. `poolSwapParamsValue` now uses
the existing public source literal's named-field order (tickSpacing,
zeroForOne, amountSpecified, sqrtPriceLimitX96, lpFeeOverride); this is a proof
representation change, with no specification edit. `SwapPoolMemory`,
`SwapPoolAllocateTrace`, `SwapPoolSelectTrace`, `SwapPoolCorrect`,
`SwapBeforeSource` / `Correct`, and `SwapBodyCorrect` complete both currency
branches and source composition. `assignTuplePair` now accepts a remaining
tuple tail, so the before-hook's three assignments reuse it. `Swap.lean`
connects dispatcher pc 1279, ABI decoding, all guards, hooks, pool swap,
accounting, and return. Build `/tmp/swap-public-build.log` passed 4128 jobs;
the shared-helper regression `/tmp/swap-tuple-regression-build.log` rebuilt
ModifyLiquidity successfully (3999 jobs).

Audit `/tmp/swap-complete-audit.log` checked ten declarations. The public
theorem depends on 7651 concrete native facts and the standard three axioms;
no unexpected axioms or `sorryAx`. No heartbeat increase or spec edit.
This brought the proof count to 32/33 public ABIs plus the constructor. The final
Donate proof is complete as described below. Its source AST was checked in
`/tmp/donate-ast.log`; the generated block interfaces for pc 9980–10650 are
`/tmp/donate-blocks.txt`.

### Donate completed (2026-10-10)

`Donate.lean` connects dispatcher pc 9980, the pool-key/two-amount/bytes decoder,
nonpayable and calldata guards, lock/delegate-call/initialization checks,
`Hooks_beforeDonate`, `Pool_donate`, balance accounting, the event,
`Hooks_afterDonate`, and the signed balance-delta return. It covers malformed
calldata, zero liquidity, int128 cast failures, accounting overflow, failed or
invalid hook replies, static violations, and the memory-allocation out-of-gas
branches under the existing gas bound.

`PoolDonateModel`, `PoolDonateDeltaSource`, `PoolDonateGrowthSource`,
`PoolDonateTailSource`, and `PoolDonateSource` give the internal source proof.
`PoolDonateCastTrace`, `PoolDonateGrowthTrace`, `PoolDonateStatic`, and
`PoolDonateTrace` establish its bytecode trace. The two fee-growth writes follow
the bytecode's read/write order, including aliased slots, without a noncollision
assumption. Before/after hook encoding and execution share the Bool-parameterized
`DonateHook*` helpers; `BeforeDonateHookTrace` and `AfterDonateHookTrace` specialize
them. `DonateEvent*` handles the event, and the `Donate*Correct` modules compose
all steps through the public result.

The accounting trace now exposes the memory-cost inequality needed by a later
hook. `AccountDeltaTrace`, `AccountDeltaCallTrace`, `AccountPoolTrace`, and
`AccountPoolCallTrace` retain their previous interfaces as wrappers around the
stronger cost lemmas. `functionResultTrace_mono` is defined once in
`FunctionResultTrace`; `FunctionTraceMono` preserves its existing import path.
The full capstone build also rebuilt Swap and ModifyLiquidity successfully.
No heartbeat limit or specification change was required for Donate.

### ModifyLiquidity completed (2026-10-10)

The public `modifyLiquidity` proof is complete and axiom-audited. The following
notes record its dependency proofs and public assembly. The active ABI is now
`swap`; `donate` follows it.

`PoolTicksSource` proves function 60 (`Pool_checkTicks`) and its call wrapper.
`PoolTicksTrace` proves the inlined pc 5584 through 5680 checks, including all three
revert branches and the parameter-object stores performed by the first block.
The source audit uses only the three standard axioms; the trace uses 150 native
facts plus those axioms.

`LiquidityAddSource` proves function 73 (`LiquidityMath_addDelta`), including
negative-sum and uint128-overflow rejection. `LiquidityAddTrace` proves pc 17774
through its return or revert using the same mathematical sum. Its source audit
uses only the standard three axioms; its trace uses 46 native facts plus those
axioms (`/tmp/modify-leaves-axioms.log`). `UnsignedRangeSource` generalizes the
source range test by width, and `UnsignedWordRange` proves the corresponding
shift test on encoded signed integers. Both leaves compile without placeholders.

`Slot0TickSource` proves function 69 (`Slot0Library_tick`) and its call wrapper,
using the existing sign-extension lemmas. The extracted word is canonical int24.
`Pool_updateTick` (function 61) now has a complete source body and call wrapper in
`PoolUpdateTickSource` and `PoolUpdateTickCall`. Its prelude, fee initialization,
checked net-liquidity update, and final write are split into small modules.
`ResolvedStorage`, `TickStorage`, and `PoolFeeGrowthStorage` prove the mapping
alias and field operations. The second global fee read is explicitly taken
after the first tick fee write; no mapping-slot noncollision assumption is used.
`SignedRangeSource`, `Signed128Range`, `TickLiquidityWords`, `TickGrossWords`,
and `TickNetArithmetic` share the range, packing, and signed arithmetic facts.

The source body and call audits use only the three standard axioms.
`Int128AddTrace`, `TickUpperNetTrace`, and `PoolUpdateTickFeeTrace` build and audit
with respectively 55, 58, and 69 concrete native facts plus the standard axioms
(`/tmp/modify-update-tick-axioms.log`). `TickFeeGuardTrace` proves the current-tick
guards for both inlined updates. `TickLowerStartTrace` proves the lower tick hash
and read at pc 6949, and `TickLowerFeeTrace` proves its zero-gross/fee branch.
`TickLowerTrace`/`TickLowerStoreTrace` and `TickUpperTrace`/`TickUpperStoreTrace`
now cover both complete inlined updates, including their final storage writes.
`PoolUpdateTickLowerCorrect` and `PoolUpdateTickUpperCorrect` connect those traces
to `poolUpdateTickResult`, the result proved by the source body and call wrapper.
They preserve execution environment and original accounts, retain the uint128
return bound, and cover every revert/static branch in source order. The lower
continuation reads the upper tick from the state after the lower write.
`TickResultMemory` proves that the lower result stores and mapping scratch writes
preserve the pool-slot word for the upper update.

The complete lower and upper result audits use respectively 315 and 295 concrete
native facts plus the three standard axioms; the memory proof uses only the
standard axioms (`/tmp/modify-update-tick-correct-axioms.log`). All these modules
build without placeholders.

Function 62 (`Pool_tickSpacingToMaxLiquidityPerTick`) is also complete.
`TickSpacingSource` proves its body and call wrapper, including zero spacing.
`SignedDivisionWords`, `SignedRemainderWords`, and `WordIntegerArithmetic` give
generic mathematical bridges for SDIV, SMOD, and integer word arithmetic;
`SignedDivisionSource` and `SignedModStep` supply the source expression rules and
the missing generic SMOD reachability step. `TickSpacingArithmetic` proves the
exact compiled limit, and `TickSpacingTrace`/`TickSpacingCheckTrace` cover pc 7329
through 7256 or either gross-liquidity-limit revert. The source, arithmetic, and
SMOD step audits use only the three standard axioms; the complete check trace
uses 107 concrete native facts plus those axioms (`/tmp/modify-spacing-axioms.log`).
Function 63 (`TickBitmap_flipTick`) is complete. `TickBitmapStorage`,
`TickBitmapArithmetic`, `TickBitmapPrelude`, and `TickBitmapSource` prove the
mapping access, signed compression, source body, and call wrapper.
`TickBitmapStoreStatic`, `TickBitmapStoreTrace`, and `TickBitmapTrace` cover
pc 16652 through the dynamic return, the alignment revert, or static halt.
`TickBitmapCorrect` connects the result while preserving the execution
environment and original accounts. The caller's tick bound (absolute value at
most 887272) justifies the compiler's direct use of SAR 8 as the int16 key.
The source and arithmetic audits use only the three standard axioms; the result
trace uses 91 concrete native facts plus those axioms
(`/tmp/modify-bitmap-axioms.log`). All modules build without placeholders.

Function 64 (`Pool_getFeeGrowthInside`) is complete. `PoolFeeInsideRegion`,
`PoolFeeInsidePrelude`, and `PoolFeeInsideSource` prove its three wrapping
subtraction formulas, body, and call wrapper. `PoolFeeInsideMemory` preserves
words above mapping scratch space. `PoolFeeInsideStartTrace`,
`PoolFeeInsideRegionTrace`, and `PoolFeeInsideTrace` connect pc 5722 to pc 5802
through all three regions, using unchanged source accounts and exact fee words.
The source and memory proofs use only the standard axioms; the complete trace
audit is `/tmp/modify-fee-axioms.log`. All these modules build without placeholders.

Function 90 (`Position_calculatePositionKey`) and function 65 (`Position_get`)
are complete for this caller. `PackedWordABI` and `PositionKeySource` prove the
58-byte packed encoding and key body/call. `PositionKeyMemory` proves the four
overlapping stores produce that exact byte sequence; `PositionKeyCompiled`
connects the hash and cleanup writes. `PositionStorage` proves the position
reference and packed liquidity read. `PositionGetSource`, `PositionGetMemory`,
and `PositionGetTrace` connect pc 5802 to pc 5915 with the position slot, its
initial liquidity word, exact memory, and unchanged accounts. The source,
storage, key, and memory audits use only the standard axioms; the complete get
trace uses 67 concrete native facts plus those axioms
(`/tmp/modify-position-key-axioms.log`, `/tmp/modify-position-get-axioms.log`).

Function 91 (`FullMath_mulDiv`) is complete for the Q128 specialization used
by this caller. `WordMulModSource`, `WordBorrowSource`, and `WordLocals` provide
the reusable expression and frame lemmas. `FullMathWords`, `FullMathPrelude`,
`FullMath128Reduce`, `FullMath128Inverse`, and `FullMath128Source` prove the
source body and call, including overflow rejection and both return branches.
`FullMath128Trace` connects pc 22275 through 22359/22396 to any valid return
destination, preserving memory and accounts, or reaches the shared revert.
The body and call use only the standard axioms; the trace audit is
`/tmp/modify-full-math-axioms.log`. All modules build without placeholders.
The general-denominator specialization will still need a proof when a caller
requires it.

Function 66 (`Position_update`) is complete for this caller.
`WordPackedStore` proves packed unsigned writes at offset zero for arbitrary
byte widths, preserving the high bits. `PositionWriteStorage` connects the
liquidity and fee fields. `PositionFeesStoreSource`, `PositionFeesSource`,
`LiquidityAddWords`, `PositionLiquiditySource`, and `PositionUpdateSource`
prove the full source body and call. The original liquidity is used for both
fee calculations, and fee reads occur after any liquidity write.
`PositionStoreStatic` proves both first-SSTORE static halts.
`PositionFeesComputeTrace`, `PositionFeesTrace`, `PositionLiquidityTrace`,
and `PositionUpdateCorrect` cover pc 5915 through pc 12458, with all source
reverts, static halts, exact returned fee words, unchanged memory, and the
source post-state accounts. The trace preserves the execution environment
and original accounts. Source/storage proofs use only the standard axioms;
the complete result trace uses 276 concrete native facts plus those axioms.
Audits are `/tmp/modify-position-update-axioms.log` and
`/tmp/modify-position-correct-axioms.log`. All modules build without placeholders.

The next fee conversions `SafeCast_toInt128_uint256` (compiled pc 12458) are
already covered by `SafeCast.lean` (body, successful/reverting calls and traces).
Function 67, `toBalanceDelta`, is complete for this caller. `WordSignedShiftSource`
proves signed SHL, and `BalanceDeltaSource` proves packing, body, and call for
arbitrary signed words. `BalanceDeltaTrace` connects the inlined pc 5999 routine
through its caller's next liquidity-sign branch to pc 6620/6036. Its source
audit uses the standard axioms, and its trace uses 42 concrete native facts
plus those axioms (`/tmp/modify-balance-delta-axioms.log`).
Function 68, `Pool_clearTick`, is complete. `TickClearSource` proves the three
ordered zero writes, body, and call. `TickClearStatic`, `TickClearTrace`, and
`TickClearCorrect` cover both inlined paths at pc 6642 and 6686, including static
halts and the exact hash memory. The body and call use only the standard axioms;
each result trace uses 59 concrete native facts plus those axioms
(`/tmp/modify-tick-clear-axioms.log`). All four modules build.
General-denominator `FullMath_mulDiv` is complete. `WordLowBit` proves the
nonzero lowest-bit mask by induction. `FullMathGeneralWords`, `FullMathReduce`,
`FullMathInverse`, and `FullMathSource` model and execute the full source
algorithm; `FullMathTrace` connects pc 22851 to an arbitrary valid return pc,
including the short-product path and all six inverse updates. The mask, body,
and call audits use only standard axioms; the trace uses 161 concrete native
facts plus those axioms (`/tmp/modify-full-math-general-axioms.log`). All build.
The Q128 reduction and inverse now reuse the general proofs and build.
Function 108, `FullMath_mulDivRoundingUp`, is complete in `FullMathRoundWords`,
`FullMathRoundSource`, and `FullMathRoundTrace`. The trace covers pc 23656 through
the general division call, exact division, increment, and overflow revert. The
body and call use only standard axioms; the trace uses 213 concrete native facts
plus those axioms (`/tmp/modify-full-math-round-axioms.log`). All modules build.
Function 107, `UnsafeMath_divRoundingUp`, is complete in `DivRoundWords`,
`WordModSource`, `DivRoundSource`, and `DivRoundTrace`. The arithmetic bound
justifies the unbounded source addition, including the zero-denominator case.
The trace at pc 23318 preserves memory and accounts. The body/call audit uses
standard axioms; the trace adds 14 concrete native facts
(`/tmp/modify-div-round-axioms.log`).
Function 93, the unsigned `SqrtPriceMath_getAmount0Delta` overload, is complete.
`Amount0Words`, `WordBoundedSubSource`, `Amount0Sort`, `Amount0Numerators`,
`Amount0Branches`, and `Amount0Source` cover the source body and call.
`Amount0CoreTrace` and `Amount0Trace` connect both compiled entries (23165 for
rounding up, 23348 for rounding down), including sorted prices and every revert.
The body/call audit uses standard axioms; the up/down traces add 303/257 concrete
native facts (`/tmp/modify-amount0-axioms.log`). All modules build.
Function 92, `SafeCast_toInt256`, is complete in `SafeCast256Source` and
`SafeCast256Trace`. The body/call use standard axioms; traces for pc 17653 and
17691 add 29/27 concrete native facts (`/tmp/modify-safe-cast256-axioms.log`).
The duplicate signed-shift proof was removed: `WordSignedShiftSource` now imports
the existing lemma in `WordSignedSource`, and `BalanceDeltaSource` rebuilds.
Function 70, the signed amount-zero helper, is complete. `LiquidityMagnitude`
covers both signs, including the minimum int128 value and the wrapping cast.
`CheckedAmountSource`/`CheckedAmountTrace` share the checked return and negation.
`SignedAmount0Words`, `SignedAmount0Path`, `SignedAmount0Source`,
`SignedAmount0PathTrace`, and `SignedAmount0Trace` compose the entire helper from
pc 17703 to any valid return pc. Body/call use standard axioms; the trace adds
483 concrete native facts (`/tmp/modify-signed-amount0-axioms.log`). All build.
Function 18, signed `SafeCast_toInt128`, is complete in `SafeCast128Source`
and `SafeCast128Trace`. `SignedNormalizeRange` characterizes when a signed cast
preserves its input, and `Signextend128Range` connects that range check to the
compiled sign-extension comparison. The source body/call use only the three
standard axioms; the trace uses 36 concrete native facts plus those axioms.
Functions 109 (`SqrtPriceMath_absDiff`) and 94 (unsigned amount-one) are complete.
`AbsDiffWords`/`AbsDiffSource` connect the conditional source difference with the
compiled SAR/ADD/XOR idiom. `FullMath96Words`/`FullMath96Trace` specialize the
existing general FullMath model to Q96, sharing shift facts in `WordPow2`.
`Amount1Words`, `Amount1TailSource`, `Amount1Source`, and `Amount1Trace` cover the
rounded and unrounded paths at pc 23010/23101. Their source proofs use only the
three standard axioms; the Q96 and amount-one traces add 103/171 concrete native
facts (`/tmp/modify-amount1-axioms.log`).
Function 72, signed amount-one, is complete in `SignedAmount1Words`,
`SignedAmount1Path`, `SignedAmount1Source`, `SignedAmount1PathTrace`, and
`SignedAmount1Trace`, from pc 17610 to an arbitrary valid return pc. Its body/call
use standard axioms; the trace adds 262 native facts. `SignedAmountSource`,
`CheckedAmountPath`, and `CheckedAmountPathTrace` now share the signed branch and
checked-return composition with amount-zero. Both source/trace pairs rebuild;
amount-zero's audit remains 483 native facts plus the standard axioms
(`/tmp/modify-signed-amount-axioms.log`). `WordBoolean` shares the existing
nonzero-word fact with hook validation. No source semantics changed.
Source composition for function 17, `Pool_modifyLiquidity`, is in progress;
all its direct internal callees have proofs. `PoolModifyPrelude` proves the
initial locals and tick validation. `PoolModifyTicks` proves the entire first
conditional mutation, including both tick updates, gross-liquidity limits,
and both bitmap flips. The upper tick is read after the lower tick's writes.
The lowered source's generated storage aliases are included explicitly.
`PoolModifyContext` records the locals preserved through those calls.
`CallContinuation`, `BlockContinuation`, `ConditionalSource`, `LocalStruct`,
and `TupleLocals` contain reusable source-composition lemmas.

`PoolModifyFees` proves statements 8–22 of the lowered body: fee-growth lookup,
position lookup, position update, both checked fee conversions, and packing
and assigning `feeDelta`. `PoolModifyClears` proves statement 23, including
the negative-delta guard and both conditional clears. `PoolLiquidityStorage`
and `PoolModifyLiquidity` prove the packed uint128 pool-liquidity access and
checked update used in the middle price region. All these modules build, and
their source audits contain only `propext`, `Classical.choice`, and `Quot.sound`
(`/tmp/modify-pool-composition-axioms.log`).

The source proof for statement 24, the three amount-calculation regions, is complete.
`SignedAmountsSource` and `CheckedSignedAmount` share the signed amount call
and int128 check. `BalanceDeltaAssign` shares packing and assignment.
`PoolModifyRegionAmount`, `PoolModifyInside`, and `PoolModifyPricePrelude`
build. `PoolModifyOutside` separates its price lookups, checked amount, and
packing to keep kernel reduction shallow. `PoolModifyAmounts`, its frame/result
lemmas, `PoolModifyFinish`, and `PoolModifyAccounting` compose all regions and
the return. `PoolModifySource.poolModifyBody` and `PoolModifyCall` now build
(`/tmp/modify-pool-source2.log`). Their axiom audit contains the three standard
axioms and the concrete `tickSqrtRangeCheck` native fact
(`/tmp/modify-pool-source-axioms.log`). Function 17's bytecode composition is
the active work; the three public placeholders remain.

Function 17's trace now covers the allocator and initial state, the complete
tick-mutation block, and fee/position accounting. `Allocate128Trace` retains
the compiler capacity-failure branch and exact counters. `PoolModifyStartTrace`
initializes the four-word state record. `PoolModifyTicksTrace` composes both
tick updates, limits, and bitmap branches, including zero delta, reverts, and
static halts; its audit reports 755 concrete native facts plus the standard
three axioms (`/tmp/modify-pool-ticks-trace-axioms.log`). `BlockResultTrace`
shares normal/terminal continuation composition. `PoolModifyFeesTrace` joins
fee-growth and position lookups, the ordered position writes, both checked
fee conversions, and packing (`/tmp/modify-pool-fees-trace.log`).

Function 17's complete inlined trace now builds in `PoolModifyTrace`, from pc 5584
through the caller's pc 6046 boundary. It covers parameter construction, tick
validation, allocation and state initialization, both tick updates, fee/position
accounting, conditional tick clears, all three amount regions, and the two packed
return values. `PoolModifyClearsTrace` includes the negative-delta stack shuffle;
`PoolModifyAmountsTrace` includes the zero-delta path. `PoolModifyRegionAmountTrace`
shares the four amount/cast calls through `PoolModifyCheckedAmountTrace` and
`CheckedSignedAmountTrace`; the in-range branch preserves the packed liquidity
word and covers arithmetic failure and the static SSTORE halt. Memory framing is
in `PoolModifyTicksMemory`, `PoolModifyAccountingMemory`, `PoolModifyAllocationMemory`,
and `PoolModifyParamsMemory`. The full trace assumes the caller-established
parameter/state allocation geometry and `ptr + 128 <= solcMaxU64`; discharging
that capacity condition at the public entry remains part of public composition.
`Allocate128Trace` retains the failure path for that later gas argument.

The focused full-trace build passes (`/tmp/modify-pool-trace.log`, 3813 jobs).
Its audit reports 3,251 concrete native facts and the three standard Lean axioms,
with no unexpected dependencies (`/tmp/modify-pool-trace-axioms.log`). The same
audit covers the amount trace (1,597 native facts), accounting trace (2,304),
clear trace (159), fee trace (610), and source call (one concrete TickMath audit).
The public `ModifyLiquidity.lean`, `Swap.lean`, and `Donate.lean` placeholders
remain; no other Lean placeholders or project-authored axioms were found.
Packed-delta addition and subtraction now have complete source and bytecode
proofs in `BalanceDeltaCombineSource`, `BalanceDeltaAddTrace`, and
`BalanceDeltaSubTrace`. The traces retain both checked int128 casts. Addition
reaches pc 6084, where the caller packs the result and emits its event. The
focused build passes (`/tmp/modify-balance-combine-traces.log`); the trace audits
report 68 and 74 native facts, respectively, plus the three standard axioms,
and both source audits use only standard axioms (`/tmp/modify-balance-audit.log`).

Function 19, `_accountPoolBalanceDelta`, is complete in `AccountPoolSource`
and `AccountPoolTrace`. It accounts currency 0 and then currency 1, preserving
that order even when keys alias. `AccountDeltaCallTrace` supplies the source
result bridge and scratch-memory framing. The build passes
(`/tmp/modify-account-pool-trace.log`); the pool trace has 209 native facts,
the delta bridge 174, and the source call zero, all with only the three standard
axioms beyond those facts (`/tmp/modify-account-pool-audit.log`).

Function 32, `Hooks_callHookWithReturnDelta`, is complete in `HookDeltaSource`,
`HookDeltaReplyTrace`, and `HookDeltaTrace`, including skipped parsing, the exact
64-byte reply check, and signed decoding. `SignedBytesDecode` and
`BytesObjectWord` supply reusable decoding and memory lemmas. Its focused build
passes (`/tmp/modify-hook-delta-trace.log`). The trace audit has 309 native facts
plus the standard three; the source call has only the standard three.

The source proof for function 35, `Hooks_beforeModifyLiquidity`, now builds in
`BeforeLiquiditySource` and `BeforeLiquidityCall`. `LiquidityHookABI` and
`LiquidityHookSource` cover add/remove selectors and both before/after payload
layouts. `HookWrapperSource` shares the permission expression and payload call
block with initialize. The before-hook source and ABI encoder audits each have
four concrete native facts plus standard axioms; the shared wrapper uses only
standard axioms (`/tmp/modify-liquidity-helpers-audit.log`).

Function 35's complete compiled trace now builds in `BeforeLiquidityHookTrace`.
It includes the caller-equals-hook shortcut, both permission checks, canonical
struct copies, dynamic calldata copying, allocation, hook invocation and reply
validation, and the continuation at pc 5511. `BeforeLiquidityAllocationGas`
discharges payload-capacity failures under the existing gas bound. The encoder
retains both copying/expansion costs and a lower bound on active memory.
`LiquidityStructEncodeTrace` shares the key/parameter copies;
`BytesValueTrace`, `WordBytesCallMemory`, and `WordBytesCallAllocation` generalize
the dynamic-tail machinery. `BytesCallTrace` now uses the common bytes-value
trace. `MemorySlice.returnData` shares framing previously specific to pool keys.
`NatSubBounds` supplies proved linear lower bounds to prevent exponential
case splitting across chains of natural-number gas subtractions.

The complete before-hook trace audit has 668 concrete native facts and the three
standard axioms; its branch trace has 549, preparation 266, and encoder 154.
The allocation-gas proof has only standard axioms. Selector-word byte identities
use kernel evaluation (`/tmp/modify-before-liquidity-trace-audit.log`). The full
capstone regression build exposed a duplicate `hookFlagExpr` declaration from
the shared-wrapper refactor; that new Boolean permission expression was renamed
`hookPermissionExpr`, keeping the older validation expression intact. The
capstone rebuild passes (`/tmp/modify-hook-capstone-check.log`, 3,888 jobs),
including the new before-hook trace and source call. The placeholder scan still
finds only the three public ABI placeholders; no project-authored axioms occur.

Function 36, `Hooks_afterModifyLiquidity`, now has complete source and compiled
proofs in `AfterLiquidityCall` and `AfterLiquidityHookTrace`. They cover the
self-caller shortcut, positive/nonpositive liquidity selection, both permission
bits, the complete payload encoder/allocator, the shared external hook call,
optional delta parsing, malformed replies, checked packed-delta subtraction,
and the two returned words at an arbitrary valid continuation. The trace starts
at pc 14427 and requires the existing gas bound, paid memory potential, and
caller-established struct/calldata geometry. Public composition must establish
those entry facts. No specification or semantics changed in this segment.

`AfterLiquidityStructEncodeTrace` reuses the before-hook struct memory proofs.
`WordBytesCallTailAllocation` handles the compiler's allocation continuation
without an extra stack argument. `WordBytesCallAllocation_arith`,
`wordBytesCallAllocation_end_toNat`, and `WordBytesCallAllocationGas` share the
header arithmetic, rounded free pointer, and capacity-failure gas argument with
the before hook. The source call proof uses restricted `dsimp only` for its
frame's contract projection: plain definitional equality unnecessarily evaluates
the six-entry HashMap and exhausts heartbeats.

The complete regression build passes (`/tmp/modify-after-liquidity-capstone.log`,
3,914 jobs), including `Correct`, both hook traces, and both source call theorems.
The after-hook trace audit reports 837 concrete native facts plus the standard
three axioms; active branch 716, preparation 311, encoder 164, and source call 4.
The source result normalization, generic allocation-gas proof, and selector-word
byte identity use no native facts. There are no unexpected axioms
(`/tmp/modify-after-liquidity-audit.log`). The scan still finds only the three
public ABI placeholders, with no project-authored axioms.

Public `ModifyLiquidity` now has complete ABI decoding, source prelude, compiled
decoding, lock/delegate/pool validation, and the source/compiled before-hook
connection. `ModifyLiquidityBeforeCorrect` preserves the key and liquidity
parameter records, cached pool slot, environment, and initial account map. It
also retains a 4,000-byte allocation margin and paid memory potential at pc 5511.
The public caller's pool call is now connected through pc 6046. The active
obligation is preserving its memory gas bound through the pool continuation,
then completing the public delta/event/after-hook/accounting/return sequence.
Swap and donate remain outstanding.

`HookCallPaidPrefixTrace`, `HookReplyCostTrace`, `HookCallPaidTrace`, and
`MemoryPaidBound` retain the call/copy memory costs and derive the post-reply
allocation margin under the existing gas bound. The original hook-call and
reply interfaces remain available. The before-hook continuation now carries
paid memory; `BeforeLiquidityReplyMemory` supplies the byte-slice preservation
and free-pointer bounds used by public composition. No specification or
semantics changed.

The regression build passes (`/tmp/modify-entry-final-build.log`, 3,932 jobs),
including `Correct`, public decode/validation, before-hook correctness, and the
after-hook trace. The audit `/tmp/modify-entry-audit.log` reports no unexpected
axioms: ABI decoder 4 concrete native facts, compiled decoder 418, source
prelude/validation 0, compiled validation 117, before-hook correctness 673,
before-hook trace 669, paid call prefix 149, cost-preserving reply 119, paid hook
call 263, and after-hook trace 837. The allocation-bound lemmas use only standard
axioms.

`ModifyLiquidityPoolPreludeSource`, `ModifyLiquidityPoolPrepareTrace`, and
`ModifyLiquidityPoolCorrect` connect source statements 16–19 to the inlined
`Pool_modifyLiquidity` proof. The signed-128 cast revert and parameter allocation
guard are covered. The normal continuation has the two packed pool deltas at
pc 6046, the exact source return frame, preserved caller key/parameter records,
and a 3,600-byte allocation margin. `PoolModifyPreserveMemory` proves those byte
slice and free-pointer facts for arbitrary caller memory. The public return
predicate now also retains `Cₘ aw ≤ C` through the complete inlined pool call.

`ReachCost` proves fuel independence above remaining gas and rebases an existing
routine to retain its incoming cost floor. `BlockTraceCost` applies the same
construction to source block traces. These generic proofs use only standard
axioms. `BalanceDeltaAddCostTrace` reuses the existing add-delta proof with its
cost floor retained. This avoids propagating counter inequalities through all
of the pool's arithmetic dependencies.

The remaining memory work uses exact active-word summaries. The lower/upper
tick entry, fee guard, net path, store, source return, two-tick update, and spacing
limit now expose exact active words. Their original interfaces are projections
of those stronger proofs. `PoolModifyTickActiveWords` shows that the two-tick
update does not expand memory when its state record is already active.
`PoolModifyTwoTicksPaidTrace` and `PoolModifyLimitsPaidTrace` retain paid memory
through the update and subsequent liquidity-limit checks using `BlockTraceCost`.

The bitmap, tick-clear, fee-growth, position, and amount paths now expose exact
active words. Their legacy interfaces project the stronger proofs.
`PoolModifyPaidTrace` composes the complete paid pool call: initial allocations,
tick updates and bitmap flips, fee and position preparation, conditional clears,
and amount arithmetic. `ReachCostExists` and `ResultTraceCostExists` retain costs
when the continuation also carries existential stack values. `PositionGetCostBlock`
retains the scratch-memory expansion cost across the storage access at pc 5912.
Its arithmetic proof sums separate inequalities before calling `omega` with
`splitNatSub := false`; splitting all fifteen truncated subtractions is too costly.
The gas bound and semantics are unchanged.

The paid-pool build `/tmp/pool-paid-capstone-build.log` passes (3,900 jobs).
The audit `/tmp/pool-paid-audit.log` is clean: public pool correctness 3,305
concrete native facts, paid pool trace 3,251, position cost block 67, paid tick
trace 755, paid fees 610, and paid post-fee continuation 1,751. The generic
existential cost-retention lemmas use only standard axioms.

The public tail now has built proofs for checked delta addition and event emission
(`ModifyLiquidityDeltaCorrect`), the after-hook call and tuple assignments
(`ModifyLiquidityAfterCorrect`), and conditional hook accounting, caller accounting,
and the two-word ABI return (`ModifyLiquidityAccountingCorrect`). The event covers
its static halt with the source `emitStatic` rule. `AfterLiquidityReplyMemory`
preserves the pool key and free pointer across callback reply allocation.
`MemoryAccessCost`, `AccountPoolMemory`, `AccountPoolCallTrace`, `SignedPairABI`,
`ABIResultTrace`, and `BlockCorrectComposition` provide the supporting composition
and memory facts. The latest accounting build passes in
`/tmp/modify-accounting-correct-build.log`; the event/static connection passes in
`/tmp/modify-delta-static-build.log`.

`ModifyLiquidityPoolFinishCorrect`, `ModifyLiquidityHooksCorrect`, and
`ModifyLiquidityBodyCorrect` now compose the complete public execution.
`ModifyLiquidity.lean` connects its dispatcher arm, nonpayable and calldata
guards, ABI decoding, source prelude, and execution proof. The capstone build
passes (`/tmp/modify-liquidity-capstone-build.log`, 4,228 jobs).

The audit `/tmp/modify-liquidity-complete-audit.log` reports no unexpected axioms:
public refinement 5,501 concrete native facts, hooks/pool continuation 4,841,
delta/event correctness 179, after-hook correctness 842, and accounting 270.
Generic block composition, ABI refinement glue, and memory-cost telescoping use
only standard axioms. Diagnostic traces were removed. Projection proofs for
nested source frames use `simp only` on the frame definition; direct `rfl` can
eagerly reduce symbolic packed-delta arithmetic and exhaust heartbeats. No
heartbeat increase was needed for the finished assembly.

The pool connection audit (`/tmp/modify-pool-audit.log`) has no unexpected
axioms: public pool correctness 3,305 concrete native facts, preparation 90,
delta-add cost trace 68, exact and paid two-tick traces 490 each, lower tick source
return 315, upper return 295, and exact/paid spacing-limit traces 107 each.
All 19 audited declarations are clean. Byte-slice preservation, active-word bounds,
fuel independence, and cost rebasing use only standard axioms. The regression
build `/tmp/modify-pool-capstone-build.log` passes (4,176 jobs). The final regression
`/tmp/modify-pool-final-build.log` also passes (4,179 jobs), including `Correct`,
the public pool connection, both paid pool prefixes, delta addition, public
decoding, and the after-hook trace. The latest placeholder scan reports exactly
`Swap.lean:27` and `Donate.lean:27`; there are no project-authored axioms. The
overall refinement remains unfinished.

### Unlock completed

`Unlock.lean` now proves the complete public refinement. `UnlockBodyTrace` joins
entry decoding, lock checks, static halts, request construction, and the callback.
`UnlockFinishTrace` connects the callback to the return decoder and closing lock
store. `BytesResultTrace` supplies generic refinement glue for one bytes return.
The proof covers arbitrary legal dynamic offsets, callback failure/depth limits,
malformed reply decoding, nonzero final delta count, and successful return.

`UnlockAllocationFailureGas.unlockAllocationFailure_outOfGas` discharges both
compiler capacity checks under the existing strict `poolManagerGasBound`. The
entry costs compose as 339 + 16 + 197 + 117 + 271 + 154 = 1094, excluding memory
expansion, input-copy words, and the callback's net gas. `CallGasEvidence` retains
the actual Theta input/returned gas. No call costs or gas inequalities are assumed.
`AllocationPanicGas` retains another 23 operation gas before REVERT. Above the
critical reply range, the proof uses parent memory, callee memory, and the raw
reply copy cost; parent/callee memory alone does not suffice near the boundary.

The critical range uses a proved 18-gas callback lower bound. `BytesWordOverlap`
shows a large valid payload needs offset at least 32; `UnlockReplyFootprint` finds
two nonzero bytes at least 32 apart. `MemoryFootprint` assigns memory potentials
0, 7, or 14. `OperationPotential*`, `RecursiveOperationGas`,
`StepCallOperationGas`, `RecursiveOperationPotential`, and `CalleeOperationGas`
prove that memory/stack potential plus remaining gas cannot increase across any
successful opcode, including recursive calls. `CalleeReturnWork` additionally
retains four units spent by RETURN. Fresh EVM execution therefore pays memory
expansion plus 14 + 4 for the critical valid reply. `ThetaSuccess`,
`CallbackOperationGas`, `CalleeReturnGas`, and `CallbackMemoryGas` carry these
facts through the exact opaque callback witness.

Native precompiles are handled separately and exhaustively. `PrecompileSmallOutput`
strengthens the fixed output bounds to 64 bytes using the existing checked FFI
output theorems. `PrecompileExpmodGas` shows the callback selector makes modexp's
base-length word too large for any uint256 gas allowance. `UnlockCallbackPrefix`
shows identity's echoed request fails the return ABI offset bound. `PrecompileReply`
and `UnlockPrecompile` conclude that every valid precompile reply is at most 64
bytes, which satisfies both allocators. All these facts are proved locally;
EVMLean and the provided bytecode/summary files remain unchanged.

The public Unlock axiom audit reports 665 dependencies: 662 concrete native-decide
facts plus `propext`, `Classical.choice`, and `Quot.sound`. There are no unexpected
axioms or placeholder dependencies. The capstone rebuild succeeds (3737 jobs).
Four ABI obligations remain: Initialize,
ModifyLiquidity, Swap, and Donate. The tight gas-bound audit below remains valid.

## Verified specification correction (2026-10-09)

During the `exttload(bytes32[])` proof, a legal empty array with one trailing
calldata byte exposed a specification error in `calldataWordAt`: its direct
`uint256(data[offset + j])` cast is rejected by Solm because indexing bytes
produces `bytes1`. Both `exttload(bytes32[])` and `extsload(bytes32[])` returned
64 bytes successfully in the EVM while Solm reported `spec stuck: assign: type error`.
The specification now converts through `uint8` before widening to `uint256`.
The diagnostic is `EmptyArrayDiagnostic.lean`; run it with
`lake env lean --run Benchmarks/UniswapV4PoolManager/EmptyArrayDiagnostic.lean`.
All four diagnostic cases agree on success after the correction. The full differential
suite was rerun afterward: 1875 cases, 1856 agree (634 successful), zero disagreements
and zero stuck cases, 15 out-of-gas cases and four allocation-limit cases.
This correction changes only the Solm model; the pinned Solidity and bytecode are unchanged.

## Compiler settings and provenance

- Upstream: `Uniswap/v4-core`, commit `46c6834698c48bc4a463a86d8420f4eb1d7f3b75`.
- Main contract: `src/PoolManager.sol:PoolManager`; 45 source units in `contracts/`.
- Solmate: `4b47a19038b798b4a33d9749d25e570443520647`.
- Compiler: `0.8.26+commit.8a97fa7a.Linux.g++`; binary SHA-256
  `d5f23436f443edb85d8e76906d12f0a86ce0490e7663a9e608efeb7a93f149ef`.
- Settings from the pinned `foundry.toml`: optimizer enabled, 44,444,444 runs,
  via IR, Cancun, metadata bytecode hash `none`. The build manifest records the
  six upstream remappings. The exact 0.8.26 pragma and upstream settings take
  precedence over the scaffold prompt's general compiler advice.
- Runtime: 24,009 bytes, including 12 metadata bytes. Creation: 24,194 bytes;
  its executable prefix is 185 bytes.
- Repository generator baseline: `57ab07976ac45cf5aa4c26fb1d3063dd998a5739`.
  Source changes are confined to this directory. Generation used `--no-register`.

The initial command, run at the repository root with the import closure already
in `contracts/`, was:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/scaffold.py all \
  --dir Benchmarks/UniswapV4PoolManager \
  --solc /tmp/equivm-solc-0.8.26 --main src/PoolManager.sol --contract PoolManager \
  --runs 44444444 --via-ir --evm-version cancun \
  --module Benchmarks.UniswapV4PoolManager --metadata-hash none \
  --remapping @ensdomains/=node_modules/@ensdomains/ \
  --remapping @openzeppelin/=lib/openzeppelin-contracts/ \
  --remapping ds-test/=lib/forge-std/lib/ds-test/src/ \
  --remapping forge-std/=lib/forge-std/src/ \
  --remapping hardhat/=node_modules/hardhat/ \
  --remapping solmate/=lib/solmate/ --no-register
```

Final checks:

```text
python3 scripts/scaffold.py check --dir Benchmarks/UniswapV4PoolManager
ok   poolManagerBytecode matches the hex artifact
ok   validJumps: matches the JUMPDEST scan
ok   poolManagerCreationBytecode matches the hex artifact
ok   creationValidJumps: matches the JUMPDEST scan
ok   Selectors.lean: 33 entries match the ABI in SpecSyntax order
ok   Immutables.lean offsets match immutableReferences
ok   sources.sha256 verified

lake build Benchmarks.UniswapV4PoolManager.Correct
Build completed successfully (3585 jobs).
```

## Differential run

The full run used seed **2026**, count **50**, before the final bytecode walk and
again after adding the refinement hypotheses. Its command and results are:

```sh
# In the isolated package described below:
lake --log-level=error exe solm-difftest --only PoolManager --count 50 --seed 2026
```

```text
PoolManager: 1875 cases: 1856 agree (634 successful), 0 disagree, 0 stuck, 15 EVM out of gas, 0 spec out of fuel, 4 unsupported (allocation cap)
```

The coverage line, wrapped at transition boundaries, reports `successful/cases`:

```text
constructor 17/25; balanceOf(address,uint256) 44/56;
supportsInterface(bytes4) 33/52; transfer(address,uint256,uint256) 8/53;
settle() 0/51; initialize((address,address,uint24,int24,address),uint160) 1/52;
mint(address,uint256,uint256) 0/54; extsload(bytes32) 46/53;
extsload(bytes32,uint256) 25/54; extsload(bytes32[]) 41/53;
take(address,address,uint256) 0/56; setProtocolFeeController(address) 10/50;
collectProtocolFees(address,address,uint256) 3/53; settleFor(address) 0/57;
approve(address,uint256,uint256) 36/52; unlock(bytes) 0/53;
donate((address,address,uint24,int24,address),uint256,uint256,bytes) 0/53;
setOperator(address,bool) 35/51; allowance(address,address,uint256) 41/51;
modifyLiquidity((address,address,uint24,int24,address),(int24,int24,int256,bytes32),bytes) 0/52;
sync(address) 11/53; owner() 48/53;
updateDynamicLPFee((address,address,uint24,int24,address),uint24) 0/55;
exttload(bytes32[]) 43/52; exttload(bytes32) 45/55;
swap((address,address,uint24,int24,address),(bool,int256,uint160),bytes) 0/51;
isOperator(address,address) 46/57; clear(address,uint256) 0/53;
setProtocolFee((address,address,uint24,int24,address),uint24) 0/52;
protocolFeeController() 47/52; transferOwnership(address) 3/50;
burn(address,uint256,uint256) 0/53; protocolFeesAccrued(address) 45/54;
transferFrom(address,address,uint256,uint256) 6/54; stray 0/100.
```

The random generator does not seed the hashed transient lock word or an initialized
pool at the matching pool-key hash. Those guards explain the zero-success locked
operations, fee setter, and dynamic-fee update. Its standard callees do not return
ABI-encoded `bytes` for `unlockCallback`, explaining `unlock`. Unmatched selectors
always revert, so `stray` correctly has no success. The 19 inconclusive cases are
gas exhaustion or the interpreter's allocation cap, not specification failures.

Two focused sequences supplemented that coverage. A constructor plus 21 successful
runtime calls covered unlock, initialization, protocol fee setup, adding/removing
liquidity, both swap directions and amount signs, donation, fee collection,
mint/burn, take, native/ERC20 settlement, settleFor, clear, sync, and dynamic-fee
updates. A second constructor plus seven successful calls exercised all ten hook
callbacks, dirty selector padding, and nonzero hook deltas. Every comparison agreed
on success. These fixtures seed the lock to exercise valid mid-unlock entry states;
they do not simulate an entire reentrant unlock transaction.

Additional arithmetic diagnostics checked all 256 single-bit positions and adjacent
intervals for BitMath, selected TickMath boundaries and round trips, and 294 FullMath
boundary combinations. These supplement the bytecode review, not the proofs.

To reproduce the full run without changing the global target registry, run this
setup at the repository root, then run the command above in the printed directory.
It uses the repository CLI and harness with only this target registered. Running
`--only PoolManager` at the repository root alone does not register it.

```python
from pathlib import Path
import json

repo = Path.cwd().resolve()
test_dir = Path('/tmp/uniswap-v4-difftest')
test_dir.mkdir(exist_ok=True)
test_dir.joinpath('lakefile.toml').write_text(
    'name = "PoolManagerDiff"\nversion = "0.1.0"\n'
    '[[require]]\nname = "EquiVM"\npath = ' + json.dumps(str(repo)) + '\n'
    '[[lean_exe]]\nname = "solm-difftest"\nroot = "Main"\n')
test_dir.joinpath('lean-toolchain').write_text(repo.joinpath('lean-toolchain').read_text())
main = repo.joinpath('Tests/DiffTest/Main.lean').read_text()
main = main.replace('import Tests.DiffTest.Targets',
    'import Benchmarks.UniswapV4PoolManager.DiffTarget')
main = main.replace('open Solm.DiffTest Tests.DiffTest',
    'open Solm.DiffTest\n\ndef allTargets : List Target :=\n'
    '  [Benchmarks.UniswapV4PoolManager.diffTarget]')
test_dir.joinpath('Main.lean').write_text(main)
manifest = json.loads(repo.joinpath('lake-manifest.json').read_text())
manifest['name'] = 'PoolManagerDiff'
manifest['packagesDir'] = str(repo / '.lake/packages')
manifest['packages'].append(dict(type='path', name='EquiVM', dir=str(repo),
    manifestFile='lake-manifest.json', configFile='lakefile.toml', inherited=False))
test_dir.joinpath('lake-manifest.json').write_text(json.dumps(manifest))
# The evmlean FFI build expects its test corpus relative to the working directory.
corpus = test_dir / 'EthereumTests'
if not corpus.exists():
    corpus.symlink_to(repo / '.lake/packages/evmlean/EthereumTests', target_is_directory=True)
print(test_dir)
```

<details>
<summary>Focused successful-path fixture</summary>

Save as `/tmp/uniswap-v4-focused.lean` and run
`lake env lean --run /tmp/uniswap-v4-focused.lean` at the repository root after
`lake build Benchmarks.UniswapV4PoolManager.DiffTarget`.

```lean
import Benchmarks.UniswapV4PoolManager.DiffTarget
open Solm Solm.DiffTest Solm.Interp ABI Ethereum Ethereum.EVM
open Benchmarks.UniswapV4PoolManager

def addressValue (n : Nat) : Value := .address (EVM.address n)
def intValue (n : Int) : Value := .int n
def zeroSalt : Value := .fixedBytes ⟨31, by decide⟩ (List.replicate 32 0)
def poolKeyValue (fee := 3000) (hooks := 0) : Value :=
  .tuple [addressValue 0, addressValue 0x5000, intValue fee, intValue 60, addressValue hooks]
def liqParams (n : Int) : Value := .tuple [intValue (-120), intValue 120, intValue n, zeroSalt]
def swapParams (direction : Bool) (n : Int) (limit : Nat) : Value :=
  .tuple [.bool direction, intValue n, intValue limit]

def setTransient (t : Target) (σ : AccountMap) (slot value : Nat) : AccountMap :=
  let evm := initialState σ σ (.ofNat t.gas) default (t.env t.runtime t.selfAddress 0 .empty true)
  match t.config.transientBackend.write
    { base := "rawTransient", steps := [.aindex (.int slot)] }
    (.elem (.int (.uint ⟨256, by decide⟩))) (.int value) evm with
  | .ok e => e.accountMap
  | _ => σ

def invoke (t : Target) (σ : AccountMap) (name : String) (args : List Value)
    (caller := 0x2000) (value := 0) : IO AccountMap := do
  let some tr := t.contract.transitions.find? (·.name == name) | throw (IO.userError s!"no transition {name}")
  let some cd := encodeCallWithSelector? ((Ethereum.KEC (String.toByteArray (transitionSigStr tr))).extract 0 4) (tr.params.map Param.ty) args
    | throw (IO.userError s!"encoding {name}")
  let c : Case := {
    label := name
    σ := transferValue σ (EVM.address caller) t.selfAddress value
    I := t.env t.runtime (EVM.address caller) value cd true
  }
  let result := runCase t c
  IO.println s!"{name}: {result.verdict.describe}"
  match result.verdict with
  | .agree "success" => return result.postState.getD σ
  | .agree why => throw (IO.userError s!"{name} unexpectedly {why}; calldata {hex cd}")
  | _ => throw (IO.userError s!"{name} failed; calldata {hex cd}")

def main : IO Unit := do
  let (target, _) := diffTarget.resolveRuntime (Rng.ofSeed 2026)
  let target := { target with callees := target.callees ++ [(EVM.address 0x6000, callee (wordBytes 32 ++ wordBytes 0))] }
  let (ctor, σ?) := runConstructor target poolManagerCreationBytecode [addressValue 0x2000] 0 (EVM.address 0x2000)
  IO.println s!"constructor: {ctor.describe}"
  let mut σ := σ?.getD target.world
  σ ← invoke target σ "unlock" [.bytes .empty] 0x6000
  σ ← invoke target σ "initialize" [poolKeyValue, intValue (2^96)]
  σ ← invoke target σ "setProtocolFeeController" [addressValue 0x2000]
  σ ← invoke target σ "setProtocolFee" [poolKeyValue, intValue 500]
  σ := setTransient target σ 0xc090fc4683624cfc3884e9d8de5eca132f2d0ec062aff75d43c0465d5ceeab23 1
  σ ← invoke target σ "modifyLiquidity" [poolKeyValue, liqParams 1000000, .bytes .empty]
  σ ← invoke target σ "swap" [poolKeyValue, swapParams true (-100) 4295128740, .bytes .empty]
  σ ← invoke target σ "swap" [poolKeyValue, swapParams false 50 1461446703485210103287273052203988822378723970341, .bytes .empty]
  σ ← invoke target σ "donate" [poolKeyValue, intValue 100, intValue 200, .bytes .empty]
  σ ← invoke target σ "modifyLiquidity" [poolKeyValue, liqParams 0, .bytes .empty]
  σ ← invoke target σ "mint" [addressValue 0x2000, intValue 0x5000, intValue 1]
  σ ← invoke target σ "burn" [addressValue 0x2000, intValue 0x5000, intValue 1]
  σ ← invoke target σ "take" [addressValue 0, addressValue 0x3000, intValue 1]
  σ ← invoke target σ "settle" [] 0x2000 1
  σ ← invoke target σ "settleFor" [addressValue 0x3000] 0x2000 1
  σ ← invoke target σ "clear" [addressValue 0, intValue 1] 0x3000
  σ ← invoke target σ "sync" [addressValue 0x5000]
  σ ← invoke target σ "settle" []
  σ ← invoke target σ "collectProtocolFees" [addressValue 0x3000, addressValue 0, intValue 0]
  σ ← invoke target σ "modifyLiquidity" [poolKeyValue, liqParams (-1000000), .bytes .empty]
  σ ← invoke target σ "initialize" [poolKeyValue 8388608 0x2000, intValue (2^96)]
  σ ← invoke target σ "updateDynamicLPFee" [poolKeyValue 8388608 0x2000, intValue 1000]
  IO.println s!"Focused successful-path sequence complete; accounts: {σ.size}"
```

</details>

<details>
<summary>Focused hook fixture</summary>

Save as `/tmp/uniswap-v4-hooks.lean` and run
`lake env lean --run /tmp/uniswap-v4-hooks.lean` at the repository root.

```lean
import Benchmarks.UniswapV4PoolManager.DiffTarget
open Solm Solm.DiffTest Solm.Interp ABI Ethereum Ethereum.EVM
open Benchmarks.UniswapV4PoolManager

def addressValue (n : Nat) : Value := .address (EVM.address n)
def intValue (n : Int) : Value := .int n
def zeroSalt : Value := .fixedBytes ⟨31, by decide⟩ (List.replicate 32 0)
def poolKeyValue (fee := 3000) (hooks := 0) : Value :=
  .tuple [addressValue 0, addressValue 0x5000, intValue fee, intValue 60, addressValue hooks]
def liqParams (n : Int) : Value := .tuple [intValue (-120), intValue 120, intValue n, zeroSalt]
def swapParams (direction : Bool) (n : Int) (limit : Nat) : Value :=
  .tuple [.bool direction, intValue n, intValue limit]

def setTransient (t : Target) (σ : AccountMap) (slot value : Nat) : AccountMap :=
  let evm := initialState σ σ (.ofNat t.gas) default (t.env t.runtime t.selfAddress 0 .empty true)
  match t.config.transientBackend.write
    { base := "rawTransient", steps := [.aindex (.int slot)] }
    (.elem (.int (.uint ⟨256, by decide⟩))) (.int value) evm with
  | .ok e => e.accountMap
  | _ => σ

def invoke (t : Target) (σ : AccountMap) (name : String) (args : List Value)
    (caller := 0x2000) (value := 0) : IO AccountMap := do
  let some tr := t.contract.transitions.find? (·.name == name) | throw (IO.userError s!"no transition {name}")
  let some cd := encodeCallWithSelector? ((Ethereum.KEC (String.toByteArray (transitionSigStr tr))).extract 0 4) (tr.params.map Param.ty) args
    | throw (IO.userError s!"encoding {name}")
  let c : Case := {
    label := name
    σ := transferValue σ (EVM.address caller) t.selfAddress value
    I := t.env t.runtime (EVM.address caller) value cd true
  }
  let result := runCase t c
  IO.println s!"{name}: {result.verdict.describe}"
  match result.verdict with
  | .agree "success" => return result.postState.getD σ
  | .agree why => throw (IO.userError s!"{name} unexpectedly {why}; calldata {hex cd}")
  | _ => throw (IO.userError s!"{name} failed; calldata {hex cd}")

-- Echo the requested hook selector with deliberately dirty bytes4 padding;
-- beforeSwap returns three words, the other callbacks return two.
def hookCode : ByteArray := ⟨#[
  0x5f,0x35,0x60,0xe0,0x1c,0x63,0x57,0x5e,0x24,0xb4,0x14,
  0x60,0x24,0x57,
  0x5f,0x35,0x60,0xe0,0x1c,0x60,0xe0,0x1b,0x60,0xab,0x17,0x5f,0x52,
  0x60,0x01,0x60,0x20,0x52,0x60,0x40,0x5f,0xf3,
  0x5b,0x5f,0x35,0x60,0xe0,0x1c,0x60,0xe0,0x1b,0x60,0xab,0x17,0x5f,0x52,
  0x60,0x01,0x60,0x20,0x52,0x60,0x60,0x5f,0xf3]⟩

def main : IO Unit := do
  let (target, _) := diffTarget.resolveRuntime (Rng.ofSeed 2026)
  let target := { target with callees := target.callees ++ [(EVM.address 0x7fff, hookCode)] }
  let (ctor, σ?) := runConstructor target poolManagerCreationBytecode [addressValue 0x2000] 0 (EVM.address 0x2000)
  IO.println s!"constructor: {ctor.describe}"
  let mut σ := σ?.getD target.world
  let key := poolKeyValue 3000 0x7fff
  σ ← invoke target σ "initialize" [key, intValue (2^96)]
  σ := setTransient target σ 0xc090fc4683624cfc3884e9d8de5eca132f2d0ec062aff75d43c0465d5ceeab23 1
  σ ← invoke target σ "modifyLiquidity" [key, liqParams 1000000, .bytes (wordBytes 123)]
  σ ← invoke target σ "swap" [key, swapParams true (-100) 4295128740, .bytes (wordBytes 456)]
  σ ← invoke target σ "swap" [key, swapParams false 50 1461446703485210103287273052203988822378723970341, .bytes .empty]
  σ ← invoke target σ "donate" [key, intValue 100, intValue 200, .bytes .empty]
  σ ← invoke target σ "modifyLiquidity" [key, liqParams 0, .bytes .empty]
  σ ← invoke target σ "modifyLiquidity" [key, liqParams (-1000000), .bytes .empty]
  IO.println s!"All hook callbacks completed with dirty selector padding and nonzero deltas; accounts: {σ.size}"
```

</details>

## Bytecode and source differences

`extsload(bytes32,uint256)`, selector `0x35fd631a`, shifts the count by five and
adds the return prefix with wrapping EVM arithmetic (arm PC 9693; span arithmetic
PCs 9768–9770; shared RETURN at PC 2516). Counts such as `2^251` can return
successfully with a declared array length that does not match the returned data.
A direct run of the unmodified bytecode reproduced this in 2,599 gas out of 10,000.
A gas bound above `2^24` cannot exclude this behavior.

The user authorized a well-formedness condition in the DSS Common style.
`Syntax.poolManagerWF` requires `224 + 32*n < 2^256` for nonpayable range-`extsload`
calldata satisfying the entry length guards. It is a refinement hypothesis, not a
runtime `require`: the bytecode does not enforce it. Generated function stubs,
runtime theorems, and the contract theorem carry it. This explicitly restricts
the call domain, including some cheap calls, without a mapping-slot noncollision
assumption. The available repository example is `Benchmarks/Dss/Cure/Common.lean`
(`cureStorageWF`).

The specification follows these compiled details where direct typed translation
would lose information:

- Empty array forms of raw `extsload`/`exttload` still perform the assembly
  do-while loop's first read. Range `extsload` also reads its first slot at count zero.
- Hook reply validation checks length and the first four bytes, allowing dirty
  bytes4 padding. `beforeSwap` truncates its fee word to uint24. Raw reply handling
  retains these rules; strict typed tuple decoding would reject valid replies.
- Packed tick writes, cached pool slot0/liquidity values, sequential fee-growth
  reads/writes, and transient reserve updates preserve bytecode ordering even when
  derived storage slots alias.
- PoolId hashing uses sign-extended tick spacing in a 256-bit word; position hashing
  uses packed 20/3/3/32-byte fields. FullMath/Newton operations wrap where compiled
  arithmetic wraps; liquidity/delta operations retain their checked arithmetic.
- ABI tuple parameters are unpacked into Solm struct values at entry. Casts are
  explicit where a notation type annotation alone would not perform conversion.

These are modeling corrections, not claims of new source vulnerabilities.
`PoolManager.spec.json` retains the original translator diagnostics and draft call
facts. Its library-call entries are not the authoritative external ABI.

## Guidance for the proving session

`SpecSyntax.lean` is authoritative. `Spec.lean` selects its 12-entry
`Syntax.externalABI`: `balanceOf(address)`, `unlockCallback(bytes)`, and before/after
initialize, add liquidity, remove liquidity, swap, and donate. The first two use
typed return decoding; hooks use raw calls and explicit validation. Currency
transfers use raw native/ERC20 calls with the bytecode's success rules.

`original` is the sole immutable, at runtime offset 13606. The constructor sets
it to `address(this)`; generated immutable plumbing patches that word. The
constructor preserves the high bits of owner slot zero and emits the ownership
event. There is no receive or fallback function.

Assembly's arbitrary persistent and transient words are modeled by static arrays
spanning the 256-bit slot space. They are storage aliases, not memory
representations. Persistent declarations keep slots 0 through 6 modulo `2^256`.
`TickInfo.liquidityPacked` represents one packed word. Prove the slot-layout
identities; do not assume hash noncollision.

The initial scaffold had 35 proof obligations: 33 function bodies, the
constructor, and `restrictImmutables_of_fit` in `Common.lean`. All are now
discharged. Runtime summaries have 67 shards (1,346 units); creation summaries
have 68 shards (1,358 units). Shared helpers cover the arithmetic, arbitrary slot
aliases, callback reentrancy, and gas arguments used by the public proofs.

The adapter below reproduces generated files without changing repository scripts.
It disambiguates scalar/array overloads, recognizes the leading-zero `balanceOf`
selector's PUSH3, selects the reviewed ABI, and threads WF/gas hypotheses. Smaller
summaries at the specified repeated-squaring block starts (runtime and its embedded
creation copy) avoid exponential symbolic-expression growth. Save the adapter as
`/tmp/uniswap-v4-regenerate.py` and invoke from the repository root:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 /tmp/uniswap-v4-regenerate.py lean
PYTHONDONTWRITEBYTECODE=1 python3 /tmp/uniswap-v4-regenerate.py report
PYTHONDONTWRITEBYTECODE=1 python3 /tmp/uniswap-v4-regenerate.py blocks
PYTHONDONTWRITEBYTECODE=1 python3 /tmp/uniswap-v4-regenerate.py proof
lake build Benchmarks.UniswapV4PoolManager.Correct
```

Use `proof` alone after specification edits. It overwrites generated stubs, so
preserve completed proofs before using it in a later session. Do not rerun
`sol2solm.py` over the finished specification.

<details>
<summary>Generator adapter</summary>

```python
"""Contract-local generator adapters; repository scripts remain unchanged."""
from pathlib import Path
import inspect
import re
import sys
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path.cwd() / 'scripts'))
import evm_tools
_original_names = evm_tools.overload_names

def names(signatures):
    result = _original_names(signatures)
    duplicates = {v for v in result.values() if list(result.values()).count(v) > 1}
    for sig, name in list(result.items()):
        if name in duplicates and '[]' in sig:
            result[sig] = name + '_array'
    assert len(set(result.values())) == len(result)
    return result

evm_tools.overload_names = names
# Include selectors with leading zero bytes, e.g. PUSH3 0xfdd58e.
source = inspect.getsource(evm_tools.selector_compares)
source = source.replace('if ins.opcode != 0x63:', 'if not (ins.opcode == 0x63 or ins.opcode == 0x62 and ins.argument == 0xfdd58e):')
exec(source, evm_tools.__dict__)

D = Path('Benchmarks/UniswapV4PoolManager')
M = 'Benchmarks.UniswapV4PoolManager'
mode = sys.argv[1]
if mode == 'blocks':
    import scaffold
    import generate_rd_blocks as rd
    _segments = rd.bounded_supported_segments
    def segments(block, max_instructions=rd.MAX_SUMMARY_INSTRUCTIONS):
        # Repeated squaring duplicates symbolic terms. Bound just this run more
        # tightly in both runtime and creation's embedded runtime.
        if block and block[0].pc in (18089, 18274):
            max_instructions = min(max_instructions, 16)
        return _segments(block, max_instructions)
    rd.bounded_supported_segments = segments
    raise SystemExit(scaffold.main(['blocks', '--dir', str(D), '--module', M, '--force']))
if mode == 'lean':
    import scaffold
    raise SystemExit(scaffold.main(['lean', '--dir', str(D), '--module', M, '--force']))
if mode == 'report':
    import bytecode_report
    raise SystemExit(bytecode_report.main([str(D), '--output', str(D/'PoolManager.report.md')]))
if mode == 'proof':
    import proof_skeleton as p
    _spec = p.render_spec
    def spec(c):
        calls, c.external_calls = c.external_calls, []
        result = _spec(c)
        c.external_calls = calls
        result = result.replace('/-! ## Config -/',
          '/-- Audited against the pinned interfaces; defined with the specification. -/\n'
          'def externalABI : ExternalCallABI := Syntax.externalABI\n\n/-! ## Config -/')
        return result.replace('externalABI := defaultExternalCallABI', 'externalABI := externalABI')
    p.render_spec = spec
    _signature = p.body_signature
    def signature(c, t, global_guard):
        result = _signature(c, t, global_guard)
        return result.replace('    (hsel :',
          '    (hWF : Syntax.poolManagerWF σ I)\n'
          '    (hGas : Syntax.poolManagerGasBound g)\n    (hsel :')
    p.body_signature = signature
    _correct = p.render_correct
    def correct(c, global_guard):
        result = _correct(c, global_guard)
        result = result.replace('runtimeRefinement config',
          'runtimeRefinementWithWF Syntax.poolManagerWF Syntax.poolManagerGasBound config')
        result = result.replace('contractRefinement config',
          'contractRefinementWF Syntax.poolManagerWF Syntax.poolManagerGasBound config')
        result = result.replace('fun σ σ₀ g A I hcode hsize ↦', 'fun σ σ₀ g A I hcode hsize hWF hGas ↦')
        for t in c.transitions:
            before = f'{c.prefix}{t.cap}Body v hcode hsize'
            result = result.replace(before, before+' hWF hGas')
        return result
    p.render_correct = correct
    raise SystemExit(p.main(['--dir', str(D), '--module', M, '--force']))
raise SystemExit('unknown mode')
```

</details>

## Gas bound

Runtime theorems use `Syntax.poolManagerGasBound g`, meaning:

```text
g.toNat < B
B = 324518553658429321982441292826060
K = 2^58
C(n) = 3*n + floor(n*n/512)
B = C(K+3) + C(K-2) + 3*(K-2) + 1487
```

This is strictly above `2^24`. It abstracts compiler memory-capacity bookkeeping
and the consequent safety of pointer/size arithmetic. Individual ABI length and
offset validation remains in the modern decoder and specification guards. The
cheap range-`extsload` wrap is covered separately by WF.

The binding path is the second allocation while decoding a successful
`unlockCallback(bytes)` reply. Let `R` be raw reply size, `L` decoded byte length,
and `ceil32` round bytes up to a multiple of 32. The raw reply is copied at byte
160 (RETURNDATACOPY at PC 9249). Both allocations use the capacity check at PC
11822; the second is called from PC 9373. With return offset 32, `R >= L+64`, and
the aggregate end is `192 + ceil32(R) + ceil32(L)`. The first rounded sizes crossing
`2^64` are:

```text
L = 2^63 - 159
R = L + 64 = 2^63 - 95
ceil(R/32) = K-2
ceil(L/32) = K-4
parent active memory words after copying = K+3
```

Offset zero forces a zero decoded length. Offsets 1 through 7 force length below
`2^59` because the head words overlap; offsets 8 through 31 force length above the
uint64 decoder limit. Thus a large valid length needs offset at least 32. Trailing
data or larger offsets cannot reduce raw reply size. Larger input cannot reduce
parent cost.

The parent spends `C(K+3)` on memory, `3*(K-2)` on copying reply words, and 1,469 on
other operations, including warm CALL, TLOAD, TSTORE, dispatch, decoding, and the
panic path. A fresh EVM callee producing this reply spends at least `C(K-2)` on
memory and 18 on forming the two ABI head words and returning. Their sum is `B`.
Cold calls, nonempty input, extra callback work, and larger replies increase cost.

The 18-gas callback is attainable. Install these nine opcodes, padded with 23 zero
bytes to make code size 32, at address `L`; set the block timestamp to `R`:

```text
CODESIZE PUSH0 MSTORE ADDRESS MSIZE MSTORE TIMESTAMP PUSH0 RETURN
38 5f 52 30 59 52 42 5f f3
```

Call unlock with selector `48c89491` followed by a zero word (valid empty bytes via
offset zero), zero value, a warm caller, and zero initial lock/delta count. The
callback returns head `[32,L]` followed by zero bytes. At starting gas `B` the
bytecode can finish with allocation panic `0x41` although the value-level decode
is valid. EIP-150's call cap leaves enough callback gas at this size. Thus a larger
upper interval would admit the behavior being abstracted: the strict cutoff is
necessary.

Native precompiles give no cheaper counterexample: fixed outputs are too small;
identity echoes a callback selector that fails ABI offset validation; modexp's
cost for such a large output exceeds `B`. Other capacity-check paths require
copying/encoding near `2^64` bytes before an omitted aggregate guard can fail.
Fixed allocations between these writes are bounded (at most 256 bytes each), and
the swap loop reuses its step object. Their memory cost alone exceeds `B`. Raw hook
replies must also be copied before driving later allocations. A 256-bit span
wrap requires still greater expansion, except for the range getter restricted by
WF. Within the bound a path violating these abstractions therefore exhausts gas
before a conflicting completed result. Proving the inequalities on each relevant
path is part of the refinement obligations, not an extra axiom.

An exact sparse trace of the original runtime confirmed the 327-step panic path,
1,469 parent operation cost, and the arithmetic above without allocating the huge
buffer. Native EVM runs checked scaled versions with only the PUSH8 capacity
constant reduced, retaining all opcode costs:

| Capacity bits | Cutoff | At cutoff minus one | At cutoff / cutoff plus one |
| --- | ---: | --- | --- |
| 12 | 2,075 | out of gas | panic `0x41`, 2,075 gas used |
| 16 | 14,800 | out of gas | panic `0x41`, 14,800 gas used |
| 20 | 1,197,580 | out of gas | panic `0x41`, 1,197,580 gas used |

These scaled runs validate the gas accounting. They do not execute an actual
`2^63`-byte reply and do not replace a proof of the full bound.

<details>
<summary>Scaled native EVM gas diagnostic</summary>

Save as `/tmp/uniswap-v4-capacity.lean` and run
`lake env lean --run /tmp/uniswap-v4-capacity.lean` at the repository root.

```lean
import Solm.DiffTest.Trace
open Ethereum Ethereum.EVM Solm.DiffTest Solm.Interp

def cm (n : Nat) : Nat := 3*n + n*n/512

def main : IO Unit := do
  let text ← IO.FS.readFile "Benchmarks/UniswapV4PoolManager/runtime.hex"
  let hex := text.trimAscii.toString
  let template ← match ByteArray.ofBlob (getBlob! (if hex.startsWith "0x" then hex else "0x" ++ hex)) with
    | .ok code => pure code
    | .error e => throw (IO.userError e)
  let callback : ByteArray := ⟨#[0x38,0x5f,0x52,0x30,0x59,0x52,0x42,0x5f,0xf3] ++ Array.replicate 23 0⟩
  for bits in [12,16,20] do
    let k := 2^(bits-6)
    let length := 2^(bits-1)-159
    let replySize := length+64
    let bound := cm (k+3) + cm (k-2) + 3*(k-2) + 1487
    let mut code := template
    let limit := (UInt256.ofNat (2^bits-1)).toByteArray
    for j in [:8] do
      code := code.set! (11868+j) limit[24+j]!
    let self := EVM.address 0x1000
    let caller := EVM.address length
    let σ := (∅ : AccountMap).insert self { (default : Account) with code := code }
      |>.insert caller { (default : Account) with code := callback }
    let calldata : ByteArray := ⟨#[0x48,0xc8,0x94,0x91]⟩ ++ (UInt256.ofNat 0).toByteArray
    let I := { (default : ExecutionEnv) with
      codeOwner := self
      sender := caller
      source := caller
      code := code
      calldata := calldata
      perm := true
      header := { (default : BlockHeader) with timestamp := replySize }
    }
    let A := { (default : Substate) with accessedAccounts := (default : Substate).accessedAccounts.insert caller }
    for g in [bound-1,bound,bound+1] do
      let trace := runTrace (initialState σ σ (.ofNat g) A I) (g+1)
      match trace.result with
      | .error error => IO.println s!"bits={bits} gas={g} bound={bound}: {repr error}"
      | .ok (.revert state out) =>
          IO.println s!"bits={bits} gas={g} bound={bound}: revert, used={g-state.toNat}, payload={Ethereum.toHex out}"
      | .ok (.success _ _) => throw (IO.userError "unexpected success")
```

</details>
