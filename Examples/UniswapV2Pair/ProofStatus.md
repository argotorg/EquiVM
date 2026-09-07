# Uniswap V2 Pair proof status

The objective remains full constructor and runtime refinement under `Misc/prompt.md`.
The complete runtime proof is finished. The constructor is the only remaining proof hole.

Verified on 2026-09-07:

- `lake build Examples.UniswapV2Pair.Correct Examples.UniswapV2Pair.SpecSyntax
  Examples.UniswapV2Pair.BurnInternalCases Examples.UniswapV2Pair.MintFeeCallRuntimeCases
  Examples.UniswapV2Pair.SafeTransferCallCases` passed:
  `Build completed successfully (3633 jobs).` The latest Correct/SpecSyntax gate
  passed with 3740 jobs; only Constructor retains a hole warning.
- Mint is fully proved. `uniswapMintBody` has no `sorryAx` dependency. Its 2388 axiom
  dependencies comprise 2378 permitted native evaluation facts, the three standard
  logical axioms, and seven permitted EVM precompile output-size facts. The complete
  audit after the shared arithmetic refactor is in `/tmp/uniswap-mint-adjustment-audit.json`.
- The main Mint proof now uses four exhaustive factory continuations. It is 496 lines
  and its latest targeted build took 3.4 seconds. `SyncCumulative.lean` is 1854 lines.

Current proof structure:

- Swap’s ABI definitions and decoding proofs are in `SwapABI.lean` (612 lines).
  `SwapDecoderPrefix.lean` shares the bounds-check prefix between valid and malformed input;
  `SwapCommon.lean` is now 548 lines. `SwapDecodeRuntime.lean` completes valid decoding.
  The lock, output-positivity, reserve, and recipient guards are proved and integrated;
  both optional transfers, the callback, updated-balance calls, input calculations, the
  positive-input guard, both fee adjustments, and the invariant check are integrated.
  The full `_update`, Swap event, unlock, and empty return are integrated. `Swap.lean` is 333 lines.
  Its complete audit has 2834 dependencies: 2824 permitted native facts, three logical axioms,
  and seven precompile size facts, with no `sorryAx` or source warnings.
  `SwapOutputGuardRuntime.lean`, `SwapReserveGuardRuntime.lean`, `SwapRecipientRuntime.lean`,
  and their source helpers factor the branches. The recipient runtime audit has 73 dependencies
  (70 native facts and three logical axioms), with no holes or source warnings.
- `SafeTransferMemoryReady.lean` accommodates Swap's initial 96-byte memory. The shared
  transfer preparation, return handling, and memory invariants now support that layout;
  existing APIs remain wrappers. `CallDepthLimit.lean` proves zero-value CALL failure at
  depth 1024 with only the three logical axioms. `OptionalSafeTransferAnyDepth.lean` and
  `SwapTransfersAnyDepth.lean` compose both optional transfers at every allowed call depth.
- Callback proofs are factored into branch, header, copy, preparation, call, memory, ABI,
  and source modules. `SwapCallbackCases.lean` covers skipping, missing code, depth limit,
  call failure, and success. Its 191 dependencies comprise 181 native facts, three logical
  axioms, and seven accepted precompile size facts, with no holes or source warnings.
  Audit: `/tmp/uniswap-swap-callback-audit.json`.
- `PairBalanceCallRuntime.lean`, `PairBalanceCallCases.lean`, and
  `PairBalanceAnyDepthCases.lean` cover all four Burn/Swap balance-call sites, including
  depth-limit failure. `PairBalanceHeaderRuntime.lean` shares their calldata preparation.
  Existing Burn interfaces are wrappers. `SwapBalancesCases.lean` composes both calls and
  preserves memory invariants; its audit has 515 dependencies (505 native, three logical,
  seven precompile size facts), with no holes or source warnings.
  Audit: `/tmp/uniswap-swap-balances-audit.json`.
- `SwapInputRuntime.lean` shares the conditional subtraction routine; `SwapInputSource.lean`
  proves both source input amounts. `SwapInputGuardRuntime.lean` and
  `SwapInputGuardSource.lean` cover the zero-input rejection. `PositiveWordsSource.lean`
  factors source positivity disjunctions, used by both output and input guards.
- `SwapAdjustmentRuntime.lean`, `SwapAdjustmentSource.lean`, `SwapAdjustmentCases.lean`,
  and `SwapAdjustmentPrefix.lean` couple both fee adjustments, including overflow.
  Each input is at most its balance, so successful products guarantee subtraction is safe.
  The coupling audit has 186 dependencies (183 native and three logical), with no holes
  or source warnings. Audit: `/tmp/uniswap-swap-adjustment-audit.json`.
- `SwapInvariantRuntime.lean` proves the bounded reserve product and scaling, adjusted
  product overflow, inequality rejection, and success. `SwapInvariantSource.lean` connects
  both failure modes and success to the source require. The runtime audit has 207
  dependencies (204 native and three logical), with no holes or source warnings.
  Audit: `/tmp/uniswap-swap-invariant-audit.json`. `SwapUpdateRuntime.lean` proves the
  entry to the already-proved `_update` routine with return PC 2712.
- `SafeMathMulOverflowRuntime.lean` generalizes the existing multiplication-overflow
  proof to arbitrary memory/free pointers. `WordArithmeticSource.lean` proves generic
  checked word multiplication, overflow, and subtraction from arbitrary expressions;
  the source multiplication lemma uses only the three standard logical axioms.
  Existing Mint source arithmetic and runtime overflow interfaces wrap these helpers.
- `CodeCopyRevertSteps.lean` and `ErrorStringCopyCore.lean` generalize legacy Error(string)
  construction over arbitrary literal length, memory, and active words. The original 40-byte
  API is a wrapper. The generic core needs only the three logical axioms. `AddressComparison.lean`
  proves the correspondence between canonical words and address equality.

- Burn is fully proved, including both transfers, updated balance calls, every `_update`
  branch, optional kLast storage, the Burn event, unlocking, and the two-value return.
  Its complete axiom audit has 3248 dependencies: 3238 permitted native facts, the three
  standard logical axioms, and seven permitted precompile size axioms. No `sorryAx` and
  no source warnings. Latest audit after the shared balance and arithmetic refactors: `/tmp/uniswap-burn-adjustment-audit.json`.
  `Burn.lean` is 526 lines and builds in 7.1 seconds. The latest full gate passed with
  3735 jobs (Correct took 2.0 seconds). Both queries use one source/runtime coupling theorem,
  covering missing code, call failure, short return data, and decoded success.
- `BalanceDynamicMemory.lean` and `BalanceDynamicReturnMemory.lean` prove calldata,
  memory size, preserved free-pointer/zero-slot reads, and returned-word decoding for
  arbitrary free-memory pointers. `DynamicReturnDecodeRoutines.lean` generalizes the
  library's fixed-pointer return decoder. `BurnUpdatedBalanceRuntime.lean` and
  `BurnUpdatedBalance1Runtime.lean` prove the two entry traces and `_update` thunk;
  `BurnUpdatedBalanceCallRuntime.lean` and `BurnUpdatedBalanceCases.lean` share the call
  cases. `BurnUpdatedBalancesSource.lean` composes the source prefixes.
- The updated-balance call coupling audit has 154 dependencies: 144 native evaluation
  facts, three logical axioms, and seven accepted precompile-size axioms; no `sorryAx`.
  The generalized transfer-final-memory invariants use one native fact and the three
  logical axioms. Both source scans are clean. Audit:
  `/tmp/uniswap-burn-updated-balances-audit.json`.
- `SafeTransferFinalMemory.lean` now generalizes the final memory invariants over the
  incoming memory, free pointer, and active words; the original fixed-pointer API is
  a wrapper. `ByteArrayWriteMemory.lean` holds the existing generic in-bounds write-size
  lemma moved from `MintCommon.lean`, preserving its name and signature.
- `ErrorDynamicMemory.lean`, `ErrorDynamicRuntime.lean`, and `UpdateOverflowRoutines.lean`
  generalize overflow error memory and traces. `PairDynamicMemory.lean`, `SyncDynamicCore.lean`,
  and `SyncDynamicRuntime.lean` handle the Sync event at an arbitrary free-memory pointer.
  `UpdateCallSource.lean` accepts arbitrary caller argument expressions;
  `UpdateDynamicCallRuntimeCases.lean` couples every update branch. The old update APIs
  preserve their signatures and wrap the generalized proofs. The dynamic coupling build
  passed (3513 jobs, 2.7 seconds) and its audit has 541 dependencies: 538 native facts and
  the three logical axioms, with no `sorryAx` or source warnings. Audit:
  `/tmp/uniswap-dynamic-update-audit.json`.
- `BurnUpdateSource.lean` supplies updated-balance arguments and source prefix composition.
  `BurnKLastRuntime.lean` proves both optional-kLast branches (3470 jobs, 5.8 seconds).
  `BurnEventRuntime.lean` proves the Burn event and unlock/jump (3475 jobs, 28 seconds),
  using the missing library-candidate DUP16 combinator in `Dup16Routines.lean`.
  `PairDynamicReturnMemory.lean` proves the two-word ABI window (3458 jobs, 2.7 seconds),
  and `BurnReturnRuntime.lean` proves the complete two-word return (3474 jobs, 4.4 seconds).
  `BurnTailSource.lean`, `BurnAfterUpdateCases.lean`, and `PairReturnEncoding.lean` complete
  the source composition and coupling. The tail coupling builds in 2.9 seconds (3594 jobs).


- `BurnInternalRuntime.lean`, `BurnInternalReverts.lean`, and `BurnInternalCases.lean`
  prove the complete internal `_burn` call, including both subtraction failures and the
  successful return. Storage coupling respects the balance write before reading supply.
  Its axiom audit has 163 dependencies: 160 permitted native evaluation facts and the
  three standard logical axioms. Audit: `/tmp/uniswap-burn-internal-axioms.txt`.
- `MintFeeRootRuntime.lean`, `MintFeeRootArithmeticReverts.lean`,
  `MintFeeRootArithmeticCases.lean`, `MintFeeRootRuntimeCases.lean`, and
  `MintFeeBranchRuntime.lean` generalize the fee routine over an arbitrary return PC and
  caller stack. Existing Mint-specific theorem signatures are preserved and apply these
  shared proofs. `mintFeeSqrtPrefixRuntimeBoundedInputOfTail` similarly generalizes the
  paired sqrt calls in `MintFeeSqrtLoopBridge.lean`.
- `MintFeeAfterFactoryCases.lean` composes all valid factory-response branches into a
  complete source function-body / runtime-continuation theorem. Its stronger variant
  also preserves the original storage snapshot and block context.
- `MintFeeFactoryCallRuntime.lean` generalizes the factory code guard, static call,
  and decoder over the caller stack and memory. `MintCommon.lean` supplies shared
  memory facts and `uniswapMintFeeToTypedCall_source_of_mem`; existing APIs are wrappers.
- `MintFeeCallRuntimeCases.lean` now proves the complete `_mintFee` internal call from
  routine entry to return, assuming depth is below the external-call limit. It covers
  all factory and arithmetic failures, preserving state coupling and the context for
  later external calls. Its audit has 841 dependencies: 831 native facts, three logical
  axioms, and seven permitted precompile output-size facts; no `sorryAx`. Audit:
  `/tmp/uniswap-shared-fee-final-axioms.json`.
- `BurnCommon.lean` holds the unchanged Burn decoding and lock helpers. `Burn.lean`
  now covers both initial balance calls through decoded balances at PC 4444, including
  missing-code, depth-limit, call-failure, and short-return-data branches.
  `BurnInitialSource.lean` couples the cache prefix and those failure paths;
  `BurnInitialRuntime.lean`, `BurnFirstBalanceRuntime.lean`, and
  `BurnSecondBalanceRuntime.lean` provide their runtime traces.
- `BurnFeeEntryRuntime.lean` proves the liquidity mapping read and entry to `_mintFee`
  at PC 7696. `BurnBeforeFeeSource.lean` couples that read and preserves the cached
  reserve arguments. Burn now invokes `uniswapMintFeeCallRuntimeCases`; all fee failure
  paths are closed.
- `BurnAmountsRuntime.lean`, `BurnAmountsSource.lean`, and `BurnAmountsCases.lean`
  couple both amount calculations, including multiplication overflow and division by zero.
  `BurnAfterFeeSource.lean` threads the supply load after fee minting.
- `BurnAmountsGuardRuntime.lean`, `BurnAmountsGuardCases.lean`, and
  `BurnBeforeTransfersSource.lean` couple the positive-amount guard and the complete
  internal `_burn` call. Burn now reaches PC 4617 before the first token transfer;
  all earlier failure paths are closed. Targeted Burn validation took 3.5 seconds.
  The guard-and-burn coupling has 241 axiom dependencies: 238 permitted native facts
  and the three standard logical axioms, with no `sorryAx` or source-scan warnings.
  Audit: `/tmp/uniswap-burn-through-internal-audits.json`.
- `ErrorStringCopyRoutines.lean` factors the shared 40-byte error-literal copy and
  revert, parameterized by code, entry PC, literal offset, and caller stack. Mint's
  prior trace now wraps it, preserving the theorem signature and axiom counts.
  `StackRoutines.lean` holds the existing generic DUP12 proof moved from PermitRuntime.

- `ZeroSlotMemory.lean` proves preservation of the word at byte 96 through mapping
  scratch writes, internal mint/burn logging, and factory return-data copying. Stronger
  fee and burn coupling variants thread this equality; all prior signatures are wrappers.
  `BalanceCallMemory.lean` holds the initial and rebuilt balance-call zero-slot facts.
- `RawCallSource.lean`, `SafeTransferReturnCases.lean`, and `SafeTransferCallCases.lean`
  couple a complete `_safeTransfer` call from a size-164 memory buffer, covering failure,
  empty success, huge/short data, and boolean decoding. Its audit has 529 dependencies:
  519 native facts, the three standard logical axioms, and seven permitted precompile
  output-size facts. The memory-preserving fee and burn variants retain their 841 and
  241 dependency counts. Audit: `/tmp/uniswap-burn-first-transfer-audits.json`.
- `BurnTransfersRuntime.lean` proves both transfer-entry thunks. `BurnTransfersSource.lean`
  supplies the cached arguments and failure composition. The main Burn proof now reaches
  PC 4639 after both transfers, with every preceding failure branch closed. Its
  remaining hole starts before the two updated balance queries.
- The generic transfer runtime now reaches the external CALL at PC 6595 with an arbitrary
  bounded free-memory pointer and caller stack. `SafeTransferDynamicMemory.lean` and
  `SafeTransferDynamicRuntime.lean` prove the signature, argument, length, and selector stores.
  `SafeTransferCopyRoutines.lean` factors the word-copy iteration and four-byte tail;
  `SafeTransferDynamicCopyMemory.lean`, `SafeTransferDynamicCopyRuntime.lean`, and
  `SafeTransferDynamicCallRuntime.lean` compose copying and the EVM call witness.
  The old fixed-pointer entry theorem is now a wrapper with the same public signature.
  `lake build Examples.UniswapV2Pair.SafeTransferCallCases` passed (3495 jobs).
  The generalized entry audit has 191 dependencies: 181 native facts, three logical axioms,
  and seven permitted precompile size facts, with no source-scan warnings or `sorryAx`.
  `SafeTransferDynamicCalldata.lean` proves its 68-byte input equals the transfer ABI data;
  its targeted build passed (3487 jobs, 6.6 seconds for the leaf).
  The fixed-pointer calldata theorem is also now a wrapper. Transfer coupling and Burn
  integration passed (3579 jobs; Burn took 3.8 seconds and retains its later hole).
  MemorySteps also holds seven existing generic expansion/coverage lemmas moved from
  Skim's dynamic-offset runtime; their public signatures are preserved.
- `ReturnDataMemory.lean` now proves generic Solidity return-data allocation, size,
  length readback, first-word readback, and active-memory bounds. Existing generic empty
  return traces moved to `SkimSafeTransferReturn.lean`, retaining their public signatures.
  `SafeTransferDynamicReturnRuntime.lean` covers empty success and every nonempty return
  branch; `SafeTransferDynamicReturnCases.lean` couples them to source semantics.
  `SafeTransferDynamicCallCases.lean` now proves the complete generalized `_safeTransfer`
  call, using the library's proved gas-based return-data bound (less than 2^138).
  Its targeted build passed (3497 jobs, 2.5 seconds for the leaf). The old transfer call
  coupling also builds after the refactors (3498 jobs).
  Its axiom audit has 429 dependencies: 419 native facts, three logical axioms, and seven
  permitted precompile size facts. The nonempty return runtime has 160 dependencies
  (157 native facts and three logical axioms); the generic return-word memory lemma uses
  only the three logical axioms. All have clean source scans and no `sorryAx`.
  Audit: `/tmp/uniswap-dynamic-transfer-complete-audits.json`.
- `SafeTransferFinalMemory.lean` establishes the first transfer's final-memory invariants,
  including its free pointer, zero slot, memory size, pointer gap, and active words. Its
  targeted build passed (3500 jobs). Burn now invokes the generalized callee for its
  second transfer and closes the second-transfer revert branch; MCP diagnostics contain
  only the remaining Burn-hole warning. The subsequent Correct/SpecSyntax gate passed (3646 jobs).

- `MintSimpleFactoryCompleteCases.lean` covers fee-off and fee-on with zero kLast.
  `MintFeeFactoryCompleteCases.lean` covers fee-on with nonzero kLast using actual sqrt
  witnesses, including arithmetic overflow and fee-mint failures.
- `MintAfterFeeCases.lean` splits on the resulting total supply. Initial and proportional
  liquidity branches cover all arithmetic failures and successful liquidity calculations.
- `MintTailRuntimeCases.lean` composes liquidity checks, internal mint, reserve update,
  optional kLast storage, unlocking, and return.
- `UpdateCallRuntimeCases.lean` couples the complete internal `_update` call, with a
  generic runtime return PC and stack tail. It covers both overflow reverts and every
  cumulative-price branch, for reuse by Burn and Swap.
- `Invalid.lean` supplies generic halt/dispatch lemmas for Solidity 0.5 division-by-zero
  INVALID guards, flagged for promotion to the Reasoning library.
- The spec passes cached reserves into `_update` in Burn and Swap, matching the runtime
  call sites at PCs 4881 and 2708.
- The constructor spec initializes unlocked, rejects nonzero call value, then writes
  DOMAIN_SEPARATOR and factory, matching creation PCs 9, 10–20, 227, and 246.
  `Constructor.lean` reconstructs the exact creation artifact and connects the constructor
  scaffold to `uniswapV2PairContractCorrect`. Its body proof remains open.

Next work:

1. Finish the constructor, reusing proved routines.
2. Split the remaining existing files above 2000 lines by concern.
3. Run the completion checklist from `Misc/prompt.md` and audit both
   `uniswapV2PairCorrect` and `uniswapV2PairContractCorrect`.

Lean MCP diagnostics are the first validation path; targeted Lake builds validate imports
and full integration. No changes to bytecode, Solidity, or the Reasoning library are allowed.
