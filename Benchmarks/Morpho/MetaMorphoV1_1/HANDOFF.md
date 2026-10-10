# MetaMorphoV1_1 proving handoff

## Compiler settings and provenance

The proof target is the **local solc 0.8.37 rebuild**, as authorized when the storage-array
compiler bug was identified. The original mainnet deployment uses solc 0.8.26. Its successful
byte-for-byte reproduction is retained separately; upgrading the compiler changes both the
executable bytecode and its metadata.

- Upstream: [morpho-org/metamorpho-v1.1](https://github.com/morpho-org/metamorpho-v1.1/tree/5a0717b2c863060ff452ca324716083fe6d09374),
  commit `5a0717b2c863060ff452ca324716083fe6d09374`, main unit `src/MetaMorphoV1_1.sol`.
  The pristine tree and dependency commits are in `../metamorpho-v1.1/UPSTREAM.json`.
- Ethereum factory: `0x1897A8997241C1cD4bD0698647e4EB7213535c24`, listed by
  [Morpho](https://docs.morpho.org/developers/contracts/addresses/).
  Its creation transaction is `0x4c19401df000d3bbc3fe364049c93913e0aa350e0cbb7d01dd9f27aaa2c512e9`
  at block `21439510`.
- Reference vault: [Steakhouse PAXG](https://etherscan.io/address/0xbeef7959ae71d4e45e1863dae0b94c35244af816?amt=1-10),
  `0xBeeF7959aE71D4e45e1863dae0B94C35244AF816`, chain ID `1`.
  `provenance/vault.address.json` records the factory as creator and creation transaction
  `0xe95cfc831c42977fa643013a694390700fffe43ca462d0fd585f36a113e3c85d`.
  Etherscan marks the contract as an exact verification match.
- Historical compiler: `0.8.26+commit.8a97fa7a`. The verification source closure and settings
  are retained in `provenance/verification.standard-input.json`; the explorer responses and
  Etherscan settings excerpt are retained alongside it. The excerpt is from another vault
  using this same template. The historical comparison independently checks all bytes of the
  selected PAXG vault, including the IPFS/CBOR metadata tail.
- Current compiler: `0.8.37+commit.f401782d`, official Linux amd64 binary SHA-256
  `5de843c2c93563cc66425c99a4fb13fdbf32b4c4ae07469480faaf126e14404a`.
  [Compiler manifest](provenance/benchmark-compiler.json) records the download URL and reason.
- Settings: optimizer enabled, `200` runs, `viaIR: true`, `evmVersion: cancun`,
  `metadata.bytecodeHash: ipfs`, `appendCBOR: true`, `useLiteralContent: false`.
  All nine verification remappings are preserved in the build manifest.
- `compiler-sources/` contains the same 41 compilation units. The sole source change is the
  main unit's exact pragma, `0.8.26` to `0.8.37`; pristine upstream files remain unchanged.
  ABI, storage layout, and immutable names/types are unchanged.

| Artifact | Runtime bytes | Equals reference deployment, metadata included |
| --- | ---: | --- |
| Saved 0.8.26 template with reference immutables | 19730 | Yes |
| Current 0.8.37 template with reference immutables | 19708 | No; intentional compiler upgrade |

The comparison records are `provenance/deployment-solc-0.8.26-comparison.json` and
`provenance/deployment-comparison.json`. Current creation bytecode is 23666 bytes.

Recompile and regenerate with the pinned binary:

```sh
python3 Benchmarks/Morpho/MetaMorphoV1_1/recompile.py --solc /path/to/solc-0.8.37
```

The fresh Morpho Blue callee is in `../MorphoBlue/`: upstream commit
`55d2d99304fb3fb930c688462ae2ccabb1d533ad`, solc `0.8.19+commit.7dd6d404`,
optimizer `999999` runs, via IR, Paris, IPFS metadata. Its 15623-byte patched runtime matches
the deployed Blue code. This is a callee fixture; the vault proof target uses 0.8.37.

## Differential tests and validation

All seven scaffold checks pass. The final Lean build completed successfully (3661 jobs).
The 17 correlated cases, all three packed-slot cases, and the three array-cleanup checks pass.
The randomized run results and per-transition coverage follow below.

```sh
python3 scripts/scaffold.py check --dir Benchmarks/Morpho/MetaMorphoV1_1
lake build Benchmarks.Morpho.MetaMorphoV1_1.Correct \
  Benchmarks.Morpho.MetaMorphoV1_1.DiffTarget \
  Benchmarks.Morpho.MetaMorphoV1_1.FixedBlue.DiffTarget
lake exe solm-difftest --only MetaMorphoV1_1 --count 50 --seed 2026
lake env lean --run Benchmarks/Morpho/MetaMorphoV1_1/DifferentialScenarios.lean
lake env lean --run Benchmarks/Morpho/MetaMorphoV1_1/ArrayCleanupRegression.lean
lake env lean --run Benchmarks/Morpho/MetaMorphoV1_1/PackedStorageRegression.lean
```

On this machine the native executable command uses
`LEAN_CC=/tmp/metamorpho-native-toolchain/bin/cc` before `lake exe`; that temporary wrapper
supplies the installed Lean clang with the available C headers and linker libraries.
No repository toolchain or shared generator was changed for that workaround.

Both registered targets have name `MetaMorphoV1_1`, so `--only` selects both. The first patches
`MORPHO` to real Blue at `0xBBBBBbbBBb9cC5e90e3b3Af64bdAF62C37EEFFCb`; the second patches it to
the fixed-response interface fixture at `0x6000`. Both install true-returning ERC20 bytecode
at the asset address and no-return ERC20 bytecode at `0x5001`. Their Yul sources and compiled
bytecode are retained in `fixtures/`. `marketWords` includes three IDs checked against
CreateMarket logs; full parameters are in `provenance/created-markets.json`.

Independent random state does not supply a coherent live Blue market. The correlated fixture
run explicitly covers two successful constructors, cap submission/acceptance, a nonempty
supply queue, positive deposit and withdrawal, redemption, retaining and removing a withdrawal
market, reallocation through both withdrawal and supply, market removal, skim with both ERC20
return conventions, and a valid timelock submission. These are vault-interface tests against the fixed Blue fixture, not
claims about a live lending market.

Successful `permit` is not covered: this machine's differential runner does not provide the
required working ecrecover precompile path. The spec models the STATICCALL to address `1`;
the proof must handle it. Random coverage gaps are explained with the final results below.


Actual seed-2026 output, in registry order:

**Real Blue**

```text
MetaMorphoV1_1: 4025 cases: 4025 agree (1813 successful), 0 disagree, 0 stuck, 0 EVM out of gas, 0 spec out of fuel
  successful/cases: constructor 1/25, totalAssets() 28/51, name() 40/50, convertToAssets(uint256) 17/51, approve(address,uint256) 32/53, previewWithdraw(uint256) 23/52, revokePendingCap(bytes32) 19/50, totalSupply() 45/51, revokePendingGuardian() 15/51, lostAssets() 49/54, transferFrom(address,address,uint256) 2/50, setSupplyQueue(bytes32[]) 18/50, setSkimRecipient(address) 12/51, decimals() 47/53, withdrawQueueLength() 41/51, DOMAIN_SEPARATOR() 44/51, skimRecipient() 44/51, asset() 46/50, MORPHO() 40/50, submitCap((address,address,address,address,uint256),uint256) 0/51, maxDeposit(address) 43/50, updateWithdrawQueue(uint256[]) 6/52, guardian() 43/50, feeRecipient() 44/53, revokePendingMarketRemoval(bytes32) 18/52, previewRedeem(uint256) 20/52, isAllocator(address) 40/51, lastTotalAssets() 49/54, withdrawQueue(uint256) 7/54, setFee(uint256) 3/54, deposit(uint256,address) 0/53, acceptCap((address,address,address,address,uint256)) 0/53, balanceOf(address) 36/51, renounceOwnership() 9/52, submitTimelock(uint256) 0/50, reallocate(((address,address,address,address,uint256),uint256)[]) 10/50, pendingGuardian() 44/52, acceptOwnership() 8/51, pendingTimelock() 46/50, nonces(address) 34/50, submitMarketRemoval((address,address,address,address,uint256)) 0/51, eip712Domain() 47/51, acceptTimelock() 21/50, owner() 41/51, mint(uint256,address) 0/51, symbol() 48/51, submitGuardian(address) 1/52, supplyQueueLength() 40/52, pendingCap(bytes32) 42/50, acceptGuardian() 18/50, transfer(address,uint256) 11/52, multicall(bytes[]) 16/52, DECIMALS_OFFSET() 42/50, setIsAllocator(address,bool) 4/51, previewMint(uint256) 24/50, withdraw(uint256,address,address) 0/53, setSymbol(string) 13/51, redeem(uint256,address,address) 0/50, skim(address) 4/52, setName(string) 14/52, maxMint(address) 20/50, convertToShares(uint256) 20/50, revokePendingTimelock() 21/51, config(bytes32) 39/51, maxWithdraw(address) 8/52, timelock() 47/51, permit(address,address,uint256,uint256,uint8,bytes32,bytes32) 0/50, maxRedeem(address) 7/52, allowance(address,address) 40/52, fee() 47/51, pendingOwner() 48/53, curator() 47/53, setFeeRecipient(address) 6/51, setCurator(address) 12/51, previewDeposit(uint256) 27/54, transferOwnership(address) 7/50, supplyQueue(uint256) 8/51, stray 0/100
```

**Fixed Blue**

```text
MetaMorphoV1_1: 4025 cases: 4025 agree (1834 successful), 0 disagree, 0 stuck, 0 EVM out of gas, 0 spec out of fuel
  successful/cases: constructor 1/25, totalAssets() 27/51, name() 40/50, convertToAssets(uint256) 15/51, approve(address,uint256) 32/53, previewWithdraw(uint256) 26/52, revokePendingCap(bytes32) 19/50, totalSupply() 45/51, revokePendingGuardian() 15/51, lostAssets() 49/54, transferFrom(address,address,uint256) 2/50, setSupplyQueue(bytes32[]) 18/50, setSkimRecipient(address) 12/51, decimals() 47/53, withdrawQueueLength() 41/51, DOMAIN_SEPARATOR() 44/51, skimRecipient() 44/51, asset() 46/50, MORPHO() 40/50, submitCap((address,address,address,address,uint256),uint256) 0/51, maxDeposit(address) 43/50, updateWithdrawQueue(uint256[]) 3/52, guardian() 43/50, feeRecipient() 44/53, revokePendingMarketRemoval(bytes32) 18/52, previewRedeem(uint256) 16/52, isAllocator(address) 40/51, lastTotalAssets() 49/54, withdrawQueue(uint256) 7/54, setFee(uint256) 3/54, deposit(uint256,address) 2/53, acceptCap((address,address,address,address,uint256)) 0/53, balanceOf(address) 36/51, renounceOwnership() 9/52, submitTimelock(uint256) 0/50, reallocate(((address,address,address,address,uint256),uint256)[]) 10/50, pendingGuardian() 44/52, acceptOwnership() 8/51, pendingTimelock() 46/50, nonces(address) 34/50, submitMarketRemoval((address,address,address,address,uint256)) 0/51, eip712Domain() 47/51, acceptTimelock() 21/50, owner() 41/51, mint(uint256,address) 2/51, symbol() 48/51, submitGuardian(address) 1/52, supplyQueueLength() 40/52, pendingCap(bytes32) 42/50, acceptGuardian() 18/50, transfer(address,uint256) 11/52, multicall(bytes[]) 16/52, DECIMALS_OFFSET() 42/50, setIsAllocator(address,bool) 4/51, previewMint(uint256) 21/50, withdraw(uint256,address,address) 4/53, setSymbol(string) 13/51, redeem(uint256,address,address) 0/50, skim(address) 4/52, setName(string) 14/52, maxMint(address) 20/50, convertToShares(uint256) 19/50, revokePendingTimelock() 21/51, config(bytes32) 39/51, maxWithdraw(address) 25/52, timelock() 47/51, permit(address,address,uint256,uint256,uint8,bytes32,bytes32) 0/50, maxRedeem(address) 17/52, allowance(address,address) 40/52, fee() 47/51, pendingOwner() 48/53, curator() 47/53, setFeeRecipient(address) 5/51, setCurator(address) 12/51, previewDeposit(uint256) 25/54, transferOwnership(address) 7/50, supplyQueue(uint256) 8/51, stray 0/100
```

Zero-success entries in the random run are intentional coverage limits, not disagreements:

- `submitCap`, `acceptCap` and `submitMarketRemoval` need matching market IDs and coherent
  configuration/pending values. All three have successful correlated scenarios.
- Real Blue's random world lacks initialized market state for deposit/mint/withdraw/redeem.
  Fixed Blue supplies successful deposit, mint and withdrawal samples; the correlated sequence
  also exercises a positive withdrawal and a redemption.
- `redeem` had no successful random sample under either target: its balance, share conversion
  and withdrawal-liquidity conditions were not jointly met. The correlated redemption covers it.
- `submitTimelock` needs an authorized owner, no pending update, a different current value,
  and a new value in `[86400, 1209600]`. The correlated submission covers the valid combination
  this seed did not reach.
- `permit` has no successful sample for the ecrecover limitation above. `stray` is deliberately
  malformed or unknown-selector calldata, so zero successful calls is expected.

The executable also prints diagnostics for unavailable BN_ADD/BN_MUL/SNARKV foreign
precompiles during initialization. These are not vault-test disagreements; the vault scenarios
above do not use those precompiles.

## Where the spec follows compiled behavior

The semantic audit covers all 76 selector arms, shared runtime routines, constructor code,
and rejection of unknown/short calldata. There is no receive or fallback function. The later
proof-valuation issue below was resolved with approved bounds. The remaining function and
constructor proofs are still in progress.

- `PendingAddress` includes an explicit `uint32 padding` field. Solidity packs its declared
  address and uint64 into 224 bits, but deletion clears the entire slot. Ordinary field
  updates preserve the upper 32 bits. Minimal regression: owner calls
  `revokePendingGuardian()` with `storage[15] = 2^224`; bytecode and corrected spec both leave
  zero. The regression also covers `submitGuardian`'s immediate branch and `acceptGuardian`.
- Role helpers preserve the compiler's short-circuit read order. Pending-value updates cache
  the timelock before their first field write. `_setCap` caches `lastTotalAssets` before its
  external view calls, and `skim` caches its recipient before `balanceOf`.
- `_withdrawable` checks supply-minus-borrow underflow before calling the token's `balanceOf`.
  Checked arithmetic, narrowing checks, array allocation/growth limits, enum validation,
  short-string length checks and compiler calldata guards are explicit or supplied by the
  standard ABI/storage semantics.
- The ID hash is the hash of five ABI words. `supplyShares` and `lastUpdate` use Blue's
  `extSloads` interface with the library's exact slot derivation. The source convenience
  methods are not separate external calls in the bytecode.
- OpenZeppelin `mulDiv` uses an exact mathematical product with a checked quotient, preserving
  full-precision behavior; Morpho's multiplication helpers instead check the intermediate
  256-bit product. Rounding and division-by-zero checks remain distinct.
- SafeERC20 models low-level calls, optional Boolean returns, code-existence checks and
  failure propagation. Supply/withdraw try-catch catches callee failure; malformed return
  data after a successful call still reverts. Multicall uses self-DELEGATECALL. Revert payloads
  are abstracted by the framework, while success returns and events remain part of comparison.

The original compiler issue is
[LostStorageArrayWriteOnSlotOverflow](https://www.soliditylang.org/blog/2025/12/18/lost-storage-array-write-on-slot-overflow-bug/),
fixed in solc 0.8.32. For a short counterexample, set
`B = uint256(keccak256(abi.encode(uint256(20))))`, `storage[20] = 2^256 - B`, and
`storage[B] = 7`, then call `setSupplyQueue([])` as owner. The old runtime succeeds while
leaving `7`; 0.8.37 enters cleanup and exhausts finite gas. Ordinary two-element cleanup also
passes the regression. The enormous length is an artificial raw-storage case. No storage
backend changes or slot-noncollision axioms were introduced.

## Guidance for the proving session

Start from `Correct.lean`. The original skeleton had 78 placeholders: 76 function bodies,
the constructor, and `Common.restrictImmutables_of_fit`. Handwritten proofs now replace the
bridge and twenty-nine function stubs. Do not force-regenerate the skeleton:
that would overwrite this proof work. `SpecSyntax.lean` remains authoritative.

`Dispatch.lean` now imports five source-dispatch shards and five EVM-reach shards. Every shard
is below 2,000 lines; original theorem statements and proofs are retained. `BodyCommon.lean`
contains shared source guards, byte-length arithmetic, selector exclusion, and return encoding.

There are **eleven** immutables, including inherited OpenZeppelin fields. The test valuation
is `deployedImmutables` in `DiffTarget.lean`; values and current offsets are also in
`provenance/deployment-comparison.json`.

| Immutable | Reference valuation |
| --- | --- |
| `_asset` | `0x45804880de22913dafe09f4980848ece6ecbaf78` |
| `_underlyingDecimals` | `18` |
| `_cachedDomainSeparator` | `0x8f37e0b6d6c1781e97de5ecb3bae2dd56076e9111d4b253739015ae80df19392` |
| `_cachedChainId` | `1` |
| `_cachedThis` | `0xBeeF7959aE71D4e45e1863dae0B94C35244AF816` |
| `_hashedName` | `keccak256("") = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470` |
| `_hashedVersion` | `keccak256("1") = 0xc89efdaa54c0f20c7adf612882df0950f5a951637e0307cdcb4c672f298b8bc6` |
| `_name` | `0` (empty ShortString) |
| `_version` | `0x3100000000000000000000000000000000000000000000000000000000000001` |
| `MORPHO` | `0xBBBBBbbBBb9cC5e90e3b3Af64bdAF62C37EEFFCb` |
| `DECIMALS_OFFSET` | `0` |

The theorem is parameterized over fitting immutable valuations; it is not restricted to the
test valuation. Use current `Immutables.lean` offsets, never the historical offsets.

`external-abi.lean.inc` supplies the manual boundary encodings: five-word MarketParams,
six uint128 Market fields, Position's uint256/uint128/uint128, two separate uint256 results
for `supply` and `withdraw`, dynamic bytes32 arrays for `extSloads`, and the ERC20/IRM calls.
It converts named memory structs to ABI tuples and converts decoded structs back. The actual
runtime uses `extSloads` for positions; the `position` entry documents the complete interface.

Expect the queue loops, cap enablement/removal, reallocation, fee/loss accounting, full-precision
mulDiv, SafeERC20 call paths, multicall, EIP712/permit and constructor immutables to need most
work. Reason over raw packed slots and cached reads; preserve storage effects around calls.
View-call preservation can justify cached queue lengths. Array cleanup must account for
finite gas on enormous raw lengths; the overflow regression's out-of-gas result is not a
successful equivalence test. Begin with the simple getters and shared arithmetic/call helpers.

`MetaMorphoV1_1.report.md` is the runtime block/source report. A full creation disassembly can
be generated with `python3 scripts/bytecode_report.py Benchmarks/Morpho/MetaMorphoV1_1
--full-creation --output /tmp/metamorpho-full-report.md`. Executable init code ends at PC 3893;
the embedded runtime starts at byte 3894, followed by the two constructor event-topic constants.

## Proof valuation issue found on 2026-10-08

The randomized differential suite was rerun with `--only MetaMorphoV1_1 --count 50` and exited
successfully: both targets again reported 4025 agreements, with zero disagreements or stuck
cases. Those targets use fitting immutable stores.

The generated `MetaMorphoV1_1Immutables` structure represents `_underlyingDecimals` and
`DECIMALS_OFFSET`, both declared uint8, as unrestricted `EVM.Word` fields. Consequently,
`metaMorphoV1_1Correct` and `metaMorphoV1_1DECIMALS_OFFSETBody` quantify over invalid valuations.
At `DECIMALS_OFFSET = 256`, the runtime masks the value with 255 and returns zero, but the
source returns 256, which cannot be ABI-encoded at the declared uint8 return type.

`ImmutableTypeRegression.lean` preserves the executable reproduction and two kernel-checked
facts about the mask and failed return encoding. Both theorem axiom audits contain only
standard Lean axioms. Its module build and executable run pass, with this output:

```text
DECIMALS_OFFSET=255: agree (success)
EVM return word: 255
DECIMALS_OFFSET=256: DISAGREE: the returned values do not ABI-encode at the declared return types
EVM return word: 0
```

The approved correction adds proof fields for `_underlyingDecimals.toNat < 256` and
`DECIMALS_OFFSET.toNat < 256` to the valuation structure, deriving these bounds from
`immutablesFit` in `restrictImmutables_of_fit`. This preserves the final
`metaMorphoV1_1ContractCorrect` statement and the scope of all fitting immutable stores; it
does not require any specification, bytecode, generated block-summary, or Solidity changes.
The user approved this valuation change on 2026-10-08. The bridge is now proved from
`immutablesFit`; its axiom audit contains only `propext` and `Quot.sound`.

Completed functions: `DECIMALS_OFFSET`, `MORPHO`, `asset`, `lostAssets`, `lastTotalAssets`,
`timelock`, `curator`, `guardian`, `skimRecipient`, `owner`, `pendingOwner`, `totalSupply`,
`fee`, `feeRecipient`, `supplyQueueLength`, `withdrawQueueLength`, `decimals`,
`pendingTimelock`, `pendingGuardian`, `balanceOf`, `nonces`, `isAllocator`, `pendingCap`,
`config`, `allowance`, `supplyQueue`, `withdrawQueue`, `setCurator`, `setSkimRecipient`,
`transferOwnership`, `acceptOwnership`, and `renounceOwnership`.

Every completed function covers successful execution, nonzero callvalue rejection, and
oversized calldata rejection. The queue getters cover bounds failures; the setters cover
authorization, unchanged-value rejection, and static-call halts. The ownership functions cover
authorization and static-call halts, preserving the unused portions of packed storage slots.
`decimals` also covers uint8 sum overflow. All thirty-two individual axiom audits contain only
standard Lean axioms and permitted concrete evaluation axioms; none contains `sorryAx`.
The full `Correct` target passed at the thirty-two-function checkpoint (3619 jobs).
There are **45 remaining placeholders** in other functions and the constructor. This is an
intermediate checkpoint, not a completed correctness proof.

Logs include `/tmp/metamorpho-32-functions-build.log`,
`/tmp/metamorpho-transfer-ownership-build.log`, and `/tmp/metamorpho-accept-ownership-build.log`.

The next dependency chain is `_maxDeposit` and the market/share arithmetic helpers used by
`maxDeposit` and `maxMint`; these functions are not constant limit getters in this specification.

The following dependencies now have completed proofs (the ABI-function count is unchanged):

- `Arithmetic`, `CheckedArithmetic`, `MarketArithmetic`, and `MulDiv`: source arithmetic and
  shared EVM checked addition, multiplication, division, and zero-floor subtraction routines.
- `SharesToAssetsUp` and `SharesToAssetsUpRoutines`: rounded-up share-to-asset conversion,
  including all arithmetic failure branches, on both the source and EVM sides.
- `PackedSource`, `MorphoSlots`, and `MemoryArraySource`: source packed encoding, casts, nested
  storage-slot hashes, and the singleton array used by `MorphoLib_supplyShares`.
- `MemoryRoutines`, `MemoryArrayData`, `MemoryArrayRoutines`, and `PackedHashMemory`: allocation,
  first-element access, singleton memory contents, and two-word hash buffers. The memory proofs
  establish the length, contents, free cursor, and preservation of earlier allocated words.
- `MorphoSlotRoutines.supplySharesReachEncoding`: EVM execution from pc 14078 through the nested
  hashes and singleton construction to pc 14169. It assumes the explicit allocation bound
  `ptr.toNat + 256 < 2^64`; callers must discharge it. Its audit contains 152 allowed axioms,
  including concrete evaluation facts, and no `sorryAx` or unexpected axioms.
- `SupplySharesSource`: the source supply-share reader, parameterized by the actual typed
  `extSloads` call. It covers a nonempty decoded array, call failure, decoding failure, and an
  empty decoded array.
- `ExtSloadsABI`, `ExtSloadsMemory`, `ExtSloadsEncode`, and `ExtSloadsSetup`: the exact 100-byte
  singleton request, preservation of its input array, the encoding loop, and the input stack
  at STATICCALL pc 14210.
- `ExtSloadsCall.extSloadsStaticcall`: couples the actual EVM call witness to the source call,
  including the depth-limit branch, and reaches pc 14211. Its audit contains only the three
  standard axioms and three permitted concrete evaluation axioms.

Recent successful dependency build logs include `/tmp/metamorpho-slot-routines-build.log`,
`/tmp/metamorpho-memory-array-routines-build.log`, `/tmp/metamorpho-slots-hash-memory-build.log`,
`/tmp/metamorpho-extsloads-setup-build.log`, and `/tmp/metamorpho-extsloads-call-build.log`.

## New unresolved return-buffer allocation mismatch

Do not continue ordinary function proofs until this issue is resolved, as required by
`Misc/prompt.md`. The previous approval concerned the uint8 immutable bounds; it did not
authorize changing the source semantics outside this benchmark or restricting the gas domain.

`ExtSloadsAllocationRegression.lean` contains a symbolic buffer of exactly `2^64` bytes:
the ABI offset is 32, the array length is one, and all remaining bytes are zero. It proves:

- `oversizedReturn_sourceAccepts`: the current external ABI decoder accepts a one-element array.
- `oversizedReturn_allocatorRejects`: with free cursor 512, the compiled allocation guard fails.
- `oversizedReturn_evmReverts`: from a successful-call state at pc 14211 with that buffer, the
  supplied block summaries reach the allocation panic at pc 2690 and prove `RDrev`.
- `oversizedReturn_withinGasDerivedBound`: the buffer is within the existing proved bound for
  opaque EVM return data.
- `oversizedReturn_memoryGasFits`: its EVM memory expansion costs less than `2^120` gas, a budget
  allowed by the current 256-bit gas domain.

These are checked local boundary facts, **not** an end-to-end counterexample to `Correct`.
In particular, no complete transaction or callee `Theta` reachability witness is asserted.
The source-acceptance proof uses only standard Lean axioms. The conditional bytecode-revert
proof uses 74 allowed axioms, including concrete bytecode facts, with no unexpected axioms.

The source frame does not track a compiler memory cursor. `ABI.decodeReturnValues?` checks
the signed total-size bound and the individual uint64 offset/length bounds, but not the
compiler's cumulative allocation bound. The source also does not reserve the copied return
buffer. Thus decoder well-formedness alone cannot discharge the allocator guard. The earlier
explicit `ptr + 256 < 2^64` obligation also requires a cumulative memory invariant at callers.

The recommended repair is to retain the unconditional theorem and explicitly model allocation
failure: add a memory cursor and allocation operation to Solm, propagate the cursor across
internal calls, and annotate the benchmark's compiler allocation sites, including the raw
return-buffer copy and decoded array. Likely library changes would involve
`Solm/Semantics/Types.lean`, `Solm/Syntax/Basic.lean`, `Solm/Semantics/Exec.lean`, the interpreter
and syntax support, and the affected `Reasoning` combinators. This exceeds the current
benchmark-only edit scope and needs a scope decision before implementation. A smaller gas
domain is an alternative change to the theorem's claim, not an implicit assumption we may add.

Regression build log: `/tmp/metamorpho-extsloads-allocation-regression-build.log`.

## Resumption on 2026-10-09: external-call reachability established

The saved `ExtSloadsOversizedCallee.lean` trace typechecks. It executes a concrete 21-byte
callee from its initial state and returns `oversizedReturn` using `2^120` gas. The buffer
remains symbolic: no test attempts to allocate `2^64` bytes.

This resumption extended that file with the following checked facts:

- `oversizedCalleeTheta` proves a successful `Theta` invocation of the callee installed at
  address `0x6000`, called from `0x6001`, with zero value and static permissions.
- `oversizedCalleeTypedCall` supplies the same witness to `typedCallViaEVM` for the actual
  `extSloads` singleton request, for every requested slot.
- `oversizedCalleeCallAccepted` combines that call with the existing ABI-decoder proof: the
  decoder accepts a one-element array from an output of size exactly `2^64`.
- `acceptedCallDoesNotBoundReturnSize` refutes the proposed general implication from
  successful typed calls and accepted array decoding to `out.size < 2^64`.

These results close the callee-reachability gap in the earlier boundary evidence. They do
**not** assert an end-to-end vault transaction counterexample or refute `Correct`: the vault's
post-call state in `oversizedReturn_evmReverts` is still a hypothesis. In addition, Solm's
external-call relation existentially quantifies the callee gas, so a boundary discrepancy
alone is insufficient to refute the existential top-level refinement. Replacing the actual
successful call with a different failing call would not satisfy the requested same-call proof
discipline.

The focused `ExtSloadsOversizedCallee` module build passes. No differential suite or previous
audit was rerun. No specification, theorem signature, bytecode, generated summary, or shared
library was changed, and no placeholder or assumption was added. The 45 existing placeholders
remain.

The allocation-model repair remains unresolved. A benchmark-local alternative to shared
Solm changes is explicit cursor passing through internal helper arguments and results, with
raw return-buffer reservation and decoded-value allocation checks at the compiled sites.
That requires updating the affected source helpers and their proofs, not merely adding a
fixed output-size check. The user has been asked to choose between that local rewrite and an
explicit scope expansion for shared Solm memory accounting. Keep the directory restriction
in force unless the user changes it.

## Local allocation repair: checked helpers and complete supply-share routine

The benchmark-local cursor-passing repair is now underway within the existing directory
restriction. No shared Solm or Reasoning source has been edited. The earlier scope question
does not prevent this local work; there is no authorization to expand the edit scope.

`Spec.lean` now appends three internal helpers, preserving every original function index:
`__solcAllocateMemory`, `__solcExtSloads`, and `__solcMorphoSupplyShares`. Their syntax is in
`AllocationSyntax.lean`, `ExtSloadsAllocationSyntax.lean`, and
`SupplySharesAllocationSyntax.lean`. The original source readers and their upstream callers
have **not yet** been redirected or given cursor arguments/results. Thus this is a modular
repair in progress, not a completed repair of the top-level specification.

Checked new results:

- `AllocationSource.lean` / `AllocationRoutines.lean`: exact source and bytecode allocator
  success/failure, including rounding and wraparound, without an assumed allocation bound.
- `ExtSloadsSimulation.extSloadsPostCallSimulation`: all post-call paths from pc 14211
  through raw-buffer reservation, dynamic-array decoding/allocation/copy, to pc 14256 or
  `RDrev`. It uses the same actual call witness and derives the return-size bound from it.
  The component files cover malformed headers, missing payload, and both allocation failures.
- `ExtSloadsAllocationRepair.oversizedReturn_repairedSourceReverts`: the registered helper
  reverts for the actual successful oversized callee witness at cursor 512. This remains a
  helper-level regression, not a top-level transaction counterexample.
- `MorphoSlotAllocation.lean`: the supply-share prefix covers failure at either 96-byte hash
  allocation or the 64-byte singleton-array allocation; success reserves 256 bytes total.
- `SupplySharesAllocationSource.lean`: complete source execution of the registered
  cursor-aware reader, including allocation failure, external-helper failure, empty array,
  and successful `(value, cursor)` return.
- `SupplySharesAllocationRoutines.supplySharesAllocationSimulation`: complete internal
  routine simulation from pc 14078 through the actual STATICCALL and back to an arbitrary
  valid caller continuation, or paired source/EVM revert. Success returns the matching
  cursor at memory slot 64, with its lower/upper bound and memory-size invariant. The only
  cursor input restriction is the ordinary lower bound 96; allocation fits are case splits,
  not assumptions. `SourceState` is carried across the same call.

Focused builds for the new supply-share routine pass (log
`/tmp/metamorpho-supply-shares-simulation-build.log`). The existing `Correct` scaffold also
built after the first two helpers were registered; registering the third helper has been
validated by focused builds, but a new full `Correct` build is not yet run. The 45 original
placeholders remain, and no new placeholder or axiom has been introduced. No differential
suite or previous audit was rerun.

Next: thread cursor results through the actual source call graph and account for other
compiled allocations in those callers. Do not reset the cursor at each internal call, use a
fixed return-size restriction, or replace the actual successful call by a different failed
call. `SupplySharesAllocationSetup.lean` links its fixed prefix to calldata construction;
`ExtSloadsValueRoutines.lean` proves the empty/nonempty array continuation. Caller proofs
that retain allocated memory will additionally need prefix-preservation facts; the present
routine theorem exposes the cursor invariant but does not yet return `MemoryPrefix`.

## Cursor propagation and complete market-parameter reader

The preceding registration/root-status paragraph is superseded. `Spec.lean` now appends six
helpers, adding `__solcMarketParams`, `__solcExpectedMarketBalances`, and `__solcMaxDeposit`.
`MaxDepositAllocationSyntax.lean` threads the cursor through the three reader calls and the
`_maxDeposit` loop. The actual `maxDeposit` transition (index 19) initializes the cursor to
128 and returns the result component. Its original three prefix statements, including both
the nonpayable check and calldata-length check, are preserved. All original function indices
are preserved. Other roots, including `maxMint`, still use their original call chains; the
whole-contract allocation repair is incomplete. `Common.lean` only needs the new transition
definition in the selector-signature simplification. The full existing `Correct` scaffold
built after this integration (log `/tmp/metamorpho-max-deposit-cursor-build.log`).

The compiler's `_marketParams` reader now has a complete, checked internal simulation:
`MarketParamsAllocationRoutines.marketParamsAllocationSimulation`. It begins at pc 16116,
shares the actual STATICCALL witness with the source, and returns to any valid continuation
or produces paired source/EVM reverts. It covers the initial 160-byte zero-struct reservation,
failed calls, short returns, both subsequent 160-byte reservations, and rejection of each
noncanonical address. Success supplies the exact five field words, source struct value,
`SourceState`, and the bounded cursor at memory slot 64. Allocation fits and valid decoding
are conclusions of the case split, not assumptions on callees.

Components: `MarketParamsAllocationSource.lean` (complete source execution),
`StructAllocationRoutines.lean` (the fixed allocator), `MarketParamsCallMemory.lean` and
`MarketParamsAllocationSetup.lean` (initial memory and call setup), `MarketParamsCall.lean`
(same-call correspondence), `MarketParamsABI.lean` (exact ABI success/failure conditions),
`MarketParamsReturnAllocation.lean` (post-call allocations and size guard),
`MarketParamsReturnMemory.lean` (buffer and field-memory facts), and
`MarketParamsDecodeRoutines.lean` (address checks and field stores). Focused build passes:
`/tmp/metamorpho-market-params-simulation-build.log`.

Next dependency is `__solcExpectedMarketBalances`: its syntax reserves 384 bytes after the
`market` call (192-byte return buffer plus 192-byte decoded struct), and 32 bytes after the
conditional `borrowRateView` call. Its source execution, EVM simulation, interest arithmetic,
and the eventual maxDeposit loop remain to prove. Existing `MarketArithmetic.lean` covers
only zero-floor subtraction, not interest accrual. Both completed reader simulations will
need additional `MemoryPrefix` output for callers retaining previously allocated objects.

The 45 original placeholders remain. No new placeholder or assumption was introduced. No
differential suite or previous audit was rerun, and no file outside this benchmark was edited.

## Market-call prefix and six-field decoder

`MarketReadSimulation.marketReadSimulation` now covers the balance reader from pc 16911
through the actual `market` STATICCALL, both 192-byte reservations, six `uint128` field
checks, and pc 16966. Every failed call, short/malformed return, or allocation failure has
a matching source/EVM revert. Success carries the actual source call, `SourceState`, exact
field words, cursor at memory slot 64, and `MemoryPrefix` below the incoming cursor. The
remaining elapsed-time and interest-accrual computation is **not** included in this theorem.

Source components: `MarketParamsHashSource.lean` proves the five-word market identifier
hash and its internal call; `MarketBalancesAllocationSource.lean` proves source execution
through the market call and the 384-byte reservation. `MarketABI.lean` characterizes all six
uint128 checks. Runtime components: `MarketCallMemory.lean`, `MarketCall.lean`,
`MarketReturnAllocation.lean`, `MarketReturnMemory.lean`, and `MarketDecodeRoutines.lean`.
`StructAllocationRoutines.lean` now includes the 192-byte allocator and a general aligned
reservation-splitting fact.

Reusable local helpers were factored into `ScalarTupleABI.lean`, `SingleWordCallMemory.lean`,
`StaticCallSimulation.lean`, and `StructReturnMemory.lean`. Both reader families use them;
the existing market-parameter simulation still builds after these refactorings. Focused
combined build passed in `/tmp/metamorpho-market-read-simulation-build.log`. `git diff --check`
passed. No differential suite or prior audit was rerun; the 45 original placeholders remain.

Next: checked timestamp subtraction at pc 12234, then the short-circuit tests at 16991,
17001, 17007 (helpers 17600 and 17578). No-accrual returns through 17012. Accrual enters
17069, encodes `borrowRateView` through 12112/17114/17198, calls at 17225, reserves 32 bytes
on return through 17524, then computes Taylor terms, interest, and optional fees. Read exact
generated summaries before composing these paths. The older supply-share and market-parameter
whole-routine interfaces still need memory-prefix outputs for callers retaining allocations.

## Elapsed time, allocating casts, and the complete rate call

`MarketBalancesSource.lean` and `MarketBalancesRoutines.lean` now cover checked timestamp
subtraction, the three short-circuit accrual tests, time-underflow rejection, and the
no-accrual return. The full source no-accrual/time-underflow paths are proved; their final
composition with the existing market-read simulation remains. `CheckedArithmetic.lean`
now includes the shared checked subtraction routine at pc 12234.

Important compiler allocation discovered and reported: `UtilsLib_toUint128` at pc 19367
unconditionally reserves 64 bytes for its error string, even on successful casts. The
authorized cursor repair now appends a seventh helper, `allocatedToUint128Function`, and
`allocatedMarketBalancesFunction` routes its three possible casts through it. The new
helper is appended last, preserving earlier helper indices. `Uint128AllocationSource.lean`
and `Uint128AllocationRoutines.lean` prove the source calls and all bytecode outcomes:
allocation failure, value overflow, and success with the advanced cursor, sufficient memory,
and preserved earlier allocations. This is not a new input bound or assumption.

`BorrowRateSimulation.borrowRateSimulation` is now checked from pc 17069 through pc 17239.
It constructs the exact 356-byte request, shares the actual `borrowRateView` STATICCALL
result with the source (including the depth-limit branch), rejects failed calls and short
returns, and handles the 32-byte allocation. Success supplies the decoded rate, SourceState,
cursor, memory prefix, and a source continuation through the call/reservation. Components:
`BorrowRateABI`, `BorrowRateCall`, `BorrowRateSetup`, `BorrowRateReturn`, `BorrowRateSource`,
`BorrowRateReadMemory`, and `BorrowRateEncodeMemory`. `MarketParamsEncode.lean` proves the
shared five-field encoder at pc 12112. `WordCallMemory.lean` and `wordWindowPrefix_load` are
reusable local memory helpers. Focused builds passed for these components; the simulation
build log is `/tmp/metamorpho-borrow-rate-simulation-build.log`.

Next is the Taylor expansion and interest arithmetic. Source function 79 computes
first=x*n, second=mulDivDown(first,first,2e18), third=mulDivDown(second,first,3e18), and
checked `(first+second)+third`. Bytecode: checked multiply 12002 returns first at 17278;
17278 squares first, returning 17300; 17300 divides by 2e18 and multiplies second*first,
returning 17320; 17320 divides by 3e18 and calls checked add 12077 with return 17327;
17327 calls checked add again, with caller-supplied return (17332 in this path). 17332
then swaps into checked multiplication for interest, returning 17338; that divides by
1e18 and enters the allocating cast at 19367. Read exact summaries for stack details.
`WadMultiply.lean` and the added mulDivDown call wrappers already prove source multiplication.

The 45 original placeholders still remain. No original audit or differential suite was
rerun, no assumption was added, and edits remain within this benchmark. `git diff --check`
passed at this milestone. Overall cursor repair still affects only maxDeposit; other roots
need repair before their proofs can be completed.

## Taylor and interest arithmetic

`TaylorWords.lean`, `TaylorSource.lean`, and `TaylorRoutines.lean` now prove the full
Taylor helper, including every checked-multiplication failure. `taylorSumsFit` derives
both final-addition bounds from the already checked square, so the proof adds no input
assumption. The focused Taylor build passed in `/tmp/metamorpho-taylor-routines-build.log`.
`MarketInterestSource.lean` and `MarketInterestRoutines.lean` pair the two source calls
with pc 17239 through the first cast at pc 19367, including Taylor and interest-product
overflow. `Uint128Add.lean` proves the checked narrow source addition and the compiler
routine at pc 16879, for success and panic. Their combined focused build is recorded in
`/tmp/metamorpho-market-interest-routines-build.log`.

Next compose the two 64-byte allocating casts and the borrow/supply asset updates,
then the optional fee branch. The cast return pc 17353 is shared by the borrow-assets
and fee-shares additions. The second interest cast returns to pc 17378. These routines
must retain the market's memory loads through the allocations and stores.

## Asset updates and fee branch

`MarketAssetsSource.lean` proves the two allocating casts and checked borrow/supply asset
updates, on success and every failure. `MarketAssetsRoutines.lean` pairs these with bytecode
pc 19367 through pc 17387 (before the final supply store). `MarketAssetsMemory.lean` proves
the memory effects after that store: both changed fields, preservation of disjoint fields,
free cursor, size, and the prefix below the market struct. Supporting reusable local files:
`CursorCastSource`, `CastFieldSource`, `CastAddFieldRoutines`, `CastStoreMemory`, and
`MarketValueUpdates`. Focused builds passed; see `/tmp/metamorpho-market-assets-routines-build.log`
and `/tmp/metamorpho-market-assets-memory-build.log`.

`SharesDownSource.lean` proves function 81 for canonical uint128 market totals (including
product overflow). These internal bounds come from decoded/updated market fields.
`MarketFeeSource.lean` proves the entire fee body, including subtraction underflow,
share-product overflow, allocation/cast failure, and checked share-total overflow.
`MarketFeeArithmetic.lean` covers pc 17400 to 19367; `MarketFeeRoutines.lean` pairs the complete
fee source body with pc 17400 to 17012, using the same value and cursor. Success memory is
`castStoreMemory` at the shares field. Build logs:
`/tmp/metamorpho-market-fee-arithmetic-build.log`, `/tmp/metamorpho-market-fee-routines-build.log`.

`MarketBalanceFinal.lean` now checks the pc 17387 supply store and fee/no-fee branch, plus
a generic four-word uint128 return routine at pc 17012 with arbitrary returndata (the rate
call has replaced the original market returndata). It also proves source returns for updated
market values. Composition of asset updates, fee selection, optional fees, and final return
is next; then prepend interest and the already proved rate/market external-call simulations.
The 45 original placeholders remain. No old audit or differential suite was rerun.

## Complete market-balance helper

`MarketBalancesSimulation.marketBalancesSimulation` is now checked and built. It starts
at pc 16911 with the Morpho address, market-parameter pointer, and return address, and
pairs the full source helper with either EVM revert or the final four-word return. It covers
the actual `market` call, decoding and allocation, timestamp underflow, skipped accrual,
the actual rate-model call, Taylor/interest arithmetic, both asset casts/updates, optional
fees, and the final return. Success includes SourceState, all four returned values, the
current cursor and its bounds, sufficient memory, and preservation below the entry cursor.
Build passed: `/tmp/metamorpho-market-balances-simulation-build.log`.

Composition modules: `AccruedBalanceSimulation` (pc 19367 through assets/fees/return),
`InterestBalanceSimulation` (pc 17239 through return), and `MarketAccrualSimulation`
(pc 17069, actual rate call through return). `BalanceSnapshot` in
`AccruedBalanceSimulation.lean` packages final memory/frame, three updated totals, cursor,
and prefix; its `rebase` method composes prefixes. Borrow shares stay the original word96.
`WordWindow.lean` proves that aligned field loads determine the complete byte window and
therefore arbitrary 32-byte loads. This bridges the six field loads from the market decoder
to the call encoder's existing window interface.

Next: integrate the complete reader into `_maxDeposit`'s loop. Input memory to the balance
helper needs the 160-byte market-parameter window and `MarketParamsLoads`; the existing
market-parameter simulation returns `marketParamsReadMemory`, whose field/window properties
can supply these. The existing supply-share and market-parameter readers do not yet expose
memory-prefix results, but maxDeposit mostly retains scalar stack values between calls;
check whether the new caller actually needs these before extending them.

Elaboration lesson: explicitly `dsimp only` frame-update definitions when proving
`frameA.contract = contract`. Definitional unification otherwise unfolds the entire contract
and times out. Keep `wordWindowRead_of_fields (count := 6)` explicit: solving `32 * ?count = 192`
by definitional unification also times out. No heartbeat increases were retained.

## Completed public maxDeposit

`metaMorphoV1_1MaxDepositBody` is proved without placeholders. Focused build passed:
`/tmp/metamorpho-max-deposit-build.log`. There are now 44 original placeholders left.
The theorem includes entry guards, all address-decoding failures, the complete allocated
internal function and queue loop, actual external calls, arithmetic failures, and the final
scalar return. `MaxDepositEntry` and `MaxDepositBodySource` supply the public boundary;
the final connection uses `RDret.reEquivExecutionGen` with the actual final account map.

New composition modules: `MarketParamsDecoded`, `CursorCallSource`, `AllocatedReaderCalls`,
`MaxDepositReadersSource`, `MaxDepositReadersSimulation`, `MaxDepositArithmeticSource`,
`MaxDepositArithmeticSimulation`, `MaxDepositLoopSyntax`, `MaxDepositQueueSource`,
`MaxDepositQueueRoutines`, `MaxDepositInvariant`, `MaxDepositIteration`, `MaxDepositLoop`,
and `MaxDepositFunction`. The three reader simulations now expose storage preservation;
the parameter reader additionally exposes its struct's lower bound and end-before-cursor
bound. These facts are derived, not assumptions. The loop induction uses remaining queue
length; static-call storage preservation keeps the cached length equal to storage slot 20.

Next is `maxMint`, whose bytecode first calls the already proved maxDeposit helper and then
the accrued-fee/assets calculation and conversion. Extend the previously authorized cursor
model through expectedSupplyAssets (function 51), accruedFeeAndAssets (29), convertToShares
(22), and public transition 59. The other public roots still use the original helpers.
ExpectedSupplyAssets retains market parameters in memory across the supply-share read, so
the supply-share simulation will need to expose memory-prefix preservation as well as its
cursor and storage facts. Its current success witness uses concrete call/buffer/array memory.

Public maxMint entry PCs: 2173 nonpayable, 2179 length, 2191 address decoder call, 2198 calls
13894 with stack `[2215, 2234, 1578, 32] ++ R`. PC 2215 calls accruedFeeAndAssets at 12247;
2223 reads totalSupply slot 2 and calls checked add at 12077; 2234 enters conversion at 14489.
No differential suite or prior audit was rerun.

## maxMint readers and accrued-assets loop

The authorized cursor model now extends through public transition 59 (`maxMint`).
`MaxMintAllocationSyntax` appends expectedSupplyAssets (original function 51),
accruedFeeAndAssets (29), and convertToShares (22), bringing the helper list to ten.
`Common.maxMintSelectorOf` unfolds the new transition; no original theorem signatures changed.
The extension was reported when made. Other public roots remain as before.

`SupplyAssetsSimulation.supplyAssetsSimulation` is complete and built. Entry 12483 retains
three caller words plus the Morpho word, performs supply-share reading, market balance
calculation, then conversion to assets rounding down, and returns to an arbitrary valid PC.
It exposes the actual final state, storage preservation, cursor, and memory bounds.
The supply-share allocation simulation now additionally exposes preservation below the
entry cursor and cursor monotonicity. `SupplySharesMemoryPrefix` and `HeapWordWindow`
justify retaining the market-parameter memory window across that read.
`SharesToAssetsDown` and `SharesToAssetsDownRoutines` cover the source and PC 18378 routine.
The combined build also rechecked public maxDeposit successfully:
`/tmp/metamorpho-supply-assets-simulation-build.log`.

`AccruedAssetsIteration` and `AccruedAssetsLoop` are complete and built. The induction runs
from PC 12288 to 12296, preserves storage and the later fee-calculation locals, and covers
every actual external-call, allocation, and checked-add revert. `AccruedAssetsPrefix`
connects function entry 12247 and the initial five source statements to that loop. Success
exposes a source continuation from body.drop 5 and `AccruedAssetsTailLocals`.

`AccruedAssetsTotals` proves the source loss adjustment, checked total-assets addition,
and interest subtraction. `AccruedAssetsTotalsRoutines` covers the same bytecode through
PC 12353, with all failure cases. `AccruedFeeGuard` proves the short-circuit condition:
no fee returns to the caller with stack `[newLost, newTotal, feeShares] ++ R`; a fee reaches
12369 with `[interest, ret, newLost, newTotal, feeShares] ++ R`.
These modules have passed focused builds (logs `/tmp/metamorpho-accrued-*-build.log`).
The most recent edits only wrap long lines in these files and SupplyAssetsSimulation.

Next dependency is OpenZeppelin full-precision mulDiv. The source function 66 uses an
unbounded integer product followed by division and a uint256 range check. The specialized
denominator 1e18 EVM routine starts at 16398; generic mulDiv starts at 16544. Both compute
the high product word as `sub (sub (mulMod x y (not 0)) (mul x y)) (lt mm (mul x y))`.
Generic 16573 rejects denominator <= high word; 16581 computes the power-of-two factor and
six Newton inverse refinements; 16654 combines the corrected numerator and inverse.
Do not dump the entire 16581 expression; use a named Newton-step abstraction.
The specialized routine uses division by 2^18, a high-word shift by 238, and constant
inverse 78156646155174841979727994598816262306175212592076161876661508869554232690281.
Those dependencies and the full maxMint proof are now complete; see the next section.

## Completed public maxMint

`metaMorphoV1_1MaxMintBody` is proved without placeholders and its focused build passed:
`/tmp/metamorpho-max-mint-build.log`. There are now 43 original placeholders left, including
the constructor. No differential suite or previous audit was rerun. No new assumptions or
specification changes were needed after the previously recorded cursor-model extension.

The full-precision arithmetic chain is complete in `FullMulProduct`, `FullMulTwos`,
`FullMulInverse`, `FullMulRemainder`, and `FullMulNumerator`. It proves the high product word,
lowest power-of-two factor, remainder subtraction, combined numerator, and six Newton
inverse refinements. `FullMulDivRoutines` covers generic entry 16544, and `FullMulDivWad`
covers the specialized 1e18 denominator at 16398, including all revert cases.
`FullMulDivSource` connects source function 66. `MathMulDivDownSource` and
`MathMulDivDownRoutines` cover the round-zero wrapper, source function 60 and runtime 17811.

`DecimalScale` and `DecimalScaleRoutines` prove the exact exponentiation cutoff at 77 and
the compiler routine at 14402. `ConvertSharesSource` and `ConvertSharesRoutines` prove
source function 24 and runtime entry 14489, including every checked addition and division
failure. These helpers currently cover round zero; round one remains for later callers.

`AccruedFeeSource`, `AccruedFeeRoutines`, and `AccruedFeeSimulation` complete fee charging
after the guard at 12353. `AccruedAssetsSimulation.accruedAssetsSimulation` is the complete
allocated helper from 12247 to an arbitrary valid return PC. Its success witness includes
the actual final account map, storage preservation, memory cursor and bounds, source
ExecFuncBody returning `[tuple [shares, total, lost], cursor]`, and runtime stack
`[lost, total, shares] ++ R`. It requires stack bound R.length + 35.

`AllocatedConvertSource` and `AllocatedConvertSimulation` compose that helper with
totalSupply and checked share conversion. The latter enters 2215 with
`[assets, 2234, ret] ++ R` and returns the converted word to ret, with stack bound
R.length + 38. `MaxMintEntry` and `MaxMintBodySource` provide the public boundary.
Public maxMint now reuses maxDeposit's complete simulation and scalar return encoder.

All new modules passed focused builds. Small line-wrapping edits after the public build
touch FullMulDivWad, FullMulDivSource, AccruedFeeSimulation, and AllocatedConvertSimulation;
these were included in the successful `/tmp/metamorpho-total-assets-cursor-dependencies-build.log`
rebuild, which also rechecked maxMint after the totalAssets cursor extension.
No generated block summaries were edited.

## Completed public totalAssets

The totalAssets extension has now been made and reported. `TotalAssetsAllocationSyntax`
replaces transition 0: it keeps the three entry guards, calls the allocated accrued-assets
helper with initial cursor 128, and extracts total assets from the returned nested tuple.
The helper list is still ten entries. `Spec.contract` now changes transitions 0, 19, and 59;
`Common.totalAssetsSelectorOf` unfolds the new transition. Original signatures/docstrings
are preserved. The dependency rebuild above passed.

`TotalAssetsSource` and `TotalAssetsRoutines` both pass LSP checks and focused builds.
`metaMorphoV1_1TotalAssetsBody` passed its focused build:
`/tmp/metamorpho-total-assets-build.log`. Its normal path
is 11049 -> 11055 -> 11066 -> accrued-assets entry 12247 (return PC 11075, tail `[32]`),
then the 11075 scalar encoder. There are now 42 original placeholders.
A final line-wrap in TotalAssetsSource happened after that build; include it in the next rebuild.

After totalAssets, convertToShares (60) and previewDeposit (73) share entry 1029, which
jumps to 11760; guards are at 11760 and 11766, then 11778 enters accrued-assets at 12247
with stack `[3533, 11793, 1578, 32] ++ R`. Return 3533 reads totalSupply and enters checked
add 12077, returning to 11793. That block loads calldata word 4 and enters already-proved
conversion 14489. These two public roots still need the same authorized cursor extension.
Their source can call allocatedConvertToShares with `[assets, 0, 128]` and extract result 0.

## Share views completed and asset views in progress

`convertToShares` and `previewDeposit` now have complete public proofs;
`/tmp/metamorpho-public-share-views-build.log` passed. There are 40 original placeholders.
The share-view cursor extension sets transitions 60 and 73 to `allocatedShareViewBody`,
which calls `allocatedConvertToSharesFunction` with `[assets, 0, 128]` and returns
its first component. `ShareViewEntry`, `ShareViewConversionSimulation`, and
`ShareViewSource` contain the shared entry, fee/conversion trace and source wrappers.
The simulation starts at 12247 with `[3533, 11793, ret] ++ R`, uses the already
proved accrued-assets helper, then 3533 -> checked add -> 11793 -> 14489.
It accepts arbitrary real accounts/external outcomes through `SourceState`.

Next: asset conversions. The same authorized cursor repair has now been extended
to internal function 41 `_convertToAssets` and public transitions 2/24
(`convertToAssets`, `previewRedeem`), reported immediately to the user.
`AssetViewsAllocationSyntax` appends an eleventh helper, `allocatedConvertToAssetsFunction`,
and changes those two bodies to call it with `[shares, 0, 128]`. Function27
`_convertToAssetsWithTotals` is the arithmetic helper. Shared runtime entry7734
jumps11122, guards11122/11128, then11140 ->12247 with `[3533,11155,1578,32]`.
3533 adds storage2 and fee shares;11155 loads calldata4 and jumps15343.
Latest extension awaits dependency rebuild and proofs.

## Asset views completed

`convertToAssets` and `previewRedeem` now have complete public proofs; 38 original
placeholders remain. `/tmp/metamorpho-public-asset-views-build.log` passed 3776jobs,
including shared-prefix regressions MaxMint/ConvertToShares/PreviewDeposit.
New modules: ConvertAssetsSource (function27, rounding0), ConvertAssetsRoutines
(entry15343 -> checked total+1 ->15355 -> decimal14402 ->12515 -> checkedAdd ->15337
-> MathMulDiv17811 ->11757), AllocatedAssetsSource, AssetViewEntry,
AssetViewConversionSimulation, AssetViewSource. All LSP clean and built.
`allocatedAccrualTotalsPrefixSource` in AllocatedConvertSource now factors the common
fee-accrual/cursor/totalSupply prefix for both conversion families.
The source cursor extension for asset views passed the full focused dependency build
`/tmp/metamorpho-asset-views-cursor-dependencies-build.log` (3770jobs).
Next: Math_mulDiv rounding1 for previewMint/previewWithdraw. Their public cursor
roots have not yet been extended. Their existing allocated helpers already accept
rounding parameters, but all present source/runtime conversion proofs use rounding0.

## Upward rounding and preview wrappers

`MathMulDivUp`, `MathMulDivUpSource`, `MathMulDivUpRoutines` are complete and built.
`mathMulDivUpFits := fullMulDivFits ∧ (nonzero natural remainder -> checked q+1 fits)`.
`mathMulDivUpWord` branches on remainder=0; naturalMulModSource uses unbounded
source multiplication and nonzero modulus. Runtime17811 -> fullMulDiv ->17827
->19213/19222 ->17837 ->17870 ->17881 ->17846, then17854 for exact result or
17856 checked increment ->17868; overflow9453. Stack boundR+17.
Source theorem `mathMulDivUpPrefix` differs from runtime `mathMulDivUpReachRemainder`.

ConvertShares/AssetsSource frames, OffsetValues, ArgsSource/Revert now accept optional
rounding UInt256 default0. UpSource modules reuse their argument proofs with mode1.
ConvertSharesUpRoutines starts14419 (upward checkedadd continuation14465/14478);
ConvertAssetsUpRoutines starts15275 (numerator+1,15287scale,15337reorder). All LSP clean
and built. `allocatedConvertFrame`/`allocatedAssetsFrame` have optional rounding;
PrefixSource/AccrualReverts infer an implicit rounding from the caller frame.
Allocated*Locals accepts optional mode default0; totals/argument lemmas generalized.
New AllocatedConvertUpSource/AllocatedAssetsUpSource prove only the upward tail.

Authorized cursor repair extended/reported to public previewMint53 and previewWithdraw4
via UpwardViewsAllocationSyntax; no new internal functions. Roots call existing
allocated helper with `[shares or assets, 1, 128]`, project result0. Full focused
dependency build `/tmp/metamorpho-upward-views-cursor-dependencies-build.log` passed
3786jobs, including all previous six public proofs. Width fixes and helper rebuild
`/tmp/metamorpho-upward-view-helpers-build.log` passed3736jobs afterwards.
PreviewMintEntry starts3500 ->3506 ->3518 ->12247 `[3533,3544,1578,32]`;
PreviewWithdrawEntry starts10805 ->10811 ->10823 ->12247 `[3533,10838,1578,32]`.
Shared shape of simulation preserved: R+37, source allocated frame mode1, actual
external accounts and cursor; 3544->15275 and10838->14419. Simulations and public source
wrappers LSP-clean. Public PreviewMint/PreviewWithdraw proofs written and validation
in progress at this handoff update.

## Preview build complete; withdrawal limits in progress

Both public preview proofs passed `/tmp/metamorpho-public-upward-views-build.log`
(3766 jobs). There are 36 original placeholders. `TokenBalanceCall` proves the exact
single-address balanceOf ABI request, scalar decoder, and STATICCALL at19570 with
actual source/external states. It was LSP clean before the withdrawal cursor extension.

The authorized cursor repair now also covers internal functions83 `_withdrawable`,
59 `_simulateWithdrawMorpho`, and23 `_maxWithdraw`, plus public roots63/66
maxWithdraw/maxRedeem. `WithdrawViewsAllocationSyntax` appends these three helpers
after the previous eleven, and reserves32 after balanceOf. The change was immediately
reported. Its dependency rebuild is pending. The successful runtime path19571 ->19578
->19604 ->19618 ->11329 ->19631 ->19640 ->19584 reserves32 then returns the minimum
of supplyAssets, checked(totalSupplyAssets-totalBorrowAssets), and token balance.

## Withdrawal helper and loop completed

The cursor extension passed `/tmp/metamorpho-withdraw-views-cursor-dependencies-build.log`
(3801 jobs), including all eight conversion/preview publics plus MaxMint and TotalAssets.
There are still36 original public/constructor placeholders; no new placeholders were added.
The helper list now has14 appended functions. Publics63/66 are transformed but still unproved.

New completed, LSP-clean helpers:
- `Minimum`: branchlessMinimum, minimumWord_toNat/comm, using Nat xor cancellation.
- `MinimumSource`: source/internal-call proof for originalfunction86 UtilsLib_min.
- `TokenBalanceReturn`: failure19571->2921, short/success32-byte allocation through
  19604/19618/11329/19631, then19640 reads the scalar. Generic tailR, boundsR+7/R+10/R+3.
- `TokenBalanceMemory`: returned word, cursor, protected memory; size includes max96
  because the free-pointer write can extend small memory. No assumptions added to the model.
- `TokenBalanceSource`: generic source call, decode/allocation failure, and prefix;
  requires the actual immutable MORPHO address and actual typedCallViaEVM result.
- `WithdrawableRoutines`: checkedsubtract19481->19496, call setup->19570,
  tokenBalanceReturnSize from existing callViaEVM bound, minimum return19584.
- `WithdrawableSource` and `WithdrawableSimulation`: complete allocated function83,
  runtime19481, R+13, actual external state, cursor and MemoryPrefix. All failure branches.
  `/tmp/metamorpho-withdrawable-simulation-build.log` passed.
- `WithdrawLoopSyntax`: explicit reader/arithmetic/iteration syntax for allocated function59.
  Reuses accruedAssetsCondition/Post. Originalfunction59 body kernel equality proved.
- `WithdrawLoopReaders`: parameters then supplyShares then balances, runtime16116 to16053,
  R+27 with generic tail, protects parameters through both later calls and returns loanToken load.
  `/tmp/metamorpho-withdraw-loop-readers-build.log` passed.
- `WithdrawLoopArithmeticSource/Simulation`: 3 tuple extracts, assetsDown conversion,
  allocated withdrawable call, runtime16053 ->18378 ->16063 ->19481 ->16069, R+14.
  Source continuation starts at arithmetic.drop7. Focused build passed.
- `WithdrawLoopState`: locals invariant (i/assets/cursor/no withdrawQueue local), generic
  insert/reader/converted/post/remaining preservation; zeroFloorSub then assignment and break.
- `WithdrawLoopRoutines`: queue15998->11491->16012->16116;16069 subtract/test;
  exit15984->12234. The exit does not yet execute the final checked subtraction.
- `WithdrawLoopIteration`: complete iteration, R+32, outcome break or ok, actual storage
  preservation, cursor lower/upper/size. Updated cursor result build passed.
- `WithdrawLoop`: remaining-length induction, early break, static storage preservation;
  ends12234 `[original, remaining, 12410, total, supply] ++ R`.
  `/tmp/metamorpho-withdraw-loop-build.log` passed.
- `SimulateWithdrawFunction`: full allocated function59 at15935, source init i0/for/return,
  ends12234 as above. LSP clean; focused build passed
  `/tmp/metamorpho-simulate-withdraw-function-build.log`.
  Three line-width fixes after this build affect WithdrawLoopArithmeticSimulation,
  WithdrawLoopState, and SimulateWithdrawFunction; include them in the next checkpoint build.

Important runtime naming correction: loop15976 stack is
`[MORPHO, i, original, remaining, total, supply, len] ++ R`.
The original amount is x2 and current remainder is x3. The early-break stack at16091
swaps the first two entries;15984 ignores those heads. No source-model mismatch.

Next: originalfunction23 `_maxWithdraw`, allocated helper. Source indices after cursor expansion:
0..3 initialize assets/newTotalSupply/newTotalAssets/feeShares;
4..6 allocated accrued call;7 assign feeShares;8 assign newTotalAssets;9 totalSupply_body;
10 checked assign newTotalSupply;11 balanceOf_body(owner);12 asset conversion mode0;
13 assign assets;14..16 allocated simulate-withdraw call;17 checked assets-minus-remainder;
18 return nested triple plus cursor. Need kernel syntax lemmas for these indices.
No internal balanceOf_body proof exists yet; originalfunction58, source can use
MappingStorage.evalStorage_balanceOf with canonical owner. Runtime15882 ->12247
returns15894 `[lost,total,feeShares,owner,15935] ++ R`, then checkedAdd to15909.
15909 hashes owner (slot0), reads balance and enters15343 conversion, then15935 loop.
Final checked subtraction12234 returns12410, which reorders `[assets,total,supply,ret] ++ R`
to `[total,supply,assets] ++ R` at ret. RootmaxWithdraw return1970 extracts the scalar;
rootmaxRedeem return1572 enters share conversion14489.

## Public withdrawal limits completed

`MaxWithdraw` and `MaxRedeem` are now proved, reducing the original placeholders to34.
Both are LSP-clean. Their joint focused build passed in
`/tmp/metamorpho-public-withdraw-views-build.log`.
The separate MaxWithdraw build passed3773jobs. All helper builds below passed.

New modules: BalanceInternalSource (originalfunction58 balanceOf_body), MaxWithdrawBalance
(slot0 owner hash and memory preservation), MaxWithdrawSource (zero locals and accrued call),
MaxWithdrawConversionSource/State/ConversionSimulation (checked supply addition, balance,
assets conversion), MaxWithdrawTailSource (simulation call and checked final subtraction),
MaxWithdrawFunction (whole allocatedfunction23), WithdrawViewEntry (shared Bool-selected
maxWithdraw/maxRedeem guards and address decode), MaxWithdrawBodySource,
MaxRedeemBodySource, MaxRedeemReturn. No spec/model changes in this context.

`maxWithdrawFunctionSimulation` starts15882 `[ownerWord,ret]++R`, boundR+38, and returns
actual source/external state, storage preservation, cursor≥96 and memory≥96,
source tuple[assets,supply,total]+cursor, and runtime ret `[total,supply,assets]++R.
It includes every accrual, checked-add, conversion, liquidity-loop, and subtraction failure.
`maxWithdrawConversionSimulation` starts15894, boundR+20, and ends15935; memory becomes
twoWordHashMem ownerWord0mem, whose size and cursor are preserved for96≤mem.size.

Generalized session-created `withdrawLoopSimulation` and `simulateWithdrawFunctionSimulation`
to require only96≤mem.size (plus cursor≥96/free), removing cursor<2^64 and cursor≤mem.size
inputs and outputs. This is necessary for empty queues with initial cursor128/memory96.
Actual iterations still provide stronger bounds from successful allocations. No model change.
The prior AccruedAssetsSimulation API is unchanged (a temporary strengthening was undone).

`WithdrawViewEntry` Boolean false selects1940/ret1970/stack[1970,32]; true selects1534/
ret1572/stack[1572,1578,32]. Shared11163->1567->15882, boundR+8. Canonical address conversion
uses `keyValueToWord_address` before `keyValueToWord_address_of_canonical`; they are not
definitionally the same as UInt256.ofNat(address.toNat), and attempting exact caused slow whnf.
maxWithdraw1970 encodes the third stack word. MaxRedeem1572 reorders then14489 share conversion,
1578 scalar encode. Source three tuple extracts need `dsimp only[maxRedeemPublicTail,List.append]`
and separate `apply consNormal` / `exact h` to avoid expensive elaboration at the third let.

Other completed builds: max-withdraw-balance, max-withdraw-source (3740jobs),
max-withdraw-conversion-source, max-withdraw-tail-source, max-withdraw-state,
max-withdraw-conversion-simulation, max-withdraw-function, withdraw-public-helpers,
max-redeem-source, max-redeem-return, all logs `/tmp/metamorpho-<name>-build.log`.
Line-width check and git diff --check passed; one101-column MaxWithdrawBodySource line was
wrapped before the current joint public build. Earlier three loop width fixes are built.

## Public approval completed

`Approve` is proved, reducing original placeholders to 33. LSP clean and focused build passed
(`/tmp/metamorpho-public-approve-build.log`). No model changes or assumptions added.
New modules: ApprovalSource (original functions 72 and 36), ApprovalCalls, ApproveBodySource,
ApprovalStatic, ApprovalRoutines, ApproveEntry. All helper builds passed. One formatting-only
line wrap in ApprovalSource followed the public build; include it in the next dependency build.

ApprovalSource covers the bool event overload, both zero-address guards, nested allowance
storage writes, and static failure. ApprovalCalls proves both call wrappers and `_msgSender`.
Runtime 16692 checks owner; 16709 checks spender; 16725 writes nested mapping slot 1, emits,
and returns. Static proof stops at SSTORE 16782. Public entry 10846 checks nonpayability/length,
11163 decodes the address, 10874 loads value/caller; 4161 encodes true.
`approvalStoreReturn` has arbitrary memory/stack tail; no allocation invariants needed.
`approvalScratchMem` is two nested twoWordHashMem writes; `approvalReturnMem` adds event data.
Canonical address masks require an explicitly typed UInt256 mask equality, not inferred
`EVM.word` notation. Hash normalization similarly uses typed keccakWord equalities.

Next active work: Transfer, first the shared `_update` source/runtime helper (function 73).
Source `_update`: from-zero checked supply add; otherwise balance read, sufficient-balance
guard, wrapping debit. Then to-zero wrapping supply debit, otherwise wrapping balance credit
read from the already updated storage. Preserve this order without collision assumptions.

## Public transfer completed

`Transfer` is proved, leaving 32 original placeholders. Focused builds passed both before and
after formatting (`/tmp/metamorpho-public-transfer-build.log`,
`/tmp/metamorpho-transfer-format-build.log`, 3539 jobs). No model changes or assumptions.
New helper modules: BalanceMutation, BalanceUpdateSource, TransferInternalSource, TransferGuards,
TransferBodySource, TransferRoutines, TransferStatic, TransferEntry. All are built/LSP clean.
BalanceUpdateSource proves the nonzero-address path of function 73 `_update`; mint and burn
branches are still to be proved when needed. TransferInternalSource proves function 42
`_transfer`, including zero-address guards, insufficient balance, and static violation.
BalanceMutation keeps the recipient balance read after the sender write; no slot-noncollision
or sender/recipient inequality assumptions. Wrapping casts use signedAddWrap/signedSubWrap.

Runtime transfer: 12728 sender guard -> 12745 recipient guard -> 12761 balance check -> 12780
stores/emits/returns. Zero-address reverts 12898/12879; insufficient balance reverts 12854.
First SSTORE 12829 is separately proved for static execution. Store bound is R+10.
Public entry 4123 -> 4129 -> 4141 -> 11163 -> 4151 -> 12728, return 4161 reused from ApproveEntry.

Current work: TransferFrom. AllowanceInternalSource (function 74), SpendAllowanceSource
(function 43), and SpendAllowanceCalls are written, LSP clean; first two focused builds passed,
Calls build running in `/tmp/metamorpho-spend-allowance-calls-build.log`.
Source allowance helpers distinguish unlimited (`UInt256.lnot 0`) from finite. Finite path
checks sufficiency before owner/spender address guards and then writes without an event.
SpendAllowanceCalls exposes Allowed, State, call success/revert/static and environment equality.
Runtime allowance work still pending: 12530 hashes/reads, unlimited -> 12579 return, finite ->
12585 balance guard -> 12593 owner guard -> 12599 spender guard -> 12614 SSTORE -> 12579 return.
12614 stores allowed-value and pushes four zeros ahead of the return PC; bound R+7.
Public TransferFrom: 10441/10447 nonpay/96-byte check; 10459 -> 11163 -> 10469 -> 11185 ->10477.
10477 calls 12530 with [from,caller,value,10492,from,to,value,4161]; 10492 ->12728 Transfer routine.

## Delegated transfer completed

`TransferFrom` is proved, leaving 31 original placeholders. Focused build passed
(`/tmp/metamorpho-public-transfer-from-build.log`, 3630 jobs), and LSP is clean. No model changes
or added assumptions. The final one-line wrap in TransferFromBodySource followed the build;
include it in the next dependency build.

All allowance helpers are now built: AllowanceInternalSource, SpendAllowanceSource, Calls,
Lookup, Guards, Store, Static, Function. Lookup computes the nested slot and branches on
`allowed + 1`; allowanceAddOne_ne_zero proves the finite case. Static stops at SSTORE 12646.
`spendAllowanceFunctionReturn/Revert/Static` use a source State's executionEnv/accountMap,
bound R+11, and return the exact `spendAllowanceState` accounts. Return requires permission
only for a finite allowance. Unlimited allowances work under static calls.

New TransferFunction proves return/revert/static of the full internal transfer over an arbitrary
source state, bound R+10. TransferFromEntry proves both address decoders and 100-byte calldata
guard; use generic `solcDecodeLenCheckOk/Short/Huge` for width96 (no `_4_96` library aliases).
TransferFromBodySource threads source allowance state into the balance reads. Public theorem
also preserves the dispatcher's selector stack tail; it is not an empty stack.

The only pending work is the remaining original placeholders. Next active group:
RevokePendingTimelock (entry2053, selector61) and RevokePendingGuardian (entry10526, selector7).
Both use `_checkGuardianRole`, delete their pending packed record, and emit caller.
AccessControl only contains owner-role helpers; find/prove guardian-role helpers before these.


## Pending-change revocations completed

All four public revocations now have complete proofs. LSP diagnostics are clean and focused
builds passed. Original placeholder count is now 27. No spec/model changes in this group.

- `GuardianRoleSource.lean`: source function 10 `_checkGuardianRole`, owner or guardian.
- `PackedDeletion.lean`: generic byte-field clear word, adjacent clears, overwrite, missing-account
  handling, and full-slot deletion of pendingTimelock (slot17) and pendingGuardian (slot15,
  including its existing uint32 padding). No added storage assumptions.
- `RevocationSource.lean`: Bool-selected (true=guardian) source bodies, success/revert/static.
- `RevocationRole.lean`: owner comparison then optional guardian check. Timelock PCs
  2070→2090/2152→2095; guardian PCs10543→10563/10610→10568; sharedrevert2137.
- `RevocationEntry.lean`: nonpay/length guards, store-return, first SSTORE static at2098/10571.
- `RevokePendingTimelock.lean`, `RevokePendingGuardian.lean`: complete public proofs.
  `/tmp/metamorpho-public-revocation-build.log` passed3527jobs.
  Public signatures were subsequently wrapped only for width; format rebuild queued separately.
- `CuratorGuardianSource.lean`: function9 `_checkCuratorOrGuardianRole` source proof.
  Source OR parses right-associatively: guardian OR (curator OR owner).
- `MarketRevocationMutation.lean`: delete pendingCap[id] slotmapping16 entirely;
  delete config[id].removableAt slotmapping13 preserving low192bits.
- `MarketRevocationSource.lean`: Bool-selected (true=cap) source bodies with bytes32 id.
- `MarketRevocationRole.lean`: runtime authorization shared between cap and market-removal:
  market PCs7757guardian→7891curator→7779ownerchoice→7870owner→7785require→7790store;
  cap PCs10678guardian→10784curator→10700ownerchoice→10763owner→10706require→10711store.
  Both use sharedrevert7855. Guardian comparison masks on right, unlike other comparisons.
- `MarketRevocationStore.lean`: exact slot hashing, storage/event/return, and static at
  7815 (market-removal) /10724 (cap). Prefixes copied only from provided summaries.
- `MarketRevocationEntry.lean`: entries7739/10660, length checks7745/10666, bytes32 decoding.
  First build missed Decode import, then fixed and LSP clean; final public build covers fix.
- `RevokePendingCap.lean`, `RevokePendingMarketRemoval.lean`: complete public proofs.
  `/tmp/metamorpho-public-market-revocation-build.log` passed3542jobs.
- All intermediate helper focus builds passed. `git diff --check` passed.
- `TransferFrom` formatting rebuild from previous handoff passed3630jobs.

Next active group: AcceptTimelock (entry4895, selector41), AcceptGuardian(entry4172,selector48).
No edits to these yet. Internal `_setTimelock` stores timelock, msgSender/event, then deletes
pendingTimelock. `_setGuardian` stores packed guardian, msgSender/event, deletes pendingGuardian.
Each public acceptance reads pending validAt, requires nonzero and timestamp≥validAt, then calls
its setter on pending value. Start by proving these internal setters. Source atSpecSyntax187,
212, publicacceptances1322/1385. Read summaries before choosing any runtime PCs.

## Timelock and guardian acceptance completed

`AcceptTimelock` and `AcceptGuardian` are proved; 25 original placeholders remain.
Joint focused build passed3619jobs: `/tmp/metamorpho-public-accept-pending-build.log`.
LSP clean, new files fit100columns, no model/spec changes or assumptions.
Previous revocation-format build also confirmed passed3527jobs.

- SetTimelockSource (function2) and SetGuardianSource (function5) prove internal setter
  success/static/calls. Timelock stores14, event, clears17; guardian updates packed12,
  event, clears15. SetPendingRoutines proves bytecode14755/15404 return/static. Static
  SSTORE PCs14759/15435. Return boundsR+5/R+7; timelock changes memory atfreepointer,
  guardian preservesmemory.
- AcceptPendingSyntax defines packed read, time/value, sourcebody/frame, sourceguardprefix.
  Booltrue=guardian. Time uses UInt256.ofNat(timestamp), matching EVM wrapping.
- AcceptPendingSource proves success/static and missing/premature reverts.
- AcceptPendingEntry proves nonpay/lengthguard at4895/4901 (timelock) or4172/4178 (guardian).
- AcceptPendingGuards: read4912/4189, nonzerotime→4925/4211, timepassed→4931/4217;
  missing→4249, premature→4234. Source-state based bridges, boundR+4.
- AcceptPendingRoutines: valuejump4931/4217→setter14755/15404, sharedreturn1867STOP.
  pendingGuardianValueWord converts maskedvalue to canonicaladdress word.
  StoreReturn/Static boundR+7, exactacceptPendingState accounts.
- All intermediate focus builds passed (source,entry,guards,routines).

Current active function: SubmitGuardian, entry4368 selector45. Original placeholder untouched.
Internal setterdone. Need prove pendingGuardian value+validAt writes, owner+guards,
zero-currentguardian immediate setter versus deferredpendingrecord path, static and reverts.
Source SpecSyntax1357; runtime blocks024/025. No edits for this function yet.

## Guardian submission completed

`SubmitGuardian` is proved; 24 original placeholders remain. Focused public build passed3630jobs
(`/tmp/metamorpho-public-submit-guardian-build.log`), LSP clean. No model/spec changes.
All helper builds passed except the first ScheduledGuardianStatic standalone build, which had
an .olean file-not-found race with LSP/dependency work; subsequent SubmitGuardianRoutines and
public builds succeeded and cover it. Do not rerun differential suite or audit.

- PendingTimeStorage: uint64 at offset20 (pendingGuardian.validAt), arithmetic word, exact
  bytecode mask/shift equivalence, source storageLocStore. UInt256.shiftLeft must unfold with
  explicit if_neg, then Fin.shiftLeft_val; direct `change` can time out on the Fin comparison.
  Nat.land/lor wrapper names and Nat.and/or operator names sometimes need explicit `change`.
- PendingGuardianMutation: low64 cast, source assignments of address and time, states, snapshot
  of timelock and checked timestamp+timelock bound. Scheduled state preserves padding/high32bits.
- SubmitGuardianSyntax: fixed decoded locals, adminFrame, guards, scheduled frame and AST.
  The actual elaborated `as uint256` time sum is `.inRange`, not `.cast`: overflow is modeled
  correctly in existing SpecSyntax, no repair needed. Checked addition occurs after value write.
- ScheduledGuardianSource: deferred update success, overflow revert, staticfirstwrite.
- SubmitGuardianSource: complete source success/static/guardrevert/overflowrevert.
- SubmitGuardianEntry:4368nonpay→4374length32→4386decoder11163→4393owner12917→4401.
- SubmitGuardianGuards:4401unchangedguard→4426pendingtimeguard→4445branch;
  unchangedrevert1143, pendingrevert4572. BoundR+6; output[currentword,newword,newword]R.
  solcAddrMask_clean_left needs explicit `(w := UInt256.ofNat value.val)` to avoid EVM.word
  vsUInt256.ofNat rw failures.
- ScheduledGuardianRoutines:4458 writes15value→12077checkedadd→4491timewrite/event/STOP.
  BoundR+7. `scheduledGuardianReachAdd` retains old timelock snapshot. Same update state threaded
  through overflow path. ScheduledGuardianStatic firstSSTORE4485,prefixfromprovidedsummary.
- SubmitGuardianRoutines:4445→4449→15404 immediate setter (return1867) or4458scheduled.
  StoreReturn/Static/RevertOverflow share exact source state; boundR+7.
- `git diff --check` passed, new files fit100columns after two wraps before public build.

Current active: SubmitTimelock, entry6869 selector33. Original placeholder untouched.
New TimelockBoundsSource proves function1 `_checkTimelockBounds`, source calls and reverts;
LSP clean, not yet built. Upper1209600,lower86400.
Runtime (blocks035/036):6869nonpay→6875length32→6887loadword+owner12917return6897.
6897new≠old14guard→6908pending17high64zero→6918upperbound→6928lowerbound→6938branch.
Upperrevert7088,lower7073,unchanged1143,pending4572.
6938new>old→6946→14755setterreturn1867; else6955 writespending17low192value (mask184),
then12077checkedtimestamp+oldtimelock return7029. 6955 stack afterwrite:
[timestamp,oldtimelock,7029,new,32,eventTopic]R; eventTopic definedinprovidedsummary.
7029takes[time,new,32,eventTopic]R, updateshigh64of17 preservinglow192, emits andstops,boundR+9.
Need prove pendingTimelock uint192 value + uint64 time storage first; valid new value bound means
uint184 cast is identity. Read summaries for staticfirstwritePC and eventtopic; do not guess.

## Timelock submission completed

`SubmitTimelock` is proved; 23 original placeholders remain. Focused public build passed
(`/tmp/metamorpho-public-submit-timelock-build.log`), LSP clean, `git diff --check` passed.
No model/spec changes. Do not rerun the differential suite or audit.

- TimelockBoundsSource: function1 `_checkTimelockBounds`, upper1209600/lower86400,
  source call success and revert. Build passed3494jobs.
- PendingTimelockStorage: low192 value and high64 timestamp packed updates, exact bytecode
  mask/shift identities, storageLocStore proofs. For pendingTimeHighShift, unfold shiftLeft,
  Fin.shiftLeft_val, Nat.shiftLeft_eq, then change only the modulo divisor with conv_lhs;
  globally rewriting UInt256.size breaks the dependent Fin type of data.val.
- PendingTimelockMutation: source assignments, state after each store, checked time snapshot.
- SubmitTimelockSyntax: decoded/admin/post-bounds frames; different/noPending/increase guards;
  prefix includes `_checkTimelockBounds`. Source value cast184 is identity under bounds.
  For Int comparison simplification use Int.ofNat_eq_natCast and Nat.cast_lt, not Int.ofNat_lt.
- ScheduledTimelockSource and SubmitTimelockSource: all success, static, guard, overflow paths.
- SubmitTimelockEntry:6869→6875length32→6887loadword/owner12917return6897; badlength/nonpay.
- SubmitTimelockGuards:6897different→6908pendingtimezero→6918upper→6928lower→6938branch;
  reverts1143/4572/7088/7073. BoundR+4.
- ScheduledTimelockRoutines:6955 low192 store masked184 (bounded value makes masks equal),
  checked addition12077→7029 high64 store/event/STOP. BoundR+9. Exact source state match.
- ScheduledTimelockStatic: first SSTORE6982, prefix copied from generated summary throughr20.
- SubmitTimelockRoutines:6938→6946→14755setter/1867STOP or6955deferred, all outcomes.
  StoreReturn/RevertOverflow take timelockInBounds; source hgood supplies it.
- All helper builds passed, public build3635jobs passed; new files fit100 characters.

Current active: SetIsAllocator selector52 entry3552. Original placeholder untouched.
SpecSyntax1420: nonpayable, calldata bound, `_checkOwner`,
require(isAllocator[newAllocator] != newIsAllocator), assign bool mapping, emit.
Need inspect decoder/runtime summaries and reuse MappingStorage/IsAllocator/Decode helpers.

## Allocator setter completed

`SetIsAllocator` is proved; 22 original placeholders remain. Focused public build3531jobs passed
(`/tmp/metamorpho-public-set-is-allocator-build.log`), all helper builds passed, LSP clean,
new files fit100characters, git diff --check passed. No model/spec changes.

- AllocatorMutation: slot11 address mapping, low-byte boolean read/normalized word,
  state preserving upper31bytes, generic source read/assignment. boolWordNeSource compares
  arbitrary stored bool bytes by normalized words. Avoid broad simp with `w.val=0 ↔ w=0`:
  it loops. Use simp only to rewrite wordToElem, then split zero cases and decide.
- SetAllocatorSource: decoded/admin frames, unchanged guard, source success/static/revert.
  Parameters are semantic address and raw UInt256 flag, canonical flag0∨1 for guard.
- SetAllocatorEntry:3552nonpay→3558length64→3570addressdecoder11163ret3577,
  3577boolcanonicalcheck→3592owner12917ret3599. Bad flag and length/nonpay reverts.
  Reuse boolWordClean_iff and u256_sub_eq_zero_iff_eq.
- SetAllocatorGuards:3599 computes addressmapping11 in scratchmem, reads/normalizes bool,
  unchanged→1143, different→3637[flag,addr]R, mem twoWordHashMem addr11solcFreePtrMem.
  Rewriting raw generated storage/hash expression by folded helper failed; rewrite the
  source-side condition backwards with allocatorBoolWord_bytecode, then `exact` matches.
- SetAllocatorRoutines:3637write/event/STOP, maskflag255=normalizedflag for canonical values,
  exact setAllocatorState match. twoWordHashMem_solcMappingSlot_any needs no memory bound.
- SetAllocatorStatic: prefix3637throughr22, firstSSTORE3696. BoundR+8.

Current active: SetFeeRecipient selector71 entry1158. Original placeholder untouched.
SpecSyntax1582: owner, new!=old feeRecipient, !(new=0 && fee!=0), `_accrueInterest`,
assignfeeRecipient,event. Prove dependency `_accrueInterest` first (SpecSyntax194).
No work yet beyond reading this path; inspect existing accrued-fee simulation and token mint proofs.

## Fee-recipient setter completed

`SetFeeRecipient` is proved; 21 original placeholders remain. Public build 3760 jobs passed
(`/tmp/metamorpho-public-set-fee-recipient-build.log`); public LSP clean, new files fit 100
characters, git diff --check passed. Original public theorem API/docstring preserved.

Authorized/reported cursor correction: new `AccrueInterestAllocationSyntax` appends
`allocatedAccrueInterestFunction` (index105), wrapping allocated fee/assets calculation and
returning its cursor, and replaces transition71's accrual call with cursor128. Spec imports it;
Common.setFeeRecipientSelectorOf unfolds allocatedSetFeeRecipientTransition. Existing original
function3 remains unchanged. Other mutating transitions need the same correction when active.

Completed dependencies:
- UpdateLastAssetsSource: function47 store22 + event; generic source call/return/static.
- UpdateLastAssetsRoutines:16830 store/event/return, first static SSTORE16870. R+6.
- MintSupplySource: mint branch of function73 `_update`, checked slot2 supply increment,
  then recipient balance read/store (after supply write), then Transfer. All source outcomes.
- MintInternalSource: function48 `_mint`, nonzero recipient + `_update`, all call outcomes.
- MintRoutines:17718 recipientguard→17735 load supply→12077 checkedadd→17783 ordered stores
  and Transfer/return. R+10. No storage-slot noncollision assumption. Static SSTORE17786.
- AccrueInterestSource/TailSource: allocated calculation, tuple unpacking, lastTotalAssets
  store22 then lostAssets store23/events, optional mint, event + cursor return.
- AccrueInterestRoutines:14262→12247 ret14340, then16830 ret14353, loss store and branch to
  14369 directevent or14382→17718 mint ret14397→14369. Named work stacks/memory.
- AccrueInterestSimulation: all runtime/source outcomes, R+40, SourceState preserved through
  writes and actual external-call state. Success includes I.perm=true, frame/state/cursor,
  mem/out/RD; does NOT assert memory cursor preservation after event writes.
- FeeRecipientMutation: high-address (offset12,size20) packed storage, low96 bits preserved.
- SetFeeRecipientSource/Entry/Guards/Routines: complete public composition. Guard1317 consumes
  an additional stack item (selector); pass w::tag::R, not arbitrary empty R.

Proof engineering: `rw [← hs.env] at rd` can also rewrite the initial state and calldata words
in a public trace; use `nth_rw 1 [← hs.env] at rd` when only the current execution env should
change. This fixed an elaborator timeout; public theorem needs default heartbeats.
`addressOfNat_eq_iff_solcAddrMask_eq` puts the mask on the LEFT. Use solcAddrMask_clean_left.
For bytecode packed stores, instantiate source helper's slot as UInt256.ofNat18 and unfold
codeOwnerStorageWord before rw: matching against literal⟨18⟩ inside storage getD can fail.

Current active: SetFee selector28 entry7417, original placeholder untouched. Shares the now
completed interest-accrual dependency. No work yet beyond reading its public placeholder;
inspect transition28 and runtime path, then extend the authorized cursor correction to it.

### Fee setter completed

`SetFee.lean` now has its original public theorem proved with default heartbeats and
maxRecDepth 2000. Public build passed (3763 jobs):
`/tmp/metamorpho-public-set-fee-build.log`. **20 original placeholders remain.**

The authorized cursor correction extends `AccrueInterestAllocationSyntax.lean` with
`allocatedSetFeeTransition`, replacing transition 28's body index 7 call with
`__solcAccrueInterest(128)`. `Spec.lean` replaces transition 28 and
`Common.setFeeSelectorOf` unfolds the correction. Dependency build passed 3738 jobs,
and all setter leaves plus Dispatch passed 3762 jobs. No new assumptions or sorries.

New helpers: `FeeMutation.lean` (low96 store, preserving upper160), `SetFeeEntry.lean`
(nonpay/calldata/owner), `SetFeeGuards.lean` (same fee, cap, recipient checks),
`SetFeeSource.lean` (all source paths), `SetFeeRoutines.lean` (7511 store+event+STOP).
Entry 7417→7423→7435→12917(return7445), equality→7465, cap→7480,
recipient checks→7489→7495→14262(return7511, value, mask96, selector).
Source `setFeeAllowed` is different fee ∧ value≤5e17 ∧ ¬(nonzero fee ∧ zero recipient).
After accruing, the fee store reads the **post-accrual** slot18, as bytecode does.

Proof detail: `setFeeState.executionEnv` is propositionally preserved by
`storageStore_executionEnv`, not definitionally. Explicitly rewrite it after
`msgSenderCall` before equating the final frame. Otherwise `change`/unification unfolds
contract and times out. Type the final fee-read fact with the exact final frame for simp.
Public source environment rewrite uses `nth_rw 1 [← hs'.env]` to avoid rewriting I
inside the initial state and calldata stack words. Width≤100 for new files; diff check clean.

Current active next function: `Name.lean` selector1 entry10884; original placeholder
still untouched. Source simply returns storage `_vaultName`. `Symbol.lean` analogous
selector44 entry4587. No string helper work yet. Do not rerun differential tests or audit.

### Name getter completed; shared string machinery

`Name.lean` now has its original public theorem proved with default heartbeats and
maxRecDepth 2000. Focused public build passed (3551 jobs):
`/tmp/metamorpho-public-name-build.log`. **19 original placeholders remain.**

Reported and applied the authorized cursor correction to both metadata getters:
`StringViewAllocationSyntax.lean` adds a local string read followed by
`__solcAllocate(128, bytes.size + 32)` and return. `Spec.lean` replaces transitions 1
and 44, and `Common.lean` selector proofs unfold those replacements. The bytecode copies
the storage string, then the allocator enforces the 64-bit cursor limit; the original
source getter omitted that panic branch. No extra assumptions or shared semantics edits.

String helpers (all checked/built): `StringHeader.lean` and `StringHeaderRoutines.lean`
decode valid headers and reject malformed ones at 11801. `StringStorageSource.lean`
proves the source payload and its size. `StringViewSource.lean` proves all source
outcomes. `StringAllocation.lean` relates the rounded copy size and source allocation.
`StringCopyLoop.lean` proves arbitrary-length copying with storage-slot wraparound;
`StringCopyMemory.lean` defines short/long memory layouts and the short header mask.
`StringMemoryRead.lean` proves payload reads and length-word preservation.
`StringReturnMemory.lean` proves generic ABI header + MCOPY + trailing-zero encoding.
`StringReturnRoutines.lean` composes 2379→11086→4335 into the shared encoder.
`StringAllocatedReturn.lean` composes allocation and return for any storage base slot.
`NameEntry.lean` and `NameCopyRoutines.lean` cover the name-specific entry/copy path.

Name path: 10884(nonpay)→10890(length guard)→10901→11801(return10916), then short
4753 or long 10932→10955→10999(loop11023)→11007; both reach4643→11329 allocator
return2379→11086→4335. Data at160, length128, copied end160+32*ceil(len/32).
Both empty strings and enormous strings that fail allocation are covered.

Active next: Symbol selector44 entry4587. Runtime path has corresponding
4587→4593→4604→11801(return4619), short4753 or long4635→4659→4703(loop4727)→4711.
It then uses the same allocator and encoder. Current plan is to generalize the loop
and copy routing across the two bytecode instances, preserving one induction proof.

### Symbol getter completed and common string proof factored

Both public getters now build together (3555 jobs), with default heartbeats:
`/tmp/metamorpho-public-string-getters-build.log`. **18 original placeholders remain.**
The original public statements/docstrings remain intact. No new model changes since
the already reported shared string allocation correction.

`NameEntry.lean` became `StringEntry.lean`, parametrized by `symbol : Bool`.
`NameCopyRoutines.lean` became `StringCopyRoutines.lean`; its public helper is
`stringCopyToAllocation v symbol`. Added `StringCopyBlocks.lean` for the two loop
instances and `StringCopySetup.lean` for short/long routing. `StringCopyLoop.lean`
now has one `stringCopyLoop v symbol` induction used by both getters.
All new string files are ≤100 columns and `git diff --check` passed.

A concurrent intermediate dependency build reported a missing StringCopyMemory.olean
during refactoring. The subsequent consolidated public build rebuilt all affected
dependencies and passed; do not treat the older failed log as a current proof error.

### DOMAIN_SEPARATOR completed

`DOMAIN_SEPARATOR.lean` now proves its original public theorem with default heartbeats
and maxRecDepth 2000. Both cache checks and the rebuilt five-word Keccak preimage are
covered, along with nonpayable/huge-calldata reverts. No specification correction was
needed: the public rebuild allocates 192 bytes from cursor128, which always fits.
**17 original placeholders remain.**

New helpers: `DomainHashSource.lean` (type hash, five words, functions45/build-domain),
`DomainSource.lean` (function38/cache selection and public source body),
`DomainMemory.lean` (preimage length/free/data), `DomainHashRoutines.lean`
(13028→11329→13174→return), `DomainCacheRoutines.lean`
(12937/address check→13180/chain check→12987→cached12993 or rebuild13028),
and `DomainEntry.lean` (9689→9695→9706→12937).
The internal runtime theorem accepts arbitrary free≥96 with free+192<2^64 and
preserves the exact conditional memory; it can be reused by Permit.
Public encoding reuses `maxDepositEncodeReturn` at1578.

Lean detail: `uInt256OfByteArray` is not definitionally `ofNat(fromByteArrayBigEndian)`;
rewrite with `uInt256OfByteArray_eq`. Normalize literal UInt256.toNat by `change`
after pointer arithmetic, so simp does not unfold the variable pointer too early.

Active next function: Eip712Domain selector40 entry4948. Its source calls
functions `_EIP712Name`, `_EIP712Version`, and `ShortStrings_toString` (the latter
checks low8 length≤31, returns the prefix). Fallback storage is used only when
_name/_version equals 255. Investigate full source and bytecode before implementation.

Focused public DOMAIN_SEPARATOR build passed (3549 jobs):
`/tmp/metamorpho-public-domain-separator-build.log`.

### Eip712Domain in progress (17 original placeholders still remain)

Reported and applied the authorized allocation correction: new
`Eip712AllocationSyntax.lean` preserves the original prefix/default declarations,
then allocates after each string read (64 bytes for an immutable short string;
32+string byte length for a storage fallback), and allocates32 for empty extensions.
`Spec.lean` replaces transition40; `Common.eip712DomainSelectorOf` unfolds it.
Dependencies passed 3536 jobs (`/tmp/metamorpho-eip712-allocation-deps-build.log`).
A consolidated shared build passed 3580 jobs, including ShortStringRoutines, Name,
Symbol, DOMAIN_SEPARATOR (`/tmp/metamorpho-eip712-shared-check-build.log`).
Public Eip712Domain theorem is still the original placeholder.

New checked helpers:
* `ShortStringSource.lean`: low8 length, validity≤31, prefix bytes; generic
  `evalExpr_wordAnd`; source function89 returns/reverts.
* `Eip712StringSource.lean`: functions39/_EIP712Name and40/_EIP712Version,
  immutable sentinel255 versus storage slots5/6, validity/bytes, source bodies and
  caller wrappers, payloadsize<2^255.
* `Eip712StringAllocationSource.lean`: selected allocation size and source returns/reverts.
* `ShortStringMemory.lean`: exact runtime memory (allocate64, initialize32, calldata
  exhausted copy, replace length, store word), length/free/payload/MemoryPrefix.
* `ShortStringRoutines.lean`: 18425/18521 short decoder→11329 allocator→18452→ret;
  malformed length→18471 revert. Built in the consolidated check above.
* `FallbackStringMemory.lean`: arbitrary-cursor storage-copy memory, padded coverage,
  length/data/free-pointer preservation, MemoryPrefix. Built.
* `FallbackStringSetup.lean`: 11857→11801 decoder; 11872 short→11957→ret;
  long11872→11888→11900→11914. Generic storage base Keccak lemma. Built.
* `FallbackStringCopy.lean`: complete11857 valid copy→ret/end cursor; invalid-header
  revert. Uses generalized shared loop induction. LSP clean and focused build started
  `/tmp/metamorpho-fallback-string-copy-build.log` (session57218).
* `StringBuffer.lean`: length/padded allocation/data predicate; MemoryPrefix.readWords
  and StringBuffer.preserve. LSP clean; build started
  `/tmp/metamorpho-string-buffer-build.log` (session3493).

Refactors: `StringStorageSource.stringStorageLayout` now public; added generic
`storageStringReadAt`/`storageStringReadAtReverts`, and existing metadata read theorems
wrap them. `StringCopyBlocks.lean` adds StorageStringLoopKind (metadata Bool/fallback),
pc/exit/stack selectors and generic step/exit summaries. `StringCopyLoop.lean` now
has ONE `storageStringCopyLoop` induction; original `stringCopyLoop v symbol` API
wraps the metadata case. Existing public name/symbol rebuilt successfully.

Important memory detail: MemoryPrefix preserves 32-byte windows starting≥96, so it
already tolerates allocator writes at64 and hash scratch at0. StringBuffer.preserve
extends it to arbitrary string payload lengths using padded allocation coverage.
`MemoryArrayData.lean` already has writeOutsideSource_size/read for calldata zero-fill;
reuse those. ByteArray.write beyond source does not extend destination itself, but the
following word writes do.

Remaining EIP work: compose fallback copy with18505→11329→11757→ret and domain
sentinel branches18416/18512. Assemble source transition (defaults + two calls and
allocations). Prove 7-component ABI encoding and runtime5068→11086→5104→11086→5118
→5158(fallthrough emptyarray)→5166 RETURN. Reuse StringReturnRoutines/Memory for shared
11086 encoder, probably generalize it to arbitrary source/destination and internal ret.
The public entry4948→4954→4965 calls18416 with[_name,5008,5104];5008 calls18512 with
[_version,5049] and saved name pointer. 5049 allocates32 for empty extensions, return5068.

### Eip712Domain completed; next Skim

The original public Eip712Domain theorem is now fully proved. Focused public build passed
3649 jobs (`/tmp/metamorpho-public-eip712-domain-build.log`). **16 placeholders remain.**
No further specification correction beyond the preceding allocation correction was needed.
Generic fallback and short string routines now return a `StringBuffer`, free pointer and
`MemoryPrefix`; `StringBuffer.preserve` reuses `HeapWordWindow.memoryPrefix_read_words`.
`StringEncoderMemory` and `StringEncoderRoutines` extract the shared payload encoder;
StringReturnMemory/Routines now wrap those, preserving their old APIs. Name and Symbol
rebuilt successfully. EIP helpers cover source defaults/calls/allocation/reverts, seven-value
ABI encoding, two string encoders, empty extensions, and final RETURN. New files are named
Eip712{SourcePrefix,Source,ABI,ReturnMemory,EncodeMemory,FinishRoutines,EncodeRoutines,
ExtensionsRoutines,Entry}, Eip712String{Memory,Routines}, FallbackString{Allocation,Routines}.
All helpers passed focused builds. Two final edits only wrapped long lines in
Eip712SourcePrefix and Eip712EncodeRoutines.

Next selected function: Skim (selector57, entry2710). Inspection only so far. It needs a
balanceOf STATICCALL at2795 and SafeERC20_safeTransfer at15818. Existing TokenBalanceCall
simulation is fixed to19570 and can be generalized. Source internal functions are in
SpecSyntax; no SafeERC20 proof helpers yet. Inspect transfer/raw-call allocation behavior
before deciding whether a source cursor correction is needed. Do not switch to another
public function because this dependency is difficult. No current confirmed new mismatch.

### Skim transfer dependency completed

Confirmed, reported, and applied the authorized allocation-accounting correction for Skim:
the raw token-call return buffer can panic before optional-return validation. New
SafeTransferAllocationSyntax defines cursor-aware Address/optional-return/safeTransfer helpers;
Spec appends them at function indices106–108 and replaces transition57. Existing function
indices are preserved. Skim passes cursor160 after balanceOf's fixed32-byte reservation.
SafeTransfer allocates100 rounded to128, then accounts for nonempty raw return data.

All dependency helpers are proved and focused builds passed: ZeroCallSimulation,
AddressVerifySource/Routines, CallReturnMemory/Allocation/Routines/Source,
AddressCallSource, OptionalReturnSource/Routines, OptionalCallSource/Simulation/Routines,
TwoWordCallMemory, SafeTransferABI/Source/Memory/Routines. The complete
`safeTransferSimulation` matches runtime15818→11329→15877→18967→CALL18992→15478
return allocation→18567 address validation→19007 optional Boolean→14753→caller.
It covers both parent permission modes, depth failure, request/return allocation failure,
call failure, empty data with code check, and canonical/noncanonical Boolean decoding.
Latest build passed3605jobs `/tmp/metamorpho-safe-transfer-routines-build.log`.

Skim public theorem remains the original placeholder (16 total remain). Next work is its
balance call, recipient guard, event/static halt, then public composition. Entry2710;
balance call setup2755→2795; after CALL2796 stack[ok,recipient,ptr,token]R. Success
2796→2803→2867→2882→11329 allocator→2895→2904[ptr,recipient,token]R
→2809[2821,recipient,balance,token]R→15818[token,recipient,balance,2821,balance,token]R.
Failure2796→2921. Short return via2867→2913→2882→allocator→2895→917.
At initialptr128 the successful allocation always fits, cursor160. Reuse TokenBalanceCall
ABI/request memory and TokenBalanceMemory postcall facts. Source balance statement is
externalCall(.var token) balanceOf0[.env this] amount false (inspect actual DSL lowering).
Use `tokenBalanceReturnSize` for size<2^255; `typedStaticcallSimulation` accepts arbitraryPC.
Recipient is low160bits slot19; Storage.evalStorage_skimRecipient exists. At2821 event succeeds
using generated block2821 when I.perm=true; for false step toLOG3pc2865 then RD.log3Static.
`msgSenderCall` is in ApprovalCalls and source `ExecStmt.emitStatic` handles the final halt.

Useful new transfer API: SafeTransferRoutines.safeTransferSimulation requires SourceState,
free pointer<2^64, pointer≥128, mem.size≥128, free64 and zero96 words. It returns either
source revert+RDrev, or evm'/cursor/mem'/out and SourceState, source function success,
and RD at caller ret. SafeTransferSource uses an abstract optional callee ExecFuncBody,
avoiding duplicate source proofs. Runtime routines use generic stack tails.

### Skim completed; next SetName

Skim's original public theorem is now fully proved, including nonpayable/short/huge/noncanonical
calldata, zero recipient, failed and short balance returns, all SafeERC20 paths, and final
LOG3 static halt. Focused public build passed3661jobs (`/tmp/metamorpho-public-skim-build.log`).
**15 original placeholders remain.** Added SkimSource, SkimBalanceRoutines, SkimBalanceMemory,
SkimEntry, SkimEvent, and SkimSimulation; all LSP-clean and built. Initial memory has size96;
SkimBalanceMemory proves that the balance request's first write at128 fills the zero slot,
then return copying and free-pointer update preserve it. SkimSimulation composes calls from
pc2755 through success/revert/static outcomes; Skim.lean handles dispatcher and ABI decoding.
No new correction beyond the previously recorded transfer allocator correction.

Next selected public function: SetName(string), entry2240, selector58. Original source is
nonpayable/calldata bound→_checkOwner→_vaultName=newName→emitSetName. SetSymbol shares the
string-storage writer. No setter helpers exist yet; current string helpers are reads/encoders.
Reasoning.Storage has bytes/string backend write lemmas (roughly lines1300–1505), and
Reasoning.StorageLoops may provide loop machinery. No newly confirmed mismatch.

### SetName decoder and storage loops

SetName remains selected; its public theorem is still the original placeholder (15 remain).
Confirmed and reported a missing initial string-allocation panic in the source model:
ABI decoding admits lengths near the 64-bit maximum, while the runtime allocator at11329
can fail before the owner check. Applied the previously authorized allocator correction to
both metadata setters in StringSetAllocationSyntax, with Spec overrides at58 and55. Their
source bodies now account for allocation from128 of32+length. No function indices changed.

Completed and built: CalldataBytesRoutines, StringCalldata, StringDecoderEntry,
CalldataBytesMemory, StringDecoder, StringStorageWrite, StringSetSource, StringStorageHash,
StringClearLoop, StringBufferWords, and StringDataLoop. The shared decoder11698 covers
malformed heads/offsets/lengths, allocation panic, payload bounds, and successful StringBuffer
construction. StringSetSource covers allocation/owner/header reverts, assignment static halt,
and successful assignment plus event. StringStorageWrite exposes exact source storage order.
StringClearLoop proves both setters' old-data clearing loops. StringDataLoop proves full-word
stores directly against solidityDataWordsForwardFrom; latest build passed3604jobs in
/tmp/metamorpho-string-data-loop-build.log. StringCopySetup now reuses the extracted slot hash
facts instead of its identical inline native_decide proofs. No new assumptions/placeholders.

Next: mask/partial-word lemmas, clearing preparation and full storage-writer composition,
static paths, event encoder/LOG path, then SetName public composition. StringBuffer only
specifies payload bytes, so partial-word proofs should mask the unused bytes rather than
assume zero padding. Reuse Reasoning.Memory.tailMask_toByteArray and storage arithmetic.

### SetName storage path and public proof

Completed StringMask (kernel-checked concrete masks, generic masked StringBuffer tail),
StringStorePrefix/Static/ShortStore, StringLongTail/LongStore, StringClearStart/Storage,
StringWriteState/Routines, StringSetStorage/Entry/Simulation. All have no placeholders.
The complete writer covers old-data clearing, short packed headers, full data-word loops,
masked partial tails, long headers, first-SSTORE static halts, invalid old-header panic,
event encoder11086 and LOG/STOP2399. Account maps match the source backend's exact write order;
no slot-noncollision hypothesis is used. StringSetSimulation connects the owner check and
all source outcomes after successful initial string allocation. Its focused build passed3636jobs.

SetName.lean now has its complete public proof and is LSP-clean. The focused public build
is running in /tmp/metamorpho-public-set-name-build.log; verify it before declaring SetName
finished. It composes the dispatcher, nonpayable branch, shared decoder, allocation failure,
and StringSetSimulation. All its helpers also support SetSymbol (Bool true), so that public
proof can follow after SetName's build passes. Remaining original placeholders become14
once SetName is validated; SetSymbol is still untouched at this checkpoint.

Proof performance: avoid `contradiction` on a context containing RD hypotheses; it unfolds
large runtime expressions before reaching a simple `some _ = none`. Use `cases hnone`
directly. Supply `(immWords := wordsOf (immStore v))` explicitly to generated packed summaries.
For a goal containing `D_J (deployedRuntime v)`, use PatchedValidJumps, not the Runtime variant.

### Both metadata setters completed

SetName's public build passed3657jobs (/tmp/metamorpho-public-set-name-build.log). SetSymbol's
public proof now reuses the shared Bool-parameterized helpers; its build also passed3657jobs
(/tmp/metamorpho-public-set-symbol-build.log). Both original statements/docstrings are preserved.
**13 original placeholders remain.** No new source correction beyond the recorded allocation
accounting change, and no new axiom declarations. StringMask's finite facts use decide +kernel.

Next selected function: SubmitMarketRemoval, selector39, entry5196. Begin with its source at
SpecSyntax1292 and existing MarketParams/cap-storage helpers. Do not switch away because an
internal dependency is difficult. No new mismatch has been identified.

### SubmitMarketRemoval completed

The original public theorem is fully proved and its focused build passed3683jobs
(`/tmp/metamorpho-public-market-removal-build.log`). **12 original placeholders remain.**
No source correction or new axiom was needed. CuratorRoleSource proves the modular curator
role call; MarketParamsCalldata/Fields/Decoder prove the complete five-word struct decoder,
its allocated memory, and its ID hash. MarketRemovalStorage/Syntax/GuardsSource/Source prove
the source outcomes; Role/Guards/Static/Store/Entry connect the runtime paths. The public
proof covers malformed calldata, nonpayable calls, role/guard rejection, checked timestamp
overflow, first-SSTORE static halt, packed timestamp update, event, and return.

Performance lesson: split Bool-dependent storage slots before applying storage-read lemmas.
Leaving `if pending then 16 else 13` in a mapping slot can make elaboration normalize crypto
for minutes. Likewise simplify the Bool-dependent returned word before using word equality.
Use explicit `(evm := evm)` where a local helper result has no expected type.

Next selected function: SetSupplyQueue, selector10, entry9964. Its calldata array remains in
calldata; it checks allocator role, length≤30, each market's cap, then writes slot20's array
and emits an event. Reuse storage-loop machinery and prior clear-loop proofs where possible.
No newly confirmed mismatch. Do not rerun the differential suite or initial audit.

### SetSupplyQueue completed

The original public theorem is fully proved. Its focused build passed3676jobs
(`/tmp/metamorpho-public-supply-queue-build.log`). **11 original placeholders remain.**
No source change, extra assumption, or axiom declaration was introduced.

AllocatorRoleSource proves the modular allocator-role call. DynamicCalldata,
WordArrayCalldata, CalldataArrayView, SupplyQueueEntry, and SupplyQueueRole cover complete
array decoding and authorization. SupplyQueueSyntax/CapCheck/Loop/Length/Source prove the
source and runtime validation loop and all reverts. SupplyQueueStorageSource,
WordArrayStorage/Algebra, and SupplyQueueStorageMatch establish exact storage equivalence.
SupplyQueueClearLoop/StorePrepare/WriteLoop/Finish/Static/Store complete all runtime paths.

The enormous old-length issue is resolved by finite gas. CountedStorageStep strengthens
RD.sstore to preserve its exact step count and positive gas cost. SupplyQueueClearLoop
proves a lower bound of40gas per iteration; lengths at least2^251-30 cannot finish.
For smaller old lengths, the concrete keccak(20) value establishes separation from slot20.
Zeroing order commutes even with repeated slots, and any cleared prefix is overwritten by
the new array. No mapping/array noncollision assumption was needed. The concrete data-base
hash uses native_decide; its numerical bounds use decide.

Generic config-cap reads now accept any bytes32-valued expression through
evalStorageRef_bytes32FieldExpr and SourceMemory.configCapRead. Existing public helper
statements remain available. All new proof files are below2000lines and width100.

Performance lesson: use `dsimp only [supplyQueueSourceState]` before rewriting its account
map. A `change` with metavariables for the source account-map arguments can normalize
crypto and recursive storage folds for minutes. Explicit residual stack arguments also
help when passing a generated RD summary through a `simpa`.

Next selected function: AcceptCap. Prove its `_setCap` internal dependency first and reuse
the existing expectedSupplyAssets and storage-array machinery. SubmitCap also uses this
dependency. Do not switch away because the dependency is difficult. No newly confirmed
mismatch; do not rerun the differential suite or initial audit.

### AcceptCap internal dependency completed

The complete allocated `_setCap` simulation now builds without placeholders:
`/tmp/metamorpho-set-cap-simulation-build.log`. It covers zero caps, existing markets,
new markets, both external readers, checked total-assets addition, queue events, final
packed storage writes, all revert branches, and all static-mode halts.

The previously authorized benchmark-local allocation repair was extended through
SetCapAllocationSyntax: allocatedSetCapFunction threads the allocation cursor through
expectedSupplyAssets; allocatedAcceptCapTransition supplies288 after its160-byte decoder
allocation. Spec registers this helper and uses the allocated transition for selector30.
SubmitCap still needs this repair when its proof is selected. No bytecode, Solidity,
generated blocks, shared library, or original public theorem signature was changed.

No storage noncollision premise was introduced. Queue reads occur after the actual
preceding writes. SetCapEventRuntime handles arbitrary resulting uint256 queue lengths
by finite induction, including memory-address wrap. SetCapSimulation needs account
presence internally; AcceptCapStorage.pendingCapPresent derives it from the public
nonzero pending timestamp, so the public theorem gains no assumption.

New proof modules include SupplyAssetsContinuation (reused by SupplyAssetsSimulation),
WordArrayRead, SetCapEnableSource/Runtime/Simulation, SetCapEventSource/Runtime,
SetCapReadersSimulation, SetCapFrames, SetCapFinishSimulation, SetCapNewMarketSimulation,
SetCapTailSimulation, and SetCapSimulation. Generic storage and allocation helpers also
include StorageAlias, LowBytesStorage, BoolByteStorage, and WordArrayPush.

AcceptCapSource and AcceptCapEntry build successfully3658jobs; AcceptCapGuards builds
successfully3644jobs. MarketParamsCalldataMemory proves decoded heap invariants;
MappingScratchMemory proves mapping-hash writes preserve heap bytes and the free cursor.
The public AcceptCap proof has now been written and is undergoing LSP validation.
Do not count its original placeholder as finished until the focused public build passes.
The other10 original placeholders remain untouched. AcceptCap remains selected.

Proof performance: give RD hypotheses explicit memory names before applying a generated
summary. Otherwise simp may miss a proved hash equality because the actual memory is
expanded into nested ByteArray.write expressions. UInt256 word equality uses u256_inj.

### AcceptCap completed

The original public theorem now builds successfully3782jobs:
`/tmp/metamorpho-public-accept-cap-build.log`. It covers complete ABI decoding, nonpayable
rejection, pending timestamp checks, and every allocated `_setCap` outcome. The original
statement and docstrings are preserved. **10 original placeholders remain.**

Next selected function: SubmitCap, selector18, entry8864. Reuse `_setCap` and the curator
role proof; establish its market last-update reader and both immediate/scheduled branches.
Stay with SubmitCap until complete; no differential suite or initial audit rerun.

### SubmitCap last-update dependency completed

SubmitCap remains selected. Its allocated last-update source/runtime simulation now
builds successfully3634jobs (`/tmp/metamorpho-last-update-simulation-build.log`). It covers
slot-hash addition overflow, singleton-array allocation, STATICCALL, call failure,
malformed returns, return-buffer and array allocation failures, empty-array rejection,
and uint128 truncation. LastUpdateSimulation preserves account storage, the decoded
MarketParams heap prefix, and the final free-memory cursor.

The authorized benchmark-local allocation repair was extended to SubmitCap in
SubmitCapAllocationSyntax/Spec/Common. The reader reserves160 bytes before its call,
threads the decoder cursor back to the caller, and supplies it to allocatedSetCapFunction.
This was announced before editing. No original theorem signature or generated file changed.

ExtSloadsSetup now exposes extSloadsEncodeReturn; ExtSloadsSimulation now exposes
extSloadsAfterBufferSimulation and extSloadsReturnValues_cons. Existing public helper
signatures are preserved and SupplySharesAllocationRoutines rebuilt successfully.

Next: public SubmitCap decoder, curator/asset guards, post-reader guards, immediate
_setCap branch, scheduled pending-cap writes and event, then public composition.
The original SubmitCap placeholder is still untouched;10 original placeholders remain.

### SubmitCap completed

The public SubmitCap theorem builds successfully3811jobs:
`/tmp/metamorpho-public-submit-cap-build.log`. The original statement and docstring
are preserved. **9 original placeholders remain.**

SubmitCapCalldata/Entry cover the tuple-plus-cap decoder and nonpayable rejection.
SubmitCapRole/Asset prove the authorization and asset guards. SubmitCapSyntax and
PrefixSource connect these to the allocated last-update reader. Guards/GuardsSource,
Uint184Cast, ImmediateSource/Simulation, ScheduleSource/Runtime/Static, and TailSimulation
cover both branches and every revert/static outcome. PendingCapStorage captures the
timelock before the first packed write, matching bytecode without a slot noncollision
assumption. The lower branch reuses SetCapSimulation and derives account presence from
the positive old cap. The tail and last-update simulation build passed3774jobs:
`/tmp/metamorpho-submit-cap-tail-build.log`.

Shared factoring: ScalarTupleABI.scalarTupleValueDecode now supplies the existing
MarketParamsCalldata and scalarTupleReturnDecode proofs. MarketRemovalSyntax exposes
marketParamsTupleStructSource. Original helper APIs remain intact.

Next selected function: UpdateWithdrawQueue, selector20, entry7984. Remain with it until
complete. The remaining functions are UpdateWithdrawQueue, Permit, Multicall, Deposit,
Mint, Withdraw, Redeem, Reallocate, Constructor. Do not rerun the differential suite or
initial audit. Main-thread-only proof work continues.

### UpdateWithdrawQueue allocation and first loop

UpdateWithdrawQueue remains selected;9 original placeholders remain. The authorized
benchmark-local cursor correction now covers its two word-array reservations and the
allocated supply-share calls in its removal loop (UpdateWithdrawQueueAllocationSyntax,
Spec/Common). Generated artifacts and original public signatures are unchanged.

Entry, role, UintArrayCalldata, explicit Syntax, both runtime/source allocation paths,
and the full first-loop simulation pass LSP. Allocation source build passed3566jobs:
`/tmp/metamorpho-update-withdraw-queue-allocation-source-build.log`. First-loop focused
build passed3666jobs in `/tmp/metamorpho-update-withdraw-queue-build-loop.log`.

New memory machinery: WordArrayInitMemory exposes sparse-gap zero reads and reuses
Attester.wordArrayHeaderMemory facts; WordArrayPrefix tracks initialized array prefixes.
UpdateWithdrawQueueMemory proves initialization, scratch preservation, and per-step writes.
UpdateWithdrawQueueReady captures source locals through both loops. BuildSource proves
bounds/duplicate reverts and success; BuildRuntime proves the matching8690→8163 iteration;
BuildLoop composes these to8171, preserving the initialized arrays and free pointer.

Shared factoring: ArrayStorage.evalStorage_withdrawQueue_local now supports any local
index name; old evalStorage_withdrawQueue and accruedAssetsQueueRead APIs delegate to it.
CalldataArrayIndexRuntime contains the former SupplyQueueCapCheck indexing helpers;
SupplyQueueCapCheck imports it. WordArrayIndexRuntime covers the memory-array index routine
at12057, address normalization, and withdrawal-queue out-of-bounds reversion.

Next: removal loop8175→8183, then final storage replacement/event and public composition.
Maintain fresh storage-array bounds at each read: config deletion may alias queue storage;
do not assume slot noncollision or a30-element bound. SupplySharesAllocationRoutines and
its memory-prefix lemmas are already proved and must be reused. No suite/audit rerun.

### UpdateWithdrawQueue removal loop

The complete removal-loop simulation now passes LSP: RemoveSelect, RemoveRuntime,
RemoveSource, Reader, RemovalTailSource/Runtime, Delete, Omitted, and RemoveLoop.
UpdateWithdrawQueueHeap preserves the two completed arrays as external reader calls
advance the allocation cursor. MarketConfigDeletion proves that clearing all three
packed fields matches a zero-word write. LocalArrayBoolSource factors the local bool
array condition shared by both loops. BuildSource now uses this shared helper.

RemoveLoop covers fresh array-bound rejection, cap/pending-cap rejection, all allocated
supply-share reader outcomes, timelock rejection, static SSTORE, and successful deletion.
It threads SourceState, local variables, arrays, and the cursor to PC8183. The retained
path leaves the state unchanged. A focused removal/first-loop rebuild is next, followed
by final queue storage replacement, event, and public composition. No new assumptions.

### UpdateWithdrawQueue completed

The public theorem passes LSP and its focused build passed3734jobs:
`/tmp/metamorpho-public-update-withdraw-queue-build.log`. The original public statement
and docstring are preserved. **8 original placeholders remain.**

The removal/first-loop build passed3685jobs:
`/tmp/metamorpho-update-withdraw-queue-remove-loop.log`. The final storage tail and existing
SetSupplyQueue theorem passed3712jobs: `/tmp/metamorpho-update-withdraw-queue-store.log`.

StorePrepare, ClearLoop, WriteLoop, Finish, StoreStatic, TailSource, Storage, and Store
prove replacement, gas exhaustion for enormous cleanup lengths, static failure, and return.
Loops composes both loops with the tail; Simulation handles both allocation reservations
and all allocation failures; UpdateWithdrawQueue joins decoder, role, and body simulation.

WordArrayStorage now contains generic replacement-backend and list-indexing lemmas.
WordArrayStorageAlgebra exposes source/runtime replacement accounts and their equality
under proved header/data separation; clearWordArray_shift removes an unnecessary count
bound from the older helper. SupplyQueueStorageSource/Match use these shared lemmas with
unchanged APIs. Withdrawal-queue separation uses concrete keccak evaluation and the
cleanup gas bound, not an added assumption. Formatting checks cover all new modules.

Next selected function: Permit, selector65, entry1586. Remain with it until complete.
Remaining: Permit, Multicall, Deposit, Mint, Withdraw, Redeem, Reallocate, Constructor.
No differential-suite or initial-audit rerun; no subagents; no commits/staging.

### Permit completed

The public Permit theorem passes LSP and its focused build passed 3669 jobs:
`/tmp/metamorpho-public-permit-build.log`. The original public statement and docstring
are unchanged. **7 original placeholders remain:** Multicall, Deposit, Mint, Withdraw,
Redeem, Reallocate, Constructor. No added assumptions or Permit specification changes.

Signature recovery is complete in ECDSATrySource/Return, ECDSAErrorSource,
ECDSARecoverSource, EcrecoverOutput/ABI/Memory/Call, ECDSATryRuntime,
ECDSAErrorRuntime, ECDSARecoverRuntime, and ECDSASimulation. The precompile's output
shape is derived from its semantics, including empty output, canonical addresses,
call/depth failure, high-s rejection, zero signer, and success. The recovery simulation
build passed 3600 jobs (`/tmp/metamorpho-permit-recovery-simulation-build.log`).
Earlier source/helper builds: `/tmp/metamorpho-permit-hash-helpers-build.log` (3541 jobs),
`/tmp/metamorpho-permit-recovery-source-build.log` (3520 jobs).

NonceSource models the wrapping nonce increment, source calls, and static execution.
PermitHashSource/Memory/Runtime and PermitNonceRuntime/Static prove the actual nonce
store, six-word preimage, allocation, and hashing. Their build passed 3604 jobs:
`/tmp/metamorpho-permit-nonce-hash-build.log`. TypedDataHashSource/Memory/Runtime,
DomainCursorMemory, and TypedDataDomainRuntime cover both domain-cache branches and
the EIP-712 envelope. PermitDigestRuntime composes these with the nonce operation.

PermitData, PermitPrefixSource, PermitTailSource, PermitApprovalRuntime, and
PermitBodySimulation connect source execution to recovery and approval. Body simulation
build passed 3643 jobs (`/tmp/metamorpho-permit-body-simulation-build.log`). PermitABI
and PermitEntry cover short/huge calldata, both noncanonical addresses, noncanonical
uint8, nonpayable calls, and deadline rejection. CalldataValueDecode supplies reusable
selector-relative static-field decoding, including bytes32.

Shared factoring: WordPrefixMemory generalizes WordCallMemory to arbitrary short prefixes;
PackedWordsMemory handles allocated word preimages, with DomainMemory delegating to it.
PackedSource.evalExpr_addressToWord removes repeated address-word encoding work from
DomainHashSource and PermitHashSource. New Permit/recovery files and auxiliary modules
contain no sorry/admit/axiom declarations. All files are below 2000 lines.

Next selected original function: Multicall. Stay with it until complete, working through
its dependencies first. No differential-suite or initial-audit rerun; main thread only;
no commits or staging. Public Permit build is complete; no build remains running.
