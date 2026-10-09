# CometWithExtendedAssetList hand-off

Current status (2026-10-09): the constructor input-size decision is resolved. The user requested
a separate bounded copy of the refinement relation, keeping the deployment encoder unchanged.
Comet now uses `typedConstructorRefinementWithCodeBound` and
`contractRefinementWFWithCodeBound` from `Solm/RefineWithCodeBound.lean`. Both add the premise
`I.code.size < UInt256.size` on deployments. Existing relations, the active config, and decoding
are unchanged. The old encoder-guard proposal/review below is historical and superseded.
The full proof is complete: the constructor and all runtime paths are proved without sorries
or custom axioms. The Comet-only build passes. The top-level theorem's audit reports the three
standard Lean axioms and 25,922 permitted concrete evaluation certificates. See the completion
record at the end of this document; earlier open-goal notes are historical.

## Compiler settings and provenance

Upstream: https://github.com/compound-finance/comet/tree/f766f51583c23acc33b2a7824654ef2029a96804

Main source: `contracts/CometWithExtendedAssetList.sol`; contract: `CometWithExtendedAssetList`.
The 11-file import closure is shared under `Benchmarks/CompoundIII/contracts/` and is copied
byte-for-byte from that commit. No old scaffold or other EquiVM branch was used as input.

Compiler: `0.8.15+commit.e14f2714.Linux.g++` (compiler commit `e14f2714`).
Official linux-amd64 binary SHA-256:
`5189155ce322d57fb75e8518d9b39139627edea4fb25b5f0ebed0391c52e74cc`.

Optimizer enabled, 1 run, via IR, no explicit EVM version (solc resolves its default to London),
default metadata (IPFS).
The pinned `hardhat.config.ts` additionally supplies a custom Yul optimizer sequence. The user
confirmed that this sequence must be included, rather than using solc's default sequence:

```text
dhfoDgvulfnTUtnIf [xa[r]scLM cCTUtTOntnfDIul Lcul Vcul [j] Tpeul xa[rul] xa[r]cL gvif CTUca[r]LsTOtfDnca[r]Iulc] jmul[jul] VcTOcul jmul
```

The exact standard-JSON settings and every source AST are in the build artifact. The scaffold
command uses an absolute `--sources-root`, because this version of the automation resolves
relative paths against `--dir`. It also supplies the optimizer details through `--settings-json`.

Runtime template: 18,599 bytes; creation code: 21,425 bytes. Immutables remain zero in the template;
`ImmutableCode.lean` patches their compiler-declared sites. `sources.sha256` pins the source files.

Artifact SHA-256 values (file bytes unless explicitly marked decoded):

| Artifact | SHA-256 |
| --- | --- |
| `runtime.hex` | `ef6c8af03601e46a1703da55e58d7dd8e56c1d5f556781dd99ca32af13f4851d` |
| `creation.hex` | `34bd91fe8f86045aa658677fa7da59c557554386ba75eca74c7bec180315e4ec` |
| `CometWithExtendedAssetList.abi.json` | `d82a92ea4a59cd0099739dd43a7049d5cbb4f5371b7f3df387a42a818d636d2f` |
| `CometWithExtendedAssetList.storage.json` | `fbd5e44efb886cf0a6dff74d63570ef21cf5f8af25127a9a2055bce664441f81` |
| `CometWithExtendedAssetList.metadata.json` | `e8ba96b6950dbe7d4dc10cad170120c51b25876ba27ab9d0c7ad51ccde10a45a` |
| `CometWithExtendedAssetList.build.json` | `3c79329d72349fc7130ea26aa873a14b16dda09fc5ae55374387e88041e3e719` |
| `CometWithExtendedAssetList.sol.ast.json` | `8e6a6d6cc9f1c66bba3b54ed594eb531f7c06510808e506d274e73da04394c5b` |
| `sources.sha256` | `5a2613aac75a32813fc28c176377d7f6d303e278721606dc2fe25d5148e31d46` |
| decoded bytes of `runtime.hex` | `eec7d24e54618967bd5c76aab25257dc990dc1f1ca31f4181dd0b05d523a844d` |
| decoded bytes of `creation.hex` | `a8ea000c5b2817a55393711e1c82aa3419e1463e3c5d95887db37997f66d3605` |

## Differential testing

Required command (seed defaults to 2026):

```sh
lake exe solm-difftest --only CometWithExtendedAssetList --count 50
```

The target uses ABI-specific callees, small and boundary amounts, and repeated asset addresses
to make successful token operations more likely. Repeated callee entries install identical code;
they only weight the input pool. Random storage, malformed calldata, nonzero call value, static
execution, sequences, and constructor fuzzing remain enabled.

This container needed a native C compiler wrapper for EVMLean's crypto dependency. The run uses
`PATH=/tmp/compound-build-bin:/root/EquiVM-proof-1/.lean4-skills/bin:$PATH` before the command above.
`/tmp/compound-build-bin/cc` invokes Lean 4.29.0's bundled clang with
`--sysroot=/tmp/compound-sysroot`, the sysroot's `usr/include/x86_64-linux-gnu`, and Lean's
`include/clang` include directories. The sysroot contains unpacked Debian `libc6-dev` and
`linux-libc-dev` packages. A normal installation with working `cc` and libc headers does not
need this wrapper. The approved registry cleanup removes the absent CometRewards target from
`Tests/DiffTest/Targets.lean`, allowing the normal test executable to build.

Final run: 2026-10-08, seed 2026, exit status 0. Exact summary and coverage:

```text
CometWithExtendedAssetList: 3625 cases: 3619 agree (2279 successful), 0 disagree, 0 stuck, 0 EVM out of gas, 0 spec out of fuel, 6 inapplicable
successful/cases: constructor 0/25, isLiquidatable(address) 42/51, getReserves() 27/52, isSupplyPaused() 48/53, governor() 44/50, totalSupply() 30/50, baseTrackingSupplySpeed() 47/51, initializeStorage() 14/53, storeFrontPriceFactor() 45/50, transferFrom(address,address,uint256) 2/52, pauseGuardian() 43/51, withdrawFrom(address,address,address,uint256) 4/50, borrowPerSecondInterestRateSlopeHigh() 50/54, userCollateral(address,address) 42/50, borrowPerSecondInterestRateSlopeLow() 51/52, userNonce(address) 41/51, baseBorrowMin() 43/51, decimals() 43/50, targetReserves() 50/52, borrowBalanceOf(address) 33/52, isBorrowCollateralized(address) 37/50, getAssetInfoByAddress(address) 12/51, getPrice(address) 1/53, supplyTo(address,address,uint256) 4/53, transferAsset(address,address,uint256) 1/51, baseScale() 45/51, pause(bool,bool,bool,bool,bool) 24/53, extensionDelegate() 44/51, totalsCollateral(address) 41/50, supplyPerSecondInterestRateSlopeLow() 44/50, isWithdrawPaused() 47/52, balanceOf(address) 29/51, borrowPerSecondInterestRateBase() 48/52, quoteCollateral(address,uint256) 9/52, getUtilization() 47/53, supplyPerSecondInterestRateSlopeHigh() 47/52, totalBorrow() 30/50, isAbsorbPaused() 47/50, supplyFrom(address,address,address,uint256) 0/50, absorb(address,address[]) 5/53, borrowKink() 45/51, baseMinForRewards() 44/53, supplyPerSecondInterestRateBase() 43/51, baseTrackingBorrowSpeed() 46/52, getBorrowRate(uint256) 47/51, getCollateralReserves(address) 20/51, isAllowed(address,address) 43/51, isTransferPaused() 42/50, numAssets() 49/50, supplyKink() 46/52, transfer(address,uint256) 3/51, trackingIndexScale() 45/52, approveThis(address,address,uint256) 12/54, accrueAccount(address) 19/56, transferAssetFrom(address,address,address,uint256) 2/51, withdrawTo(address,address,uint256) 3/50, baseToken() 42/52, liquidatorPoints(address) 42/50, getAssetInfo(uint8) 39/50, hasPermission(address,address) 50/53, isBuyPaused() 48/50, getSupplyRate(uint256) 45/50, userBasic(address) 43/53, assetList() 47/52, withdrawReserves(address,uint256) 4/51, buyCollateral(address,uint256,uint256,address) 1/54, baseTokenPriceFeed() 45/52, supply(address,uint256) 2/52, withdraw(address,uint256) 1/52, stray 100/100
```

The requested operations all have successful random cases: supply 2, withdraw 1, transfer 3,
absorb 5, and buyCollateral 1. The two zero-coverage entries are explained as follows:

- Random constructor configurations did not satisfy the combined callee/configuration guards;
  six could not be ABI-encoded by `selfDeployment` and are the six inapplicable cases. The
  deterministic deployment below supplies a valid configuration and exercises constructor success.
- `supplyFrom` requires operator permission, a supported asset, and a viable balance/index state.
  None of its 50 random cases completed those guards. Separate deterministic replay checks passed
  for both base-token and collateral `supplyFrom`, with caller/from `0x2000`, destination `0x3000`,
  and amount 1 after initialization and supply.

The deterministic sequence also passed initialization, asset-info decoding, base supply/transfer/
withdrawal, collateral supply/transfer/withdrawal, empty-account absorb, and collateral purchase.
A separate nonempty-liquidation check used both indices at `10^15`, account `0x3000` with principal
`-10^6`, one unit of collateral and its assets-in bit set, and total borrow principal `10^6`;
`isLiquidatable`, `balanceOf`, and `absorb([0x3000])` all agreed successfully. These supplemental
checks use `runCase` with the same constructor-derived target and replay oracle.

The target's deterministic constructor fixture has already executed successfully on both sides:
it returns 18,599 bytes and 25 immutable values, and checks the returned code against the patched
template. Constructor fuzz cases remain enabled.

The native executable also emits existing BN_ADD/BN_MUL/SNARKV startup diagnostics before the
target report. The Comet fixture does not call those precompiles; its complete results are above.

## Specification choices following the bytecode

The dispatcher has no global call-value guard. Named external functions retain their individual
nonpayability checks; fallback is payable and returns the delegatecall's raw bytes.

The assembly transfer-return check accepts empty returndata or exactly one nonzero 256-bit word.
It is not a canonical ABI `bool` decoder. Low-level calls preserve the success flag and raw bytes.

The reentrancy flag lives at `keccak256("comet.reentrancy.guard")`, outside the compiler's declared
storage layout. A symbolic unused fixed array after slots 0–7 places `__reentrancyGuard` at the
exact slot without assuming hash noncollision. `DiffTarget.lean` removes only the unreachable
padding declaration from random-state generation; it keeps the already-generated concrete backend.
The modifier cleanup executes after either successful return branch.

The specification keeps the compiler's evaluation order where it matters for storage and calls:
the tuple assignment in `accrueInternal` writes the borrow index before the supply index;
collateral balances are read before their price-feed calls; `getReserves` snapshots the packed
totals before the external balance query; and principal records are copied before aggregate
storage updates. `balanceOf` and `borrowBalanceOf` perform signed conversion and value calculation
only in their selected branch. `withdrawReserves` checks nonnegative reserves before converting.

The runtime and constructor block walk is complete, including all 68 selector arms, internal
routines, and the payable fallback. There is no separate receive function. The report's
`UNSUPPORTED_F4` label is `DELEGATECALL`, modelled directly by Solm. Runtime bytes from pc 18482
are two event-topic constants followed by metadata, separated from executable code by `INVALID`
at pc 18481; their apparent opcodes are data. The constructor's embedded runtime begins at
creation offset 2826. The report's final selector comparison uses `SUB`, so the `withdraw` arm
must also be read directly at runtime pc 768–784. No semantic finding remains open.

## Notes for the proving session

No contract-correctness proofs were authored. The 139 intended generated stubs are: 68 function
bodies, the constructor, `restrictImmutables_of_fit`, 68 selector dispatch facts, and the
unmatched-calldata fallback refinement in `Correct.lean`. There are no specification holes or
new axiom declarations.

Final checks passed: `python3 scripts/scaffold.py check --dir Benchmarks/CompoundIII/Comet`
prints seven `ok` lines, and `lake build Benchmarks.CompoundIII.Comet.Correct` completes
successfully (3,635 jobs). The generated runtime and creation block modules are included in that
build. The shared source closure and artifact hashes were rechecked after the audit.

Two approved corrections to `scripts/proof_skeleton.py` are required to reproduce this skeleton.
Immutable accessors use direct hash-map simplification instead of the timing-out `grind` template.
For fallback/receive contracts the generator omits false no-dispatch/revert claims and emits an
explicit unmatched-calldata refinement stub. Generated files were regenerated with `--force`.

`DiffTarget.lean` defines the constructor arguments and callee addresses: base token `0x6000`,
price feed `0x6001`, collateral token `0x6002`, extension `0x6003`, asset-list factory `0x6004`,
asset list `0x6005`. Governor is `0x2000`, pause guardian `0x3000`. One collateral is configured.
Base token has 6 decimals; the price feed has 8. Reward and interest speeds are zero in the
fixture, while runtime proofs quantify over well-typed immutable valuations.

`fixtureDeployment` runs the actual constructor, replays its external calls, compares the
resulting state, extracts all 25 immutable values, and verifies the returned runtime against
`ImmutableCode.lean`'s patched template. `diffTarget` fails if that fixture does not deploy.

The generated external-call table covers `balanceOf(address)`, `approve(address,uint256)`,
`decimals()`, `assetListFactory()`, `transferFrom(address,address,uint256)`, and
`transfer(address,uint256)`. Its TODO entries for `getAssetInfo(uint8)`, `latestRoundData()`, and
`createAssetList((address,address,uint8,uint64,uint64,uint64,uint128)[])` are implemented directly
in `SpecSyntax.lean`: selector encoding, raw call, success check, and tuple return decoding.
The factory encoder includes the array offset, length, and seven static words per element.
`CometWithExtendedAssetList.spec.json` retains the original translator diagnostics; the completed
model is `SpecSyntax.lean`. The table's three TODO comments describe entries handled by those
explicit adapters, not remaining specification holes.

The loops, packed state updates, external call boundaries, and immutable constructor patching
are expected to dominate the proof effort. The optimized Yul and the full runtime/creation block
report are available alongside the compiler artifacts.

## Proof audit, 2026-10-08: immutable valuation bounds (resolved with approval)

The required differential suite was rerun successfully with the command above. Its current
output is in `difftest.log`: 3625 cases, 3619 agree (2279 successful), zero disagreements or stuck
cases, and six inapplicable constructor cases. This target uses constructor-derived immutables.

The generated proof scaffold quantifies over a larger set of immutable values than that target.
`CometWithExtendedAssetListImmutables` gives `decimals` and `numAssets` unrestricted `EVM.Word`
fields, although their declared types in `SpecSyntax.lean` are `uint8`. The unconditional body
lemmas and `cometWithExtendedAssetListCorrect` therefore include values such as 256. This is a
counterexample to the scaffold's claimed runtime equivalence: the getter bytecode masks the
word with 255 and returns zero, while the source returns 256, which cannot encode as `uint8`.

`ScaffoldAudit.lean` reproduces both getters at 255 (successful agreement) and 256 (disagreement).
It uses the actual deployed runtime from `immStore` of a scaffold valuation, the full original
contract, zero call value, valid four-byte calldata, and 100000 gas. It also proves that 256
cannot satisfy `returnEquiv` for a `uint8` return, and that the EVM mask produces zero. These
small theorems use only standard Lean axioms and do not depend on unfinished proof theorems.
Run `lake env lean Benchmarks/CompoundIII/Comet/ScaffoldAudit.lean` to reproduce the evidence.

The user approved the correction: add the proof fields
`decimals_lt : decimals.toNat < 256` and `numAssets_lt : numAssets.toNat < 256` to the immutable
valuation structure. Derive them from the existing `immutablesFit` hypothesis when proving
`restrictImmutables_of_fit`. This restricts the scaffold to well-typed valuations while
preserving the requested whole-contract refinement statement, specification, and bytecode.
The audit now uses an explicitly untyped store for these regression checks.

Proof work stopped at this finding as required by `Misc/prompt.md` sections 1 and 10. The Lean
skill additionally requires discussion before changing declaration signatures. No existing
proof statement, specification, bytecode, or generated block summary has been changed. The full
goal remained incomplete at that checkpoint, with the original 139 proof placeholders present.

## Proof progress after approval

The approved `decimals_lt` and `numAssets_lt` fields are now in `Immutables.lean`.
`restrictImmutables_of_fit` is proved from `immutablesFit`, including both bounds, using the
generic extraction lemmas in `ImmutableValues.lean`. The regression audit now constructs an
explicitly untyped store for its deliberately invalid 256 cases.

All 68 source selector-dispatch facts are proved. `SourceSelectors.lean` establishes selector
uniqueness using kernel evaluation, and `SourceDispatch.lean` retains the scaffold's theorem
signatures. The oversized original dispatcher file is split into three runtime-reach files
plus the source-dispatch file; `Dispatch.lean` imports them. Its runtime traces are unchanged.

The immutable-getter source prologue, signed calldata-size checks, return-memory round trip,
and source/EVM refinement connection are proved in `GetterSource.lean`, `GetterCommon.lean`,
and `SelectorRefinement.lean`. The last module handles named calls in a contract with a fallback.
All 24 immutable getters and five pause-status getters are complete. The mapping getters
`userNonce`, `totalsCollateral`, `userCollateral`, `isAllowed`, `liquidatorPoints`, and `userBasic`
are complete, as is `hasPermission`. The utilization getter, both rate getters, and both total
getters, both balance getters, `initializeStorage`, `pause`, `getPrice`, `getAssetInfo`, and
`getAssetInfoByAddress`, `getCollateralReserves`, `getReserves`, `quoteCollateral`, and
`withdrawReserves`, `accrueAccount`, and `approveThis` are complete.
This is 54 of the 68 ABI body proofs. Together with the selector facts and immutable extraction,
123 of the original 139 placeholders are filled; 16 remain,
including the constructor and fallback. The full contract theorem is still incomplete.

Shared helpers cover canonical address decoding, two-address decoding, packed unsigned and
signed storage fields, static multiword returns, and the internal permission routine. The
`SignedFields` lemmas connect the source's signed normalization to `SIGNEXTEND` and ABI encoding;
`userBasic` therefore includes negative principals. No new custom axioms have been introduced.

The shared rate routines and accrued-interest-index routine now cover success and all arithmetic
reverts. Their proofs retain the source and bytecode evaluation orders. Every accrual caller
supplies a 40-bit elapsed time, so the intermediate rate/time/index products fit in 256 bits;
the proofs retain both 64-bit index overflow checks. Timestamp-limit and elapsed-time-underflow
paths are also proved. These helpers support the completed total and balance getters. The balance proofs cover
positive, zero, and negative account principals. Checked negation of the minimum int104 value
is proved to revert in both the source and bytecode. Shared source reads, unsigned conversion,
present-value arithmetic, and checked-address refinement are factored for reuse.

Initialization covers the timestamp and both index writes, preserving the other packed fields.
The proof includes repeat-initialization reverts, timestamp overflow, and static-call rejection.
`PackedWrites`, `ScalarWrites`, and the state-changing selector adapters support later mutations.
The pause proof validates all five canonical bool arguments, both authorized callers, the packed
flag update, the event/return path, and static-call rejection. Its helper files separate argument
decoding, source execution, authorization, flag assembly, and the packed write.

The price proof covers arbitrary oracle code, including call-depth failure, call reverts, short
responses, both uint80 canonicality checks, and nonpositive signed prices. `StaticCallBridge`
connects zero-value static calls to the source call relation. `PriceDecode`, `PriceSource`,
`PriceMemory`, `PriceChecks`, and `PriceResponseEvm` compose into the reusable `PriceInternal`
routine. The public entry includes canonical address decoding and return encoding; its targeted
build completed successfully (`get-price-build.log`).

The internal asset-info routine is now proved through allocation, arbitrary static calls,
short-return rejection, eight canonical field checks, and struct construction. `AssetDecode`,
`AssetSource`, `AssetReads`, `AssetStructMemory`, `AssetChecks`, `AssetCallMemory`,
`AssetZeroMemory`, and `AssetResponseEvm` compose into `AssetInternal`; the targeted build
passed (`asset-internal-build.log`). The axiom audit reports only the standard basis and
accepted concrete native-decision facts, with no source-scan findings. `AssetExternal` also
builds. `AssetEncoding`, `AssetEncoderEvm`, `AssetResultMemory`, and `AssetReturn` complete
the return proof. The public `GetAssetInfo` body now builds (`get-asset-info-build.log`) and
passes the axiom audit with the same accepted trust basis.
`ScalarTupleDecode` factors the shared price/asset tuple decoder; `MemoryAllocate` now supports
any bounded allocation rounded to a multiple of 32 while retaining its price-facing API.

`GetAssetInfoByAddress` also builds and passes its axiom audit (`get-asset-address-build.log`).
`AssetSearch` relates every external call to the source loop, including exhausted searches,
call failures, and malformed responses. `AssetSearchEvm` proves the bytecode loop by a decreasing
remaining-asset count, with bounds on all allocations. `AssetMemory` and `AssetReturn` share
the return encoding proof between both asset getters.

`GetCollateralReserves` builds with the affected asset, price, and storage proofs
(`collateral-and-regression-build.log`). Its axiom audit contains 680 entries, all from the
accepted standard/native basis (`collateral-axiom-audit.log`). `TokenBalanceCall`,
`TokenBalanceMemory`, and `TokenBalanceResponse` cover the external balance query and decoder;
the collateral helpers read storage after the call and cover subtraction underflow.
`CallWordMemory` and `FreeWordReturn` factor shared memory facts.

`GetReserves` covers timestamp/accrual failures, totals snapshots before the token query,
arbitrary balance responses, signed conversion, both present values, signed addition overflow,
and negative-result ABI encoding. Its targeted build is recorded in `get-reserves-build.log`;
the axiom audit reports 1,286 entries from the accepted standard/native basis and no source-scan
findings. `Signed256`, `SignedWord`, and `SignedArithmeticEvm` provide shared signed arithmetic;
the `Reserves*` modules separate source execution, response handling, and bytecode composition.
`QuoteCollateral` covers asset lookup, both price queries, preservation of the asset structure,
both discount subtractions, all four checked products, and both zero-divisor cases. Its targeted
build passed (`quote-collateral-build.log`), and its axiom audit reports 1,440 entries from the
accepted standard/native basis with no source-scan findings. `QuoteTrace` separates the call
sequence from source/bytecode composition; `QuoteInternal` proves the reusable internal routine.
The asset search now also exposes its allocation bound, and `PriceAssetMemory` proves preservation
of asset words across price queries. `CheckedDivEvm` and `divSourceZero` provide division helpers.
`WithdrawReserves` now covers canonical calldata, governor authorization, reserve-query failures,
negative and insufficient reserves, token transfer, and the event's static-mode halt. Its targeted
build passed; its axiom audit reports 2113 accepted standard/native axioms with no custom axioms
or source-scan findings. `TransferOutInternal` is independently reusable and audited (253 accepted
standard/native axioms), with a zero-value CALL bridge valid in either permission mode, ABI
payload/memory proofs, and optional token-return-data validation. `ReservesTrace` packages the
existing reserve routine for source/EVM composition. No specifications were changed.

`accrueInternal` is now proved as a reusable source call and EVM routine. This includes timestamp
bounds, elapsed-time underflow, the zero-elapsed return, both interest-index writes in order,
static-mode failure at the first SSTORE, both optional reward updates, and the final timestamp
write. `DivBaseWei`, `TrackingIncrementEvm`, and the tracking branch/source modules cover all
arithmetic and zero-divisor failures. `AccrualWrites` proves packed uint64 field replacement and
storage transport. No custom assumptions are used: `accrue_call` uses the three standard axioms;
`cometAccrueInternal` uses 1201 accepted standard/native axioms. Both targeted builds passed.
`InternalOutcome` packages normal, revert, and static results for reusable void internal calls.
`updateBasePrincipal` is now proved through both reward branches, checked signed negation,
index subtraction, reward multiplication/division, uint64 reward accumulation, index selection,
and all five packed UserBasic field writes. Static mode fails at the first SSTORE. The memory
proof includes principal/index/accrued updates and preservation across mapping-hash scratch
writes. `updateBase_call` uses the standard basis plus one accepted native bit-vector fact;
`cometUpdateBasePrincipal` uses 755 accepted standard/native axioms, with no source-scan findings.
`WordStructMemory` and `WordStructStore` provide generic fixed-word memory-structure proofs;
`AggregateStorage`, `PackedStateWrites`, and the UserBasic modules connect aggregate source
reads/writes to packed storage without assuming distinct hash slots.

`AccrueAccount` composes these routines with canonical address decoding, the five-field storage
load, allocation, and the final STOP. It covers malformed calldata, nonpayability, accrual/reward
failures, and static execution. Its targeted build passed (`accrue-account-build.log`); its axiom
audit reports 2351 accepted standard/native axioms and no source-scan findings. The ABI count is
now 54 after also finishing `ApproveThis`. That proof covers canonical two-address/uint256
calldata, governor authorization, missing token code, CALL depth failure, arbitrary token code,
and both call outcomes, including static parent execution. The source and compiler both ignore
token return data. Its targeted build passed (`approve-this-build.log`); the axiom audit reports
706 accepted standard/native axioms and no source-scan findings. `TwoAddressUintDecode` factors
the ABI routine for later supply/withdraw/transfer entry points. The combined accrual, reserve,
and quote regression build also passed (`accrue-account-regression-build.log`, 3700 jobs).
The next proofs are the collateral checks needed by transfers and withdrawals. Remaining work
also includes supply, liquidation, and the constructor/fallback.

The shared collateral-check dependencies now include signed present value, asset membership,
and signed debt-price multiplication. Signed present value covers positive/negative principal
and minimum-int104 failure (`signed-present-build.log`, 3537 jobs; bytecode audit: 238 accepted
standard/native axioms). Asset membership covers both the uint16 and uint8 bit fields and
out-of-range offsets (`is-in-asset-build.log`, 3531 jobs; bytecode audit: 86 accepted axioms).
Signed debt-price multiplication covers the exact negative-product overflow boundary and
division by zero (`signed-mul-price-build.log`; bytecode audit: 211 accepted axioms).
All three source-call proofs use only the three standard axioms. The axiom/source audits
reported no custom assumptions or source-scan findings. `TypedBits`, `BitMembershipWords`, and
`SignedDebtWords` isolate the reusable arithmetic facts.

Targeted builds have been used throughout, including all completed ABI proof modules.
No bytecode, Solidity source, specification, or supplied block summary was changed by this work.

The complete shared collateral loop now has source and EVM proofs. `CollateralMathEvm`
composes unsigned price multiplication, factor multiplication, and signed conversion (254
accepted standard/native axioms). `CollateralValueSource` and `CollateralValueEvm` preserve
asset-query → balance-read → price-query order, cover every failure, and bound each successful
iteration's allocation to 928 bytes. The value EVM audit reports 1036 accepted axioms; its
source audit uses only the standard three. `UserCollateralRead` extracts the existing getter's
read helpers and adds generic expression reads; the public getter regression build passed.
`MappingScratch` proves hash scratch-space preservation without any slot-noncollision premise.

`CollateralLoopControl`, `CollateralLoopSelected`, and `CollateralLoopEvm` cover membership,
skipped assets, early solvency returns, selected-asset failures, signed liquidity addition, and
termination with the approved uint8 asset-count bound. `CollateralLoopSource` follows the same
trace. The loop EVM audit reports 1419 accepted standard/native axioms; source uses only the
standard three. Targeted builds passed (`collateral-loop-evm-build.log`, 3591 jobs;
`collateral-loop-source-build.log`, 3551 jobs). The shared loop is complete; the initial
principal/present-value/base-price prefix and the two ABI wrappers were completed next.

`CollateralCheckSource` and `CollateralCheckEvm` now prove the full internal checks, including
nonnegative principal, minimum-int104 failure, both packed asset bitfields, signed present value,
the external base-price call, debt-price arithmetic, and the complete asset loop. Their targeted
builds passed (3560 and 3613 jobs); source uses only the standard three axioms and the EVM proof
uses 1994 accepted standard/native axioms. `UintCastWord` factors arbitrary unsigned-width casts.
`CollateralCheckExternal` connects the shared trace to public source bodies and bool returns.
Both `IsBorrowCollateralized` and `IsLiquidatable` are complete, including malformed address
calldata and nonpayability. Their audits report 2218 and 2085 accepted standard/native axioms,
respectively, with no custom assumptions or source-scan findings. Their targeted build log is
`collateral-check-abis-build.log`. The count is now 56/68 ABI proofs and 125/139 original
placeholders filled, leaving 14 placeholders. No specification changes were needed.

`updateAssetsIn` is now complete as a reusable internal source call and EVM routine.
`AssetMembershipSource` covers all balance-crossing guards, both membership fields, out-of-range
offsets, and static writes; its audit uses only the standard three axioms.
`AssetMembershipEvm.cometUpdateAssetsIn` threads the corresponding bytecode, proves exactly
which memory changes are possible (unchanged memory or the mapping hash scratch writes), and
preserves source-state correspondence. Its audit reports 540 accepted standard/native axioms,
with no custom assumptions or source-scan findings. The targeted source and EVM builds passed
(3539 and 3574 jobs). `TypedBitUpdates` supplies generic unsigned OR, complement, and bit-update
proofs. `assignUserBasicField` extends the existing storage helpers. The next dependency is the
collateral-withdrawal routine. The public ABI count remains 56/68 and 14 placeholders remain.

`withdrawCollateral` is now complete. `WithdrawCollateralSource.withdrawCollateral_call`
proves the full internal call, and `WithdrawCollateralEvm.cometWithdrawCollateral` composes
the bytecode from pc 16281 through its return. The prefix checks both uint128 subtractions,
writes totals before the user balance, and covers static writes. The tail handles asset-search
failure, membership updates, collateral rejection, token-transfer failure, and event emission.
Both source and EVM preserve the original read/write order without slot-noncollision assumptions.
The source audit reports the three standard axioms; the EVM audit reports 3141 accepted
standard/native dependencies, no custom assumptions, and no source-scan findings. The combined
targeted build passed (3671 jobs).

Supporting modules added in this step include `CollateralStorage`, `CollateralStoreEvm`,
`CheckedSub128Evm`, `CollateralMappingMemory`, `CollateralEventEvm`, and `InternalDynamicOutcome`.
The last module generalizes the void routine result to permit changed memory and return data.
All withdrawal modules are small and contain no placeholders. No spec changes were needed.
The next dependency for the withdrawal ABIs is `withdrawBase`, especially its `principalValue`,
`principalValueSupply`, `principalValueBorrow`, `safe104`, `signed104`, and
`withdrawAndBorrowAmount` callees. Existing accrual, signed-present-value, principal update,
collateral-check, and token-transfer proofs should be reused. The ABI/placeholder counts remain
56/68 and 14 respectively.

The principal-magnitude helpers are complete: `PrincipalMagnitudeSource.principalMagnitude_call`
handles both `principalValueSupply` and `principalValueBorrow`; `PrincipalSupplyEvm` proves the
pc 12917 routine, and `PrincipalBorrowEvm` proves the inlined pc 12813 routine. They cover all
multiplication/addition overflow, subtraction underflow, zero-index division, and uint104 bounds.
The source audit reports three standard axioms; the borrow EVM audit reports 202 accepted
standard/native dependencies and no findings. The combined targeted build passed. `SafeUintSource`
provides a generic source narrowing guard (including safe104/safe128); `Signed104Source` and
`PrincipalCastEvm` complete the signed104 cast and both EVM cast routines.

`CheckedAddSubSource` is a generic source composition helper for checked addition followed by
subtracting one. It also avoids a Lean kernel recursion failure seen when embedding that proof
directly with nested principal expressions; the final caller checks with maxRecDepth 2000.
`SignedNegation` proves full uint256 checked negation, its minimum-word characterization,
negative magnitude interpretation, and nonnegative int104 negation. `PrincipalValueModel` is
complete and its callable lookup checks by rfl. Full `PrincipalValueEvm` and
`PrincipalValueSource` now pass targeted builds and audits (459 accepted standard/native
dependencies for the EVM theorem, three standard axioms for the source theorem). Neither audit
found custom axioms or source issues. `PrincipalValueWords` links the returned word to its
source integer and proves canonical int104 sign extension under `PrincipalValueFits`.

`WithdrawAmountsSource.withdrawAmounts_call` and `WithdrawAmountsEvm.cometWithdrawAmounts`
are complete for `withdrawAndBorrowAmount`, including all four return branches and arithmetic
reverts. Their audits report three standard axioms and 255 accepted standard/native
dependencies respectively, with no findings. The combined build is in
`withdraw-amounts-build.log`. The EVM entry is pc 15228 with `[old, next, ret] ++ R`, requires
`R.length + 10 ≤ 1024`, and returns `[borrowAmount, supplyAmount] ++ R` on success.
`WithdrawAmountsModel` supplies the source callable, amounts, fits predicate, and principal
difference lemmas; `WithdrawAmountsWords` proves uint104 bounds and the positive-field mask.
`Signed104SubEvm` proves the checked subtraction at pc 13082 for a nonnegative difference,
including overflow. `Negate104PackedEvm` accepts an unextended int104 input at pc 10633.
`SignedArithmeticWords` generalizes signed word addition/subtraction and source range checks.
`Signed104Encoding` links sign extension to signed interpretation and proves packed negation.

Lean lesson: source proofs whose goals contain `if` on `signed104` comparisons can recurse
while elaborating even a plain `by_cases`. Keep `signed104` locally irreducible in these
proofs; increasing maxRecDepth did not help. The completed source file uses maxRecDepth 2000.
`bindParams?` builds locals from the tail, so two-argument entry frames must insert the second
argument first. For Nat mask rewriting, explicitly `change Nat.land ...`, as `&&&` can leave
the rewrite matcher unable to find `nat_land_mask_eq_mod`.

Next is the full `withdrawBase` composition. Its initial runtime PCs are 15734 (accrual),
15748 (user-basic allocation/read), 15788 (signed amount), 15797 (principal conversion),
15813 (withdrawal split), 15820 and 15841 (totals writes), followed by
totals writes, updateBasePrincipal, collateral checks, transfer, and events. ABI and placeholder
counts are still 56/68 and 14; the completed internal helpers are prerequisites for these ABIs.

The `WithdrawBaseMathModel/Source/Evm` modules are now complete. `cometWithdrawBaseMath` starts
at pc 15776 with `[signextend principal, 15852, ptr, recipient, amount, src, ret] ++ R` and
requires `R.length + 22 ≤ 1024`. It returns pc 15820 with `withdrawBaseMathStack` or reverts;
`WithdrawBaseMathFits` records all present-value, signed amount/subtraction, principal conversion,
and withdrawal-split guards. `withdrawBaseMath_source` proves the matching seven statements and
explicit final frame. Audits report three standard source axioms and 954 accepted standard/native
EVM dependencies; no findings. The combined targeted build is `withdraw-base-math-build.log`.
`SignedSubEvm.cometSignedSubNonnegRight` extends pc 9713 subtraction to any signed left operand
and a nonnegative right operand, including underflow. Its source counterpart is
`signedNarrowRangeSourceUnderflow` in `SignedArithmeticWords`.

Important entry detail: pc 15734 hardcodes arithmetic/store continuation pc 12591; it is an inlined entry
with `[src, recipient, amount] ++ R`, not a generic four-word internal-call entry. After accrual,
pc 15748 has `[recipient, amount, src, ret] ++ R`. It calls mapping-slot helper 2428 via 12490,
then user-basic allocation/load at 7655 (allocation 6982, inline load 7670), returning to 15762.
15762 loads principal from memory and enters 15776. Next: prove this account read/allocation,
then packed totals writes after pc 15820, updateBasePrincipal, checks, transfer, and events.

`UserBasicAllocation` and `WithdrawBaseRead` are complete and built. The generic allocation/load
starts at pc 7655 with `[slot, ret] ++ R` and needs `R.length + 9 ≤ 1024`, a known free pointer,
and `free + 160 < 2^64`. It returns a five-word `UserBasicMemory`; its concrete memory model
has proved size and free-pointer properties. `cometWithdrawBaseRead` starts at pc 15748 with
`[recipient, amount, word src, ret] ++ R`, uses `R.length + 13 ≤ 1024`, and returns pc 15776
with `withdrawBaseBasic` and `withdrawBaseReadMemory`. Math then leaves memory unchanged.

`WithdrawBaseTotalsModel/Source/Evm` are complete, with three standard source axioms and 272
accepted standard/native EVM dependencies; no audit findings. The combined build is
`withdraw-base-totals-build.log`. Source preserves the frame across two packed assignments.
The outcome orders supply subtraction, permission check, supply write, borrow addition, borrow
write. The borrow total is read after the supply write; no disjoint-storage assumption is used.
EVM `cometWithdrawBaseTotals` requires `R.length + 19 ≤ 1024` and uint104 amount bounds. It starts
at pc 15820 with `[borrowed, supplied, 12598, ptr, principal, 15852, balance, recipient, amount,
src, 12591] ++ R` and finishes pc 12598 with `[ptr, principal, 15852, balance, recipient, amount,
src, supplied] ++ R`, or reverts/static-halts. Thus the `ret` parameter in earlier read/math
helpers must be instantiated to **12591** here; it is the borrow-store arithmetic continuation,
not the final withdrawal return destination.

Supporting modules: `Checked104Evm` proves uint104 subtraction at 12353 and addition at 12293
with all failure paths. `TotalsPrincipalWrite` provides packed-field correspondence and source
assignment/state-preservation facts. `TotalsPrincipalStoreEvm` covers both permitted writes;
`TotalsPrincipalStatic` proves the pc 12322 static halt by copying the supplied decoded prefix
only (the supplied RuntimeBlocks were not changed). Next: invoke `cometUpdateBasePrincipal`
via pc 12598; prove its concrete memory preserves the free pointer/size, then complete the
negative-balance minimum/collateral check and transfer/event tail. No mismatch or blocker found.


`withdrawBase` is now complete end to end. `WithdrawBaseSource.withdrawBase_call` proves the
source call; `WithdrawBaseEvm.cometWithdrawBase` proves pc 15734 through its final return.
The combined targeted build `withdraw-base-build.log` passed (3740 jobs). The source audit has
three standard axioms plus the accepted `signextend104_bitvec._native.bv_decide.ax_1_8` dependency
(the tool labels that name custom); the bytecode audit has 5010 accepted standard/native/BV
dependencies. No sorry, unsupported custom axiom, or source-scan finding was reported.

The full bytecode theorem takes `[word src, word recipient, amount, ret] ++ R`, requires
`R.length + 42 ≤ 1024`, known free pointer, free >= 96, memory size >= 96, and
`free.toNat + 576 + 928 * v.numAssets.toNat < 2^64`. It returns an existential
`WithdrawBaseTrace` together with `internalDynamicRun ret R`. Its source counterpart accepts
arbitrary caller expressions and returns `internalStmtResult`. The model preserves the original
user-basic snapshot across totals writes; all subsequent reads use their actual current states.

New supporting modules: `UpdateBaseMemory` (size/free-word preservation), `WithdrawBaseEventsEvm`
(15905 event and optional 15983 present-value/Transfer event), `WithdrawBaseTransferEvm`,
`WithdrawBaseTailEvm`, `WithdrawBaseTrace`, `WithdrawBaseTailModel`, `WithdrawBaseTransferSource`,
`WithdrawBaseTailSource`, `WithdrawBaseModel`, `WithdrawBaseFrames`, `WithdrawBaseReadySource`,
`WithdrawBaseAfterSource`, `WithdrawBaseTotalsResult`, and `InternalBlockComposition`.
The tail starts 15852 with `[balance, recipient, amount, src, supplied, ret] ++ R` and needs
`R.length + 41 ≤ 1024`; the negative branch negates at 10671, checks baseBorrowMin at16026,
checks collateral at10164 via12096/16076, and joins the transfer path15861.

Kernel lesson: rewriting `withdrawBaseTotalsResult` directly after substituting the complete
caller state caused `(kernel) deep recursion detected`, even at maxRecDepth10000. It was
isolated to that result conversion (not trace induction). `withdrawBaseTotals_result` proves
the conversion with generic state/amount arguments; callers apply the proved lemma. Likewise
`internalStmtResult.cast` specializes internal-call results without unfolding caller state.
`internalBlockResult.prependBlock` composes a successful block with any internal outcome.
All new files are clean in LSP. A harmless unreachable-cases warning remains in WithdrawBaseEvm.

Next: prove `withdrawInternal` and its three ABI callers (Withdraw, WithdrawTo, WithdrawFrom).
No reentrancy-guard routine proof exists yet: source `nonReentrantBefore` loads
`__reentrancyGuard`, requires status != 1, stores 1; `nonReentrantAfter` stores 0. The guard slot
is 91163063775796598582698250372395185889154745920815755245223157833676084630444 (padding+8).
Search Reasoning/Solc.lean reentrancy-prefix section before new helpers. Existing permission,
pause flags, balanceOf, safe128, base withdrawal, and collateral withdrawal proofs are available.
WithdrawTo dispatcher pc907 jumps5465 (callvalue guard), next5472; WithdrawFrom pc1294 jumps2270,
next2277. Track block successors rather than guessing PCs. Original counts remain56/68 ABIs,
125/139 placeholders filled,14remaining. No spec changes or suspected semantic blocker.


Withdrawal checkpoint (2026-10-09, all public withdrawal entries complete):
- 59/68 ABI entries complete; 128/139 original placeholders filled; 11 remain.
- Completed original WithdrawTo, WithdrawFrom, Withdraw theorem bodies, preserving signatures/docstrings.
- Axiom audits: WithdrawTo 6866, WithdrawFrom 6582, Withdraw 6865, each accepted standard/native/BV only;
  zero non-native/non-BV extra axioms and zero source findings. Source never adds assumptions.
- Individual builds passed (withdraw-to-build.log 3832 jobs; withdraw-from-build.log 3833 jobs).
  Combined final build is withdraw-public-build.log (session 20464 at time of note).

Reentrancy modules: ReentrancyModel/Storage/Source/Memory/Evm prove source before/after and runtime.
Guard slot = 91163063775796598582698250372395185889154745920815755245223157833676084630444.
Runtime reads it from code bytes 18514..18546; memory scratch copy+restore preserves size/free pointer.
cometReentrancyBefore: RD12245[ret,R], R+6, hs,hret -> internalMemoryRun at ret,R,
reentrancyMemory v mem, reentrancyOutcome evm true. Revert guard==1; static write; success write1.
cometReentrancyAfterStop: RD2308 R,R+6,hpermtrue,hs -> SourceState of reentrancyState evm false,
RDret empty. Source reentrancy_call uses generic enter Bool; internalStmtResult.

PermissionState generalizes permissionMemory size/free to memory>=96 and permissionBool_state hs.
WithdrawAuthModel/Source/Evm prove pause bit2 zero + permission src/operator. cometWithdrawAuth:
RD15597[operator,src,to,asset,amount]++R, R+13,hs -> if WithdrawAuthValid then
RD15632[asset,to,amount,src]++R, permissionMemory src operator mem; else RDrev.
No storage/environment change during authorization. Source ready inserts __c1,__c2.

Safe128Evm.cometSafe128 completes runtime guard at12207: R+6,hret -> amount<2^128 and
RDret[amount,R] OR too large and RDrev. Uses existing generic arithmetic/source lemmas.
WithdrawAssetModel/Source/Evm composes asset selection, optional balanceOf for max256, and base/collateral.
Trace constructors: base hb hm ht; balanceFailed hb hm hv; allBase hb hm hv ht;
 tooLarge hb width; collateral hb width ht. hb compares asset to v.baseToken.
withdrawAsset_source ht frame hf : ExecStmt withdrawAssetStmt with internalStmtResult
 (withdrawAssetReady frame v evm src asset amount) (withdrawAssetReturn v asset) result.
WithdrawAssetArgs contains contract,immutables,src,to,asset,amount getters.
cometWithdrawAsset: RD15632[asset,to,amount,src,ret,R], R+44,hs,hret,hfree,hlo96,hmem96,
free+672+1696*numAssets<2^64 -> exists WithdrawAssetTrace and internalDynamicRun ret R result.
Base max case calls balance at18252, ret15708; validity/word rewritten with hs.storageRead/env.
Base ordinary calls15734 ret3121; collateral calls safe128 then16281 ret3121.
DynamicReturnEvm.cometDynamicReturn maps internalDynamicRun3121[ret,R] to ret R (R+1,hret).

WithdrawInternalModel/Source/Evm: exact withdrawInternalCallable lookup rfl; entry inserts reverse params.
WithdrawInternalAfter: unauthorized, reverted, staticViolation, done (asset.ok plus permtrue;
returns reentrancyState evm false). WithdrawInternalTrace: before reverted/static or done before.ok+After.
withdrawInternal_call generic five expressions and argument evaluation equations.
cometWithdrawInternalAfter: RD15597[operator,src,to,asset,amount,2308,R], R+44,ee.permtrue,
 hs,hfree,hlo96,hmem96,free+672+1696N<64 -> exists AfterTrace + voidOutcomeRun.
cometWithdrawInternalStart: RD12245[ret,R], R+6,hs,hret, continuation callback -> fullTrace+voidOutcomeRun.
Callback receives arbitrary successful SourceState evm', permtrue, RDret R at reentrancyMemory.
voidOutcomeRun is reused from AccrueAccountInternal (success RDret evm.accountMap empty).

Public wrappers:
- WithdrawTo: selector54 ->907->5465 value->5472 decode2001 ret5485 withfinal2308;
  5485 calls before12245 ret5494, then caller/caller ->15597.
- WithdrawFrom: selector10 ->1294->2270 value->2277 decode2215 ret2290 final2308;
  2290 before12245 ret2302 then caller ->15597.
- Withdraw: selector67 0xf3fef3a3 / 4093572003; final dispatcher SUB at768 (not ordinary EQ arm).
  Fallthrough778[]->6868 value->6875 length64->6887 validateaddr ret6901;
  6901 before12245 ret6909 [asset,2308];6909 pushes caller x3 plusamountcalldata36 ->15597.
- WithdrawDispatch and DispatchLast prove missing final branch. DispatchLast proves reach768
  when first67 EQ selectors all miss; helper reusable for fallback. No supplied blocks modified.
- Withdraw/To/From source use explicit .return[], yielding returned(some[]), not fallthrough none!
  New VoidCallSource.explicitVoidSourceResult and voidCallPrologue_source handle this.
  New SelectorRefinement.explicitVoidReturnEquiv for some[]. Original voidReturnEquiv still none.
- Source theorem inference needs explicit evm := initState... because operator uses evm.executionEnv.source.

ThreeAddressUintCalldata provides generic-named-address calldata decoding to conditional valid/none;
ThreeAddressUintDecode proves runtime2215 decoder (output reversed four words) at R+11.
Shared helper decodeScalarWord_calldata_address parameterized offset n, word exists and offset<2^64.
Decoder runtime2215->2228 validate first ret2238->2238 validate second ret2253->2253 third ret2040;
2040 reads amount at100 and returns [amount,asset,to,src,R].
Critical elaboration lesson: use `have r8 := block_2040 ... hvalid r7; exact <witnesses,r8>`.
Putting block_2040 directly inside existential expected RD triggered 800k heartbeat timeout;
separating it makes elaboration ~1s. Explicit `change` on intermediates helps too.

Next: supply dependency chain. SpecSyntax functions: supplyInternal424, doTransferIn574,
supplyBase690, supplyCollateral713, transferBase747, transferCollateral786.
Incoming transfer helper is not proved yet. No semantic blocker found.
Remaining: Supply/SupplyTo/SupplyFrom, Transfer/TransferFrom/TransferAsset/TransferAssetFrom,
 BuyCollateral, Absorb, Constructor, Correct fallback. Do not stop goal at this checkpoint.


## Incoming transfer checkpoint — October 9, 2026

`doTransferIn` is complete at source and bytecode levels. The targeted build in
`transfer-in-build.log` passed (3876 jobs), including TransferInSource,
TransferInEvm, Withdraw, WithdrawTo, WithdrawFrom, and ApproveThis. Audits:
`transferIn_call` uses three standard axioms; `cometTransferInInternal` has
544 standard/native-decision dependencies, no unexpected axioms or findings.
ABI progress remains 59/68, with 11 original placeholders remaining.

New modules: CallThreeWordMemory, TransferFromPayload, TokenBalanceTrace,
TransferCallSource, TransferInModel, TransferInSource, BalanceWordDecode,
TransferInBalanceBefore, TransferInBalanceAfter, EmptyTupleDecode,
CheckedSub256Evm, TransferInResponse, TransferReplyMemory, TransferFromMemory,
TransferInCallEvm, TransferInEvm. All are LSP clean. TransferOutSource now uses
TransferCallSource; TransferMemory uses TransferReplyMemory; ApproveResponseEvm
uses EmptyTupleDecode. Original signatures/docstrings preserved.

- `TransferCallTrace asset payload evm : Option (EVM.State × ByteArray)` captures
  code absence and opaque CALL result plus ERC20 empty/32-byte-nonzero validation.
  `transferCall_source` proves its four-statement block for arbitrary asset/payload
  expressions. `transferCallFrame` binds ok/data/checked.
- `TokenBalanceTrace asset evm : Option (EVM.State × UInt256)` captures opaque
  STATICCALL with balanceOf(this), bool success and at least 32 bytes.
  `tokenBalanceTrace_source` works in arbitrary frames; `wordCallResult` handles
  unsigned word-valued source calls.
- `TransferInTrace` first balance failure or first balance success plus
  `TransferInAfter`. The latter handles transfer failure, second balance failure,
  and checked post-minus-pre. Source `transferIn_call` takes arbitrary caller,
  three argument expressions, frame.contract and three evaluation equations.
- `cometTransferInInternal`: RD 13272 [asset, sender, amount, ret] ++ R;
  R.length+16 <=1024, free=ptr, 96<=ptrNat, ptrNat+132<2^64, hret, SourceState.
  Produces TransferInTrace and TransferInRun at ret. Success free is ptr+64,
  freeNat<=memory.size; success returns measured received amount, not request.
- `TransferInRun v ee g s0 ret free R`: none RDrev; some(state,value) existential
  account map/memory/active words/returndata/counters, SourceState, memory free
  pointer=free, freeNat<=memory.size, RD ret [value]++R.
- `cometTransferInAfter`: starts 13340 [dummy,sender,amount,asset,32,pre,
  tokenBalanceSelectorWord,ret]++R. Same R+16; free=ptr,96<=ptr,ptr+100<64.
  Produces TransferInAfter and TransferInRun free=ptr+32.
- First query:13272->1550->13319->STATICCALL13324->13325->13332->13606,
  success13621->allocator6982->9678->9546->9558->13630->13340.
  Returns stack[dummy,sender,amount,asset,32,pre,selector]++R and
  tokenBalanceReturnMemory at first ptr. Failure13637->7166; short9693.
- CALL13349 builds100-byte transferFrom payload, CALL13402, response13403.
  Success13572->allocate0->5253 empty tuple decoder->13587->13414.
  Empty return13563->13443;32 bytes13423->13434->13443;invalidreverts.
  Success13449[asset,32,pre,selector,ret,R] with transferFromOutputMemory.
- Second query13449->1550->13476->STATICCALL13480->13481->13488->13503.
  Success13516->allocator6982->9678->9546->9558->13525->13496->8603.
  Stack[post,pre,2425,ret,R]; checkedSub2568603->8611->2425->ret.
- `cometAllocatedWordDecode`: common decoder starts6982[ptr,32,9678,32,ptr,ret,R],
  R+9,ptrNat+32<64,hret; yields memLoadptr in writeWordmem64(ptr+32).
- `cometShortWordDecode`: starts9693[dummy,ptr,R],R+8,ptr+32<64,out.size<32;
  allocator then short decode ->RDrev.
- `cometDecodeEmptyTuple`:5253[ptr,ret,R],R+4,hret ->retR,memunchanged.
- `cometCheckedSub256`:8603[x,y,ret,R],R+5,hret; if yNat<=xNat returns sub elsepanic.

Next work: repayAndSupplyAmount at13148, then supplyBase/supplyCollateral.
Source SpecSyntax892; new<old=>0,0; new<=0=>checked104(new-old),0;
old>=0=>0,checked104(new-old); else=>checked104(-old),uint104(new).
Can reuse principalDecrease next old, checkedPrincipalNegSource,
cometSigned104SubNonneg, cometNegate104Packed, mask104_positivePrincipal.
PCs inspected:13148 compares signextendednew<old ->13259 zero return;
fall13167 tests0<new ->13199 else13174. 13174calls13082(new,old,ret13184);
13184returns[0,maskdiff,R]. 13199testsold<0 ->13234 else13207.
13207calls13082(new,old,ret13216);13216returns[maskdiff,0,R].
13234calls10633(old,ret13243);13243returns[masknew,masknegold,R].
See WithdrawAmountsModel/Source/Words/Evm for mirrored routines.

## Checkpoint: supply family complete

Completed RepayAmounts*, SupplyBase*, SupplyCollateral*, SupplyAsset*, SupplyInternal*,
and the public Supply, SupplyTo, SupplyFrom proofs. Counts: 62/68 ABI bodies complete,
131/139 original placeholders filled; 8 remain (four transfer ABIs, BuyCollateral,
Absorb, Constructor, Correct fallback). No spec edits or new assumptions.

Validation:
- supply-internals-build.log: 3912 jobs successful, including all three withdrawals.
- supply-public-build.log: 3934 jobs successful, including all three supply and withdrawal ABIs.
- Public supply audits: Supply 6101, SupplyTo 5820, SupplyFrom 5942 axioms,
  all standard/native/concrete BV evaluator trust; no unexpected axioms or source findings.
- supplyCollateral_call: standard 3; cometSupplyCollateral: native 2142, no unexpected.
- Earlier SupplyBase call/EVM audits: standard+concrete BV / native 3567, no unexpected.
- RepayAmounts call/EVM audits: standard 3 / native 257, no unexpected.

Key new APIs:
- cometSupplyBase: PC12418 [from,dst,amount,ret,R], R+42, free pointer >=96,
  freeNat+224<2^64 -> SupplyBaseTrace plus internalDynamicRun.
- cometSupplyCollateral: PC13820 [from,dst,asset,amount,ret,R], R+30, amount128,
  freeNat>=96, freeNat+576+768*numAssets<2^64 -> SupplyCollateralTrace plus dynamic run.
  Source call supplyCollateral_call has no input-width premise (internal body only).
- cometSupplyAsset: PC12105 [asset,dst,amount,from,ret,R], R+44, free>=96,
  mem>=96, free+576+768*numAssets<2^64; chooses supplyBase or supplyCollateral.
  Max amount uses borrowBalanceOf(dst), including signed104-min failure.
- cometSupplyInternalAfter: PC12067 [operator,from,dst,asset,amount,2308,R], R+44,
  permission true and same memory bounds -> SupplyInternalAfter + voidOutcomeRun.
- cometSupplyInternalStart: PC12245 reentrancy entry with continuation; analogous
  to withdrawal. supplyInternal_call is the source internal-call theorem.
- AuthorizationSource factors shared pause-and-permission source proof:
  AuthorizationValid evm bit operator owner; authorizationBlock bit ownerName;
  authorizationFrame frame evm bit operator owner; authorization_source.
  WithdrawAuthSource now delegates bit2/"src"; supply uses bit0/"from".
- PermissionState adds permissionRuntime_nonzero/zero; withdrawal and supply share them.
- ReentrancyModel adds reentrancyOutcome_perm; both internal entry proofs use it.
- AssetDispatchSource adds generic evalExpr_address_eq and evalExpr_uint256_max
  (library candidates), reused by withdrawal/supply source routing.
- CollateralMappingMemory adds WordStructMemory.userCollateral (two scratch writes).
- PackedGetter adds mask128Clean (left mask). CheckedAdd128Evm and CheckedSub128Evm
  share it; Mask128Evm proves PC2451 uint128 mask routine.
- TotalsCollateralData models complete two-field totals tuple reads/writes.
  WordStructAllocation generalizes allocation; UserBasicAllocation delegates common facts.
  TotalsCollateralMemory/Allocation, High128Write, TotalsCollateralStoreEvm built.

SupplyCollateral proof decomposition:
Read13861->13881 allocates64 bytes for totals and preserves AssetMemory region;
TotalEvm13881->13952 checks total+amount uint128 and supply cap, writes memory;
BalanceEvm13952->14040 checks old dst balance+amount;
Write14040->14071 writes whole totals struct then dst low128;
Member14071->14132 membership->14077 event encoder13801->14109 return.
AfterTotalEvm,AfterAssetEvm,Evm compose; Source uses Prefix/Prepare/After files.
All preserve exact storage/read order, including potential mapping aliases.

Next: transferCollateral then transferBase, then four public transfer ABIs.
SpecSyntax lines747/786; no transfer implementation files created yet at this checkpoint.
transferCollateral reads both src/dst balances before checked subtraction/addition and
both writes. Reuse checkedNarrowSubSource*, checkedUintAddSource*, cometCheckedSub128,
cometCheckedAdd128, cometStoreLow128, assetMembership_call/cometUpdateAssetsIn,
assetSearch_call/cometAssetSearchInternalBounded, collateralCheck_call/cometCollateralCheck.
PCs inspected from supplied blocks:15329 initial src root6 hash;15382 reads src and hashes
first dst mapping;15413 reads dst and calls checkedSub128;15425 calls checkedAdd128;
15435->mapping->15449->mapping->15459->13718ret15469 writes src;
15469->mapping->15482->mapping->15492->13718ret15502 writes dst;
15502 assetsearchret15511;15511 src membershipret15523;15523 dst membershipret15532;
15532 collateralcheckret15541;false->15192;true->15547->13801->14109 logs andreturns.

## Checkpoint: collateral transfers complete

TransferCollateralModel/Frames/Locals/PrefixSource/Trace/TailSource/Source and
Stacks/Read/MathEvm/Write/PrefixEvm/CheckEvm/MemberEvm/TailEvm/Evm are complete.
`transferCollateral_call` has only the three standard axioms;
`cometTransferCollateral` has 3018 accepted standard/native axioms, no unexpected axioms.
The targeted transfer-collateral-build.log finished successfully (3950 jobs), including
all six completed supply/withdraw public ABIs as regression checks.
MappingScratch now provides AssetMemory.scratchOrSame, shared with withdrawal.
The collateral routine preserves the exact read-both/write-source/write-destination order.
There are still 62/68 complete public ABIs and eight original placeholders overall.
Next: transferBase, then its four public transfer ABIs. Base transfers read both user
structures, perform both signed balance/principal calculations, update totals, then update
the two principals. Do not compose supply/withdraw totals: their storage order differs.

## Checkpoint: base-transfer components and EVM assembled

TransferBaseEvm now passes LSP, including `cometTransferBaseAfterAccrue` and `cometTransferBase`.
The source assembly (`TransferBaseFrames`, ReadySource, AfterSource, Source) is still to do.
TransferBaseModel defines the exact callable and proves its lookup by rfl.
Its Trace/AfterAccrue cover math failure, totals revert/static, pair-update revert/static,
and tail success/failure. It reuses withdrawBaseNext/Supplied/Borrowed and
supplyBaseNext/Supplied/Repaid from the completed withdrawal/supply models.
Original remaining placeholders still eight (62/68 ABIs complete).

New complete components:
- TransferBaseRead: RD14675->14741, R+14, free>=96, mem>=96, free+320<2^64;
  reads both original account structures into free and free+160. ReadMemory preserves both;
  free cursor becomes free+320. UserBasicAllocation adds userBasicAllocatedMemory_prefix.
- TransferBaseMathModel/Frames, BalanceEvm/Source, AmountsSource, MathEvm/Source:
  math RD14741->14841, R+22. Fits = WithdrawBaseMathFits src AND SupplyBaseMathFits dst.
  Source executes both balances, both principal conversions, then withdraw/repay splits.
- TransferBaseTotalsModel/Source, SupplyTotalsEvm/BorrowTotalsEvm/TotalsEvm:
  checked104(total+increase), checked104(sum-decrease), then one packed store, supply first.
  Borrow reads the updated state. Full14841->14930, R+17 where R includes dst,ret.
  TotalsChangeFits/State/Outcome/Stmt/Result shared by both fields.
  totalsChangeOutcome_perm and transferBaseTotalsOutcome_perm give successful state's perm.
- TransferBaseUpdateModel/Memory/Evm/Source: two updateBasePrincipal calls in order,
  original snapshots for both basic structs. RD14930->14950, R+33 including ret separately.
  Pair memory preserves size/free, requires srcPtr+96<=dstPtr, both>=96.
- TransferBaseEventsEvm/Source: conditional burn and mint, source state unchanged.
  EVM14959->ret, R+16; Mint helper14977->ret R+13. Needs both amounts<104 and ee.perm=true.
- TransferBaseTailModel/Source/Evm: BorrowMin + collateral check for negative src balance,
  then events. RD14950->ret, R+41, free+416+928*numAssets<64, free<=memsize+32.
  TailTrace constructors nonnegative,tooSmall,failed,rejected,accepted; no destination/amount
  in trace because events preserve source state. Args includes src,dst,balance,withdrawn,
  supplied,baseSupplyIndex-none,contract,immutables; .insert preserves all six local names.
- Top cometTransferBase RD14664[src,dst,amount,ret,R], R+41,
  free>=96, mem>=96, free+736+928*numAssets<2^64. Returns Trace+internalDynamicRun.

Shared refactors, all existing theorem signatures preserved:
- BaseBalanceSource shares presentValue/signed256/checked signed add/sub source composition.
  Existing WithdrawBaseMathSource and SupplyBaseMathSource delegate the first three statements.
- TupleLocalSource.tuplePairLets_source is a generic library candidate, used twice by transfer.
- CheckedAddSubSource adds checkedNarrowAddSubSource for arbitrary width and subtrahend.
- TotalsPrincipalRead supplies sourceState_totalsPrincipalRead/supplyPrincipalRead/
  borrowPrincipalRead; existing supply/withdraw totals EVM proofs now share these.
- WordStructMemory.writeDisjoint (library candidate); UpdateBaseMemory_preserveLater keeps
  the second memory structure intact across the first account's principal/reward/index writes.
- PackedPresentValueEvm.cometPresentSupplyFromPacked handles2959[word,12716,principal,ret,R],
  R+8; reused by all supply/withdraw/transfer events.
- PrincipalTransferEventSource shares conditional source burn/mint (parameterized local names).
  Existing SupplyBaseEventsSource and WithdrawBaseTransferSource delegate to it.
- BorrowMinimumSource owns existing withdrawBaseBorrowMin_eval (moved unchanged from
  WithdrawBaseTailSource), used by both transfer and withdrawal.

Builds completed:
transfer-base-math-build.log 3945 jobs, includes all six supply/withdraw publics.
transfer-base-components-build.log 3972 jobs, includes collateral transfer and six publics.
transfer-base-tail-build.log 3964 jobs, includes all components plus six publics.
Latest full TransferBaseEvm build was started as transfer-base-evm-build.log; check current session.

Axiom audits (all no warnings, no unexpected assumptions):
transferBaseMath_source standard3; cometTransferBaseMath native1159;
transferBaseTotals_source standard3; cometTransferBaseTotals native299;
transferBaseUpdate_source standard3 + accepted signextend104_bitvec native BV fact;
cometTransferBaseUpdate native773.
Full cometTransferBase and final source still need audits after assembly.

Lean notes: avoid raw `rw` on iff under dependent if; use `simp only` for BaseBalanceFits iff.
Normalize baseBalanceFrame/baseBalanceInt/baseBalanceBlock with simp before composing to avoid
kernel deep-recursion through boolean aliases. Contract equality of nested frames can trigger
huge reduction: `simp only [frame aliases]` first, then exact hc, instead of raw exact/change.
For source memory prefix use an explicitly instantiated `have hp := ...` then `.mono`;
passing the whole expression directly into expected type can exhaust unification heartbeats.
`UInt256.ofNat 12` and literal12 may need a typed memLoad equation before rewriting
signextend104_idem. Match `uadd_toNat` (not addWord_toNat) when rewriting `+` syntax.

Next source assembly follows WithdrawBaseFrames/ReadySource/AfterSource/Source.
ReadBlock has FOUR statements: read srcUser;read dstUser;let srcPrincipal;let dstPrincipal.
Use evalUserBasic and evalBasicPrincipal; do not compose the two existing two-statement reads
because that changes local insertion order. ReadyFrame is MathFrame(ReadFrame(AccruedFrame)).
MathFits hf.1.2.1.1 supplies strict -2^255<signedWord srcBalance for final checks.

## Checkpoint: all four public transfers complete

TransferBaseFrames/ReadySource/AfterSource/Source now complete. Full TransferBase source call
and EVM audits have no unexpected axioms (source standard3 + accepted signextend104 BV fact;
EVM native5044). transfer-base-complete-build.log completed3970jobs.

TransferAssetModel/Source/Evm prove the internal asset branch: max uint256 uses balanceOf(src),
base uses TransferBase, collateral safe128 then TransferCollateral. Reuses withdrawBalanceValid/
withdrawBalanceWord from WithdrawAssetModel. EVM entry14550[solcAddrMask,asset,dst,amount,src,ret,R],
R+44, free>=96,mem>=96,free+736+1696*numAssets<64. Finishes internalDynamicRun ret R.
TransferAuthEvm entry14496[operator,src,dst,asset,amount,R],R+13, pausebit1+permission;
success14531[asset,dst,amount,src,R],permissionMemory. Reuses AuthorizationSource.
TransferInternalModel/Source/Evm add reentrancyBefore, authorization, src!=dst, asset branch,
reentrancyAfter. Trace/After results include all revert/static branches. Sourcecall complete.
EVM After takes returnsBool Bool, entry14496[...,transferReturnPC returnsBool,R],R+44,
free+736+1696*numAssets<64. End at2116 for bool /2308 for void. Start theorem is continuation-based
at12245. TransferPublicReturn proves both completions using freeWordReturnData and reentrancy write.
ReturnOutcome.returnOutcomeRun is generic returned-byte-array outcome (GENERALIZES voidOutcomeRun).
CallReturnSource.explicitSourceResult andcallReturnPrologue_source generalize explicit void returns.
AssetDispatchSource added generic evalExpr_address_ne. All earlier source consumers checked by build.

Public files complete (original theorem statements/docstrings preserved):
Transfer /TransferFrom /TransferAsset /TransferAssetFrom. Separate source/EVM helpers;
TransferAssetPublicSource/Evm names distinguish public from internal asset branch helpers.
All4LSP clean, audits native6976/native6724/native6820/native7040 respectively; zero unexpected
axioms and source warnings. transfer-family-build.log **Build completed successfully(4010 jobs)**
includes all4publictransfers + all6supply/withdrawregressions.
Count now66/68ABIs,135/139originalholesfilled. Only4Lean sorries:
Correct.lean fallback,Constructor.lean,BuyCollateral.lean,Absorb.lean.
No semantic blockers. No new spec changes. No build sessions running.

Next: BuyCollateral dependencies already proved: reservesInternal(9825), transferIn(13272),
quoteInternal(17965), collateralReservesInternal(9561),safe128(12207),transferOut(16113).
SpecSyntax1463ff body: reentrancyBefore;pausebit4;getReserves;require not(reserves>=0&&
uint256reserves>=targetReserves);transferIn(baseToken,caller,baseAmount),assign received baseAmount;
quoteCollateral(asset,baseAmount);require quote>=minAmount;getCollateralReserves(asset);
require quote<=reserves;safe128quote;transferOut(asset,recipient,quote);emit BuyCollateral;
reentrancyAfter (implicit fallthrough). Need preservation of memory/free pointer and bounds through
all external routines. Buy report PCs6413–6744, public entry808. Read exact blocks before tracing.

## Checkpoint: buyCollateral complete

QuoteFinishEvm / QuoteInternal now expose QuoteRunBounded, cometQuoteFinishBounded,
cometQuoteAfterAssetBounded, and cometQuoteInternalBounded while preserving old interfaces.
Internal quote succeeds with free <= initial+576+768*numAssets; its input requires
free+832+768*numAssets<2^64. QuoteCollateral regression built (quote-bounded-build.log,3565jobs).
Bounded internal quote axiom audit native1124, no unexpected axioms or warnings.

CollateralReservesTrace wraps the existing collateral reserves query with wordCallResult and
TransferInRun; output free=input+32 with free<=memory.size. LSP clean and
collateral-reserves-trace-build.log completed3571jobs.

BuyCollateralModel defines staged traces from lock/pause/reserves to transfer-in, quote,
collateral reserves, safe128, transfer-out, event, and reentrancy-after. BuyCollateralFrames,
TailSource, Source complete all source paths, including public calldata prologue/fallthrough.
Source audit standard3 only. Bytecode helper files BuyCollateralTransferEvm, QuoteEvm,
ReservesEvm, Internal, Evm all complete. Uses total memory bound free+928+768*numAssets<2^64.
BuyCollateralCalldata proves the address,uint256,uint256,address decoder and adds reusable
decodeScalarWord_calldata_uint256. BuyCollateral.lean original theorem/docstring preserved,
proof complete. Audit native3906, no unexpected axioms or warnings. All new files LSP clean;
buy-collateral-complete-build.log **Build completed successfully(3679jobs)**.

Now67/68ABIs complete,136/139originalholesfilled. Only3sorries remain:
Absorb.lean,Constructor.lean,Correct.lean fallback. No build sessions running. No semantic blocker.
NextAbsorb: sourceinternal487ff,public1270ff. absInternal16978–17912; outer16664–16977;
publicentry898. Requires two loops (assets, accounts), seized collateral storage writes, checked
divPrice (not yet proved), base repayment/accounting, liquidation events, liquidator points update.
gasleft source is nondeterministic letGas, can choose actual GAS results; not a mismatch.
Existing collateral-check, principal, price, repay/supply, and storage machinery should be reused.

## Checkpoint: Absorb settlement and collateral valuation

Absorb public scaffold is still the next ABI; 3 original holes remain. The full tail from
PC17240 through principal conversion, updateBasePrincipal, clearing membership, repayment,
debt arithmetic, and events is complete in AbsorbFinishModel/Source/Evm. Supporting modules:
AbsorbBalance*, AbsorbClearMembers, AbsorbTotalsEvm, AbsorbRepay*, AbsorbSettlement*,
AbsorbDebt*, AbsorbEvents*, SignedSubNonnegLeftEvm, Unsigned256Revert,
InternalPreservingOutcome, InternalFrameResult, MemoryLoadPreservation.
absorb-finish-build.log completed3689jobs; cometAbsorbFinish audit native2001, no unexpected
axioms or source warnings. Balance and repay builds/audits also passed.

AbsorbSeizeModel/Source/UserEvm/TotalsEvm/Evm complete the ordered storage update17630→17713:
read user balance, clear it, then read and subtract from collateral total. No slot noncollision
assumption. absorb-seize-build.log completed3613jobs; audit native212, no unexpected axioms.
Seize memory is twoWordHashMem asset2 after userCollateralMemory (three scratch hashes).

AbsorbCollateralMathModel/Source/FactorEvm/MathEvm (actual filenames use
AbsorbCollateralFactorEvm and AbsorbCollateralMathEvm) prove price multiplication,
liquidationFactor192 multiplication, and checked addition to deltaValue, including every revert.
AbsorbCollateralEvent proves source emit and EVM17811→17567, normalizing memory to pairEventMem.
AbsorbCollateralPriceModel/Source/Evm compose price-feed query17713, math17736→17811, event.
The successful price run grows free pointer by160, has free≤memory.size, and preserves all
complete words in the original memory prefix above scratch and below the original free pointer.
cometAbsorbCollateralPrice audit native547, no unexpected axioms/warnings.
absorb-collateral-price-build.log build initiated; check completion before recording passed.

Next: connect getAssetInfo17578→17589, mapping prefix17589→17630, seizure, and price/event into
one asset-loop iteration; then loop17110 induction, absorbInternal prefix16978, finish tail,
public accounts loop, points accounting, decoder. Constructor and Correct fallback follow.

Lean performance lessons: an inferred `have` whose type is an `if` can eagerly reduce a huge
calldata-word Decidable expression. Name the instance and mark it locally irreducible in callers
(absorbCollateralMathDecidable/absorbCollateralWordsDecidable in PriceEvm), or use abstract word
parameters in the reusable routine. This fixed the timeouts without increasing heartbeats.
For equality of outcome-to-ExecResult wrappers, prove it on abstract UInt256 arguments first;
substituting nested repayment expressions before rfl caused kernel deep recursion (AbsorbRepayResult).
Use simp only[Bool.false_eq_true,if_false,internalMemoryRun] when propagating static outcomes across
different memories/return PCs; bare exact can expand huge irrelevant memory expressions.

## Proof checkpoint: absorb asset loop and internal function, 2026-10-09

Completed the selected-asset composition, bounded asset loop, and full internal absorb routine.
`AbsorbAsset*`, `AbsorbAfterAsset*`, `AbsorbLoop*`, `AbsorbAfterLoop*`, and `AbsorbLoopTail*`
connect seizure, collateral price/arithmetic/event, loop control, balance, and settlement.
The correct loop stack is `[i, reserved, assets, oldBalance, oldPrincipal, basePrice, account,
delta, basicPtr, absorber, ret, R]`. Selected iterations allocate at most 928 bytes.

`UserBasicNormalized.lean` proves that sign-extending a packed principal preserves its source
value and memory representation. `AbsorbReadModel/Source/Evm.lean` connects snapshot allocation,
presentValue (including its minimum-principal revert), and membership-bit reads. The
`AbsorbBasePrice*` files connect the base-price call and loop initialization while preserving the
snapshot. `AbsorbInternalModel/Source/Evm.lean` and `AbsorbReadTailEvm.lean` prove the complete
16978-to-return internal function, including the liquidation check and all failure outcomes.
`absorbInternalCallable_lookup` checks the assembled body against the existing spec by `rfl`.
`absorbInternal_call` supplies the modular source call for the public accounts loop.

Validation: all new files have clean LSP diagnostics. Targeted builds passed: asset loop
3658 jobs, loop plus settlement tail 3762 jobs, and full internal source/EVM 3795 jobs.
`cometAbsorbInternal` audit: 4399 axioms, only standard and accepted native evaluation facts,
no unexpected axioms or source warnings. The source-call wrapper has four axioms, likewise
only standard/native facts. Logs: `absorb-loop-build.log`, `absorb-loop-tail-build.log`,
`absorb-internal-build.log`.

Next: public accounts loop and gas/points accounting, ABI decoder, then Absorb BodyCore.
The internal EVM helper has explicit free-pointer bound
`free + 480 + 1856 * numAssets + 256 < 2^64`. Investigating the public array decoder and
resource bounds before selecting the outer-loop invariant; no new assumptions have been added.
The three original remaining holes are still Absorb, Constructor, and Correct fallback.

## Pending user decision: public absorb resource boundary, 2026-10-09

The decoder limits do not establish the allocation budget needed for repeated absorbInternal
calls. `AbsorbResourceReview.txt` records the bytecode PCs, a concrete arithmetic witness,
why the unrestricted gas parameter does not force out-of-gas first, and the limits of this
investigation (no full counterexample to existential refinement has been certified).
No spec or scaffold statement has been changed. An asynchronous approval question is pending:
(1) model allocation failures while preserving the unrestricted theorem (recommended), or
(2) explicitly narrow the theorem with the stated resource precondition.
The user has not answered this new question yet. The earlier "I approve" applies only to the
previous immutable uint8 bounds; it does not authorize this new change.
This is the first turn with this blocking decision. Do not mark the goal complete or add an
assumption. Do not resume dependent proof edits until the user resolves the boundary.

Blocked audit update, 2026-10-09: the same allocation-limit decision remains unanswered after
three consecutive goal turns (the discovery turn and two automatic continuations). The last
continuation was no progress, not a verified process wait. The current files still contain the
same resource obligation and three original holes. The goal is being marked blocked pending
the user's choice; completion is not claimed. A later resumed goal starts a fresh blocked audit.

## Gas-bound approval and main integration, 2026-10-09

The user explicitly requested: "Please pull the latest main to narrow the theorem with a resource
bound on gas." This resolves the allocation-bound decision above; do not ask for that approval again.
HTTPS fetch updated origin/main to 35fab7c8 (wf-gasBound PR29). Merge f838742a integrated it into
commet without conflicts. All 854 prior modified/untracked local files were hash-verified unchanged.
Backup: /tmp/comet-main-integration-xx01ocvn/local-work.tar.gz, manifest.json and tracked.patch.

GasBound.lean defines cometGasBound, proved equivalent to gas.toNat < 8916549292636669 (>2^24).
It is the largest bound supported by the current worst-case per-account allocation estimate and
the proved public-loop overhead: 473760 bytes/account, 214 gas before absorbInternal, 15 gas on the
back edge. Specifically, 128 + ((gas + 15) / 229) * 473760 + 256 < 2^64.
absorbMemoryBudget_entry and _exit prove the necessary arithmetic bounds.

Correct.lean now exports runtimeRefinementWithWF trivialStorageWF cometGasBound and
contractRefinementWF trivialStorageWF cometGasBound. AbsorbBody receives hgas; the other 67 ABI
theorems and constructor statement remain unchanged. The three original sorries still remain.

New proved helpers:
- RemainingGas.lean: X_eq_of_gas_lt_fuel; rd_remainingGas; RunRemainder.start/compose/revert/
  staticViolation/sourceIn/sourceOut. Rebasing a helper at the cursor's remaining gas allows
  adding its local consumed cost back to the caller even when the helper existentially hides cost.
  compose returns outer RD with k = C + k' and cost = C + C'. This is valid by fuel independence.
- InternalCostBoundedOutcome.lean: internalCostBoundedRun and internalBoundedRun.fromRemaining.
- AbsorbInternalGas.lean: cometAbsorbInternal_cost and absorbMemoryBound_or_outOfGas.
  The latter explicitly establishes OOG if the resource bound fails under the cost invariant.
- AddressDecodeCost.lean: cometValidateAddress_cost, exact k+12 and C+46.
- AbsorbAccountsControl.lean: AccountsRead (k+39,C+141), AccountsEnter (k+58,C+214),
  AccountsIncrement (k+4,C+15), AccountsExit (k+6,C+23).
  Header stack: [ofNat i, base, 1, absorber, ofNat n] ++ R.
  Internal call stack: [absorber, accountWord, 16972, ofNat i, 1, base, 1, absorber, ofNat n] ++ R.
  Use loop invariant 229*i <= C and free <= 128+i*absorbAllocationPerAccount when assembling it.
  The public loop and points tail are not assembled yet.

Validation: gas-bound-build.log completed successfully (4235 jobs), including Correct, DiffTarget,
AbsorbInternalGas and AbsorbAccountsControl. Gas arithmetic and RunRemainder.compose audit use
only the standard three axioms. Internal_cost audit: native,4399 axioms,unexpected[]. AccountsEnter:
native,81 axioms,unexpected[]. No new sorries, bytecode edits or custom axioms.

## Historical certified static-call/ABI mismatch (scope subsequently approved)

While connecting the public loop, inspection showed ABI/Decode.lean eagerly validates every address
in address[]; solc validates elements lazily at runtime PCs16557/1393, after accrueInternal. A static
call can reach an SSTORE in accrual before the first element is inspected. This is not repaired by
any conventional upper gas bound above2^24, since the concrete failure uses3000000 gas.

AbsorbStaticDecodeWitness.lean is a compiled, sorry-free proof of:
  NOT runtimeRefinementWithWF trivialStorageWF cometGasBound config
    (deployedRuntime zeroImms) contract (immStore zeroImms).
Witness: valid all-zero immutable valuation, gas3000000, empty storage, timestamp1, perm=false,
calldata selector38 followed by absorber0, offset64, length1, and dirty address2^160 (132bytes).
evm_static certifies actual Xi=.error.StaticModeViolation; calldata_selects and
calldata_does_not_decode certify eager decode failure; gas_within_bound proves admission.
The generic no_refinement_of_static_decode_failure rules out all refinement constructors, including
fallback/receive. runtime_refinement_fails then refutes the newly narrowed universal runtime claim.
Audit:7 axioms (standard3 plus four native_decide certificates), no sorryAx/custom axioms/warnings.
An independent executable check using the constructor-derived diffTarget reproduces the same
DISAGREE, so this is not confined to the all-zero immutable valuation.

An asynchronous question asks the user to choose:
1. Fix shared ABI/Solm address-array decoding to validate elements on access (recommended; expands
   edits beyond Comet, contrary to Misc/prompt.md's current directory scope).
2. Also narrow the theorem to exclude static absorb calls whose calldata fails to decode.
Do not assume the earlier gas-bound approval authorizes either new change. No source/model or
additional precondition was changed. This is the FIRST goal turn with this NEW blocking decision;
the previous allocation blocker is resolved. Keep the goal active, not complete/blocked yet.

Second consecutive goal turn on the static-call mismatch: rechecked the witness with Lean LSP;
it still compiles and refutes the gas-bounded runtime statement. Read-only scope review confirms
there is no Comet-local decoder hook in Config and no independent selector override in
TransitionDecl. Body edits cannot affect the failed entry decode. Shared bool[] handling provides
an existing lazy-word mechanism, but address[] changes also need a review of memory/return-data
decoding. Details are appended to AbsorbResourceReview.txt. The user has not answered the scope
question. No dependent proof or shared-model edits were made. The previous turn was progress
(merge, gas-bound migration, checked resource helpers, and a certified new counterexample).
This is only the second consecutive turn for this blocker; leave the goal active at this point.

Third consecutive goal turn on the same static-call/ABI scope decision: the user has not selected
either resolution. Revalidated HEAD f838742a, unchanged shared decoder/semantics, the certified
runtime_refinement_fails statement and successful witness build, and the same three original holes.
The previous turn added scope-feasibility evidence; it was not a verified wait on a live process.
No further proof progress is possible under the present, refuted statement. The scope approval is
required to change shared decoding, or a further theorem restriction must be explicitly approved.
The blocked-audit threshold is now satisfied. Mark the goal blocked, not complete. A future explicit
resume starts a fresh blocked audit unless the user also resolves the scope decision.

## Decoder-mode approval, 2026-10-09

The user explicitly authorized adding a mode named for Comet's compiler, with changes restricted
to that mode, and requested rebuilding Solm/Reasoning only before continuing Comet. The new mode
is `DecodeMode.solc0815`, for solc 0.8.15+commit.e14f2714. The goal is active; the preceding scope
decision is resolved and must not be requested again.

ABI/Decode.lean adds new-mode cases. Its address[] branch keeps canonical addresses as values
and retains each dirty word in the existing raw-word tuple representation. The unchanged
normalizeRawBoolWord?/evalIndex? rejects that representation when the element is accessed
(a dirty address is at least 2^160, so it cannot be the valid bool words 0 or 1). This preserves
the bytecode's failure order without editing Solm's evaluator. Scalar addresses remain strict;
new-mode return-data decoding delegates to modern, retaining eager memory validation. Existing
modes are unchanged. The new mode routes static parameter lists through modern decoding in
decodeCalldataWithMode, preserving the existing scalar proofs. Reasoning/ABI.lean adds only the
new constructor cases required by exhaustive proofs. Comet's config selects solc0815.

AbsorbStaticDecodeWitness now explicitly uses baselineConfig with modern, preserving the
original counterexample. Solc0815Regression checks the same input and adjacent boundary cases;
Solc0815Decode provides array length, word-access and lazy-validation lemmas for the public loop.
Validation is in progress. Do not build Examples, other benchmark targets, or solm-difftest
(its main executable imports other benchmarks); use Comet-only regression imports.

Validation completed: solc0815-core-build.log builds Solm and Reasoning (3490 jobs).
solc0815-comet-build.log builds Correct, AbsorbInternalGas, AbsorbAccountsControl and the
new-mode regression targets (4238 jobs). No Examples or other benchmark modules were built.
All ten Solc0815Regression cases agree, including the original static-call mismatch, writable
and non-accruing dirty-element failures, strict scalar validation, truncated arrays, oversized
offsets/lengths and empty arrays. Return-data arrays remain strict. cases_agree uses only the
standard axioms and one native_decide certificate.

The public absorb proof is moving again. New checked files:
- Solc0815Decode: bounds, length, per-element read and evaluation lemmas for the new mode.
- AbsorbCalldata: exact tuple acceptance conditions, valid/invalid decode lemmas and array access.
  AbsorbCalldataValid requires head size >=68, total calldata size <2^255, canonical scalar
  absorber, offset/length <=2^64-1, and the length word and payload within calldata. PC5552's
  signed comparison against full calldata size justifies the stricter <2^255 bound.
- AbsorbDecodeWords/AbsorbDecode: EVM decoder5508->16664, exact k+76/C+278 on success; all
  invalid cases revert. cometDecodeAbsorb audit: native,175 axioms, no custom/sorry axioms.
- AbsorbAccountsModel/Evm: full public accounts loop16695->16703. Each successful iteration
  preserves consumed gas >=229*i and free <=128+i*absorbAllocationPerAccount. The entry bound
  is proved or the actual global execution is OutOfGass. The exit has free+256<2^64 for points.
  Initial free may be mem.size+32; the loop postcondition preserves that permitted gap.
  cometAbsorbAccounts audit: native,4470 axioms including accepted bv_decide certificates;
  no sorry/custom axioms. Build: absorb-accounts-evm-build.log.
- AbsorbAccountsSource: source while-loop proof from the same trace, including malformed-element
  argument reverts and internal static violations. Its final frame retains accounts, absorber,
  startGas and i=accounts.length. Build: absorb-accounts-source-build.log.

The public absorb proof is now complete. AbsorbBeforePoints{Model,Evm,Source} connects pause,
accrual and the accounts loop. LiquidatorPoints{Data,Memory,Allocation,Packed,StoreEvm} proves
the four-field source/memory/storage representation, including equivalence of four packed
source writes to the compiler's one SSTORE. AbsorbPoints{Model,CountsEvm,CountsSource,SpendEvm,
SpendSource,Evm,Source} covers all counter and spending overflow branches. AbsorbAfterAccounts
connects the gas reads/subtraction; AbsorbTrace, AbsorbInternalBodyEvm, AbsorbSource and AbsorbEvm
assemble the full function. Absorb.lean has no sorry and consumes cometGasBound.

Validation: absorb-complete-build.log builds Correct successfully (4279 jobs), still only Comet.
cometWithExtendedAssetListAbsorbBody audit: 6440 axioms total, standard axioms plus accepted
native_decide/bv_decide certificates, no sorry/custom axioms and no source warnings.
The fallback proof is now complete as well. DelegateCallReach/Bridge prove the call and
call-depth failure semantics locally in Comet; FallbackMemory proves arbitrary-length copy/read
identity; FallbackDispatch handles all 68 misses and short calldata; FallbackEvm/Source/Fallback
join the success/revert branches. Correct.lean's no-dispatch theorem uses cometFallbackRefines.
Validation: fallback-complete-build.log builds Correct successfully (4286 jobs). Fallback audit:
497 axioms, standard3/native_decide only. Full cometWithExtendedAssetListRuntimeCorrect audit:
19159 axioms, standard3/native_decide/bv_decide only, no sorry/custom axioms or source warnings.
The sole remaining sorry is the zero-call-value constructor branch (Constructor.lean:21).


## Constructor input-size boundary, 2026-10-09

ConstructorDeployment proves successful encoding preserves argument count and exposes the ABI
tail. ConstructorEncoding provides scalar/tuple inversion and prefix encoding lemmas.
ConstructorNonpayable completes the nonzero-call-value branch; Constructor.lean now uses it.

The zero-value constructor proof uncovered a separate input-domain issue. The constructor
refinement admits arbitrary initcode length, unlike the runtime calldata-size premise. The
unchanged deployment encoder can accept an asset array with 2^256 entries. Its array length
word is zero, its initcode CODESIZE word equals the empty-array deployment's word, and the first
736 argument bytes equal that empty-array encoding. The source array length remains 2^256 and
fails the <=24 guard. This is not fixed by a gas bound: the wrapped EVM copy size is only736.

ConstructorSizeWitness proves, symbolically for arbitrary n, the exact admitted configuration
encoding, then specializes arithmetic to n=UInt256.size. The checked declarations are:
- deployment: config.selfDeployment accepts the configuration, for every n.
- encodedArgs_length: ABI argument bytes =736+224*n.
- encodedLength_wraps / encodedPrefix_wraps: the length word and copied argument prefix agree
  with n=0 when n=2^256.
- codesize_wraps: the CODESIZE words agree.
- source_length_rejects / bytecode_length_accepts: the length guards disagree.
- admittedInput_wraps bundles encoder admission, actual oversize, and the three collisions.
This certifies the input/guard collision, not a complete negation of constructor refinement or
an actual full Xi execution of the huge symbolic deployment. Do not overstate the witness.

Validation: constructor-size-review-build.log builds Correct and ConstructorSizeWitness (4292
jobs); sole sorry remains Constructor.lean:21. admittedInput_wraps audit has9 axioms, standard3
plus native_decide only, no custom/sorry axioms or source warnings. No Examples/other benchmarks
were built. Decoder and shared model code were not changed further.

A pending asynchronous question requests approval to restrict Comet's selfDeployment to initcode
size <2^256. ConstructorSizeBound.proposed.patch is the exact proposed Spec.lean change; it has
NOT been applied. It would require adapting ConstructorDeployment's extraction lemma and
adding a size-bound lemma before continuing the constructor. This changes the theorem's admitted
deployments and needs explicit approval; the earlier gas-bound approval applied to runtime calls.
No further dependent constructor proof work until resolution. This is the FIRST goal turn on
this new boundary decision. Leave the goal active, not complete/paused/blocked.


Second consecutive goal turn on the constructor input-size decision: the active config remains
unchanged at f0a29d8a; the proposal is still unapplied and no approval has arrived. The previous
turn was progress (complete fallback/runtime proof and a new checked boundary witness).

This turn completed review-only validation in ConstructorSizeBoundReview.lean:
- boundedDeployment_eq_some_iff proves that the proposal admits exactly the existing encodings
  whose resulting initcode is smaller than 2^256 bytes.
- boundedDeployment_shape carries the original argument-count/ABI-tail facts plus the size bound.
- ordinaryDeployment_preserved covers every member of the witness family below the cap.
- wrappingDeployment_rejected proves that the oversized symbolic witness is excluded.
The definition is not connected to the active Comet config. The proposed patch remains unapplied.
Targeted build passed (3500 jobs), constructor-size-bound-review-build.log. Rejection audit:
9 axioms, standard3 and native_decide only; no custom/sorry axioms or source warnings.
No builds are running. No changes to ABI, Solm, Reasoning, or the active Spec config this turn.
The original zero-value constructor hole remains at Constructor.lean:21. Further dependent proof
work needs the user's decision. This is only the second recurrence; leave the goal active.


Third consecutive goal turn on the same constructor input-size decision: revalidated unchanged
active Spec.selfDeployment, the unapplied proposed patch, HEAD f0a29d8a, the successful review
build, and the sole remaining Constructor.lean:21 sorry. No user approval or external-state
resolution has arrived. The previous turn made progress by completing checked proposal proofs;
there is no running build to await and no further independent prerequisite to complete. Applying
the guard or otherwise changing the admitted constructor inputs requires the user's decision.
The blocked-audit threshold is satisfied. Mark the goal blocked (not complete). Resume with the
original full objective after an explicit decision; apply no domain change by default.

## Separate bounded relation approved; constructor resumed, 2026-10-09

The user resolved the preceding decision by asking for a copy of the constructor-refinement
relation with the bound, rather than changing the deployment encoder. They also explicitly
set the full proof goal active. No further scope approval is needed for this choice.

`Solm/RefineWithCodeBound.lean` adds `typedConstructorRefinementWithCodeBound`, an exact copy
of the original universal deployment relation with the additional premise
`I.code.size < Ethereum.UInt256.size`. `contractRefinementWFWithCodeBound` carries the same
deployment domain into whole-contract correctness. Its `of_runtime` theorem uses the existing
fixed-input execution/deployment relations. Both original relations imply their bounded
copies via `.withCodeBound`. The new module is exported by `Solm.lean`. The original
`Solm/Refine.lean`, `Spec.selfDeployment`, ABI decoding and runtime predicates are unchanged.
Comet's constructor/capstone use the new copies. The old encoder-guard proposal and
ConstructorSizeBoundReview remain historical, unapplied alternatives: do not apply that patch.

Proof continuation completed:
- ConstructorDeployment: bounded shape extraction and `cometConstructorCodeSize`, proving
  the actual `CODESIZE - 21425` equals the ABI-tail length under the new bound.
- ConstructorInput: typed ConstructorAsset/ConstructorConfig records and full successful-encoding
  inversion, including every array element. `cometConstructorInput` uses only standard3 axioms.
- ConstructorInputEncoding: exact general encoding (736+224*n bytes), not just the earlier
  witness family; `cometConstructorBoundedInput` gives the canonical config and
  `22161 + 224*c.assetConfigs.length < UInt256.size` for every admitted deployment.
- ConstructorAllocationWords: argument-size/count casts, exact first allocation end
  `1664+224*n`, and both outcomes of its 64-bit guard. The 64-bit check remains an execution
  branch; it is not a new theorem premise or a deployment filter.
- ConstructorEntry: creation blocks0→13→2711, initial allocation success→33 or panic/revert.
- ConstructorMemory: exact CODECOPY memory, its size, arbitrary argument-word reads,
  the outer offset32 and free-pointer reads. No restriction on array contents or selected words.
- ConstructorDecodeHead: creation blocks33→49→66→82→2711. `cometConstructorDecodeStart`
  composes the full prefix, including the first allocation failure. On success it reaches
  the record allocator with stack `[free,672,99,928,32,argSize,free]`, where
  `free=1664+224*n` and `argSize=736+224*n`. Main Constructor.lean consumes this theorem.

Validation: `constructor-code-bound-core-build.log` builds Solm/Reasoning (3491 jobs).
`constructor-bounded-head-build.log` builds Correct with all new active helpers (4298 jobs).
Earlier `constructor-bounded-entry-build.log` also checked ConstructorSizeWitness (4297 jobs).
No Examples or other benchmarks were built. The new relation's `of_runtime` audit is standard3
only. Bounded-input audit:7 axioms; decode-start audit:397 axioms. Both use only standard3 and
accepted native_decide certificates, with no sorry/custom axioms or source warnings.
The sole remaining sorry is Constructor.lean:27, in the zero-call-value branch. Runtime remains
complete. The whole-contract theorem is not complete and must not be reported as proved.

Next: decode the configuration record from the `cometConstructorDecodeStart` cursor. The next
672-byte allocation can also fail; retain that case. Success returns to99, then the five address
fields via2747/2767, twelve uint64 fields via2768/2788, three uint104 fields via2789/2809,
then the dynamic asset array. `constructorCopiedMemory_load` gives all canonical input words;
use write preservation while constructing the record. Later connect the full constructor source
execution, external calls, immutables and runtime-bytecode patch/return. A source reversion proof
for oversized asset arrays must accompany allocator failures; the EVM prefix alone does not
close those constructor-refinement branches.

## Constructor record and asset-array entry proved, 2026-10-09

The previous goal turn was progress: the bounded relation and constructor entry were verified.
This continuation completes the next constructor segment without adding proof holes or changing
the specification, decoder, refinement statement, bytecode, or block summaries.

New checked modules:
- ConstructorAllocate: reusable creation allocator at2711, with both success and panic/revert;
  record allocation guard is exactly `constructorRecordBase c + 672 < 2^64`.
- ConstructorScalarRead: memory-reader routines2747/2767,2768/2788,2789/2809,2810/2824 for
  addresses, uint64, uint104 and uint8. Each has explicit canonicality, read and return-jump facts.
- ConstructorRecordMemory: `constructorRecordBase c =1664+224*n`; `constructorScalarMemory c i`
  writes the first i scalar fields starting at that base. Proves size, MemoryPrefix preservation,
  arbitrary encoded-word reads, scalar reads, array offset/length and free-pointer reads.
- ConstructorDecodeAddresses/Uint64/Uint104: all twenty fixed fields decoded, using the existing
  summaries and scalar-reader lemmas. The last field remains on the stack at531 until stored.
- ConstructorDecodeScalars: stores that last field and validates offset672, reaching562 with
  memory `constructorScalarMemory c 20`. `cometConstructorDecodeRecord` includes all earlier
  allocation failures. Original definitions/statements remain as authorized.
- ConstructorAssetHeader: validates the array head and canonical length, reaches the array
  allocator at2711. Record allocation success already implies n<2^64, so its length check passes.
- ConstructorAssetAllocation: `constructorArrayBase =recordBase+672`,
  `constructorArrayEnd =arrayBase+32+32*n =2368+256*n`. The pointer-array allocation succeeds
  iff arrayEnd<2^64; otherwise the actual EVM execution reverts or runs out of gas.
- ConstructorAssetEnter: proves the payload-end check is exact equality to the copied argument
  end, stores the array length, reaches the element loop664. `cometConstructorDecodeToAssets`
  composes the complete prefix with all preceding allocation failures. Constructor.lean now
  consumes it. Its success stack is
  `[672,32,ofNat(arrayBase+32),928,argSize,ofNat n,1664,ofNat arrayBase,ofNat recordBase]`,
  memory `constructorArrayHeaderMemory c`, and existential aw/k/C. No new domain restriction.

Validation: constructor-array-allocation-build.log passed4308 jobs; constructor-assets-enter-build.log
passed4309 jobs for Correct, Comet only, including the final whitespace-only formatting changes.
`cometConstructorDecodeToAssets` axiom audit:1688 total, standard3/native_decide only, no
sorry/custom axioms and no source warnings. Constructor.lean needs maxRecDepth2000 for the larger
composed prefix. The only remaining sorry is its zero-call-value branch, now at line28.

Next: prove the asset-element loop664→2494→2508→2711 (224-byte record allocation)→2524 and
the seven field readers/stores, through2656→664. Loop input cursor is1664+224*i, pointer-array
cursor arrayBase+32+32*i, and next record free pointer arrayEnd+224*i. Final successful free
pointer should be2368+480*n; retain allocator failure cases. After the loop,685 stores the array
pointer at recordBase+640, reads baseToken from recordBase+64, creates the decimals() calldata,
and reaches STATICCALL733. CreationBlocks_003 contains664/685;007/008 contain the asset loop.
Source constructor execution (including reversion for invalid/oversized configurations), external
calls, immutables and runtime patch/return are still required. Do not mark the full goal complete.

## Constructor asset loop and first call entry proved, 2026-10-09

This continuation completes argument decoding and reaches the base-token decimals STATICCALL.
It adds no new theorem-domain restriction and no proof holes. Decoder, shared libraries,
specification, bytecode and supplied block summaries were not changed.

New checked modules:
- ConstructorAssetMemory: asset word indexing at argument index23+7*i+j; the exact encoded
  input load at1664+224*i+32*j; the seven-field memory model and preservation of input words;
  pointer-array header size/free-pointer/prefix facts.
- ConstructorAssetFields: reusable full seven-field decoder2524→2656→664. It proves both
  address canonicality checks, uint8/uint64 checks and the inline uint128 check, stores all
  seven words and the array entry. Explicit input reads and disjointness prevent aliasing.
- ConstructorAssetLoopMemory: free(i)=arrayEnd+224*i, entry(i)=arrayBase+32+32*i, and recursive
  memory after i iterations. Proves sizes, free-pointer reads, and input-prefix preservation.
- ConstructorAssetLoop: one iteration664→2494→2508→2711→2524→664 with both allocator outcomes;
  induction over all remaining assets; exit to685. `cometConstructorDecode` composes every
  decoder step from creation entry. Success iff final free=2368+480*n is below2^64; otherwise
  RDrev. The 64-bit test is an EVM execution branch, not a premise of constructor refinement.
- ConstructorDecodedMemory: a generic consecutive-word read-back lemma, scalar/asset record
  read-back, preservation of config fields and the array header, final store of the array pointer
  at recordBase+640, and resulting free-pointer/config-field loads.
- ConstructorDecimalsEnter: block685 normalized to STATICCALL733, with target baseToken,
  input/output pointer ofNat(finalFree), input size4, output size32, and GAS argument exactly
  `(g.subNat C).toUInt256` at the resulting RD counter. Memory is constructorDecimalsMemory:
  decoded memory plus the decimals selector word at finalFree. `cometConstructorDecodeToDecimals`
  composes the full prefix, including all allocation failures. Constructor.lean consumes it.

Validation: constructor-assets-loop-build.log passed4317 jobs for Comet Correct, including all
new modules and final formatting changes. No Examples or other benchmarks were built.
`cometConstructorDecode` audit:2219 axioms; `cometConstructorDecodeToDecimals` audit:2327 axioms.
Both use only standard3/native_decide certificates, with no custom/sorry axioms or source warnings.
The only remaining proof hole remains Constructor.lean:28. Runtime is complete. Goal stays active;
these EVM prefix theorems do not yet establish constructor refinement.

Next: connect the first decimals call at733 to the source constructor, prove the postcall return
checks734→742→750 and decimals≤18, then storeFrontPriceFactor≤1e18, assets.length≤24 and nonzero
baseMinForRewards. Source execution, reversion for invalid/oversized configurations, the second
price-feed decimals call, extensionDelegate.assetListFactory, internal createAssetList_call,
immutables and runtime patch/return are still required. Prove createAssetList_call once as
ExecFuncBody and use the internal-call bridge as required by Misc/prompt.md. Source reversion
must accompany the EVM allocation-failure branches; do not report the prefix as full refinement.

## Constructor decoding and both decimals calls connected, 2026-10-09

`Constructor.lean` now consumes `cometConstructorInitialCalls`. All allocation failures, the
first decimals call/decode/check failures, the three configuration-check failures, and the
second decimals call/decode/check failures establish full constructor refinement by reverting.
The remaining single sorry starts at902, after matching source execution of body.take9.
No specification, decoder, relation, bytecode, block-summary or shared-library edits in this pass.

New checked modules:
- DecimalsCall: exact selector payload49/60/229/103 (kernel-decided selector identity), return
  decoding with both length and uint8 checks, and reusable source call success/revert witnesses.
- ConstructorSourcePrefix: typed Configuration struct, argument binding, source entry/config/
  decimals frames, and matching constructor prefix execution.
- ConstructorDecimalsCall/Memory/Response/Check: STATICCALL733 source/EVM bridge, exact call
  memory and return decoding734→742→2428→2442→2711→2457→2467→2810→2478→750, every short/dirty/
  failed branch, and decimals≤18 at750→764. Small allocator proves ptr+32 fits from finalFree<2^64.
- ConstructorSourceChecks/Oversized: every base-token call outcome yields source reversion when
  assets.length>24, so decoder allocation failures now close full refinement. The source call
  witness uses the actual input state's available gas and EVM invocation, not a forced failure.
- ConstructorFirstPhase: from initial state either full refinement, or matching body.take4 and
  EVM764 with source state/account-map relation and checked decimals response.
- ConstructorChecksMemory/Checks/ChecksSource: call preserves the config and array count;
  storeFrontPriceFactor≤1e18, assets.length≤24, baseMinForRewards≠0 agree on both sides;
  successful prefix reaches832 and source body.take7.
- ConstructorPriceFeedMemory/Call/Response/Check/Source: second decimals call uses the source
  state from the first call. STATICCALL871 returns at872; decode2303→2317→2711→2332→2342→2810
  →2357→888, check exactly8, then902. Every failed/short/dirty/wrong-value case reverts on both
  sides. Its free pointer is finalFree+32; successful allocation advances it to finalFree+64.
- ConstructorInitialCalls: composes the above, preserving all facts needed by the remaining
  constructor. Its success witnesses are evm',σ',out,feed,aw,k,C; finalFree<2^64,
  ConstructorChecksValid c, SourceState initial I σ' evm', out.size<2^138, out.size≥32,
  calldataWord out0≤18, feed.size<2^138, feed.size≥32, calldataWord feed0=8,
  ExecBlock initial body.take9 to constructorSourcePriceFeed c (calldataWord out0)8,
  and RD902 with stack `[calldataWord out0,ofNat recordBase]++constructorAssetLoopStack c n`
  and memory constructorPriceFeedReturnMemory c out feed. The EVM account map is σ'.

Validation: `constructor-initial-calls-build.log`: `Build completed successfully (4338 jobs).`
Only Comet Correct was built; no Examples or other benchmarks. New files are LSP-clean.
FirstPhase audit2749 and InitialCalls audit3491 axioms: only standard3/native_decide certificates,
no custom/sorry axioms and no source warnings. The sole remaining sorry is Constructor.lean:29.
Runtime remains complete. The whole-contract theorem is not yet proved; goal remains active.

Next:902 writes governor/pauseGuardian/baseToken/baseTokenPriceFeed/extensionDelegate to
128/160/192/224/256, storeFrontPriceFactor to544 and decimals to800, then988 computes
baseScale=10^decimals (uint64), writes576 and trackingIndexScale608, checks baseScale≥1e6 and
reaches1024 or reverts. Continue immutable initialization, delegate.assetListFactory STATICCALL1291,
the internal createAssetList_call proof (once as ExecFuncBody), factory CALL1393, and deployed
runtime patch/return. CreationBlocks_004 is now compiled; do not edit it. Preserve the generic
source/EVM external-call witnesses and prove both outcomes of every remaining check.

## Initial immutables and base-scale guard proved, 2026-10-09

Further progress in the same continuation: the sole constructor sorry is now at1024, after
matching source body.take19, not at902. The remaining path has6≤decimals≤18. The baseScale<1e6
branch now closes full constructor refinement with the actual EVM/source reverts.

New checked modules:
- ConstructorDataMemory: reusable predicate preserving all decoded words in the interval
  [recordBase,finalFree), including asset records and pointer table. Proved for both calls'
  resulting memory, preserved under writes below recordBase, with scalar/pointer/count reads.
- ConstructorInitialImmsSource: generic config-field evaluation; exact first seven immutable
  inserts (five addresses, storeFrontPriceFactor and decimals); source prefix9→16.
- ConstructorInitialImmsMemory: block902's exact seven writes normalized to
  constructorInitialImmMemory c w mem. Config reads remain valid between each write; address
  and uint64 masks preserve all canonical fields. Generic address/uint64 canonicality lemmas.
- ConstructorInitialImms: reusable902→988 RD summary with exact memory and generic stack tail.
- ConstructorScaleWords: EXP10 and uint64 masking equal10^decimals fordecimals≤18, with full
  natural-word conversion bounds. EXP cases are kernel-decided; baseScale≥1e6 iffdecimals≥6.
- ConstructorScaleEvm: block988, including both the scale guard outcomes; successful memory
  stores baseScale at576 and trackingIndexScale at608, preserving ConstructorDataMemory.
- ConstructorScaleSource: exact source EXP/casts, immutable type fits, assignments and check;
  source prefix16→19 or whole-constructor revert.

Constructor.lean consumes all of these. At its sole sorry(line44), hevm'' is RD1024 with stack
`[ofNat recordBase]++constructorAssetLoopStack c n`, memory
`constructorScaleMemory c w (constructorInitialImmMemory c w
  (constructorPriceFeedReturnMemory c out feed))`, wherew=calldataWord out0. `hm''` is its
ConstructorDataMemory proof; `hsource''` executes body.take19 to constructorSourceScale c w8.
The account map remainsσ', and SourceState initial Iσ'evm' is still available. hscaleLo gives6≤w.toNat.

Validation: `constructor-scale-build.log`: `Build completed successfully (4345 jobs).`
Only Comet Correct was built; all new modules are LSP-clean and formatted to100 columns.
Axiom audits: cometConstructorInitialImms200, cometConstructorScale183 (standard3/native_decide
only); constructorSourceInitialImms_exec3, constructorSourceScaleChecked_revert3 (standard3 only).
No custom/sorry axioms or source warnings in these audits. `git diff --check` passes.
Search still finds exactlyone sorry(Constructor.lean:44), no project-authored axioms. Goal active.

Next:1024→1119→1200→1279 initializes the remaining immutables, accrualDescaleFactor and
per-second rates, and prepares delegate.assetListFactory STATICCALL1291. Reuse ConstructorDataMemory
for config reads through immutable stores. Then prove the source internal createAssetList_call
once, bridge the factory CALL1393, and finish deployed runtime patch/return.

Engineering notes: generated memory expressions use raw ByteArray.write and ofNat constants.
Normalize with a local equation `word.toByteArray.write 0 mem off32 = writeWord mem off word`
plus `simp (disch := decide) only [UInt256.toNat_ofNat_of_lt, hwrite, ...]` before applying read
lemmas. `simp [← writeWord]` cannot refold a def. Normalize32*j in instantiated scalar-read lemmas.
`UInt256.ofNat255` versus`⟨255⟩` still defeats rw despite definitional equality; an explicit
`have hbyte : (⟨255⟩ : UInt256)=UInt256.ofNat255 :=rfl` fixes it. For source immutable writes,
use refine with an evaluation hole, then apply the field lemma; supplying the locals proof
too early can infer the old frame instead of the updated immutable store.

## Remaining immutables and factory getter proved, 2026-10-09

The constructor now reaches PC1308 and source body.take36. Its sole remaining sorry is the
successful factory-getter continuation; every factory-getter failure now closes full
constructor refinement. Runtime proofs and the decoder were not changed in this continuation.

New checked modules:
- ConstructorRemainingImmsMemory: canonical uint104 fields and uint64 rates; exact normalized
  memory/stack equations for blocks1024,1119,1200. `constructorRewardMemory` writes864,704,640,
  672,736; `constructorSupplyMemory` writes768,288,320,352,384; `constructorBorrowMemory` writes
  416,448,480,512,832. Config reads survive each write. Rates divide by31536000.
- ConstructorRemainingImmsEvm: exact1024→1291 trace, preserving the delegate and free pointer.
  `constructorRemainingImmMemory` composes reward/supply/borrow writes. Low complete reads
  ending at or below288 survive. The final GAS word equals `(g.subNat C').toUInt256`.
- ConstructorRemainingImmsSource: source prefix19→34, all remaining immutable assignments,
  type fits, and uint8 asset count; `constructorSourceDelegate_exec` adds statement34, giving
  source prefix35. `constructorSourceDivNat` and `constructorSourceAssetCount` work in arbitrary
  frames with the required expression/local facts.
- ConstructorFactoryCall: getter selector0x7042e2d8 and ABI encoding proved with `decide +kernel`;
  exact address-return decode; source success/failure; STATICCALL1291→1292 bridge. Source prefix
 35→36 yields `constructorSourceFactory c w feed factoryWord`; failure yields whole-body revert.
- ConstructorFactoryResponse: generic1292→1308 response decoder or RDrev. Handles failed call,
  short data, and noncanonical address. Successful stack is `[640,base,factoryWord]++R`.
  `constructorFactoryReturnMemory mem out ptr` is
  `writeWord (callOutputMem mem out ptr 32) 64 (ptr+32)`; the returned word atptr is proved.
- ConstructorFactoryMemory: concrete pointer `constructorFactoryPtr c = ofNat(finalFree+64)`,
  pointer bounds fromn≤24, and exact memory size and payload. `constructorFactoryBaseMemory`
  composes all immutable initialization over the price-feed return memory. Its size isptr.
  `constructorFactoryInputMemory` writes the getter selector atptr and has sizeptr+32.

At Constructor.lean's sole sorry (line75 before future edits):
- `w = calldataWord out0`, `6≤w.toNat≤18`; `feedWord = calldataWord feed0 = 8`.
- `hvalid : ConstructorChecksValid c` includesn≤24; `hbound` is still the complete initcode bound.
- `hevm5 : RD ...1308 [640,recordBase,calldataWord factoryOut0]++loopStack` with memory
  `constructorFactoryReturnMemory
    (constructorFactoryInputMemory c w out feed) factoryOut (constructorFactoryPtr c)`.
- `hsource4` executes body.take36 to
  `constructorSourceFactory c w feedWord (calldataWord factoryOut0)` in stateevm4.
- `hs4 : SourceState initial I σ4 evm4`, factoryOut.size<2^138,
  `hfactory : ConstructorFactoryReturnValid factoryOut` (size≥32 and word<2^160).
- The continuation must prove the internal helper once as ExecFuncBody, then bridge its
  internal call. It must not inline the helper in the constructor.

Next helper source AST (checked with lookupCallable?): params factory:address and
assets:dynamicArray(tuple(address,address,uint8,uint64,uint64,uint64,uint128)), returnsaddress.
Its body has7 statements: letpayload, letindex, while, lowLevelCall, requireok,
letresultAddress(abiDecodeaddress), returnresultAddress. Initial packed payload AST uses
fixedBytesLit[186,21,185,209], intLit32, and arrayLength local assets. The loop body's entry is
`index (var assets) (var index)`; packed append casts tuple components0and1 to uint256, while
components2..6 are direct tupleGet (the redundant source casts were lowered away). The loop
incrementsindex with plain binary.add. See AssetSource.lean for packed encoding, source call,
decode, and internal-call patterns; execWhile_var is available in Reasoning.SolmBody.

EVM1308 writes factory-call payload header: selector0xba15b9d1 atfree, offset32 atfree+4,
asset count atfree+36; stackat1358 is
`[0,n,arrayBase+32,free+68,free,factoryWord,free]++loopStack`.
Loop1358→2075→2150→1358 appends the7 asset words; CALL1393 and response follow. Finish immutable
assetList at896, runtime patch/copy1410→1505→1598→1696→1792→1890→1988 and deployed-code equality.
Do not edit supplied bytecode/blocks/spec Solidity, or build Examples/other benchmarks.

Engineering notes: `dsimp only` between source immutable-write steps reduces nested frame
projections and avoids a200k-heartbeat timeout. Conditional memory-preservation simp needs
`disch := (first | omega | (simp only [writeWord_sparse_size]; omega))`; a single unconditional
simp can fail on the plain disjointness premise. For generic pointers, `word_add_sub_left`
proves `(ptr+n)-ptr=n`; `usub_uadd_lit_cancel` only accepts explicit ofNat pointers.
AccountAddress.ofUInt256 differs definitionally from ofNat(toNat); use
`accountAddress_ofUInt256_eq_ofNat_toNat`. `Int.ofNat_lt.mpr` avoids opaque casts in omega.

Validation: `constructor-factory-build.log`: `Build completed successfully (4351 jobs)` after
final formatting. Only Comet Correct was built; the new modules have no warnings, and
`git diff --check` passes. Exactly one sorry remains in Constructor.lean; no axiom declarations
were added. Axiom audits: RemainingImms EVM619, FactoryResponse601 (standard3/native certificates
only), RemainingImms source3, Factory call5, Factory source success/revert3, Factory payload4.
No unexpected axioms or
source warnings. The whole-contract theorem remains incomplete; the goal remains active.

## Constructor and whole-contract proof complete, 2026-10-09

`cometWithExtendedAssetListContractCorrect` in `Correct.lean` is now proved, including the full
constructor. It uses the separate `contractRefinementWFWithCodeBound` relation, the existing
`cometGasBound` for runtime calls, and `trivialStorageWF`. The added deployment premise is
`I.code.size < UInt256.size`; the original refinement relations and deployment encoder remain
unchanged. The decoder continues to use the previously implemented `solc0815` mode.

The final constructor continuation is complete:

- `CreateAssetListSyntax`, `Payload`, `Loop`, `Source`, and `Internal` prove the full internal
  helper once as `ExecFuncBody`, including successful calls and all reverting responses, then
  bridge it to the constructor's internal call. `ConstructorAssetsSource` proves the final
  source assignment and whole-body success or revert.
- `ConstructorAssetReads` and `CreateAssetListEncoder`, `Memory`, `Head`, `Evm`, `Call`, and
  `Response` prove the exact seven-word asset loop, ABI payload, factory CALL, and response
  decoder. `ConstructorAssetsMemory` and `ConstructorAssetsCall` connect those generic routines
  to the constructor's allocated configuration. Failed calls, short returndata, and
  noncanonical addresses all close the corresponding full-constructor revert branch.
- `ConstructorRuntimeWindow`, `Memory`, `Parts`, `Start`, and `Evm` prove runtime copying,
  all 70 immutable patch writes, and the final RETURN. The copied 18,599-byte runtime template
  is checked against the creation artifact. Generic window/cascade lemmas connect the returned
  bytes to `immutableLayout.runtime`.
- `ConstructorFinalMemory` proves all 25 immutable memory words; `ConstructorFinalImms` proves
  the source values have the declared types and yield the same words. `ConstructorRuntimeFinish`
  identifies the returned code with the source immutables' deployed runtime. `Constructor`
  combines the final account-map agreement, source execution, and EVM success/out-of-gas cases.

Validation:

- `lake build Benchmarks.CompoundIII.Comet.Correct` succeeds (4,374 jobs), recorded in
  `constructor-complete-build.log`. No Examples or other benchmarks were built.
- LSP diagnostics for the constructor, final memory/immutable modules, runtime return, and
  top-level correctness are clean. A source scan finds no `sorry`, `admit`, or `axiom` in Comet's
  Lean files; `git diff --check` passes.
- Constructor axiom audit: 6,769 dependencies, all standard axioms or allowed concrete
  evaluation certificates. Whole-contract audit: 25,925 dependencies, comprising `propext`,
  `Classical.choice`, `Quot.sound`, and 25,922 concrete evaluation certificates. Neither audit
  reports `sorryAx`, custom axioms, or source warnings. The source helper body and final
  immutable type-bound proofs use only the standard three axioms.

No proof obligations remain. The supplied Solidity, bytecode, and generated block summaries
were not edited. No commit or push was requested or performed.
