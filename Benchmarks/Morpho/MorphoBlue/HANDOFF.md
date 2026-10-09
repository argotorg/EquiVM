# Morpho Blue proof status

The proof is complete (2026-10-09). All 28 public entry points, short/unknown-calldata
rejection, and the constructor are connected to `morphoContractCorrect` in `Correct.lean`.
The supplied top-level theorem statements are preserved.

Final verification:

- `lake build Benchmarks.Morpho.MorphoBlue.Correct` passed, **3952 jobs**.
- The contract directory contains no `sorry`, `admit`, or axiom declarations.
- `#print axioms morphoCorrect`: **11007 concrete native-evaluator axioms**, plus
  `propext`, `Classical.choice`, and `Quot.sound`; no unapproved axioms.
- `#print axioms morphoContractCorrect`: **11917 concrete native-evaluator axioms**, plus
  the same three standard Lean axioms; no unapproved axioms. This is the trusted base
  explicitly permitted by `Misc/prompt.md`.
- Every authored Lean module is in the `Correct` import closure and is below 2000 lines.
  Generated runtime/creation summary shards are excluded from that line-count check.
- The corrected specification's differential runs agreed on all **1575 generated cases**
  (544 successful) and all **66 supplemental scenarios** (56 successful).
- Changes are confined to `Benchmarks/Morpho/MorphoBlue/`. Temporary scratch files, native
  audit build artifacts, and development logs have been removed.

To reproduce the axiom check after the build:

```sh
lake env lean --stdin <<'EOF'
import Benchmarks.Morpho.MorphoBlue.Correct
#print axioms Benchmarks.Morpho.MorphoBlue.morphoCorrect
#print axioms Benchmarks.Morpho.MorphoBlue.morphoContractCorrect
EOF
```

## 1. Compiler settings and provenance

The sources were fetched afresh from
[morpho-org/morpho-blue, v1.0.0](https://github.com/morpho-org/morpho-blue/tree/55d2d99304fb3fb930c688462ae2ccabb1d533ad),
commit **`55d2d99304fb3fb930c688462ae2ccabb1d533ad`**. All 14 files in the import closure
match the verified deployment sources byte for byte. They retain upstream paths under
`../contracts/src/`; the compilation unit is `src/Morpho.sol`, contract `Morpho`.
No existing benchmark or other branch was used as a scaffold.

Deployment: Ethereum mainnet (chain ID 1),
[`0xBBBBBbbBBb9cC5e90e3b3Af64bdAF62C37EEFFCb`](https://etherscan.io/address/0xBBBBBbbBBb9cC5e90e3b3Af64bdAF62C37EEFFCb#code).
Etherscan returned HTTP 403 in this environment. The verified sources, compiler settings,
creation bytecode, constructor argument, and deployed bytecode were instead obtained from
the [Blockscout contract API](https://eth.blockscout.com/api/v2/smart-contracts/0xBBBBBbbBBb9cC5e90e3b3Af64bdAF62C37EEFFCb)
on 2026-10-08 (`is_fully_verified: true`). Evidence and source hashes are in
[`deployment.json`](deployment.json); [`deployment.hex`](deployment.hex) pins the returned code.

- Compiler: **`0.8.19+commit.7dd6d404.Linux.g++`**.
- Binary used: `/tmp/morpho-solc-0.8.19`, downloaded from the official solc-bin repository.
  SHA-256: `7a5c1d3dc9a8eba62bb2ec37192c9178ae5fe8a54a56e5573fd3c9c17cd9eb48`.
- Optimizer enabled, **999999 runs**; **via IR**; EVM **paris**.
- Default IPFS metadata hash (`--metadata-hash ''`), with deployment remappings
  `:ds-test/=lib/forge-std/lib/ds-test/src/` and `:forge-std/=lib/forge-std/src/`.
  These remappings affect metadata even though the import closure does not use them.
- Creation code: **16055 bytes**, identical to the deployment creation code excluding its
  trailing 32-byte owner argument, `0x937ce2d6c488b361825d2db5e8a70e26d48afed5`.
- **`runtime.hex` is byte-exact with all 15623 deployed bytes**, including the 53-byte metadata
  trailer. Its decoded-byte SHA-256 is
  `fd5aa16eea01735e0e33e51e913a27f7d5ed998adc0cec2bf1f9ea368d9e1bdf`.
  Solc's unpatched output is retained separately as `runtime.template.hex`. Filling its two
  immutable sites with the independently derived mainnet domain separator produces exactly
  `deployment.hex`; no other byte changes are made.

Run from the repository root. `--sources-root` is relative to the scaffold directory, so the
reproduction command uses `../contracts` and preserves the `src/` prefix needed for metadata:

```sh
python3 Benchmarks/Morpho/MorphoBlue/regenerate.py artifacts --solc /tmp/morpho-solc-0.8.19
python3 scripts/bytecode_report.py Benchmarks/Morpho/MorphoBlue --output Benchmarks/Morpho/MorphoBlue/Morpho.report.md
python3 Benchmarks/Morpho/MorphoBlue/regenerate.py skeleton
python3 scripts/scaffold.py check --dir Benchmarks/Morpho/MorphoBlue
python3 Benchmarks/Morpho/MorphoBlue/regenerate.py check-deployment
lake build Benchmarks.Morpho.MorphoBlue.Correct
```

Both check commands print only `ok` lines. The final `Correct` build succeeds. All 43 creation
summary shards also build; the runtime has 42 summary shards. The local regeneration adapter
selects the custom storage/ABI configuration, renders bytes32 immutable plumbing, and handles
the raw signature entry described below. Shared generators and semantics are unchanged.
Do not overwrite the repaired `SpecSyntax.lean` by rerunning the draft translator.

## 2. Differential runs and coverage

Lean toolchain: `leanprover/lean4:v4.29.0`. Seed: **2026**. Both commands exit successfully:

```sh
lake exe solm-difftest --only Morpho --count 50
lake env lean --run Benchmarks/Morpho/MorphoBlue/DiffScenarios.lean
```

```text
solm-difftest: 1 target(s), seed 2026, 50 cases per transition
Morpho: 1575 cases: 1575 agree (545 successful), 0 disagree, 0 stuck, 0 EVM out of gas, 0 spec out of fuel
  successful/cases: constructor 15/25, setOwner(address) 4/53, accrueInterest((address,address,address,address,uint256)) 0/52, repay((address,address,address,address,uint256),uint256,uint256,address,bytes) 0/56, supplyCollateral((address,address,address,address,uint256),uint256,address,bytes) 0/52, setFee((address,address,address,address,uint256),uint256) 0/53, DOMAIN_SEPARATOR() 51/55, feeRecipient() 45/55, enableLltv(uint256) 3/53, borrow((address,address,address,address,uint256),uint256,uint256,address,address) 0/55, enableIrm(address) 5/52, withdraw((address,address,address,address,uint256),uint256,uint256,address,address) 0/51, isAuthorized(address,address) 42/55, position(bytes32,address) 43/53, nonce(address) 49/57, extSloads(bytes32[]) 43/52, withdrawCollateral((address,address,address,address,uint256),uint256,address,address) 0/57, createMarket((address,address,address,address,uint256)) 0/53, owner() 44/53, idToMarketParams(bytes32) 38/51, supply((address,address,address,address,uint256),uint256,uint256,address,bytes) 0/54, isLltvEnabled(uint256) 41/54, liquidate((address,address,address,address,uint256),address,uint256,uint256,bytes) 0/54, flashLoan(address,uint256,bytes) 10/52, market(bytes32) 47/56, setFeeRecipient(address) 4/54, setAuthorization(address,bool) 22/55, isIrmEnabled(address) 39/53, stray 0/100

Morpho scenarios: 66 cases: 66 agree (56 successful), 0 disagree, 0 stuck, 0 EVM out of gas, 0 spec out of fuel
```

The exact standard-run coverage line is retained above and in [`difftest.log`](difftest.log).
The generic generator chooses independent market tuples and storage keys. Adding the requested
words and callees does not make its generated storage keys equal `keccak256(MarketParams)`.
Consequently its lending transitions usually fail the market-existence/enablement guards.
`DiffScenarios.lean` supplements that sampler using the unchanged target, config, bytecode,
and standard trace-replay comparison. It constructs two markets and maintains actual EVM
post-state across supply, collateral, borrow, repay, withdrawal, interest, fees, and liquidation.
Both ERC20 return conventions and all five callbacks are exercised. Liquidation covers partial
collateral seizure and the remaining-collateral/bad-debt branch. The complete supplemental
coverage line is in [`scenarios.log`](scenarios.log).

Every externally callable operation other than successful signature authorization has successful
coverage across the two runs. `setAuthorizationWithSig` has **no successful signature or
ecrecover differential coverage**: this machine cannot execute that precompile. The 10 additional
signature cases stop before ecrecover and test expiry, nonce, truncation, dirty authorization
booleans, and delayed `v` validation in both permission modes. Their `0/10` successful count is
intentional: expected outcomes are reverts or static-mode violations. Stray calldata likewise
has no successful outcome because the bytecode rejects unknown selectors.

The constant-return IRM/oracle/token/callback fixtures exercise call boundaries and decoding;
they are not specifications of real counterparties. A cold native executable build needs a C
compiler and development headers. This container initially lacked them; temporary build tools
and headers under `/tmp` were used, without repository build-system changes.

## 3. Where the specification follows bytecode

- **Delayed signature decoding:** `setAuthorizationWithSig`, selector `0x8069218f`, increments
  nonce at runtime pc **6060**, then validates the calldata `uint8 v` at **6361–6371**.
  An eager typed decoder incorrectly reports decoding failure for a static call with dirty `v`;
  the EVM instead reaches `SSTORE` and raises `StaticModeViolation`. The spec uses a raw bytes
  fallback entry restricted to this selector, decodes `Authorization` before the deadline and
  nonce operations, and decodes `Signature` afterwards. All other unmatched/short messages
  revert. This models an existing selector; the deployed contract has no Solidity fallback.
- Nonpayability, calldata validation, code-existence checks, and the `extSloads` array allocation
  bounds are explicit or supplied by the modern ABI decoder. The calldata signed-size upper
  bound is `2^255 + 4`. The raw-array allocation includes the free-memory-pointer bound at
  pc 11535, before allocating or reading slots.
- Checked arithmetic and explicit narrowing follow the bytecode. Packed uint128 writes remain
  separate and in order; the later fields reload storage after earlier writes. Whole
  `MarketParams` assignment writes the five fields in declaration order.
- `_isSenderAuthorized` short-circuits the mapping read when the caller equals `onBehalf`.
  Safe transfers check code, make the low-level call, require success, and decode a bool only
  for nonempty returndata. IRM/oracle calls rely on their return decoding rather than adding
  a code-existence check the compiler does not perform. Callback calls check code first.
- `extSloads` uses a synthetic final `rawSlots` declaration whose backend addresses physical
  words directly; it allocates no protocol storage field. Hashing uses packed, explicitly
  padded 32-byte words and the two-byte EIP-712 prefix. These model source assembly/builtins
  without changing their effects. Revert payloads and event logs use the framework's existing
  abstraction; emit statements retain arguments and static-mode behavior.

The block-by-block runtime and constructor audit is complete. The signature ordering finding
was fixed and the differential runs repeated afterwards. No audit worksheet is included.

## 4. Proof structure and implementation notes

The immutable is `DOMAIN_SEPARATOR : bytes32`, inserted at runtime offsets **6282** and
**9401**. Its mainnet value is
`0xec6ac4ec6469375712b671d38548b711c7a4a17b4db99be41e0eb9f28cafdd2d`, derived as
`keccak256(abi.encode(EIP712Domain typehash, uint256(1), deployment address))`.
The generic constructor/runtime theorem still quantifies over valuations and patches both sites;
the bytes32 value in the Solm immutable store must use fixed bytes, not an integer value.

`SpecSyntax.modelExternalABI` contains the nine actual callee ABIs. `MarketParams` below means
`(address,address,address,address,uint256)`; `Market` means six `uint128` fields in storage order.

| Callee ABI | Selector | Mode / result |
| --- | --- | --- |
| `borrowRate(MarketParams,Market)` | `0x9451fed4` | CALL / uint256 |
| `price()` | `0xa035b1fe` | STATICCALL / uint256 |
| `onMorphoSupply(uint256,bytes)` | `0x2075be03` | CALL / void |
| `onMorphoRepay(uint256,bytes)` | `0x05b4591c` | CALL / void |
| `onMorphoSupplyCollateral(uint256,bytes)` | `0xb1022fdf` | CALL / void |
| `onMorphoLiquidate(uint256,bytes)` | `0xcf7ea196` | CALL / void |
| `onMorphoFlashLoan(uint256,bytes)` | `0x31f57072` | CALL / void |
| `transfer(address,uint256)` | `0xa9059cbb` | low-level CALL / optional bool |
| `transferFrom(address,address,uint256)` | `0x23b872dd` | low-level CALL / optional bool |

The two token entries supply the encoding; safe-transfer helpers handle optional returns.
Ecrecover is an additional raw STATICCALL to address **1**, with 128 input bytes encoding
`(digest,v,r,s)` as words. A successful recovery returns one 32-byte address word; an empty
result becomes address zero and fails the signature guard.

The selector table has **28 entries**: 27 typed transitions followed by the raw signature entry
(index 27). `setAuthorizationWithSigTransition` names `contract.fallback`, not a member of
`contract.transitions`. `Common.transitions_eq` lists only the 27 typed transitions.
`Dispatch`'s short/no-match facts use `selectorDispatchMsg`; `Fallback.lean` supplies the
separate raw-fallback rejection obligation. All EVM dispatcher reach paths are generated and
proved, including short and unmatched calldata.

All public-function proofs and the constructor are complete. Each public proof covers
success, nonpayability, malformed lengths, and applicable noncanonical argument branches.
Static-mode failures and arithmetic failures are matched at their actual bytecode positions.
The final build and top-level axiom audits are recorded above.

New local shared modules are `DispatchFacts.lean` (Solm routing), `BodyCommon.lean` (calldata
prelude, refinement bridges that accept selector dispatch alongside the raw fallback, and
return memory), `Storage.lean` (layout/evaluation bridges), and `Routines.lean` (canonical
address decoders at calldata offsets 4 and 36). `ReturnCommon.lean` handles multiword ABI
returns, `PackedStorage.lean` handles packed uint128 halves, `ErrorRoutines.lean` handles
shared allocation and require paths, and `AdminCommon.lean` handles administrative address
assignments, including static-mode violations. Reusable helpers are marked for promotion.
The bytecode, Solidity, generated runtime/creation summaries, and `Reasoning/` remain
unchanged. The specification allocation correction is documented below. All theorem
statements supplied by the scaffold are preserved.

The differential suites were rerun before proof work with the results in Section 2. The
`lake exe` command unexpectedly started rebuilding unrelated Comet modules and was stopped;
the already-built `.lake/build/bin/solm-difftest --only Morpho --count 50` ran successfully.
The supplemental scenario suite also reran successfully. No unrelated builds should be run.

`liquidate` covers both rounding directions and the bad-debt branch. `_accrueInterest`
covers the arbitrary IRM call, Taylor arithmetic, and fee-share writes. Signature authorization
covers raw ABI decoding, EIP-712 packing, the same opaque precompile-call witness on both sides,
nonce/static ordering, recovered-address checks, and the final packed authorization write.
`EcrecoverFacts` proves the precompile output is empty or a canonical address word directly
from the existing EVM semantics; it adds no assumption. `AuthorizationSigRefine` composes the
source and bytecode suffixes, and `SetAuthorizationWithSig` completes the fallback route.
Storage reloads and store order are preserved throughout; no slot-noncollision assumption is
used. The raw `extSloads` storage alias has a proved layout bridge.

`createMarket` is complete, including all guard and ABI failures, static mode, the six
storage writes in bytecode order, event memory, and the optional arbitrary-callee IRM call.
Its local `CreateMarket*` modules use shared `MarketParams*`, `MarketStateCommon`,
`MarketStorage*`, `BorrowRate*`, `WordBufferCommon`, and `Allocation` modules. The shared `_accrueInterest` routine and public `accrueInterest` are complete.
`AccrueHeap` tracks reused buffers and bounded allocations; `AccrueFeeWrites`,
`AccrueFeeRefine`, `AccrueFinishRefine`, `AccrueTailRefines`, `AccrueAssetsRefine`,
`AccrueMathRefine`, `AccrueIrmRefine`, and `AccrueFunctionRefine` assemble all branches.
`AccruePublicSource` and `AccruePublicRoutines` handle the public wrapper and its ABI,
market-created guard, and internal-call plumbing. `setFee` is now complete using that internal routine;
its `SetFee*` modules cover guards, memory preservation, and the post-accrual packed fee write.
The constructor is complete through `ConstructorABI`, `ConstructorSource`, `ConstructorMemory`,
`ConstructorReturnMemory`, `ConstructorRoutines`, and `ConstructorReverts`. The copied creation
runtime has zero immutable sites while `morphoBytecode` contains the mainnet values, despite its
header describing zero sites. `constructorTemplatePatches` proves equality after overwriting the
two sites; all other ranges match exactly. The safe-transfer callees are proved once and reused
by `flashLoan` and the lending entry points through their internal-call semantics.

The safe-transfer investigation found missing compiler allocation guards in `SpecSyntax.lean`.
`AllocationAudit.lean` proves that valid boolean returndata can exceed the size guard at pc 14555,
and that a uint64-sized result can still fail the free-pointer guard at pc 11535. These are local
post-call witnesses, not a refutation of the complete refinement theorem. The model's UInt256
gas bound does not imply a uint64 return-size bound.

The specification now threads an explicit local `__memory` cursor through both transfer helpers.
It checks input-buffer allocation, nonempty return size, rounded return allocation, and the two
64-byte require-message allocations. The second transfer in `flashLoan` and `liquidate` uses the
first transfer's returned cursor. No public ABI, storage layout, bytecode, or Solidity was changed.
The fixed cursor at the first transfer is 192 for flash loans, 544 for collateral supply, 672
for repayment, 608 for supply, 736 for withdrawal, 864 for borrowing, 672 for collateral withdrawal,
and 768 for liquidation. Accrual adds 0, 160, or 224 bytes; a nontrivial health check adds 32;
liquidation's bad-debt branch adds 192. Each count follows the pinned compiler's optimized IR.
`Solc_afterAccrueMemory` receives the fee immediately after accrual: a possible storage-slot alias
in the checked position increment cannot turn a nonzero upper-half fee into zero. The checked
arithmetic fact is in `AllocationAudit`; the completed lending proofs carry the full cursor
invariant through accrual, health checks, bad debt, and both transfers where applicable.

The corrected spec rebuilt through `Correct` and `DiffTarget` (3671 jobs), and all 66 differential
scenarios still agree (56 successful, no disagreements or stuck executions). The current native
50-case-per-transition run also agrees on all 1575 cases (544 successful, no disagreements,
stuck cases, out-of-gas results, or fuel exhaustion). The interpreter run agrees with the
native run, including its 544-success count. The sampler includes all specification literals
in its word pool, so the new allocation constants change some generated samples. The native check compiled only the six current Morpho modules and a local driver,
reusing cached framework objects; no other benchmark was rebuilt.
`SafeTransferSourceAllocation` proves both source-side allocation rejection cases and preservation
of other locals. `SafeTransferSourceTail` proves call failure, decode failure/false, and successful
optional-bool return handling. No new assumptions were introduced. The mismatch is resolved by
the specification correction, and the source lemmas are connected to the shared bytecode routines
in the completed safe-transfer refinement proofs.

`AccrueRoutinesStart` proves entry, elapsed subtraction, zero elapsed, IRM selection,
timestamp storage, and static timestamp halt. `AccruePrepareCall`, `AccrueCallReturn`, and
`AccrueCall` prove the arbitrary-callee IRM call and return decoding. `ZeroValueCallBridge`
uses the existing `RD.call`/`RD.callDepthLimit` machinery and supports either caller permission
mode. `AccrueMathRoutines`, `AccrueBorrowAssets`, `AccrueSupplyAssets`, `AccrueFeeMath`,
`AccrueFeePosition`, `AccrueSupplyShares`, and `AccrueFinish` prove the remaining bytecode
segments, including arithmetic failures, packed writes, and event/timestamp return. All
storage loads retain their actual order and use the current post-call/post-write account map.

The matching source stages are in `AccrueSourceStart`, `AccrueSourceCall`,
`AccrueSourceMath`, `AccrueSourceFee`, `AccrueSourceFeeCalc`, `AccrueSourceFeeWrites`, and
`AccrueSourceFinish`. `StateBlock` generalizes the existing pure `ABlock` continuation to
state-changing prefixes. The memory bounds and full internal/public assembly are proved. No new placeholders were added to these helpers.

`extSloads` is complete through `WordArrayABI`, `ExtSloadsSourceStep`, `ExtSloadsSource`,
`ExtSloadsDecode`, `ExtSloadsMemory`, `ExtSloadsPrepare`, `ExtSloadsReadLoop`,
`ExtSloadsReturn`, and `ExtSloadsFinish`. Both loops support arbitrary array lengths; the
allocation and decoding bounds cover all rejection paths. Generic array/value/memory facts are
reused from the proof-only `Benchmarks.EAS.Attester.LocalArray`, `WordArrayABI`,
`WordSequenceMemory`, and `StructAllocMemory` modules. Its axiom audit is clean of `sorryAx`.
