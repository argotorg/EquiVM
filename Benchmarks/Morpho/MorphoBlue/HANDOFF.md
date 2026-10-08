# Morpho Blue proof scaffold

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

## 4. Starting the proving session

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

There are **61 intentional generated `sorry`s**: 28 function bodies, the constructor,
`restrictImmutables_of_fit`, the raw fallback obligation, and 30 Solm dispatch facts for the
fallback representation. There are none in `SpecSyntax`, the calldata/model helpers, the
bytecode summaries, or the capstone. No contract proofs were written in this scaffolding pass.

Expect the most work in `liquidate` (two rounding directions and bad debt), `_accrueInterest`
(IRM reentrancy, Taylor arithmetic and fee-share writes), and signature authorization (raw ABI
entry, EIP-712 packing, precompile witness, and nonce/static ordering). Preserve reloads and
store order across mapping operations; do not introduce a storage-slot noncollision axiom.
The raw `extSloads` alias and whole-struct `createMarket` writes need explicit layout bridges.
