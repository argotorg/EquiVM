# Curve lending Vault refinement proof

## 1. Compiler settings and provenance

Target: `curve_stablecoin/lending/Vault.vy` in Curve's `curve-stablecoin` commit
`f19a18abef6e75e3e08b1aa427ede724162bce57`. The pinned main source and its entire
15-file import closure are under [contracts](contracts/). Dependencies are:

- `curve-std`: `68a13eb2ee80bd704fc259a3aed0a6ce53d59b72`, pinned by the upstream `pyproject.toml`.
- `snekmate`: `0.1.2`, pinned by the upstream `uv.lock`; source archive SHA-256
  `8ed2c6a29b90424543d1792599c5c0b5ccf6988931b43029d1ca7e520a045038`.

[provenance](provenance/) preserves the upstream settings, dependency manifests,
lockfiles and main-project license. Source URLs are the pinned
[Vault source](https://github.com/curvefi/curve-stablecoin/blob/f19a18abef6e75e3e08b1aa427ede724162bce57/curve_stablecoin/lending/Vault.vy),
[foundry.toml](https://github.com/curvefi/curve-stablecoin/blob/f19a18abef6e75e3e08b1aa427ede724162bce57/foundry.toml),
[curve-std commit](https://github.com/curvefi/curve-std/tree/68a13eb2ee80bd704fc259a3aed0a6ce53d59b72),
and the [snekmate archive](https://files.pythonhosted.org/packages/a4/f5/5b285024f0a18e699f2b144d9821b2572e8665331261c9078fdad6a7aa38/snekmate-0.1.2.tar.gz).

| Setting | Pinned value |
|---|---|
| Compiler | Vyper `0.4.3+commit.bff19ea2` |
| EVM fork | Cancun, from upstream `foundry.toml` |
| Optimization | `# pragma optimize codesize` |
| Nonreentrancy | `# pragma nonreentrancy on`; transient lock |
| Metadata | Compiler default, enabled |
| Runtime | 8,635 bytes, including 347 bytes of dispatcher tables |
| Creation | 8,717 bytes: 17-byte prefix, runtime payload, 65-byte metadata trailer |
| Immutables | None; immutable valuation is the empty store |

The upstream absolute macOS compiler and search paths are replaced with the local
Vyper executable and the pinned `contracts` directory. The upstream `solc = 0.8.26`
setting applies to Solidity, not this Vyper compilation.

The shared scaffold compiler forces `--no-bytecode-metadata`.
[compile_foundry.py](compile_foundry.py) runs that compiler adapter, then recompiles
with default metadata and regenerates the creation artifact, build settings and
hash manifest. It asserts identical runtime and verifies that the only creation
difference is the trailing 65 bytes. Both creation variants are retained in
`provenance`; the proof and differential target use the full default artifact.

SHA-256 of the decoded bytecode bytes:

```text
runtime   7f5c6c95df32b2c194d1a7cc2eacbc4fb2884edc9e64e8c82e3c11cf1d9d4893
creation  374b02cb44f10e1b17e58e3f09befd7e2fb3a5d787ddc0d90b7065ba001b3293
```

[sources.sha256](sources.sha256) pins the sources and compiler artifacts.
[artifact-check.log](artifact-check.log) contains six `ok` lines.

Commands below run from the repository root. Set `VAULT_VYPER` to a Vyper executable
whose `--version` prints the pinned version.

```sh
python3 -B Benchmarks/CurveVault/compile_foundry.py --vyper "$VAULT_VYPER"
python3 -B scripts/scaffold.py lean --dir Benchmarks/CurveVault --module Benchmarks.CurveVault --force
python3 -B Benchmarks/CurveVault/generate_blocks.py
python3 -B scripts/bytecode_report.py Benchmarks/CurveVault --output Benchmarks/CurveVault/Vault.report.md
python3 -B Benchmarks/CurveVault/generate_codesize.py
python3 -B Benchmarks/CurveVault/audit_blocks.py
python3 -B scripts/scaffold.py check --dir Benchmarks/CurveVault
lake build Benchmarks.CurveVault.Correct
```

`SpecSyntax.lean` is the audited, authored specification. Do not replace it with the
translator's initial draft. The standard proof generator was run with force before
the allowed ABI/storage edits to `Spec.lean`. Its Vyper transient-layout and
codesize-dispatch limitations are recorded in `skeleton-generation.log` and
`dispatch-generation.log`. The local generator uses the shared generator for the
prelude, function stubs, constructor and composition; it generates the proved
dispatcher from the pinned two-stage tables and preserves the audited `Spec.lean`.
No shared generator, Stele module, reasoning module or global test registry was edited.
`Vault.spec.json` is the unedited initial translation report: its 13 reported holes
are historical. Their replacements (interface address access, controller hooks,
admin percentage and optional token returns) are in the finished `SpecSyntax.lean`.

[generate_blocks.py](generate_blocks.py) uses the shared RD generator for the
executable regions: 626 runtime units in 31 shards, plus the single creation-prefix
unit. It keeps all 22 CALL/STATICCALL boundaries for the proving session. It excludes
dispatcher tables, the creation payload and metadata from instruction generation;
the generic whole-byte disassembler otherwise generates spurious BLOCKHASH summaries
for those data bytes. All artifact bytes and jump tables remain pinned unchanged.

## 2. Differential runs and coverage

The local runner registers only this target in a hidden Lake package, preserving the
repository's test registry. It invokes the repository CLI as
`lake exe stele-difftest --only Vault --count 50`, with seed **2026**.

```sh
python3 -B Benchmarks/CurveVault/run_difftest.py --only Vault --count 50
lake env lean --run Benchmarks/CurveVault/SuccessfulPaths.lean
lake env lean --run Benchmarks/CurveVault/BoundaryCases.lean
lake env lean --run Benchmarks/CurveVault/InitializeDiagnostic.lean
```

Recorded CLI result:

```text
Vault: 2525 cases: 2525 agree (756 successful), 0 disagree, 0 stuck, 0 EVM out of gas, 0 spec out of fuel
```

The exact coverage line follows. The full output is [difftest.log](difftest.log).
`PointEval failed` diagnostics are expected for sampled calls to precompile 10 with
invalid, short input; the final run has no missing-file/import exceptions or panics.

```text
successful/cases: constructor 25/25, withdraw(uint256,address) 0/50, withdraw(uint256) 0/52, withdraw(uint256,address,address) 0/51, totalAssets() 1/53, name() 49/53, convertToAssets(uint256) 0/52, approve(address,uint256) 22/53, previewWithdraw(uint256) 0/51, totalSupply() 45/52, transferFrom(address,address,uint256) 3/51, collateral_token() 44/50, pricePerShare(bool) 9/52, pricePerShare() 17/52, amm() 45/51, decimals() 49/52, asset() 36/52, increaseAllowance(address,uint256) 24/53, maxDeposit(address) 3/52, previewRedeem(uint256) 2/52, deposit(uint256,address) 0/51, deposit(uint256) 0/51, balanceOf(address) 47/57, borrowed_token() 44/53, redeem(uint256,address) 0/55, redeem(uint256,address,address) 0/52, redeem(uint256) 0/58, set_max_supply(uint256) 0/50, mint(uint256,address) 0/51, mint(uint256) 0/51, symbol() 44/52, decreaseAllowance(address,uint256) 38/52, transfer(address,uint256) 9/51, lend_apr() 0/54, previewMint(uint256) 0/51, borrow_apr() 6/56, factory() 49/52, maxMint(address) 2/52, convertToShares(uint256) 0/51, maxWithdraw(address) 0/50, maxSupply() 47/53, maxRedeem(address) 0/51, allowance(address,address) 42/53, previewDeposit(uint256) 0/52, controller() 43/54, admin() 4/51, initialize(address,address,address,address) 7/52, stray 0/100
```

Random initial states seldom combine a funded owner, suitable precision/supply,
authorized caller and three consistent external contracts. This explains the zero
successful counts on several vault and administrative arms. They are covered by
[SuccessfulPaths.lean](SuccessfulPaths.lean), which independently exercises **all 46
selector variants successfully**, using fixed controller/token responses and funded
balances. Result: `Successful paths: 46/46, 0 failures`.

[BoundaryCases.lean](BoundaryCases.lean) covers 100 cases with zero failures:
malformed symbol offsets, lengths, truncation and padding; uint8 return validation;
empty/short/false/noncanonical/oversized token returns; codeless tokens; checked
arithmetic before later calls; raw controller words in outbound calldata; and both
string getters with corrupted headers. Four deliberately enormous getter cases
exhaust EVM gas, as required by the gas argument below. See
[boundary-cases.log](boundary-cases.log).

[InitializeDiagnostic.lean](InitializeDiagnostic.lean) checks canonical symbol lengths
0, 1, 15, 16, 17, 30, 31 and 32, plus dirty padding, against final string storage words.
All nine agree successfully; see [initialize-diagnostic.log](initialize-diagnostic.log).
The initial failures on payable creation and string padding were fixed, not excluded.

## 3. Semantic audit and bytecode-specific behavior

The audit covers **all 378 executable runtime basic blocks**, bytes 0–8287, and the
creation prefix. [block-audit.tsv](block-audit.tsv) maps every block to its specification
statements, ordered observable instructions and source references. The manually
reviewed statement map is in [audit_blocks.py](audit_blocks.py). This ledger uses
source IDs to distinguish imported helpers; the generic report sometimes labels
their line numbers as unrelated lines of the main source.

Creation bytes 0–16 only copy and return the runtime payload at offset 17. They accept
call value, ignore appended constructor arguments and perform no storage writes,
calls or logs. The spec therefore has an empty **payable** constructor. The copied
payload and metadata are data during creation. Runtime bytes 8288–8634 are dispatch
tables, not instructions reachable by any entry or internal jump. There is no
fallback/receive: short or unmatched selectors revert at 6768; common guard failures
revert at 8284. Revert payloads are intentionally outside the refinement relation.

The audit fixed or recorded these differences from a direct source translation:

1. `_total_assets` checks `available_balance + total_debt` at pcs 6862–6876 **before**
   calling `admin_fees` at 6902. `lend_apr` checks both numerator products at
   1240–1287 **before** its `_total_assets` call. Deposits and mints read maxSupply
   before the second checked sum. Hoisted calls/reads now follow that order.
2. Token transfer hooks are actual calls, with EXTCODESIZE guards before the void
   call. Token `transferFrom` skips zero amounts; otherwise it calls first, checks
   success, and accepts empty output only if the token has code **after** that call.
   Nonempty output must contain a canonical true bool. Extra return bytes are ignored.
3. `initialize` persists nonzero string padding, including for canonical token
   symbols of lengths 17–32. Let `n <= 32` be the decoded length and `W` the full
   32-byte returned data word, retaining dirty padding. The 64-byte data representations are:

   ```text
   name:   "Curve Vault for " || W || uint128_be(n)
   symbol: "cv" || W || W[18:32] || uint128_be(n)
   ```

   Their logical lengths are `16+n` and `2+n`. The compiler writes the header first,
   then exactly `ceil(length/32)` data words; untouched trailing slots remain intact.
   `EncodedSymbol`, value concatenation and the allowed storage adapter preserve these
   observable words. The spec models no allocation, memory address, pointer or copying.
4. Both public string getters have a three-word loop bound. Consequently `symbol()`
   accepts raw stored lengths up to **64**, despite its declared write capacity of 34.
   Headers in `[2^256-63, 2^256-32]` wrap the loop count to zero and return an empty
   string. Other oversized headers revert, except the top 31 values, which necessarily
   run out of gas. These cases are modeled without a storage-length precondition.
5. A controller word re-read after allowance/balance writes must remain a full word
   when encoded as a `transferFrom` argument. The spec retains `_controller` as a
   uint256 storage view and casts only its **call target** to address. Its token-call
   encoder preserves the complete argument word. This avoids relying on hash-slot
   noncollision or on canonical storage after a write/call. The ordinary external
   `controller()` return still uses the initial canonical-address precondition.
6. The translator omitted the constant `decimals()` getter; its return of uint8 18
   at pc 6426 is included. Duplicate imported event declarations were removed.

Storage and effect order were checked through every shared helper:

- `_mint`/`_burn`: balance read, checked arithmetic, balance write, **then** supply
  read/arithmetic/write, then Transfer event.
- `_transfer`: recipient checks (`this` then zero), sender debit/write, **then**
  recipient read/credit/write, then Transfer. Equal keys and slot aliases retain
  the bytecode behavior.
- `_approve`: nested mapping write followed by Approval. `transferFrom` spends
  allowance even for owner==caller; withdraw/redeem skip that step for owner==caller.
- `withdraw` reads controller after allowance update and before burning;
  `redeem` reads it after burning. Borrowed token is re-read after each transfer hook.
- `_convert_to_shares` reads precision then supply; `_convert_to_assets` reads supply
  only after checking its numerator. MAX_UINT256 is a sentinel that triggers fresh
  asset calls, including the second group of calls in `maxMint`.
- `_available_balance` calls balance then fees and saturates subtraction at zero.
  Shared ceil division checks its denominator before the zero-numerator branch.
  Allowance increase/decrease intentionally wrap, then clamp overflow/underflow.
- Event signatures, indexed topics, argument order, call targets/selectors/value,
  static permissions, caller/default arguments and `address(this)` match the report.
  There are no block-header reads, creation calls, selfdestructs or delegatecalls.

### Computed dispatcher and all selector entries

For the 32-bit selector `s`, bucket `b = s % 5`. Read its five-byte record at
`8288 + 5*b`, obtaining `magic`, `table` and `size`. The secondary index is
`((magic*s) >> 24) % size`. Each seven-byte record contains the selector, 16-bit
entry pc, and flags: `flags & 254` is minimum calldata size; `flags & 1` is nonpayable.
All records have that bit set. Pcs 0–72 select/check the record, 73–89 enforce entry
guards, and 90–98 jump to the entry. Table reconstruction is asserted by the local
generator and used by its proved dispatch lemmas.

| Bucket | Magic | Secondary table | Records |
|---|---:|---:|---:|
| 0 | 8600 | 8495 | 11 |
| 1 | 46 | 8460 | 5 |
| 2 | 3593 | 8383 | 11 |
| 3 | 5120 | 8313 | 10 |
| 4 | 2092 | 8572 | 9 |

| Selector | Signature | Bucket/index | Entry pc | Min calldata |
|---|---|---|---:|---:|
| `0x00f714ce` | `withdraw(uint256,address)` | 3/1 | 4122 | 68 |
| `0x01e1d114` | `totalAssets()` | 0/5 | 1479 | 4 |
| `0x06fdde03` | `name()` | 4/1 | 6437 | 4 |
| `0x07a2d13a` | `convertToAssets(uint256)` | 1/1 | 1859 | 36 |
| `0x095ea7b3` | `approve(address,uint256)` | 4/8 | 5947 | 68 |
| `0x0a28a477` | `previewWithdraw(uint256)` | 3/2 | 4031 | 36 |
| `0x18160ddd` | `totalSupply()` | 0/10 | 6756 | 4 |
| `0x23b872dd` | `transferFrom(address,address,uint256)` | 4/0 | 5688 | 100 |
| `0x2621db2f` | `collateral_token()` | 2/4 | 110 | 4 |
| `0x28c06203` | `pricePerShare(bool)` | 3/7 | 1517 | 36 |
| `0x2a943945` | `amm()` | 1/3 | 122 | 4 |
| `0x2e1a7d4d` | `withdraw(uint256)` | 4/4 | 4107 | 36 |
| `0x313ce567` | `decimals()` | 1/4 | 6426 | 4 |
| `0x38d52e0f` | `asset()` | 0/9 | 1459 | 4 |
| `0x39509351` | `increaseAllowance(address,uint256)` | 0/7 | 6012 | 68 |
| `0x402d267d` | `maxDeposit(address)` | 2/3 | 1936 | 36 |
| `0x4cdad506` | `previewRedeem(uint256)` | 3/6 | 4932 | 36 |
| `0x6e553f65` | `deposit(uint256,address)` | 4/2 | 2143 | 68 |
| `0x70a08231` | `balanceOf(address)` | 1/0 | 6718 | 36 |
| `0x765337b6` | `borrowed_token()` | 3/4 | 99 | 4 |
| `0x7bde82f2` | `redeem(uint256,address)` | 2/1 | 5024 | 68 |
| `0x8a938f2f` | `set_max_supply(uint256)` | 0/6 | 851 | 36 |
| `0x94bf804d` | `mint(uint256,address)` | 4/5 | 3146 | 68 |
| `0x95d89b41` | `symbol()` | 0/4 | 6544 | 4 |
| `0x99530b06` | `pricePerShare()` | 3/0 | 1506 | 4 |
| `0xa0712d68` | `mint(uint256)` | 2/2 | 3136 | 36 |
| `0xa457c2d7` | `decreaseAllowance(address,uint256)` | 0/2 | 6185 | 68 |
| `0xa9059cbb` | `transfer(address,uint256)` | 2/7 | 5882 | 68 |
| `0xa980497e` | `lend_apr()` | 1/2 | 1107 | 4 |
| `0xb3d7f6b9` | `previewMint(uint256)` | 0/0 | 3060 | 36 |
| `0xb460af94` | `withdraw(uint256,address,address)` | 4/7 | 4147 | 100 |
| `0xb6b55f25` | `deposit(uint256)` | 0/8 | 2133 | 36 |
| `0xba087652` | `redeem(uint256,address,address)` | 4/3 | 5049 | 100 |
| `0xbac4daa2` | `borrow_apr()` | 2/5 | 1020 | 4 |
| `0xc45a0155` | `factory()` | 2/6 | 146 | 4 |
| `0xc63d75b6` | `maxMint(address)` | 3/9 | 2886 | 36 |
| `0xc6e6f592` | `convertToShares(uint256)` | 4/6 | 1782 | 36 |
| `0xce96cb77` | `maxWithdraw(address)` | 3/5 | 3890 | 36 |
| `0xd5abeb01` | `maxSupply()` | 0/3 | 6414 | 4 |
| `0xd905777e` | `maxRedeem(address)` | 2/0 | 4783 | 36 |
| `0xdb006a75` | `redeem(uint256)` | 2/9 | 5009 | 36 |
| `0xdd62ed3e` | `allowance(address,address)` | 3/8 | 6651 | 68 |
| `0xef8b30f7` | `previewDeposit(uint256)` | 3/3 | 2056 | 36 |
| `0xf77c4791` | `controller()` | 2/8 | 134 | 4 |
| `0xf851a440` | `admin()` | 2/10 | 6326 | 4 |
| `0xf8c8765e` | `initialize(address,address,address,address)` | 0/1 | 158 | 132 |

Default-argument variants share their body after binding defaults:

| Function | Variants | Shared body pc | Defaults |
|---|---|---:|---|
| pricePerShare | `()`, `(bool)` | 1533 | true |
| deposit | `(uint256)`, `(uint256,address)` | 2159 | receiver=caller |
| mint | `(uint256)`, `(uint256,address)` | 3162 | receiver=caller |
| withdraw | 1, 2, or 3 arguments | 4178 | receiver/owner=caller |
| redeem | 1, 2, or 3 arguments | 5080 | receiver/owner=caller |

## 4. Refinement proof, storage and ABI configuration

All 46 ABI entries and the constructor have complete proofs. The thin capstone is
`Benchmarks.CurveVault.vaultContractCorrect` in [Correct.lean](Correct.lean).
It proves `contractRefinementWF storageWF noGasBound config vaultCreationBytecode contract`.
The final build and axiom audit are recorded below. No specification, bytecode,
source-closure, or provided block-summary changes were made during this proving pass.

Final verification (2026-10-13), from the repository root:

```sh
lake build Benchmarks.CurveVault.Correct
printf '%s\n' 'import Benchmarks.CurveVault.Correct' '#print axioms Benchmarks.CurveVault.vaultContractCorrect' | lake env lean --stdin
```

The build exited successfully; its final line is:

```text
Build completed successfully (3754 jobs).
```

[correct-build.log](correct-build.log) preserves the complete build output,
including linter warnings. [axiom-audit.log](axiom-audit.log) preserves the complete,
verbatim capstone axiom output. It lists 7,972 dependencies: `propext`,
`Classical.choice`, `Quot.sound`, and 7,969 concrete `native_decide` evaluation
axioms. There are no other axioms and no selector-identity evaluation axioms.
Both the proof-hole search and the axiom-declaration search across this directory
returned no output (exit status 1). No differential tests were run.

All new Lean modules are reachable from the capstone imports. The longest authored
module is `DispatchStele.lean` at 1,706 lines; all authored modules stay below the
2,000-line limit. Shared helpers carry 73 library-candidate or generalization tags
for later promotion to `Reasoning/`.

`Initialize.lean` connects four canonical-address decoders, the uninitialized-state
guard, and the first-write static halt to `InitializeCore.lean`. That core composes
opaque `decimals()` and `symbol()` calls, checked precision arithmetic, configuration
writes, and both bounded string-storage loops. The symbol decoder covers malformed
and overflowing offsets, truncated data, dirty padding, and memory-expansion failure.
`InitializeStringSource.lean` proves the exact packed source values and storage order;
`InitializeStringWrites.lean` reaches the final supply-limit write and empty return.

Deposit and mint share `CreditInternal`, `CreditEntry`, `CreditAfterController`,
`CreditLimits`, and `CreditTail`. Their internal conversion and supply calls use
modular `ExecFuncBody` proofs. `MutationTransfer` composes the opaque controller
hook and token transfer for all four vault flows. Withdrawal and redemption are
proved through `DebitInternal`/`DebitEntry`, including allowance spending,
total-assets calls, conversion, minimum liquidity, burn, hooks, transfer, save-rate,
events, and unlock/return. `MutationEntry` handles public locks/static mode for all
four flows; `MutationConversion` shares their internal conversion calls.
`AllowanceSpend` is shared by withdrawal, redemption, and `transferFrom`.
`UintTwoAddressABI` proves the remaining three-argument calldata cases.

The string getters share the bounded copy loop, memory, ABI encoding, and malformed-header
proofs in `StringArithmetic`, `StringSource`, `StringBlocks`, `StringLoop`, `StringMemory`,
`StringEncoding`, `StringReturn`, `StringMalformed`, `StringGas`, and `StringRoutine`.
Ordinary lengths through 64 return storage bytes with cleared ABI padding. The overflow
range from `2^256 - 63` through `2^256 - 32` returns the empty string. The final 31 length
values pass the copy guard but request more return data than EVMLean's proved gas bound
allows; these executions are proved to run out of gas. A finite concrete header table
uses `native_decide`; there is no additional gas or storage precondition.
`Constructor.lean` composes the provided creation summary with the empty-constructor
library theorem and checks that the returned 8,635 bytes equal the pinned runtime.

`DispatchPrelude.lean` and `DispatchStele.lean` split the original dispatcher by
concern to keep files below 2000 lines. `Entry.lean` proves the shared guard at pc
73 and its computed jump. `Storage.lean`, `Memory.lean`, `Calls.lean`, and
`Lock.lean` hold the reusable storage, mapping-memory, external-call ABI, and
transient-lock lemmas. Completed external-call proofs use the library's opaque
`STATICCALL` bridge and prove both failed/short returns and successful decoding.
`borrow_apr` additionally proves the checked multiplication overflow branch.
`StaticWordCalls.lean` factors the scalar static-call bridge shared by the AMM and
controller helpers. The `Lend` helpers cover the zero-debt return, both checked
numerator products, the `_total_assets` call and zero denominator, the admin
percentage call, and the final checked arithmetic.
`AllowanceStorage.lean`, `ApproveArguments.lean`, and `ApproveInternal.lean` prove
the nested mapping assignment and modular `_approve` callee, preserving caller
memory from offset 192. `MutatingLock.lean` handles transient writes and the
static-mode halt at `TSTORE`, as well as source wrappers that release the lock.
The `AllowanceAdjust` helpers share the source and EVM proofs for wrapped
addition/subtraction, clamping to the uint256 maximum or zero, and the conditional
`_approve` call. Both adjustment entry points handle malformed addresses and static
mode before entering that routine.
`TransferGuard.lean`, `TransferTail.lean`, and `TransferInternal.lean` prove the
modular `_transfer` callee, including recipient checks and both checked balance
updates. The recipient balance is read after the sender debit, so the proof covers
equal addresses without a mapping-slot noncollision assumption. `Transfer.lean`
connects this callee to all public decoding, lock, static-mode, and return paths.
The `TransferFrom` helpers preserve the saved addresses across the conditional
`_approve` call, cover allowance underflow and the unlimited sentinel, then reuse
`_transfer`. `TransferFrom.lean` proves both address-decoding checks and the complete
public wrapper.
`FactoryStorage.lean` shares the factory read and admin-call encoding with the
getters. The `SetMax` helpers prove the opaque admin call, canonical address
decoding, administrator-or-factory authorization, and supply-limit update.
`Set_max_supply.lean` connects these to the void-returning mutating wrapper.
The lock helpers also prove persistent storage preservation across transient
writes and static calls, so the second factory read retains its address bound.
`ControllerCalls.lean` and `TotalAssetsCalls.lean` connect the three controller calls
to `TotalAssetsInternal.lean`, which proves `_total_assets` once with its checked
arithmetic and caller continuation. Its scratch-memory preservation theorem supports
callers with saved arguments. `CeilDiv.lean` proves the shared ceiling-division body
and bytecode routine, including zero-denominator reversion; `Arithmetic.lean` holds
its reusable cast-after-addition lemma.

`ConversionPrefix.lean` and `ConversionPrepare.lean` prove the optional `_total_assets`
call and preserve the caller's input words. `ConvertSharesArithmetic.lean` and
`ConvertAssetsArithmetic.lean` cover checked arithmetic in bytecode order.
`ConversionFinishSource.lean`, `ConversionFinish.lean`, and `ConvertAssetsFinish.lean`
connect floor and ceiling division, including zero-denominator reversion and the
`MCOPY` argument transfer. `ConvertSharesInternal.lean` and `ConvertAssetsInternal.lean`
assemble full callee-body proofs and preserve words above scratch offset 576.
The `Forward` helpers use modular internal calls for the public conversion wrappers.
`Calldata.lean` adds the single-uint256 Vyper decoder facts.
`Limits.lean` proves the branchless maximum and clamped subtraction used by the
deposit and mint limits. `MaxDepositInternal.lean`, `MaxMintCapacity.lean`, and
`MaxMintInternal.lean` preserve the saved supply limit across controller calls and
reuse the proved total-assets and share-conversion callees.
`SubOrZero.lean` and `AvailableBalanceInternal.lean` prove the available-balance
routine with both opaque controller calls. The withdrawal and redemption limits
reuse this routine and preserve the source order of balance reads; the redemption
proof carries the saved owner through the compiler's argument `MCOPY`.
`PriceArithmetic.lean`, `PriceFinishSource.lean`, `PriceFinish.lean`, and
`PriceInternal.lean` prove the shared price routine, including all overflow checks,
both rounding modes, the zero-supply constant, and rejection of a zero price.

`MintInternal.lean` and `BurnInternal.lean` prove the shared supply-changing
callees, including checked balance and supply arithmetic in the bytecode's storage
order. `TokenInternal.lean` proves the shared token transfer callee, including the
zero-amount path, the raw three-word calldata encoding, the opaque `CALL`, and
all return-data checks. `TokenReturnSource.lean` and `TokenReturnEVM.lean` connect
empty returns and canonical Boolean returns, with explicit rejection of short,
false, and noncanonical returns. `TokenOutputMemory.lean` preserves the caller's
saved words above the callee's scratch memory. These three internal routines build
without proof holes and are reused by the completed public deposit/withdrawal
callers.
`VoidCalls.lean` supplies the shared opaque-call bridge for the guarded controller
hooks and `save_rate` calls.

All 32 provided block-summary modules build; see [blocks-build.log](blocks-build.log).
The bytecode, source closure, generated summaries, and specification remain unchanged.
Differential tests were not run during the proving pass.

The runtime theorem is `runtimeRefinementWithWF storageWF noGasBound ...`.
`storageWF` requires the initial words in slots 0–4 to be below `2^160`.
It imposes no string-length, mapping-slot or transient-word restrictions, and no
condition on a callee's post-state. Direct address writers are only `initialize`
and write validated calldata/caller addresses. The controller storage write adapter
checks this already-established range; mapping writes retain all 256 bits.
Do not assume global preservation of canonical address slots under arbitrary mapping
aliases. The bodies preserve raw controller arguments where that distinction matters.

| Persistent slot | Declaration / representation |
|---|---|
| 0, 1 | borrowed token, collateral token; full-word address slots |
| 2, 3, 4 | AMM, controller, factory; controller retains a raw uint256 view internally |
| 5 | maxSupply, uint256 |
| 6; 7–8 | name length; inline data, capacity 64 bytes |
| 9; 10–11 | symbol length; inline data, capacity 34 bytes |
| 12 | allowance: `keccak(keccak(word(12) || owner) || spender)` |
| 13 | balanceOf: `keccak(word(13) || owner)` |
| 14, 15 | totalSupply, precision; uint256 |

Hash inputs use two full big-endian words, **slot before key**. There is no Solidity
packing or hashed byte-string allocation. `vyperBoundedStorage!` supplies capacities;
the narrow write adapter handles the observable string padding and header-first order.

Transient slot **0** is a full uint256 in its own storage space. State-changing
nonreentrant entries require lock!=1, write 1, execute the body, then write 0 on
success. View entries only check lock!=1. `initialize`, the five contract-address
getters and generated public getters are reentrant and do not access this lock.
Cancun supplies TLOAD/TSTORE. Static-mode violations occur at the same first write
as in the bytecode; invalid arguments are decoded before the write.

All 46 entry ABIs contain only static scalars; none has a bound-bearing dynamic
parameter. `externalABI.withMode .vyper` handles entry calldata and explicit scalar
decoding: insufficient words or dirty address/bool words revert; extra calldata is
accepted. All entries are nonpayable. No constructor parameters need decoding.

| External operation | Selector | Kind | Result / guard |
|---|---|---|---|
| decimals() | `313ce567` | STATICCALL | >=32 bytes, canonical uint8; initialize additionally requires <=18 |
| symbol() | `95d89b41` | STATICCALL | custom `decodeTokenSymbol`, bounded String[32] with retained raw word |
| admin() | `f851a440` | STATICCALL | >=32 bytes, canonical uint160 |
| rate() | `2c4e722e` | STATICCALL | >=32 bytes, uint256 |
| total_debt() | `31dc3ca8` | STATICCALL | >=32 bytes, uint256 |
| available_balance() | `092314da` | STATICCALL | >=32 bytes, uint256 |
| admin_fees() | `1b1800e3` | STATICCALL | >=32 bytes, uint256 |
| admin_percentage() | `1059fcbd` | STATICCALL | >=32 bytes, uint256 |
| on_borrowed_token_transfer_in(uint256) | `a4a87022` | CALL | EXTCODESIZE before call; success; ignore return bytes |
| on_borrowed_token_transfer_out(uint256) | `3f888681` | CALL | EXTCODESIZE before call; success; ignore return bytes |
| save_rate() | `69c6804e` | CALL | EXTCODESIZE before call; success; ignore return bytes |
| transferFrom(address,address,uint256) | `23b872dd` | CALL | raw argument-word encoding; optional canonical true bool result as described above |

Every call sends zero value. The return-value STATICCALLs have no EXTCODESIZE guard;
codeless accounts normally return empty bytes and then fail decoding. The only
explicit `abi.decode` site is the optional bool in `tkn_transfer_from`, at pcs
7629–7679; it uses Vyper scalar mode. The custom symbol decoder (pcs 400–475) considers
only the first 96 returned bytes, accepts unaligned/overlapping offsets when their
logical extent fits, requires length<=32, and does not require padded returndata.
Its retained 32-byte data word is zero-extended beyond the copied return bytes.
All named-return scalar decoders ignore trailing data, matching the fixed output size.

The completed proofs cover initializer padding/partial storage writes, malformed
string getters, external-call/reentrancy boundaries, and ordered mapping writes
followed by raw controller re-reads. Shared helpers cover asset accounting,
conversions, optional token return decoding, and the lock protocol. The block ledger
specifies the order used to avoid a storage-slot-noncollision axiom.

## 5. Gas bound

The selected bound is **`noGasBound`**, the loosest possible bound in this model.
Starting gas is a UInt256, hence at most `2^256-1`; all gas up to `2^24` is included.
No source computation reads gas. GAS occurs only immediately before CALL/STATICCALL;
the existing call relation witnesses the actual forwarded gas and callee result,
including EIP-150 behavior. The spec does not replace a gas-sensitive callee result
with a constant or assume call success.

The body proofs discharge the following low-level details:

- **Symbol return offsets (pcs 425–475).** Addition of the output base to the offset
  is checked for wrap. A wrapped later length/extent calculation could only evade
  the abstract bounds after loading a word near the end of the 256-bit address
  space. That MLOAD expands memory beyond `2^255` bytes before the extent test can
  matter. With `a` memory words, `C_mem(a)=3*a+floor(a^2/512)`; `a>=2^250` already
  costs at least `2^491`, exceeding every allowed UInt256 gas value. Such paths
  refine via outOfGas. Small invalid extents simply revert, as the custom decoder does.
- **Corrupted string getters (pcs 6437–6650).** Their loop count is
  `((length+63) mod 2^256) >> 5`, bounded by 3. Ordinary lengths 0..64 produce the
  standard encoding. Lengths `2^256-63` through `2^256-32` copy no header and return
  the encoding of an empty string; the spec explicitly includes these cheap successes.
  For `length=2^256-k`, `1<=k<=31`, the padding operation clears the low `k` bytes
  of the copied length word, making it `2^256-256^k`. The subsequent RETURN needs
  more than `2^255` bytes of memory, again costing at least `2^491` gas. Therefore
  the spec's rejection of those remaining headers cannot exclude a completed call.
  This was also checked with four focused OOG cases at ordinary gas budgets.
- **Other encoding/storage loops.** Initialization bounds the token symbol at 32,
  so the name/symbol lengths are at most 48/34 and all buffer extents are fixed and
  small. All other arguments/results/events are static scalars. There are no
  arbitrary-length source allocations or unbounded storage loops. Failure returndata
  is copied only to revert; exhaustion during that copy is already a refinement case.

No lower artificial gas ceiling is needed. The body proofs establish these
quantitative arguments without additional axioms or restrictions on valid calls.
