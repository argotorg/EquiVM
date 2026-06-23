# OZ VestingWallet (bench) — proof handoff

Read **`prompt.md`**, **`Reasoning/GUIDE.md`**, **`Examples/ERC20/PROOF_GUIDE.md`**, and the canonical
**`Examples/SimpleAuction/HANDOFF.md`** first — it holds the **full global rules, the 4-phase plan, the
per-function prompt template, and the Concurrency model** (all apply). This is the **hardest** OZ bench:
a **2-level binary-search dispatcher**, **external calls** (ERC20 `balanceOf`/`transfer`, ETH send),
solc **immutables** patched into the bytecode, vesting **arithmetic**, and `block.timestamp`. Priors:
**`Examples/Caller`** (the `CALL`↔Solm `externalCall`/`lowLevelCall` coupling, `Reasoning.ExternalCall`),
**`Examples/Auction`** (value sends + ratio arithmetic), **`Examples/Ballot`** (binary-search dispatch).

**Goal**
```
runtimeEquivalence!?! OpenZeppelinBench.VestingWallet.config …vestingWalletBenchBytecode …contract
```
no `sorry`/`admit`; axioms only `propext`/`Classical.choice`/`Quot.sound`/`ofReduceBool`. Optimizer-ON.
The bench fixes `start = 0`, `duration = 365 days (31536000)` as immutables patched into the runtime.

## Global rules (full text in `Examples/SimpleAuction/HANDOFF.md`)
1. Never duplicate — search `Reasoning/*` + `Common.lean`, **apply**; reuse → flag as refactor.
2. Respect/extend the library — missing general lemma → `Common.lean` (`-- LIBRARY CANDIDATE …`) or
   additively into `Reasoning/` if genuinely library-general.
3. One file per ABI function, parallel agents; each writes **only its own `<Fn>.lean`**.
4. Sandbox: only under `Examples/OpenZeppelinBench/VestingWallet/`; never edit `Spec.lean`/`Bytecode.lean`/
   another file (shared helpers → report for Phase 1.5).
5. Spec/Bytecode trusted — **if a body needs something the spec doesn't model (an opcode/expr that
   looks missing), STOP and report to the user**; don't edit `Spec.lean`. No new axiom; no `sorry`/`admit`.

## Dispatcher — **2-level** binary-search (3 GT pivots; reuse Ballot's `RD.gt`/`selectorSplit*` applied twice)

Lands at pc 18. 14 selectors ⇒ a depth-2 tree with **3 pivots**: `0x715018a6`, `0x96132521`,
`0xbe9a6555` (jump targets 183 / 124 / 87). **Phase-0 must disassemble and pin the exact tree shape**
(which pivot is the root, the two intermediate JUMPDESTs, each group's `firstArmPc`) and the `D_J` /
selector facts (new `Trusted.lean`). Full selector → body-PC map (verified):

| selector | function | body PC |   | selector | function | body PC |
|---|---|---|---|---|---|---|
| `0x0a17b06b` | `vestedAmount(uint64)`          | **231** | | `0x9852595c` | `released(address)`        | **503** |
| `0x0fb5a6b4` | `duration()`                   | **281** | | `0xa3f8eace` | `releasable(address)`      | **555** |
| `0x19165587` | `release(address)`             | **341** | | `0xbe9a6555` | `start()`                  | **586** |
| `0x715018a6` | `renounceOwnership()`          | **374** | | `0xefbe1c1c` | `end()`                    | **606** |
| `0x810ec23b` | `vestedAmount(address,uint64)` | **394** | | `0xf2fde38b` | `transferOwnership(address)`| **626** |
| `0x86d1a69f` | `release()`                    | **425** | | `0xfbccedae` | `releasable()`             | **657** |
| `0x8da5cb5b` | `owner()`                      | **445** | | `0x96132521` | `released()`               | **483** |

## Storage & immutables (hand-written in `Spec.lean`)
- `_owner` (address), `_released` (uint256), `_erc20Released` = `mapping(address => uint256)`.
- **`start` / `duration` are solc immutables**, *not* storage — patched into the runtime bytecode as
  PUSH constants (`start = 0`, `duration = 31536000`). `start()`/`duration()`/`end()` read the bytecode
  constant, **no SLOAD**. With `start = 0` the curve simplifies (`t - start = t`). The proof matches the
  PUSH constant; `Storage.lean` covers only `_released` (scalar) + `_erc20Released[token]` (mapping).

## Per-function files (parallel) — selectors/PCs above
| file | notes |
|---|---|
| `Owner.lean` / `Start.lean` / `Duration.lean` / `End.lean` / `Released.lean` / `ReleasedToken.lean` | getters: `_owner`; the two immutables; `end = start+duration`; `_released`; `_erc20Released[token]`. `Start`/`Duration` read **bytecode constants** (no storage). |
| `RenounceOwnership.lean` / `TransferOwnership.lean` | Ownable (one-step): `onlyOwner`; `_owner = 0` / `_owner = newOwner` (revert `OwnableInvalidOwner` on `newOwner == 0`). Share `onlyOwner` in `Common.lean`. |
| `VestedAmount.lean` (`uint64`) | the **vesting curve** over `totalAllocation = address(this).balance + _released`: `t < start → 0`; `t ≥ end → total`; else `total·(t-start)/duration`. Needs the `mul`/`div` + `min`/branch arithmetic lemmas (cf. Auction). `address(this).balance` = SELFBALANCE. **No external call.** |
| `VestedAmountToken.lean` (`address,uint64`) | same curve over `token.balanceOf(address(this)) + _erc20Released[token]` — **external call** (`token.balanceOf`) via `Reasoning.ExternalCall`. |
| `Releasable.lean` / `ReleasableToken.lean` | `vestedAmount(now) - released()` / `vestedAmount(token,now) - released(token)`; `now = uint64(block.timestamp)`. Reuse the `VestedAmount*` body lemmas (`prompt.md §3`). |
| `Release.lean` | `amount = releasable()`; `_released += amount`; **ETH send** `Address.sendValue(owner(), amount)` (`lowLevelCall` + success/`FailedCall` revert). Hardest. |
| `ReleaseToken.lean` | `amount = releasable(token)`; `_erc20Released[token] += amount`; **`SafeERC20.safeTransfer(token, owner(), amount)`** (`externalCall` + return-data success check / `SafeERC20FailedOperation`). Hardest. |

The vesting curve and `releasable = vestedAmount(now) − released` are shared by the ETH and token
paths — factor each as a reusable lemma in `Common.lean` and apply on both sides (`prompt.md §3`). The
`CALL` coupling for `balanceOf`/`transfer`/value-send goes through `Reasoning.ExternalCall` with the
external-call ABI from `Spec.lean`'s `config`.

> ⚠ **First check (any agent touching `Release*`/`VestedAmountToken`):** confirm `Spec.lean` already
> models `address(this).balance` (SELFBALANCE), `block.timestamp`, the immutable reads, and the ERC20
> `externalCall`/return-decoding. If any is absent, that is a *spec/Solm-expressiveness* gap — **stop and
> report to the user** (do not invent an encoding).

## Phases & per-function template: **see `Examples/SimpleAuction/HANDOFF.md`** (this contract's
`Correct.lean` has the 2-level no-match tails — see Phase-0's tree map). Finish:
```
lake build Examples.OpenZeppelinBench.VestingWallet.Correct
rg -n '\b(sorry|admit)\b' Examples/OpenZeppelinBench/VestingWallet
printf '%s\n' 'import Examples.OpenZeppelinBench.VestingWallet.Correct' \
  '#print axioms OpenZeppelinBench.VestingWallet.…Correct' | lake env lean --stdin
```
then add the import to `Examples.lean`.
