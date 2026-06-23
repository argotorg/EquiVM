# OZ Ownable2Step (bench) — proof handoff

Read **`prompt.md`** (repo root), **`Reasoning/GUIDE.md`**, **`Examples/ERC20/PROOF_GUIDE.md`**, and the
canonical **`Examples/SimpleAuction/HANDOFF.md`** first — that file holds the **full global rules, the
4-phase plan, the per-function prompt template, and the Concurrency model**; everything there applies
here verbatim. This file only records the Ownable2Step-specific facts. Optimizer-ON exemplar to copy:
`Examples/Ballot`. (There is also an in-progress `Examples/Ownable2Step/` proof of the same contract —
crib from it where useful, but this bench target is its own sandbox.)

**Goal**
```
OpenZeppelinBench.Ownable2Step.config ⊢
  runtimeEquivalence!?! …config …ownable2StepBenchBytecode …contract   -- in Correct.lean
```
no `sorry`/`admit`; axioms only `propext`/`Classical.choice`/`Quot.sound` + expected `ofReduceBool`.
Optimizer-ON (`solc --optimize`, 0.8.35). This is the **easiest** OZ bench: 2 address slots, no
mappings, no loops, no external calls.

## Global rules (full text in `Examples/SimpleAuction/HANDOFF.md`)
1. Never duplicate — search `Reasoning/*` + this dir's `Common.lean` and **apply**; reuse → flag as
   refactor.
2. Respect/extend the library — a missing general lemma goes (proved) in `Common.lean` tagged
   `-- LIBRARY CANDIDATE …`, or additively into the right `Reasoning/` module if genuinely library-general.
3. One file per ABI function, agents run in parallel; each writes **only its own `<Fn>.lean`**.
4. Sandbox: write only under `Examples/OpenZeppelinBench/Ownable2Step/`; never edit `Spec.lean` /
   `Bytecode.lean` / another file (shared helpers → report for the Phase-1.5 reconcile agent).
5. Spec/Bytecode are trusted — if the spec looks wrong, **stop and report to the user**, don't edit.
   No new axiom; no `sorry`/`admit`.

## Dispatcher — **linear** (like ERC20/Pow), lands at pc 18; arms ascending by selector

| selector | function | body PC | notes |
|---|---|---|---|
| `0x715018a6` | `renounceOwnership()`        | **89**  | `onlyOwner`; `_owner = address(0)`. |
| `0x79ba5097` | `acceptOwnership()`         | **99**  | `require(msg.sender == _pendingOwner)` (else `OwnableUnauthorizedAccount`); `_pendingOwner = 0`; `_owner = msg.sender`. |
| `0x8da5cb5b` | `owner()`                   | **107** | getter `_owner`. |
| `0xe30c3978` | `pendingOwner()`            | **147** | getter `_pendingOwner`. |
| `0xf2fde38b` | `transferOwnership(address)`| **164** | `onlyOwner`; `_pendingOwner = newOwner` (does **not** set `_owner` and does **not** reject `0`). |

`onlyOwner` = `require(msg.sender == _owner)` (else `OwnableUnauthorizedAccount`) — a shared check; put
it in `Common.lean` once. Phase-0 must pin the linear `firstArmPc` and the `@[valid_jumps]` `D_J` /
selector facts in a new `Trusted.lean` (do **not** edit `Bytecode.lean`).

## Storage
Hand-written layout already in `Spec.lean`: `_owner` @ slot 0 (address, offset 0, 20 bytes),
`_pendingOwner` @ slot 1 (address). Two scalar slots — `Storage.lean` needs only trivial
single-slot load/store facts (no mapping/keccak reasoning).

## Per-function files (parallel): `RenounceOwnership`, `AcceptOwnership`, `Owner`, `PendingOwner`,
`TransferOwnership`. The three getters are thin; the two mutators each have one `require`
(unauthorized) revert branch + one scalar store — split success/revert early.

## Phases 0 / 1 / 1.5 / 2 and the per-function prompt template: **see
`Examples/SimpleAuction/HANDOFF.md`** (same structure; `Correct.lean` here has one revert tail — the
linear no-match fall-through — not two). Finish:
```
lake build Examples.OpenZeppelinBench.Ownable2Step.Correct
rg -n '\b(sorry|admit)\b' Examples/OpenZeppelinBench/Ownable2Step
printf '%s\n' 'import Examples.OpenZeppelinBench.Ownable2Step.Correct' \
  '#print axioms OpenZeppelinBench.Ownable2Step.…Correct' | lake env lean --stdin
```
then add the import to `Examples.lean`.
