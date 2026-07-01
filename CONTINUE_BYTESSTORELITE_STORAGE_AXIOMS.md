# BytesStoreLite continuation: remove storage-keccak assumptions

## Objective

Continue the BytesStoreLite proof cleanup until the only BytesStoreLite-specific trusted keccak
facts left are function-selector hashes. In particular, eliminate storage-layout/hash assumptions
by making the proofs collision-aware, even if this requires case analysis for possible slot
collisions.

Target trusted boundary:

- Keep selector hash axioms in:
  - `Examples/BytesStoreLite/Bytecode.lean`
  - `Examples/BytesStoreLite/CoreBytecode.lean`
- Remove or avoid all storage-keccak/layout axioms:
  - `Examples/BytesStoreLite/StorageFacts.lean`
    - `bytesLikeDataWordSlot_ne_base`
    - `bytesStoreLiteChunkDataWordSlot_ne_length`
  - `Examples/BytesStoreLite/Bytecode.lean`
    - `bytesStoreLiteChunksDataBaseLiteral`

The desired proof style is not "assume no collision"; it is "prove both cases". Where a write slot
can alias a read/header slot, follow the bytecode write order on the Solm side and prove that the
same final storage value is produced.

## Current status

The worktree is dirty and contains user/generated changes. Do not revert unrelated files.

The most recent fully completed targeted build was:

```sh
lake build Examples.BytesStoreLite.CoreCorrect Examples.BytesStoreLite.CoreSetLongNewLong Examples.BytesStoreLite.CoreSetLongNewShortOldShort Examples.BytesStoreLite.CoreSetOldLong
```

That build passed. It took several minutes because the core proof files are large.

A later integration build was started:

```sh
lake build Examples.BytesStoreLite.Correct
```

It was interrupted by user interaction before final completion. Before interruption it had already
rebuilt `StorageLayoutFacts`, `FullPacketTag`, `FullSetPacketStorage`,
`FullPushChunkLongTail`, `FullSetLongOldLong`, `FullPushChunkCalldataWords`,
`FullSetLongOldLongReturn`, and `FullSetLongOldLongRuntime`. The only warning seen was the known:

```text
Examples/BytesStoreLite/FullPacketTag.lean:7874:5: unused variable `hlong`
```

## Important completed refactors

### Collision-aware storage helpers

`Reasoning/Storage.lean` now has collision-aware storage readback lemmas:

- `sstoreAccountMap_storage_findD_eq_if`
- `storageLoad_storageStore_eq_if`

The older non-collision corollaries remain:

- `sstoreAccountMap_storage_findD_ne`
- `storageLoad_storageStore_ne`

Use the `_eq_if` lemmas as the basis for removing non-collision assumptions. They expose the real
branch point:

```lean
if writeSlot = readSlot then val else oldValue
```

### Trusted storage boundary currently isolated

The symbolic storage-layout assumptions were isolated into:

- `Examples/BytesStoreLite/StorageFacts.lean`
- `Examples/BytesStoreLite/StorageLayoutFacts.lean`

`StorageFacts.lean` currently declares exactly the two storage separation axioms. It also derives:

- `bytesLikeDataSlot_ne_base`
- `bytesStoreLiteChunksElemSlot_ne_length`

`StorageLayoutFacts.lean` packages loop-shaped corollaries:

- `bytesStoreLiteChunkClearDataLoopSlot_ne_length`
- `bytesStoreLiteChunkLongDataLoopSlot_ne_length`
- `bytesStoreLiteChunkDataSlot_ne_length`

These files are temporary scaffolding. The end state should delete or empty `StorageFacts.lean` and
replace downstream uses with collision-aware proofs.

### Account-map load scaffolding generalized

`Examples/BytesStoreLite/CoreGetters.lean` contains:

```lean
theorem currentLengthStorageLoad_initState_of_accountMapEquiv
```

This factors the repeated proof that an init-state Solm load of slot `0` equals
`currentLengthHeaderWord σ_evm I` under `accountMapEquiv`.

The visible repeated `currentLengthHeaderWord_eq_of_accountMapEquiv` / local `hslot` scaffolding has
already been replaced in:

- `CoreGetters.lean`
- `CoreCorrect.lean`
- `CoreSetLongNewLong.lean`
- `CoreSetLongNewShortOldShort.lean`
- `CoreSetOldLong.lean`

Targeted core build passed after these replacements.

### Local lookup duplication reduced

Several byte setter proofs now have small locals-lookup helper lemmas instead of repeated inline
`store_get_ne` / `store_get_self` chains:

- `FullPacketTag.lean`
- `FullSetPacketByte.lean`
- `FullSetChunkByte.lean`
- `FullSetMappedByte.lean`

The previously verified command was:

```sh
lake build Examples.BytesStoreLite.FullSetByte Examples.BytesStoreLite.FullSetPacketByte Examples.BytesStoreLite.FullSetChunkByte Examples.BytesStoreLite.FullSetMappedByte
```

and then:

```sh
lake build Examples.BytesStoreLite.Correct
```

Both passed at that earlier point.

## Current storage axioms and downstream uses

Run this to refresh the exact locations:

```sh
rg -n "bytesLikeDataSlot_ne_base|bytesStoreLiteChunksElemSlot_ne_length|bytesStoreLiteChunk.*ne_length|bytesStoreLiteChunksDataBaseLiteral" Examples/BytesStoreLite
```

At the time of this handoff, the key uses were:

- `Examples/BytesStoreLite/FullPacketTag.lean`
  - around `1990`: `if_neg (bytesLikeDataSlot_ne_base baseSlot idx).symm`
  - around `2028`: `if_neg (bytesLikeDataSlot_ne_base baseSlot idx).symm`
  - around `2132`: `if_neg (bytesStoreLiteChunksElemSlot_ne_length chunkIndex).symm`
  - around `2174`: `if_neg (bytesStoreLiteChunkDataSlot_ne_length chunkIndex idx).symm`
  - around `2205`: `if_neg (bytesStoreLiteChunksElemSlot_ne_length chunkIndex).symm`
  - around `2240`: `if_neg (bytesStoreLiteChunkDataSlot_ne_length chunkIndex idx).symm`
  - around `2273`: `if_neg (bytesStoreLiteChunksElemSlot_ne_length oldLen)`
  - around `2305`: `if_neg (bytesStoreLiteChunksElemSlot_ne_length oldLen)`
- `Examples/BytesStoreLite/FullSetChunkOldLongReturn.lean`
  - imports `StorageLayoutFacts`
  - uses `bytesStoreLiteChunkClearDataLoopSlot_ne_length`
  - uses `bytesStoreLiteChunkLongDataLoopSlot_ne_length`
- `Examples/BytesStoreLite/FullPushChunkLongStorage.lean`
  - imports `StorageLayoutFacts`
- `Examples/BytesStoreLite/Bytecode.lean`
  - declares `bytesStoreLiteChunksDataBaseLiteral`

Do not start by deleting these axioms. First convert their immediate consumers to a branch/case
shape using the `_eq_if` storage helpers. Delete the axioms only when `rg` shows no uses.

## Strategy to remove the two separation axioms

### 1. Start with `FullPacketTag.lean`

This file already has the generic readback wrappers near the top of the storage-helper section:

- `sstoreAccountMap_storage_findD_eq_if`
- `storageLoad_storageStore_eq_if`

Find the helper lemmas around the `if_neg (...)` uses listed above. They are currently proving that
after a write to a data slot, reading the header/length slot is unchanged.

Replace each helper with a collision-aware statement. The replacement should usually return an
`if` expression rather than requiring `slot ≠ slot`.

Example shape:

```lean
Solm.EVM.storageLoad (Solm.EVM.storageStore evm owner writeSlot val) owner readSlot =
  if writeSlot = readSlot then val else Solm.EVM.storageLoad evm owner readSlot
```

Then adapt each caller by splitting:

```lean
by_cases hcollision : writeSlot = readSlot
```

In the `hcollision` branch, simplify the Solm post-state using the same write order as bytecode.
In the non-collision branch, recover the previous proof with `if_neg hcollision`.

The important design constraint: do not thread a non-collision hypothesis through large parts of a
proof that only use account-map equivalence. Split as late as possible, at the readback or final
post-state equality point.

### 2. Generalize loop facts before expanding callers

`StorageLayoutFacts.lean` currently proves loop slots are not `1`. Replace those facts with
collision-aware loop readback lemmas.

For loops clearing/writing dynamic data words, useful shapes are likely:

```lean
storageLoad (clearLoop evm ...) owner lengthSlot =
  if anyWrittenSlotEqLengthSlot then finalWrittenValue else oldLength
```

or, if encoding "any slot" is too heavy, recurse with the existing loop index and expose one `if`
per step. This is more verbose but follows Lean's existing recursion structure better.

Prefer small recursive helper lemmas over a large all-at-once theorem. The current loop facts are
already separated into:

- clear loop slot facts
- long data words loop slot facts
- direct data slot facts

Keep that separation, but make the statements collision-aware.

### 3. Preserve bytecode/Solm write order

The user specifically expects the non-collision axioms to be unnecessary if the Solm side emulates
the bytecode order. That is the correct invariant to maintain.

When a collision branch appears surprising, inspect the bytecode trace lemma and the Solm helper
being used. If they perform writes in different orders, fix the Solm helper/proof plumbing so the
sequence matches bytecode rather than adding another assumption.

Practical places to inspect:

- `FullSetChunkOldLongReturn.lean`
- `FullPushChunkLongStorage.lean`
- `FullPacketTag.lean`
- storage write helpers imported from `CoreSetOldLong.lean`

### 4. Remove `bytesStoreLiteChunksDataBaseLiteral`

This axiom is not a selector hash. It states that the optimized runtime literal for
`keccak256(uint256(1))` equals `chunksDataBase`.

To meet the target "only selector keccak hashes remain", handle this after the separation axioms.
There are two possible approaches:

1. Preferred if the project wants to keep Solidity-layout semantics explicit:
   prove the concrete storage base using whatever trusted computation mechanism is acceptable for
   storage hashes. If no such mechanism is acceptable, this cannot become a theorem over opaque
   `ffi.KEC`.

2. Preferred if the project wants no storage keccak facts at all:
   introduce a contract-specific compiled layout constant for the chunks data base, use the bytecode
   literal directly in both the bytecode-side and Solm-side BytesStoreLite spec/proofs, and stop
   stating that it equals `ffi.KEC 1`. This removes the axiom from the equivalence proof boundary,
   but it means the proof is about the compiled contract's concrete storage layout rather than a
   general theorem deriving Solidity's keccak layout.

Do not silently choose between these. The next conversation should confirm which interpretation is
desired if the answer is not already obvious from local project conventions.

## Suggested next commands

Refresh axiom/use inventory:

```sh
rg -n "axiom|bytesLikeDataWordSlot_ne_base|bytesStoreLiteChunkDataWordSlot_ne_length|bytesStoreLiteChunksDataBaseLiteral" Examples/BytesStoreLite Reasoning
```

Inspect the immediate consumers:

```sh
sed -n '1960,2320p' Examples/BytesStoreLite/FullPacketTag.lean
sed -n '1,150p' Examples/BytesStoreLite/FullSetChunkOldLongReturn.lean
sed -n '1,140p' Examples/BytesStoreLite/StorageLayoutFacts.lean
```

Build after each small conversion:

```sh
lake build Examples.BytesStoreLite.FullPacketTag
lake build Examples.BytesStoreLite.FullSetChunkOldLongReturn
lake build Examples.BytesStoreLite.FullPushChunkLongStorage
lake build Examples.BytesStoreLite.Correct
```

If build times become painful, split proof files rather than duplicating proof logic. The user has
explicitly allowed file splitting to help build times.

## Notes for the next Codex run

- Use `rg` first; avoid broad manual browsing.
- Use `apply_patch` for manual edits.
- Do not revert unrelated dirty worktree changes.
- Existing warnings about `FullPacketTag.lean` unused `hlong` are known and not the current blocker.
- The proof is long but moving. The current blocker is not conceptual impossibility; it is converting
  non-collision-shaped helper lemmas into collision-aware case splits while preserving write order.
