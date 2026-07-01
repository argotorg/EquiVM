# ERC20 Proof Guide

This note records the proof architecture, lessons learned, and working instructions for agents
maintaining or extending the ERC20 correctness proof.

## Current State

The ERC20 correctness proof is discharged through `Examples/ERC20/Correct.lean`, with the per-body
proofs factored into ERC20-local helper files.

Expected local validation:

```bash
lake build Examples.ERC20.Correct
```

ERC20 should have no `sorry` or `admit`:

```bash
rg -n '\b(sorry|admit)\b' Examples/ERC20
```

The remaining ERC20-local trusted facts are intentional:

- Function selector byte axioms in `Examples/ERC20/Bytecode.lean`.

ERC20 should not need storage-layout noncollision axioms. `ffi.KEC` is opaque, so Lean cannot prove
general Keccak noncollision facts, but the ERC20 proof should avoid depending on such facts by
matching the source semantics and bytecode storage reads exactly.

## File Roles

- `Correct.lean` is the top-level dispatcher and final assembly. Preserve its shape.
- `TotalSupply.lean`, `BalanceOf.lean`, `Allowance.lean`, `Approve.lean`, `Transfer.lean`, and
  `TransferFrom.lean` contain function-specific source/EVM/refinement proofs.
- `Common.lean` contains ERC20-wide ABI, memory, selector, and return helpers.
- `Storage.lean` contains ERC20-wide storage load/store, RBMap preservation, and bool-return facts.
- `Spec.lean` defines the Solm ERC20 spec and storage layout. Do not silently change it.
- `Bytecode.lean` defines runtime bytecode and selector/jump trusted facts.

## Proof Architecture

The top-level theorem follows the standard solc dispatcher path:

1. Prologue and non-payable guard.
2. Calldata size guard.
3. Selector load.
4. Selector-arm matching with `RD.dispatchTo`.
5. Dispatch to one body proof per ERC20 function.
6. Separate no-dispatch, short-calldata, and nonpayable revert paths.

Each function proof follows the same broad pattern:

1. Prove ABI decoding for valid calldata and all malformed calldata branches.
2. Prove the Solm source body result.
3. Prove EVM reachability through natural phases.
4. Connect source and EVM results with `reEquiv`.

For mutating functions, split success and revert branches early. Do not try to prove the whole
trace in one giant script.

## Lessons Learned

### Keep The Dispatcher Top-Level Thin

`Correct.lean` should mostly route. Body-specific complexity belongs in the relevant function file.
This keeps failures local and avoids re-elaborating the whole final theorem while developing a body
proof.

### Use Existing Solc And ABI Infrastructure First

Before writing arithmetic or calldata proofs by hand, search:

```bash
rg -n 'decodeCalldata|evmSelectorDecode|solc|dispatch|reEquiv|storageLoc' Reasoning Examples
```

Useful libraries in this proof were:

- `Reasoning.Dispatch` for selector routing and no-dispatch cases.
- `Reasoning.ABIDecode` for scalar tuple decoding.
- `Reasoning.Solc` for solc guards, selector load, and common wrappers.
- `Reasoning.Reach` for EVM stepping and reachability.
- `Reasoning.Memory` for mapping-slot and storage-load coupling.
- `Reasoning.SolmBody` and `Reasoning.Refinement` for source execution and equivalence.

### Prove Storage Map Behavior Separately From Layout

Ordinary map facts are provable and live in `Storage.lean`:

- Insert at one slot preserves lookup at a different slot.
- Erase at one slot preserves lookup at a different slot.
- EVM/Solidity zero-write update preserves lookup at a different slot.

Do not hide these as axioms. If a proof appears to need a cryptographic noncollision fact, first
check whether the source model is accidentally caching a storage value across an intervening write
while the bytecode actually reloads storage. In that case, fix the source model or proof split rather
than asserting that two Keccak-derived slots differ.

### The TransferFrom Pitfall

`transferFrom` is the only place where the compiled bytecode reloads `balanceOf[from]` after
storing `allowance[from][msg.sender]`. The source has:

```solidity
require(balanceOf[from] >= value, "ERC20: insufficient balance");
allowance[from][msg.sender] = currentAllowance - value;
balanceOf[from] -= value;
```

The `require` reads `balanceOf[from]`, but the compound assignment `balanceOf[from] -= value`
performs another storage read at the assignment site. The Solm spec must model that second read:

```lean
.assign (balanceOfRef (.var "from"))
  (valueInUInt256
    (.binary .sub (.storage (balanceOfRef (.var "from"))) (.var "value")))
```

Do not replace this with subtraction from the earlier `fromBalance` local. That shortcut creates a
false mismatch: the EVM proof then needs to show that writing `allowance[from][msg.sender]` cannot
affect `balanceOf[from]`, which is a Keccak noncollision fact unavailable in the current model.

The correct proof split has two balance facts:

- `hbalance`: the original balance is large enough for the source-level `require`.
- `hbalanceDebit`: the balance reread after the allowance store is large enough for the checked
  subtraction.

If `hbalanceDebit` fails, both source and bytecode revert through the Solidity checked-subtraction
panic path. This branch is what lets the proof stay axiom-free even in the opaque-`KEC` model.

### Avoiding New Axioms

Before adding any axiom, run through this checklist:

1. Identify the exact source expression and the exact bytecode read/write sequence.
2. Check whether a source storage compound assignment should be modeled as a fresh storage read.
3. Check whether an optimizer-style local in the Solm spec is stronger than the Solidity source.
4. Prove ordinary map behavior over `RBMap`/storage maps locally; do not axiomatize map updates.
5. If the remaining obligation is truly cryptographic, isolate it behind a narrow, documented
   boundary and first ask whether the spec/proof can be refactored to avoid depending on it.
6. After any change, inspect the final theorem's trusted footprint:

```bash
printf '%s\n' 'import Examples.ERC20.Correct' \
  '#print axioms ERC20.erc20Correct' | lake env lean --stdin
```

A targeted check for removed or suspicious axioms is often easier to read:

```bash
printf '%s\n' 'import Examples.ERC20.Correct' \
  '#print axioms ERC20.erc20Correct' | lake env lean --stdin 2>&1 | rg 'axiom_name'
```

### ERC20 Has No External Calls

ERC20 does not use `CALL`, and it does not depend on `Reasoning.ExternalCall`. If an aggregate
`Examples` build reports an `ExternalCall` failure, trace the import graph before treating it as an
ERC20 issue. The local ERC20 target is:

```bash
lake build Examples.ERC20.Correct
```

### Check One Heavy File At A Time

`Transfer.lean` and especially `TransferFrom.lean` can take several minutes to rebuild. During
development, check the edited helper first, then the dependent function file, then the top-level
ERC20 target.

Recommended order:

```bash
lake env lean Examples/ERC20/Storage.lean
lake build Examples.ERC20.TransferFrom
lake build Examples.ERC20.Correct
```

Adjust the first two commands to match the file being edited.

## Agent Instructions

1. Preserve the existing top-level shape in `Correct.lean`.
2. Keep function-specific helpers in the function file.
3. Put repeated ERC20-specific helpers in `Common.lean` or `Storage.lean`.
4. Do not move general-looking lemmas into `Reasoning/` during ERC20 work unless explicitly asked.
5. Do not edit `Spec.lean` just to make a proof easier. If the spec looks wrong, stop, explain the
   source/bytecode mismatch, and get approval before changing it.
6. Do not edit `Bytecode.lean` selector facts casually; they are trusted bytecode facts.
7. For mapping accesses, first identify the Solidity slot expression, then prove the bytecode
   scratch-memory `KECCAK256` path computes the same slot.
8. For mutating bodies, prove source behavior and EVM reachability branch by branch.
9. Treat warnings as cleanup opportunities, but prioritize proof correctness and stable structure.
10. Before introducing an axiom, document why every proof-preserving alternative failed.
11. Always finish with `lake build Examples.ERC20.Correct`, a `sorry`/`admit` scan, and an axiom
    footprint check for any new trusted names.

## Common Failure Modes

- Assuming an aggregate `Examples` failure is ERC20-related without checking imports.
- Adding a layout axiom for a basic map update fact that should be proved over `RBMap`.
- Adding a Keccak noncollision axiom before checking whether the source spec should reread storage.
- Trying to prove Keccak noncollision from the current `ffi.KEC` definition.
- Duplicating long calldata-decoding or memory lemmas instead of reusing existing ABI/Solc helpers.
- Letting a function proof grow into a single all-at-once `evm_run` block.

## Future Infrastructure Candidates

These would be useful to promote later, but should remain ERC20-local during scoped ERC20 work:

- A generic `RBMap.find?_erase_ne` theorem.
- A generic storage-update preserves lookup theorem for zero-erasing EVM storage maps.
- A reusable tactic or lemma family for solc-generated mapping-slot scratch-memory sequences.
- A formal, explicit Keccak layout assumption layer for proofs that truly cannot avoid Solidity
  mapping noncollision.
