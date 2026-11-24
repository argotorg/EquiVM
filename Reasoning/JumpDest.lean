import Ethereum.Semantics

/-!
# JumpDest — one tactic for every `JUMPDEST`-membership obligation

Every `jump`/`jumpiT` step carries a proof that its destination `pc` is a valid jump target, i.e.
`(D_J <contract>Bytecode ⟨0⟩).contains pc = true`.  A contract's listing written with
`scripts/gen_listing.py --valid-jumps <name>` states, as the theorem `<name>` tagged
`@[valid_jumps]`, that this membership is a lookup in the listing's search tree
(`(D_J code 0).contains t = ((tree.get? t.toNat).map startsJD).getD false`, proved from the
kernel-checked table by `Reasoning/Listing/JumpTable.lean`).

The `jump_dest` tactic rewrites with that theorem and evaluates the lookup in the kernel — no
per-contract macro, no `native_decide`, and no open-coded `rw [<contract>ValidJumps]; exact …`.
-/

open Ethereum.EVM

/-- Simp set holding each contract's `…ValidJumps` membership equation (a listing's
    `--valid-jumps` theorem). -/
register_simp_attr valid_jumps

/-- Discharge a `(D_J …Bytecode ⟨0⟩).contains pc = true` JUMPDEST obligation.

The tactic rewrites by the contract's `@[valid_jumps]` equation, then decides the closed tree
lookup by `decide +kernel`.  This handles both literal targets and bytecode-derived targets such
as `solcGuardTgt code` (the kernel reads the target from the listing's bytes), avoiding
call-site `change` boilerplate. -/
macro "jump_dest" : tactic =>
  `(tactic| (simp only [valid_jumps]; decide +kernel))
