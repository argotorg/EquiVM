import Ethereum.Semantics

/-!
# JumpDest — one tactic for every `JUMPDEST`-membership obligation

Every `jump`/`jumpiT` step carries a proof that its destination `pc` is a valid jump target, i.e.
`(D_J <contract>Bytecode ⟨0⟩).contains pc = true`.  Each contract's bytecode file proves a
`@[valid_jumps]` theorem that turns this membership into a lookup in the tree of its sections
(`EVM/Disassembly/JumpTable.lean`).

Discharge every such obligation with the `jump_dest` tactic, which rewrites with that theorem and
decides the lookup.
-/

open Ethereum.EVM

/-- Simp set holding each contract's `…ValidJumps` theorem. -/
register_simp_attr valid_jumps

/-- Discharge a `(D_J …Bytecode ⟨0⟩).contains pc = true` JUMPDEST obligation.

The tactic rewrites by the contract's `@[valid_jumps]` theorem, then decides the tree lookup.
Contracts that still state their `JUMPDEST` set as an array fall back to `native_decide`.
This handles both literal targets and bytecode-derived targets such as `solcGuardTgt code`,
avoiding call-site `change` boilerplate. -/
macro "jump_dest" : tactic =>
  `(tactic| (simp only [valid_jumps]
             first
               | (with_reducible (show Option.getD _ false = true)); decide +kernel
               | native_decide))
