import Ethereum.Semantics

/-!
# JumpDest — one tactic for every `JUMPDEST`-membership obligation

Every `jump`/`jumpiT` step carries a proof that its destination `pc` is a valid jump target, i.e.
`(D_J <contract>Bytecode ⟨0⟩).contains ⟨pc⟩ = true`.  Each contract has a trusted axiom
`<contract>ValidJumps : D_J <contract>Bytecode ⟨0⟩ = #[…]` listing its `JUMPDEST` set; the proof is
always "rewrite by that axiom, then decide membership".

Tag each such axiom with `@[valid_jumps]` and discharge every obligation with the `jump_dest`
tactic — no per-contract macro and no open-coded `rw [<contract>ValidJumps]; exact …` needed.
-/

open Ethereum.EVM

/-- Simp set holding each contract's `…ValidJumps` JUMPDEST-set equation.  Tag the per-contract
    `axiom …ValidJumps : D_J …Bytecode ⟨0⟩ = #[…]` with `@[valid_jumps]`. -/
register_simp_attr valid_jumps

/-- Discharge a `(D_J …Bytecode ⟨0⟩).contains ⟨pc⟩ = true` JUMPDEST obligation.

The tactic unfolds the contract's precomputed `@[valid_jumps]` table, then computes the closed
membership check.  This handles both literal targets and bytecode-derived targets such as
`solcGuardTgt code`, avoiding call-site `change` boilerplate. -/
macro "jump_dest" : tactic =>
  `(tactic| (simp only [valid_jumps]; decide +native))
