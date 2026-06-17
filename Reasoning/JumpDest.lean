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

/-- Discharge a `(D_J …Bytecode ⟨0⟩).contains ⟨pc⟩ = true` JUMPDEST obligation: unfold the
    contract's JUMPDEST set (via its `@[valid_jumps]`-tagged equation) and decide membership. -/
macro "jump_dest" : tactic =>
  `(tactic| (simp only [valid_jumps]; exact Array.contains_eq_true_of_mem (by simp)))

/-- Scanning more bytecode can only append discovered jump destinations, so an already-present
    target remains present.  This is useful for creation code with appended ABI constructor
    arguments: fixed jump destinations from the pure initcode remain valid even though the suffix is
    symbolic. -/
theorem D_J_aux_contains_of_contains {c : ByteArray} {i : ℕ}
    {result : Array Ethereum.UInt256} {target : Ethereum.UInt256}
    (h : result.contains target = true) :
    (D_J_aux c i result).contains target = true := by
  have hNincr : ∀ pc op, pc < N pc op := by
    intro pc op
    simp [N]
    omega
  have hmem_of_contains {xs : Array Ethereum.UInt256} {x : Ethereum.UInt256}
      (hx : xs.contains x = true) : x ∈ xs := by
    rw [Array.mem_iff_getElem]
    rw [Array.contains, Array.any_eq_true] at hx
    rcases hx with ⟨j, hj, hbeq⟩
    rw [beq_iff_eq] at hbeq
    exact ⟨j, hj, hbeq.symm⟩
  have aux :
      ∀ n i (result : Array Ethereum.UInt256),
        c.size - i = n →
        result.contains target = true →
        (D_J_aux c i result).contains target = true := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro i result hn hcontains
        unfold D_J_aux
        split
        · exact hcontains
        · rename_i op hparse
          apply ih (c.size - N i op)
          · rw [← hn]
            have hsize : i < c.size := by
              by_contra hlt
              have hget : c.get? i = none := by
                simp [ByteArray.get?, Nat.not_lt.mp hlt]
              rw [hget] at hparse
              simp [bind, Option.bind] at hparse
            exact Nat.sub_lt_sub_left hsize (hNincr i op)
          · rfl
          · split
            · exact Array.contains_eq_true_of_mem (by simp [hmem_of_contains hcontains])
            · exact hcontains
  exact aux (c.size - i) i result rfl h
