import EVM.Disassembly.Basic

/-!
# Sections as a search tree

Looking up a section by its offset in a list takes linear time. `Tree` stores the same
`(offset, section)` pairs as a binary search tree. `Tree.get?_eq_lookup` shows that the two
lookups agree whenever the pairs of the tree, read in order, have ascending offsets. The tree
does not have to be balanced for this.
-/

set_option autoImplicit false

namespace EVM.Disassembly

/-- A binary search tree of sections, keyed by offset. -/
inductive Tree where
  | empty
  | node (l : Tree) (p : Nat × List Instr) (r : Tree)

namespace Tree

/-- The section at offset `x`. -/
def get? : Tree → Nat → Option (List Instr)
  | empty, _ => none
  | node l p r, x => if x < p.1 then l.get? x else if x = p.1 then some p.2 else r.get? x

/-- The pairs in order, prepended to `acc`. -/
def flat : Tree → List (Nat × List Instr) → List (Nat × List Instr)
  | empty, acc => acc
  | node l p r, acc => l.flat (p :: r.flat acc)

/-- The pairs in order. -/
def toList : Tree → List (Nat × List Instr)
  | empty => []
  | node l p r => l.toList ++ p :: r.toList

theorem flat_eq : ∀ (t : Tree) (acc : List (Nat × List Instr)), t.flat acc = t.toList ++ acc
  | empty, _ => rfl
  | node l p r, acc => by simp [flat, toList, flat_eq l, flat_eq r]

theorem get?_toList : ∀ (t : Tree), t.toList.Pairwise (fun a b => a.1 < b.1) →
    ∀ x, t.get? x = t.toList.lookup x
  | empty, _, _ => rfl
  | node l p r, hs, x => by
      simp only [toList] at hs ⊢
      rw [List.pairwise_append, List.pairwise_cons] at hs
      obtain ⟨hl, ⟨hp, hr⟩, hlr⟩ := hs
      have hlp : ∀ q ∈ l.toList, q.1 < p.1 := fun q hq => hlr q hq p (by simp)
      rw [get?, List.lookup_append]
      split
      · rename_i hx
        have : (p :: r.toList).lookup x = none :=
          List.lookup_eq_none_iff.mpr fun q hq => bne_iff_ne.mpr fun e => by
            rcases List.mem_cons.mp hq with rfl | hq
            · omega
            · have := hp q hq; omega
        rw [this, get?_toList l hl x, Option.or_none]
      · rename_i hx
        rw [List.lookup_eq_none_iff.mpr fun q hq => bne_iff_ne.mpr fun e => by
            have := hlp q hq; omega, Option.none_or,
          List.lookup_cons]
        split
        · rename_i he
          simp [he]
        · rename_i he
          have hb : (x == p.1) = false := by simpa using he
          simp only [hb, get?_toList r hr x]

/-- Lookup in the tree is lookup in the list of its pairs, if the offsets are ascending. -/
theorem get?_eq_lookup {t : Tree} {L : List (Nat × List Instr)} (h : t.flat [] = L)
    (hs : L.Pairwise (fun a b => a.1 < b.1)) (x : Nat) : t.get? x = L.lookup x := by
  rw [flat_eq, List.append_nil] at h
  subst h
  exact get?_toList t hs x

end Tree

end EVM.Disassembly
