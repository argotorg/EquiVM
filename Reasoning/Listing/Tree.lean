import Reasoning.Listing.Basic
import Lean

/-!
# Listing — the table as a search tree

`List.lookup` on a contract's table walks the list, so looking up a late offset costs time
proportional to the number of sections.  A `Tree` holds the same `(offset, section)` pairs as a
binary search tree, so a lookup takes time proportional to its depth.

* `Tree.get?` looks an offset up, by structural recursion.
* `Tree.flat` lists the pairs in order.
* `Tree.get?_eq_lookup`: if a tree lists exactly the pairs of a list whose offsets strictly
  ascend, its lookup is the list's lookup.  (Nothing else about the tree is assumed: the keys
  are the pairs' own offsets, so the order of the listing is the search order.)
* `listing_tree tree from table` builds a balanced tree out of the constant `table`'s value, reusing
  the list's own element terms, adds it as the constant `tree`, and adds `tree_flat :
  tree.flat [] = table`, checked by the kernel as a definitional equality.  How the tree was
  built is not trusted; the kernel check is the guarantee.
-/

set_option autoImplicit false

namespace Reasoning.Listing

/-- A binary search tree of `(offset, section)` pairs. -/
inductive Tree where
  | empty
  | node (l : Tree) (p : Nat × Section) (r : Tree)

namespace Tree

/-- The section at offset `x`. -/
def get? : Tree → Nat → Option Section
  | empty, _ => none
  | node l p r, x => if x < p.1 then l.get? x else if x = p.1 then some p.2 else r.get? x

/-- The pairs in order, followed by `acc`. -/
def flat : Tree → List (Nat × Section) → List (Nat × Section)
  | empty, acc => acc
  | node l p r, acc => l.flat (p :: r.flat acc)

/-- The pairs in order. -/
def toList : Tree → List (Nat × Section)
  | empty => []
  | node l p r => l.toList ++ p :: r.toList

theorem flat_eq : ∀ (t : Tree) (acc : List (Nat × Section)), t.flat acc = t.toList ++ acc
  | empty, _ => rfl
  | node l p r, acc => by simp [flat, toList, flat_eq l, flat_eq r]

theorem lookup_append (x : Nat) : ∀ (A B : List (Nat × Section)),
    (A ++ B).lookup x = (A.lookup x).or (B.lookup x)
  | [], _ => by simp
  | (k, s) :: A, B => by
      simp only [List.cons_append, List.lookup_cons]
      split <;> simp [lookup_append x A B]

theorem lookup_none (x : Nat) : ∀ (L : List (Nat × Section)), (∀ q ∈ L, q.1 ≠ x) →
    L.lookup x = none
  | [], _ => rfl
  | (k, s) :: L, h => by
      have hk : (x == k) = false := by
        have := h (k, s) (by simp); simp only [beq_eq_false_iff_ne]; exact fun e => this e.symm
      rw [List.lookup_cons, hk]
      exact lookup_none x L (fun q hq => h q (by simp [hq]))

theorem get?_toList : ∀ (t : Tree), t.toList.Pairwise (fun a b => a.1 < b.1) →
    ∀ x, t.get? x = t.toList.lookup x
  | empty, _, _ => rfl
  | node l p r, hs, x => by
      simp only [toList] at hs ⊢
      rw [List.pairwise_append, List.pairwise_cons] at hs
      obtain ⟨hl, ⟨hp, hr⟩, hlr⟩ := hs
      have hlp : ∀ q ∈ l.toList, q.1 < p.1 := fun q hq => hlr q hq p (by simp)
      rw [get?, lookup_append]
      split
      · rename_i hx
        have : (p :: r.toList).lookup x = none :=
          lookup_none x _ (fun q hq => by
            rcases List.mem_cons.mp hq with rfl | hq
            · omega
            · have := hp q hq; omega)
        rw [this, get?_toList l hl x, Option.or_none]
      · rename_i hx
        rw [lookup_none x l.toList (fun q hq => by have := hlp q hq; omega), Option.none_or,
          List.lookup_cons]
        split
        · rename_i he
          simp [he]
        · rename_i he
          have hb : (x == p.1) = false := by simpa using he
          simp only [hb, get?_toList r hr x]

/-- **Tree lookup is list lookup**, for a tree that lists the pairs of a list whose offsets
strictly ascend. -/
theorem get?_eq_lookup {t : Tree} {L : List (Nat × Section)} (h : t.flat [] = L)
    (hs : L.Pairwise (fun a b => a.1 < b.1)) (x : Nat) : t.get? x = L.lookup x := by
  rw [flat_eq, List.append_nil] at h
  subst h
  exact get?_toList t hs x

end Tree

open Lean Elab Command Meta

/-- The elements of a list literal, as they occur in its term.  Long literals elaborate to
nested `let`s, and terms may carry metadata; both are looked through. -/
partial def listElems (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  let e := e.consumeMData
  if e.isAppOfArity ``List.cons 3 then listElems e.appArg! (acc.push e.appFn!.appArg!)
  else if e.isAppOfArity ``List.nil 1 then return acc
  else if e.isLet then listElems (e.letBody!.instantiate1 e.letValue!) acc
  else throwError "listing_tree: not a list literal at {e}"

/-- A balanced tree over `xs[lo:hi]`, its nodes holding the elements themselves. -/
partial def buildTree (xs : Array Expr) (lo hi : Nat) : Expr :=
  if hi ≤ lo then mkConst ``Tree.empty
  else
    let m := (lo + hi) / 2
    mkApp3 (mkConst ``Tree.node) (buildTree xs lo m) xs[m]! (buildTree xs (m + 1) hi)

/-- `listing_tree tree from table`: add the constant `tree : Reasoning.Listing.Tree`, a balanced search tree of
the pairs of the list constant `table`, and the theorem `tree_flat : tree.flat [] = table`,
checked by the kernel by definitional unfolding (`Eq.refl`). -/
syntax (name := listingTree) "listing_tree " ident " from " ident : command

@[command_elab listingTree] def elabListingTree : CommandElab := fun stx => do
  let name := stx[1].getId
  let src := stx[3]
  liftTermElabM do
    let srcName ← realizeGlobalConstNoOverloadWithInfo src
    let some c := (← getEnv).find? srcName | throwError "listing_tree: unknown constant {srcName}"
    let some v := c.value? | throwError "listing_tree: {srcName} has no value"
    let es ← listElems v #[]
    let full := (← getCurrNamespace) ++ name
    addDecl (.defnDecl { name := full, levelParams := [], type := mkConst ``Tree,
                         value := buildTree es 0 es.size, hints := .abbrev, safety := .safe,
                         all := [full] })
    let α := (← whnfR c.type).appArg!
    let lhs ← mkAppM ``Tree.flat #[mkConst full, mkApp (mkConst ``List.nil [levelZero]) α]
    let ty ← mkEq lhs (mkConst srcName)
    addDecl (.thmDecl { name := full.appendAfter "_flat", levelParams := [], type := ty,
                        value := ← mkEqRefl lhs, all := [full.appendAfter "_flat"] })

end Reasoning.Listing
