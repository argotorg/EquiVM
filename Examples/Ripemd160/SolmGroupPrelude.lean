import Examples.Ripemd160.SolmRightRoundLoop

/-!
# RIPEMD-160 Solm group preludes

Table selection and per-group additive constants for the authored compression loops.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

def leftGroupPrelude : List Stmt :=
  [ .internalCall "wordRowL" [.var "groupL"] "wordTableL",
    .internalCall "rotRowL" [.var "groupL"] "rotTableL",
    .letDecl "kL" uint256Ty (.intLit 0),
    .ite (.binary .eq (.var "groupL") (.intLit 1))
      [.assign .localVar { base := "kL" } (.intLit 0x5a827999)] [],
    .ite (.binary .eq (.var "groupL") (.intLit 2))
      [.assign .localVar { base := "kL" } (.intLit 0x6ed9eba1)] [],
    .ite (.binary .eq (.var "groupL") (.intLit 3))
      [.assign .localVar { base := "kL" } (.intLit 0x8f1bbcdc)] [],
    .ite (.binary .eq (.var "groupL") (.intLit 4))
      [.assign .localVar { base := "kL" } (.intLit 0xa953fd4e)] [] ]

def leftGroupPreludeStore (L : Store) (group : Nat) : Store :=
  let L1 := L.insert "wordTableL" (wordValue (leftWordRowWord group))
  let L2 := L1.insert "rotTableL" (wordValue (leftRotationRowWord group))
  let L3 := L2.insert "kL" (wordValue (leftConstantWord 0))
  match group with
  | 0 => L3
  | _ => L3.insert "kL" (wordValue (leftConstantWord group))

theorem leftGroupPreludeStore_get_original (L : Store) (group : Nat) (name : Ident)
    (hword : ("wordTableL" == name) = false)
    (hrot : ("rotTableL" == name) = false) (hk : ("kL" == name) = false) :
    (leftGroupPreludeStore L group).get? name = L.get? name := by
  cases group <;> simp only [leftGroupPreludeStore] <;>
    repeat' rw [store_get_ne _ _ (by assumption)]

theorem leftGroupPreludeStore_word (L : Store) (group : Nat) :
    (leftGroupPreludeStore L group).get? "wordTableL" =
      some (wordValue (leftWordRowWord group)) := by
  cases group <;> simp only [leftGroupPreludeStore] <;>
    repeat' first | rw [store_get_self] | rw [store_get_ne _ _ (by decide)]

theorem leftGroupPreludeStore_rotation (L : Store) (group : Nat) :
    (leftGroupPreludeStore L group).get? "rotTableL" =
      some (wordValue (leftRotationRowWord group)) := by
  cases group <;> simp only [leftGroupPreludeStore] <;>
    repeat' first | rw [store_get_self] | rw [store_get_ne _ _ (by decide)]

theorem leftGroupPreludeStore_constant (L : Store) (group : Nat) :
    (leftGroupPreludeStore L group).get? "kL" =
      some (wordValue (leftConstantWord group)) := by
  cases group <;> simp only [leftGroupPreludeStore] <;> rw [store_get_self]

theorem rowNatValue_eq_wordValue_leftWord (group : Nat) (hg : group < 5) :
    natValue (Model.leftWordRow group) = wordValue (leftWordRowWord group) := by
  interval_cases group <;> native_decide

theorem rowNatValue_eq_wordValue_leftRotation (group : Nat) (hg : group < 5) :
    natValue (Model.leftRotationRow group) = wordValue (leftRotationRowWord group) := by
  interval_cases group <;> native_decide

theorem evalLeftConstantLit {L : Store} {evm : EVM.State} (group : Nat) (hg : group < 5) :
    evalExpr? config { contract := contract, locals := L } evm
      (.intLit (Int.ofNat (Model.leftConstant group))) =
      .ok (wordValue (leftConstantWord group)) := by
  have hn : Model.leftConstant group < UInt256.size := by
    interval_cases group <;> native_decide
  simpa [leftConstantWord] using evalWordLit (L := L) (evm := evm)
    (Model.leftConstant group) hn

theorem execConstantIfFalse {L : Store} {evm : EVM.State}
    (group n : Nat) (constant : Nat) (hne : group ≠ n)
    (hgroup : L.get? "groupL" = some (natValue group)) :
    ExecStmt config { contract := contract, locals := L } evm
      (.ite (.binary .eq (.var "groupL") (.intLit (Int.ofNat n)))
        [.assign .localVar { base := "kL" } (.intLit (Int.ofNat constant))] [])
      (.ok { contract := contract, locals := L } evm) :=
  execGroupIfFalse "groupL" group n _ hne hgroup

theorem execLeftConstantIfTrue {L : Store} {evm : EVM.State}
    (group : Nat) (hg : group < 5)
    (hgroup : L.get? "groupL" = some (natValue group))
    (hk : L.get? "kL" = some (wordValue (leftConstantWord 0))) :
    ExecStmt config { contract := contract, locals := L } evm
      (.ite (.binary .eq (.var "groupL") (.intLit (Int.ofNat group)))
        [.assign .localVar { base := "kL" }
          (.intLit (Int.ofNat (Model.leftConstant group)))] [])
      (.ok { contract := contract, locals :=
        L.insert "kL" (wordValue (leftConstantWord group)) } evm) := by
  apply execGroupIfTrue "groupL" group _ hgroup
  exact ExecBlock.consNormal
    (execAssignLocal hk (evalLeftConstantLit group hg)) ExecBlock.nil

theorem leftGroupPreludeReturns {L : Store} (evm : EVM.State) (group : Nat)
    (hg : group < 5) (hgroup : L.get? "groupL" = some (natValue group)) :
    ExecBlock config { contract := contract, locals := L } evm leftGroupPrelude
      (.ok { contract := contract, locals := leftGroupPreludeStore L group } evm) := by
  let L1 := L.insert "wordTableL" (wordValue (leftWordRowWord group))
  have hwordCall : ExecStmt config { contract := contract, locals := L } evm
      (.internalCall "wordRowL" [.var "groupL"] "wordTableL")
      (.ok { contract := contract, locals := L1 } evm) := by
    simpa [L1, rowNatValue_eq_wordValue_leftWord group hg] using
      wordRowLCall evm group hg (evalNatVar hgroup)
  have hgroup1 : L1.get? "groupL" = some (natValue group) := by
    simp only [L1]; rw [store_get_ne _ _ (by decide), hgroup]
  let L2 := L1.insert "rotTableL" (wordValue (leftRotationRowWord group))
  have hrotCall : ExecStmt config { contract := contract, locals := L1 } evm
      (.internalCall "rotRowL" [.var "groupL"] "rotTableL")
      (.ok { contract := contract, locals := L2 } evm) := by
    simpa [L2, rowNatValue_eq_wordValue_leftRotation group hg] using
      rotRowLCall evm group hg (evalNatVar hgroup1)
  have hgroup2 : L2.get? "groupL" = some (natValue group) := by
    simp only [L2]; rw [store_get_ne _ _ (by decide), hgroup1]
  let L3 := L2.insert "kL" (wordValue (leftConstantWord 0))
  have hzero : evalExpr? config { contract := contract, locals := L2 } evm (.intLit 0) =
      .ok (wordValue (leftConstantWord 0)) := by
    simpa [leftConstantWord] using evalWordLit (L := L2) (evm := evm) 0 (by decide)
  have hletK : ExecStmt config { contract := contract, locals := L2 } evm
      (.letDecl "kL" uint256Ty (.intLit 0))
      (.ok { contract := contract, locals := L3 } evm) := ExecStmt.letDecl hzero
  have hgroup3 : L3.get? "groupL" = some (natValue group) := by
    simp only [L3]; rw [store_get_ne _ _ (by decide), hgroup2]
  have hk3 : L3.get? "kL" = some (wordValue (leftConstantWord 0)) := by simp [L3]
  apply ExecBlock.consNormal hwordCall
  apply ExecBlock.consNormal hrotCall
  apply ExecBlock.consNormal hletK
  have hcases : group = 0 ∨ group = 1 ∨ group = 2 ∨ group = 3 ∨ group = 4 := by
    omega
  rcases hcases with hgroup0 | hgroup1 | hgroup2 | hgroup3' | hgroup4
  · subst group
    apply ExecBlock.consNormal (execConstantIfFalse 0 1 _ (by decide) hgroup3)
    apply ExecBlock.consNormal (execConstantIfFalse 0 2 _ (by decide) hgroup3)
    apply ExecBlock.consNormal (execConstantIfFalse 0 3 _ (by decide) hgroup3)
    apply ExecBlock.consNormal (execConstantIfFalse 0 4 _ (by decide) hgroup3)
    simpa [leftGroupPreludeStore, L3, L2, L1] using ExecBlock.nil
  · subst group
    apply ExecBlock.consNormal (execLeftConstantIfTrue 1 (by decide) hgroup3 hk3)
    let L4 := L3.insert "kL" (wordValue (leftConstantWord 1))
    have hg4 : L4.get? "groupL" = some (natValue 1) := by
      simp only [L4]; rw [store_get_ne _ _ (by decide), hgroup3]
    apply ExecBlock.consNormal (execConstantIfFalse 1 2 _ (by decide) hg4)
    apply ExecBlock.consNormal (execConstantIfFalse 1 3 _ (by decide) hg4)
    apply ExecBlock.consNormal (execConstantIfFalse 1 4 _ (by decide) hg4)
    simpa [leftGroupPreludeStore, L4, L3, L2, L1] using ExecBlock.nil
  · subst group
    apply ExecBlock.consNormal (execConstantIfFalse 2 1 _ (by decide) hgroup3)
    apply ExecBlock.consNormal (execLeftConstantIfTrue 2 (by decide) hgroup3 hk3)
    let L4 := L3.insert "kL" (wordValue (leftConstantWord 2))
    have hg4 : L4.get? "groupL" = some (natValue 2) := by
      simp only [L4]; rw [store_get_ne _ _ (by decide), hgroup3]
    apply ExecBlock.consNormal (execConstantIfFalse 2 3 _ (by decide) hg4)
    apply ExecBlock.consNormal (execConstantIfFalse 2 4 _ (by decide) hg4)
    simpa [leftGroupPreludeStore, L4, L3, L2, L1] using ExecBlock.nil
  · subst group
    apply ExecBlock.consNormal (execConstantIfFalse 3 1 _ (by decide) hgroup3)
    apply ExecBlock.consNormal (execConstantIfFalse 3 2 _ (by decide) hgroup3)
    apply ExecBlock.consNormal (execLeftConstantIfTrue 3 (by decide) hgroup3 hk3)
    let L4 := L3.insert "kL" (wordValue (leftConstantWord 3))
    have hg4 : L4.get? "groupL" = some (natValue 3) := by
      simp only [L4]; rw [store_get_ne _ _ (by decide), hgroup3]
    apply ExecBlock.consNormal (execConstantIfFalse 3 4 _ (by decide) hg4)
    simpa [leftGroupPreludeStore, L4, L3, L2, L1] using ExecBlock.nil
  · subst group
    apply ExecBlock.consNormal (execConstantIfFalse 4 1 _ (by decide) hgroup3)
    apply ExecBlock.consNormal (execConstantIfFalse 4 2 _ (by decide) hgroup3)
    apply ExecBlock.consNormal (execConstantIfFalse 4 3 _ (by decide) hgroup3)
    apply ExecBlock.consNormal (execLeftConstantIfTrue 4 (by decide) hgroup3 hk3)
    let L4 := L3.insert "kL" (wordValue (leftConstantWord 4))
    simpa [leftGroupPreludeStore, L4, L3, L2, L1] using ExecBlock.nil

end Ripemd160
