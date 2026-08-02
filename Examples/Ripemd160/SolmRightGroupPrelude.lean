import Examples.Ripemd160.SolmGroupPrelude

/-!
# RIPEMD-160 Solm right group prelude

Table selection and per-group additive constants for the authored right compression loop.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

def rightGroupPrelude : List Stmt :=
  [ .internalCall "wordRowR" [.var "groupR"] "wordTableR",
    .internalCall "rotRowR" [.var "groupR"] "rotTableR",
    .letDecl "kR" uint256Ty (.intLit 0x50a28be6),
    .ite (.binary .eq (.var "groupR") (.intLit 1))
      [.assign .localVar { base := "kR" } (.intLit 0x5c4dd124)] [],
    .ite (.binary .eq (.var "groupR") (.intLit 2))
      [.assign .localVar { base := "kR" } (.intLit 0x6d703ef3)] [],
    .ite (.binary .eq (.var "groupR") (.intLit 3))
      [.assign .localVar { base := "kR" } (.intLit 0x7a6d76e9)] [],
    .ite (.binary .eq (.var "groupR") (.intLit 4))
      [.assign .localVar { base := "kR" } (.intLit 0)] [] ]

def rightGroupPreludeStore (L : Store) (group : Nat) : Store :=
  let L1 := L.insert "wordTableR" (wordValue (rightWordRowWord group))
  let L2 := L1.insert "rotTableR" (wordValue (rightRotationRowWord group))
  let L3 := L2.insert "kR" (wordValue (rightConstantWord 0))
  match group with
  | 0 => L3
  | _ => L3.insert "kR" (wordValue (rightConstantWord group))

theorem rightGroupPreludeStore_get_original (L : Store) (group : Nat) (name : Ident)
    (hword : ("wordTableR" == name) = false)
    (hrot : ("rotTableR" == name) = false) (hk : ("kR" == name) = false) :
    (rightGroupPreludeStore L group).get? name = L.get? name := by
  cases group <;> simp only [rightGroupPreludeStore] <;>
    repeat' rw [store_get_ne _ _ (by assumption)]

theorem rightGroupPreludeStore_word (L : Store) (group : Nat) :
    (rightGroupPreludeStore L group).get? "wordTableR" =
      some (wordValue (rightWordRowWord group)) := by
  cases group <;> simp only [rightGroupPreludeStore] <;>
    repeat' first | rw [store_get_self] | rw [store_get_ne _ _ (by decide)]

theorem rightGroupPreludeStore_rotation (L : Store) (group : Nat) :
    (rightGroupPreludeStore L group).get? "rotTableR" =
      some (wordValue (rightRotationRowWord group)) := by
  cases group <;> simp only [rightGroupPreludeStore] <;>
    repeat' first | rw [store_get_self] | rw [store_get_ne _ _ (by decide)]

theorem rightGroupPreludeStore_constant (L : Store) (group : Nat) :
    (rightGroupPreludeStore L group).get? "kR" =
      some (wordValue (rightConstantWord group)) := by
  cases group <;> simp only [rightGroupPreludeStore] <;> rw [store_get_self]

theorem rowNatValue_eq_wordValue_rightWord (group : Nat) (hg : group < 5) :
    natValue (Model.rightWordRow group) = wordValue (rightWordRowWord group) := by
  interval_cases group <;> native_decide

theorem rowNatValue_eq_wordValue_rightRotation (group : Nat) (hg : group < 5) :
    natValue (Model.rightRotationRow group) = wordValue (rightRotationRowWord group) := by
  interval_cases group <;> native_decide

theorem evalRightConstantLit {L : Store} {evm : EVM.State} (group : Nat) (hg : group < 5) :
    evalExpr? config { contract := contract, locals := L } evm
      (.intLit (Int.ofNat (Model.rightConstant group))) =
      .ok (wordValue (rightConstantWord group)) := by
  have hn : Model.rightConstant group < UInt256.size := by
    interval_cases group <;> native_decide
  simpa [rightConstantWord] using evalWordLit (L := L) (evm := evm)
    (Model.rightConstant group) hn

theorem execRightConstantIfFalse {L : Store} {evm : EVM.State}
    (group n : Nat) (constant : Nat) (hne : group ≠ n)
    (hgroup : L.get? "groupR" = some (natValue group)) :
    ExecStmt config { contract := contract, locals := L } evm
      (.ite (.binary .eq (.var "groupR") (.intLit (Int.ofNat n)))
        [.assign .localVar { base := "kR" } (.intLit (Int.ofNat constant))] [])
      (.ok { contract := contract, locals := L } evm) :=
  execGroupIfFalse "groupR" group n _ hne hgroup

theorem execRightConstantIfTrue {L : Store} {evm : EVM.State}
    (group : Nat) (hg : group < 5)
    (hgroup : L.get? "groupR" = some (natValue group))
    (hk : L.get? "kR" = some (wordValue (rightConstantWord 0))) :
    ExecStmt config { contract := contract, locals := L } evm
      (.ite (.binary .eq (.var "groupR") (.intLit (Int.ofNat group)))
        [.assign .localVar { base := "kR" }
          (.intLit (Int.ofNat (Model.rightConstant group)))] [])
      (.ok { contract := contract, locals :=
        L.insert "kR" (wordValue (rightConstantWord group)) } evm) := by
  apply execGroupIfTrue "groupR" group _ hgroup
  exact ExecBlock.consNormal
    (execAssignLocal hk (evalRightConstantLit group hg)) ExecBlock.nil

theorem rightGroupPreludeReturns {L : Store} (evm : EVM.State) (group : Nat)
    (hg : group < 5) (hgroup : L.get? "groupR" = some (natValue group)) :
    ExecBlock config { contract := contract, locals := L } evm rightGroupPrelude
      (.ok { contract := contract, locals := rightGroupPreludeStore L group } evm) := by
  let L1 := L.insert "wordTableR" (wordValue (rightWordRowWord group))
  have hwordCall : ExecStmt config { contract := contract, locals := L } evm
      (.internalCall "wordRowR" [.var "groupR"] "wordTableR")
      (.ok { contract := contract, locals := L1 } evm) := by
    simpa [L1, rowNatValue_eq_wordValue_rightWord group hg] using
      wordRowRCall evm group hg (evalNatVar hgroup)
  have hgroup1 : L1.get? "groupR" = some (natValue group) := by
    simp only [L1]; rw [store_get_ne _ _ (by decide), hgroup]
  let L2 := L1.insert "rotTableR" (wordValue (rightRotationRowWord group))
  have hrotCall : ExecStmt config { contract := contract, locals := L1 } evm
      (.internalCall "rotRowR" [.var "groupR"] "rotTableR")
      (.ok { contract := contract, locals := L2 } evm) := by
    simpa [L2, rowNatValue_eq_wordValue_rightRotation group hg] using
      rotRowRCall evm group hg (evalNatVar hgroup1)
  have hgroup2 : L2.get? "groupR" = some (natValue group) := by
    simp only [L2]; rw [store_get_ne _ _ (by decide), hgroup1]
  let L3 := L2.insert "kR" (wordValue (rightConstantWord 0))
  have hzero : evalExpr? config { contract := contract, locals := L2 } evm (.intLit 0x50a28be6) =
      .ok (wordValue (rightConstantWord 0)) := by
    simpa [rightConstantWord] using evalWordLit (L := L2) (evm := evm) 0x50a28be6 (by decide)
  have hletK : ExecStmt config { contract := contract, locals := L2 } evm
      (.letDecl "kR" uint256Ty (.intLit 0x50a28be6))
      (.ok { contract := contract, locals := L3 } evm) := ExecStmt.letDecl hzero
  have hgroup3 : L3.get? "groupR" = some (natValue group) := by
    simp only [L3]; rw [store_get_ne _ _ (by decide), hgroup2]
  have hk3 : L3.get? "kR" = some (wordValue (rightConstantWord 0)) := by simp [L3]
  apply ExecBlock.consNormal hwordCall
  apply ExecBlock.consNormal hrotCall
  apply ExecBlock.consNormal hletK
  have hcases : group = 0 ∨ group = 1 ∨ group = 2 ∨ group = 3 ∨ group = 4 := by
    omega
  rcases hcases with hgroup0 | hgroup1 | hgroup2 | hgroup3' | hgroup4
  · subst group
    apply ExecBlock.consNormal (execRightConstantIfFalse 0 1 _ (by decide) hgroup3)
    apply ExecBlock.consNormal (execRightConstantIfFalse 0 2 _ (by decide) hgroup3)
    apply ExecBlock.consNormal (execRightConstantIfFalse 0 3 _ (by decide) hgroup3)
    apply ExecBlock.consNormal (execRightConstantIfFalse 0 4 _ (by decide) hgroup3)
    simpa [rightGroupPreludeStore, L3, L2, L1] using ExecBlock.nil
  · subst group
    apply ExecBlock.consNormal (execRightConstantIfTrue 1 (by decide) hgroup3 hk3)
    let L4 := L3.insert "kR" (wordValue (rightConstantWord 1))
    have hg4 : L4.get? "groupR" = some (natValue 1) := by
      simp only [L4]; rw [store_get_ne _ _ (by decide), hgroup3]
    apply ExecBlock.consNormal (execRightConstantIfFalse 1 2 _ (by decide) hg4)
    apply ExecBlock.consNormal (execRightConstantIfFalse 1 3 _ (by decide) hg4)
    apply ExecBlock.consNormal (execRightConstantIfFalse 1 4 _ (by decide) hg4)
    simpa [rightGroupPreludeStore, L4, L3, L2, L1] using ExecBlock.nil
  · subst group
    apply ExecBlock.consNormal (execRightConstantIfFalse 2 1 _ (by decide) hgroup3)
    apply ExecBlock.consNormal (execRightConstantIfTrue 2 (by decide) hgroup3 hk3)
    let L4 := L3.insert "kR" (wordValue (rightConstantWord 2))
    have hg4 : L4.get? "groupR" = some (natValue 2) := by
      simp only [L4]; rw [store_get_ne _ _ (by decide), hgroup3]
    apply ExecBlock.consNormal (execRightConstantIfFalse 2 3 _ (by decide) hg4)
    apply ExecBlock.consNormal (execRightConstantIfFalse 2 4 _ (by decide) hg4)
    simpa [rightGroupPreludeStore, L4, L3, L2, L1] using ExecBlock.nil
  · subst group
    apply ExecBlock.consNormal (execRightConstantIfFalse 3 1 _ (by decide) hgroup3)
    apply ExecBlock.consNormal (execRightConstantIfFalse 3 2 _ (by decide) hgroup3)
    apply ExecBlock.consNormal (execRightConstantIfTrue 3 (by decide) hgroup3 hk3)
    let L4 := L3.insert "kR" (wordValue (rightConstantWord 3))
    have hg4 : L4.get? "groupR" = some (natValue 3) := by
      simp only [L4]; rw [store_get_ne _ _ (by decide), hgroup3]
    apply ExecBlock.consNormal (execRightConstantIfFalse 3 4 _ (by decide) hg4)
    simpa [rightGroupPreludeStore, L4, L3, L2, L1] using ExecBlock.nil
  · subst group
    apply ExecBlock.consNormal (execRightConstantIfFalse 4 1 _ (by decide) hgroup3)
    apply ExecBlock.consNormal (execRightConstantIfFalse 4 2 _ (by decide) hgroup3)
    apply ExecBlock.consNormal (execRightConstantIfFalse 4 3 _ (by decide) hgroup3)
    apply ExecBlock.consNormal (execRightConstantIfTrue 4 (by decide) hgroup3 hk3)
    let L4 := L3.insert "kR" (wordValue (rightConstantWord 4))
    simpa [rightGroupPreludeStore, L4, L3, L2, L1] using ExecBlock.nil

end Ripemd160
