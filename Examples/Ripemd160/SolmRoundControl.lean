import Examples.Ripemd160.SolmRoundArithmetic

/-!
# RIPEMD-160 Solm round control flow

Execution of the explicit Boolean-function selection performed at the start of each authored
compression round.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

theorem wordXor_comm (x y : UInt256) : UInt256.xor x y = UInt256.xor y x := by
  apply u256_inj
  simp only [word_toNat_xor, Nat.xor_comm]

theorem wordLand_comm (x y : UInt256) : UInt256.land x y = UInt256.land y x := by
  apply u256_inj
  simp only [uland_toNat, Nat.and_comm]

theorem wordLor_comm (x y : UInt256) : UInt256.lor x y = UInt256.lor y x := by
  apply u256_inj
  simp only [word_toNat_lor]
  exact Nat.lor_comm _ _

abbrev uint256Ty : Option ABIType :=
  some (.elem (.int (.uint ⟨256, by decide⟩)))

def leftFSelection : List Stmt :=
  [ .letDecl "fL" uint256Ty (.intLit 0),
    .ite (.binary .eq (.var "groupL") (.intLit 0))
      [.internalCall "f0" [.var "bl", .var "cl", .var "dl"] "fL0",
       .assign .localVar { base := "fL" } (.var "fL0")] [],
    .ite (.binary .eq (.var "groupL") (.intLit 1))
      [.internalCall "f1" [.var "bl", .var "cl", .var "dl"] "fL1",
       .assign .localVar { base := "fL" } (.var "fL1")] [],
    .ite (.binary .eq (.var "groupL") (.intLit 2))
      [.internalCall "f2" [.var "bl", .var "cl", .var "dl"] "fL2",
       .assign .localVar { base := "fL" } (.var "fL2")] [],
    .ite (.binary .eq (.var "groupL") (.intLit 3))
      [.internalCall "f3" [.var "bl", .var "cl", .var "dl"] "fL3",
       .assign .localVar { base := "fL" } (.var "fL3")] [],
    .ite (.binary .eq (.var "groupL") (.intLit 4))
      [.internalCall "f4" [.var "bl", .var "cl", .var "dl"] "fL4",
       .assign .localVar { base := "fL" } (.var "fL4")] [] ]

def leftFSelectionStore (L : Store) (group : Nat) (b c d : UInt256) : Store :=
  let L0 := L.insert "fL" (natValue 0)
  match group with
  | 0 => (L0.insert "fL0" (wordValue (runtimeLeftF 0 b c d))).insert
      "fL" (wordValue (runtimeLeftF 0 b c d))
  | 1 => (L0.insert "fL1" (wordValue (runtimeLeftF 1 b c d))).insert
      "fL" (wordValue (runtimeLeftF 1 b c d))
  | 2 => (L0.insert "fL2" (wordValue (runtimeLeftF 2 b c d))).insert
      "fL" (wordValue (runtimeLeftF 2 b c d))
  | 3 => (L0.insert "fL3" (wordValue (runtimeLeftF 3 b c d))).insert
      "fL" (wordValue (runtimeLeftF 3 b c d))
  | _ => (L0.insert "fL4" (wordValue (runtimeLeftF group b c d))).insert
      "fL" (wordValue (runtimeLeftF group b c d))

theorem evalGroupEq {L : Store} {evm : EVM.State} (name : Ident) (group n : Nat)
    (hgroup : L.get? name = some (natValue group)) :
    evalExpr? config { contract := contract, locals := L } evm
      (.binary .eq (.var name) (.intLit (Int.ofNat n))) =
      .ok (.bool (decide (group = n))) := by
  exact evalNatEq (evalNatVar hgroup) (by simp [evalExpr?, natValue, pure])

theorem execGroupIfFalse {L : Store} {evm : EVM.State} (name : Ident)
    (group n : Nat) (thenBody : List Stmt) (hne : group ≠ n)
    (hgroup : L.get? name = some (natValue group)) :
    ExecStmt config { contract := contract, locals := L } evm
      (.ite (.binary .eq (.var name) (.intLit (Int.ofNat n))) thenBody [])
      (.ok { contract := contract, locals := L } evm) := by
  apply ExecStmt.iteFalse
  · simpa [decide_eq_false hne] using evalGroupEq (evm := evm) name group n hgroup
  · exact ExecBlock.nil

theorem execGroupIfTrue {L L' : Store} {evm : EVM.State} (name : Ident)
    (group : Nat) (thenBody : List Stmt)
    (hgroup : L.get? name = some (natValue group))
    (hbody : ExecBlock config { contract := contract, locals := L } evm thenBody
      (.ok { contract := contract, locals := L' } evm)) :
    ExecStmt config { contract := contract, locals := L } evm
      (.ite (.binary .eq (.var name) (.intLit (Int.ofNat group))) thenBody [])
      (.ok { contract := contract, locals := L' } evm) := by
  apply ExecStmt.iteTrue
  · simpa using evalGroupEq (evm := evm) name group group hgroup
  · exact hbody

theorem leftFSelectionReturns {L : Store} (evm : EVM.State) (group : Nat)
    (b c d : UInt256) (hg : group < 5)
    (hgroup : L.get? "groupL" = some (natValue group))
    (hb : L.get? "bl" = some (wordValue b))
    (hc : L.get? "cl" = some (wordValue c))
    (hd : L.get? "dl" = some (wordValue d))
    (hb32 : b.toNat < 2 ^ 32) (hc32 : c.toNat < 2 ^ 32)
    (hd32 : d.toNat < 2 ^ 32) :
    ExecBlock config { contract := contract, locals := L } evm leftFSelection
      (.ok { contract := contract, locals := leftFSelectionStore L group b c d } evm) := by
  let L0 := L.insert "fL" (natValue 0)
  have hzero : evalExpr? config { contract := contract, locals := L } evm (.intLit 0) =
      .ok (natValue 0) := by simp [evalExpr?, natValue, pure]
  have hgroup0 : L0.get? "groupL" = some (natValue group) := by
    simp only [L0]; rw [store_get_ne _ _ (by decide), hgroup]
  have hb0 : L0.get? "bl" = some (wordValue b) := by
    simp only [L0]; rw [store_get_ne _ _ (by decide), hb]
  have hc0 : L0.get? "cl" = some (wordValue c) := by
    simp only [L0]; rw [store_get_ne _ _ (by decide), hc]
  have hd0 : L0.get? "dl" = some (wordValue d) := by
    simp only [L0]; rw [store_get_ne _ _ (by decide), hd]
  apply ExecBlock.consNormal (ExecStmt.letDecl hzero)
  interval_cases group
  · let L1 := L0.insert "fL0" (wordValue (runtimeLeftF 0 b c d))
    let L2 := L1.insert "fL" (wordValue (runtimeLeftF 0 b c d))
    have hcall : ExecStmt config { contract := contract, locals := L0 } evm
        (.internalCall "f0" [.var "bl", .var "cl", .var "dl"] "fL0")
        (.ok { contract := contract, locals := L1 } evm) := by
      simpa [L1, runtimeLeftF] using f0Call evm b c d
        (evalWordVar hb0) (evalWordVar hc0) (evalWordVar hd0)
    have hfL1 : L1.get? "fL" = some (natValue 0) := by
      simp only [L1]; rw [store_get_ne _ _ (by decide)]; simp [L0]
    have hf01 : L1.get? "fL0" = some (wordValue (runtimeLeftF 0 b c d)) := by simp [L1]
    have hassign : ExecStmt config { contract := contract, locals := L1 } evm
        (.assign .localVar { base := "fL" } (.var "fL0"))
        (.ok { contract := contract, locals := L2 } evm) := by
      exact execAssignLocal hfL1 (evalWordVar hf01)
    have htrue : ExecStmt config { contract := contract, locals := L0 } evm
        (.ite (.binary .eq (.var "groupL") (.intLit 0))
          [.internalCall "f0" [.var "bl", .var "cl", .var "dl"] "fL0",
           .assign .localVar { base := "fL" } (.var "fL0")] [])
        (.ok { contract := contract, locals := L2 } evm) := by
      apply execGroupIfTrue "groupL" 0 _ hgroup0
      exact ExecBlock.consNormal hcall (ExecBlock.consNormal hassign ExecBlock.nil)
    apply ExecBlock.consNormal htrue
    have hg2 : L2.get? "groupL" = some (natValue 0) := by
      simp only [L2]; rw [store_get_ne _ _ (by decide)]
      simp only [L1]; rw [store_get_ne _ _ (by decide), hgroup0]
    apply ExecBlock.consNormal (execGroupIfFalse "groupL" 0 1 _ (by decide) hg2)
    apply ExecBlock.consNormal (execGroupIfFalse "groupL" 0 2 _ (by decide) hg2)
    apply ExecBlock.consNormal (execGroupIfFalse "groupL" 0 3 _ (by decide) hg2)
    apply ExecBlock.consNormal (execGroupIfFalse "groupL" 0 4 _ (by decide) hg2)
    simpa [leftFSelectionStore, L2, L1, L0] using ExecBlock.nil
  · let L1 := L0.insert "fL1" (wordValue (runtimeLeftF 1 b c d))
    let L2 := L1.insert "fL" (wordValue (runtimeLeftF 1 b c d))
    have hfalse0 := execGroupIfFalse (evm := evm) "groupL" 1 0
      [.internalCall "f0" [.var "bl", .var "cl", .var "dl"] "fL0",
       .assign .localVar { base := "fL" } (.var "fL0")] (by decide) hgroup0
    apply ExecBlock.consNormal hfalse0
    have hcall : ExecStmt config { contract := contract, locals := L0 } evm
        (.internalCall "f1" [.var "bl", .var "cl", .var "dl"] "fL1")
        (.ok { contract := contract, locals := L1 } evm) := by
      simpa [L1, runtimeLeftF] using f1Call evm b c d hb32
        (evalWordVar hb0) (evalWordVar hc0) (evalWordVar hd0)
    have hfL1 : L1.get? "fL" = some (natValue 0) := by
      simp only [L1]; rw [store_get_ne _ _ (by decide)]; simp [L0]
    have hf11 : L1.get? "fL1" = some (wordValue (runtimeLeftF 1 b c d)) := by simp [L1]
    have hassign := execAssignLocal (evm := evm) hfL1 (evalWordVar hf11)
    have htrue : ExecStmt config { contract := contract, locals := L0 } evm
        (.ite (.binary .eq (.var "groupL") (.intLit 1))
          [.internalCall "f1" [.var "bl", .var "cl", .var "dl"] "fL1",
           .assign .localVar { base := "fL" } (.var "fL1")] [])
        (.ok { contract := contract, locals := L2 } evm) := by
      apply execGroupIfTrue "groupL" 1 _ hgroup0
      exact ExecBlock.consNormal hcall (ExecBlock.consNormal hassign ExecBlock.nil)
    apply ExecBlock.consNormal htrue
    have hg2 : L2.get? "groupL" = some (natValue 1) := by
      simp only [L2]; rw [store_get_ne _ _ (by decide)]
      simp only [L1]; rw [store_get_ne _ _ (by decide), hgroup0]
    apply ExecBlock.consNormal (execGroupIfFalse "groupL" 1 2 _ (by decide) hg2)
    apply ExecBlock.consNormal (execGroupIfFalse "groupL" 1 3 _ (by decide) hg2)
    apply ExecBlock.consNormal (execGroupIfFalse "groupL" 1 4 _ (by decide) hg2)
    simpa [leftFSelectionStore, L2, L1, L0] using ExecBlock.nil
  · let L1 := L0.insert "fL2" (wordValue (runtimeLeftF 2 b c d))
    let L2 := L1.insert "fL" (wordValue (runtimeLeftF 2 b c d))
    apply ExecBlock.consNormal (execGroupIfFalse "groupL" 2 0 _ (by decide) hgroup0)
    apply ExecBlock.consNormal (execGroupIfFalse "groupL" 2 1 _ (by decide) hgroup0)
    have hcall : ExecStmt config { contract := contract, locals := L0 } evm
        (.internalCall "f2" [.var "bl", .var "cl", .var "dl"] "fL2")
        (.ok { contract := contract, locals := L1 } evm) := by
      simpa [L1, runtimeLeftF] using f2Call evm b c d hc32
        (evalWordVar hb0) (evalWordVar hc0) (evalWordVar hd0)
    have hfL1 : L1.get? "fL" = some (natValue 0) := by
      simp only [L1]; rw [store_get_ne _ _ (by decide)]; simp [L0]
    have hf21 : L1.get? "fL2" = some (wordValue (runtimeLeftF 2 b c d)) := by simp [L1]
    have hassign := execAssignLocal (evm := evm) hfL1 (evalWordVar hf21)
    have htrue : ExecStmt config { contract := contract, locals := L0 } evm
        (.ite (.binary .eq (.var "groupL") (.intLit 2))
          [.internalCall "f2" [.var "bl", .var "cl", .var "dl"] "fL2",
           .assign .localVar { base := "fL" } (.var "fL2")] [])
        (.ok { contract := contract, locals := L2 } evm) := by
      apply execGroupIfTrue "groupL" 2 _ hgroup0
      exact ExecBlock.consNormal hcall (ExecBlock.consNormal hassign ExecBlock.nil)
    apply ExecBlock.consNormal htrue
    have hg2 : L2.get? "groupL" = some (natValue 2) := by
      simp only [L2]; rw [store_get_ne _ _ (by decide)]
      simp only [L1]; rw [store_get_ne _ _ (by decide), hgroup0]
    apply ExecBlock.consNormal (execGroupIfFalse "groupL" 2 3 _ (by decide) hg2)
    apply ExecBlock.consNormal (execGroupIfFalse "groupL" 2 4 _ (by decide) hg2)
    simpa [leftFSelectionStore, L2, L1, L0] using ExecBlock.nil
  · let L1 := L0.insert "fL3" (wordValue (runtimeLeftF 3 b c d))
    let L2 := L1.insert "fL" (wordValue (runtimeLeftF 3 b c d))
    apply ExecBlock.consNormal (execGroupIfFalse "groupL" 3 0 _ (by decide) hgroup0)
    apply ExecBlock.consNormal (execGroupIfFalse "groupL" 3 1 _ (by decide) hgroup0)
    apply ExecBlock.consNormal (execGroupIfFalse "groupL" 3 2 _ (by decide) hgroup0)
    have hcall : ExecStmt config { contract := contract, locals := L0 } evm
        (.internalCall "f3" [.var "bl", .var "cl", .var "dl"] "fL3")
        (.ok { contract := contract, locals := L1 } evm) := by
      simpa [L1, runtimeLeftF] using f3Call evm b c d hd32
        (evalWordVar hb0) (evalWordVar hc0) (evalWordVar hd0)
    have hfL1 : L1.get? "fL" = some (natValue 0) := by
      simp only [L1]; rw [store_get_ne _ _ (by decide)]; simp [L0]
    have hf31 : L1.get? "fL3" = some (wordValue (runtimeLeftF 3 b c d)) := by simp [L1]
    have hassign := execAssignLocal (evm := evm) hfL1 (evalWordVar hf31)
    have htrue : ExecStmt config { contract := contract, locals := L0 } evm
        (.ite (.binary .eq (.var "groupL") (.intLit 3))
          [.internalCall "f3" [.var "bl", .var "cl", .var "dl"] "fL3",
           .assign .localVar { base := "fL" } (.var "fL3")] [])
        (.ok { contract := contract, locals := L2 } evm) := by
      apply execGroupIfTrue "groupL" 3 _ hgroup0
      exact ExecBlock.consNormal hcall (ExecBlock.consNormal hassign ExecBlock.nil)
    apply ExecBlock.consNormal htrue
    have hg2 : L2.get? "groupL" = some (natValue 3) := by
      simp only [L2]; rw [store_get_ne _ _ (by decide)]
      simp only [L1]; rw [store_get_ne _ _ (by decide), hgroup0]
    apply ExecBlock.consNormal (execGroupIfFalse "groupL" 3 4 _ (by decide) hg2)
    simpa [leftFSelectionStore, L2, L1, L0] using ExecBlock.nil
  · let L1 := L0.insert "fL4" (wordValue (runtimeLeftF 4 b c d))
    let L2 := L1.insert "fL" (wordValue (runtimeLeftF 4 b c d))
    apply ExecBlock.consNormal (execGroupIfFalse "groupL" 4 0 _ (by decide) hgroup0)
    apply ExecBlock.consNormal (execGroupIfFalse "groupL" 4 1 _ (by decide) hgroup0)
    apply ExecBlock.consNormal (execGroupIfFalse "groupL" 4 2 _ (by decide) hgroup0)
    apply ExecBlock.consNormal (execGroupIfFalse "groupL" 4 3 _ (by decide) hgroup0)
    have hcall : ExecStmt config { contract := contract, locals := L0 } evm
        (.internalCall "f4" [.var "bl", .var "cl", .var "dl"] "fL4")
        (.ok { contract := contract, locals := L1 } evm) := by
      simpa [L1, runtimeLeftF, wordXor_comm] using f4Call evm b c d hd32
        (evalWordVar hb0) (evalWordVar hc0) (evalWordVar hd0)
    have hfL1 : L1.get? "fL" = some (natValue 0) := by
      simp only [L1]; rw [store_get_ne _ _ (by decide)]; simp [L0]
    have hf41 : L1.get? "fL4" = some (wordValue (runtimeLeftF 4 b c d)) := by simp [L1]
    have hassign := execAssignLocal (evm := evm) hfL1 (evalWordVar hf41)
    have htrue : ExecStmt config { contract := contract, locals := L0 } evm
        (.ite (.binary .eq (.var "groupL") (.intLit 4))
          [.internalCall "f4" [.var "bl", .var "cl", .var "dl"] "fL4",
           .assign .localVar { base := "fL" } (.var "fL4")] [])
        (.ok { contract := contract, locals := L2 } evm) := by
      apply execGroupIfTrue "groupL" 4 _ hgroup0
      exact ExecBlock.consNormal hcall (ExecBlock.consNormal hassign ExecBlock.nil)
    apply ExecBlock.consNormal htrue
    simpa [leftFSelectionStore, L2, L1, L0] using ExecBlock.nil

@[simp] theorem leftFSelectionStore_fL (L : Store) (group : Nat) (b c d : UInt256)
    (hg : group < 5) :
    (leftFSelectionStore L group b c d).get? "fL" =
      some (wordValue (runtimeLeftF group b c d)) := by
  interval_cases group <;> simp [leftFSelectionStore]

theorem leftFSelectionStore_get_original (L : Store) (group : Nat) (b c d : UInt256)
    (hg : group < 5) (name : Ident)
    (hf : ("fL" == name) = false) (hf0 : ("fL0" == name) = false)
    (hf1 : ("fL1" == name) = false) (hf2 : ("fL2" == name) = false)
    (hf3 : ("fL3" == name) = false) (hf4 : ("fL4" == name) = false) :
    (leftFSelectionStore L group b c d).get? name = L.get? name := by
  interval_cases group
  · simp only [leftFSelectionStore]
    rw [store_get_ne _ _ hf, store_get_ne _ _ hf0, store_get_ne _ _ hf]
  · simp only [leftFSelectionStore]
    rw [store_get_ne _ _ hf, store_get_ne _ _ hf1, store_get_ne _ _ hf]
  · simp only [leftFSelectionStore]
    rw [store_get_ne _ _ hf, store_get_ne _ _ hf2, store_get_ne _ _ hf]
  · simp only [leftFSelectionStore]
    rw [store_get_ne _ _ hf, store_get_ne _ _ hf3, store_get_ne _ _ hf]
  · simp only [leftFSelectionStore]
    rw [store_get_ne _ _ hf, store_get_ne _ _ hf4, store_get_ne _ _ hf]

def rightFSelection : List Stmt :=
  [ .letDecl "fR" uint256Ty (.intLit 0),
    .ite (.binary .eq (.var "groupR") (.intLit 0))
      [.internalCall "f4" [.var "br", .var "cr", .var "dr"] "fR0",
       .assign .localVar { base := "fR" } (.var "fR0")] [],
    .ite (.binary .eq (.var "groupR") (.intLit 1))
      [.internalCall "f3" [.var "br", .var "cr", .var "dr"] "fR1",
       .assign .localVar { base := "fR" } (.var "fR1")] [],
    .ite (.binary .eq (.var "groupR") (.intLit 2))
      [.internalCall "f2" [.var "br", .var "cr", .var "dr"] "fR2",
       .assign .localVar { base := "fR" } (.var "fR2")] [],
    .ite (.binary .eq (.var "groupR") (.intLit 3))
      [.internalCall "f1" [.var "br", .var "cr", .var "dr"] "fR3",
       .assign .localVar { base := "fR" } (.var "fR3")] [],
    .ite (.binary .eq (.var "groupR") (.intLit 4))
      [.internalCall "f0" [.var "br", .var "cr", .var "dr"] "fR4",
       .assign .localVar { base := "fR" } (.var "fR4")] [] ]

def rightFSelectionStore (L : Store) (group : Nat) (b c d : UInt256) : Store :=
  let L0 := L.insert "fR" (natValue 0)
  match group with
  | 0 => (L0.insert "fR0" (wordValue (runtimeRightF 0 b c d))).insert
      "fR" (wordValue (runtimeRightF 0 b c d))
  | 1 => (L0.insert "fR1" (wordValue (runtimeRightF 1 b c d))).insert
      "fR" (wordValue (runtimeRightF 1 b c d))
  | 2 => (L0.insert "fR2" (wordValue (runtimeRightF 2 b c d))).insert
      "fR" (wordValue (runtimeRightF 2 b c d))
  | 3 => (L0.insert "fR3" (wordValue (runtimeRightF 3 b c d))).insert
      "fR" (wordValue (runtimeRightF 3 b c d))
  | _ => (L0.insert "fR4" (wordValue (runtimeRightF group b c d))).insert
      "fR" (wordValue (runtimeRightF group b c d))

theorem rightFSelectionReturns {L : Store} (evm : EVM.State) (group : Nat)
    (b c d : UInt256) (hg : group < 5)
    (hgroup : L.get? "groupR" = some (natValue group))
    (hb : L.get? "br" = some (wordValue b))
    (hc : L.get? "cr" = some (wordValue c))
    (hd : L.get? "dr" = some (wordValue d))
    (hb32 : b.toNat < 2 ^ 32) (hc32 : c.toNat < 2 ^ 32)
    (hd32 : d.toNat < 2 ^ 32) :
    ExecBlock config { contract := contract, locals := L } evm rightFSelection
      (.ok { contract := contract, locals := rightFSelectionStore L group b c d } evm) := by
  let L0 := L.insert "fR" (natValue 0)
  have hzero : evalExpr? config { contract := contract, locals := L } evm (.intLit 0) =
      .ok (natValue 0) := by simp [evalExpr?, natValue, pure]
  have hgroup0 : L0.get? "groupR" = some (natValue group) := by
    simp only [L0]; rw [store_get_ne _ _ (by decide), hgroup]
  have hb0 : L0.get? "br" = some (wordValue b) := by
    simp only [L0]; rw [store_get_ne _ _ (by decide), hb]
  have hc0 : L0.get? "cr" = some (wordValue c) := by
    simp only [L0]; rw [store_get_ne _ _ (by decide), hc]
  have hd0 : L0.get? "dr" = some (wordValue d) := by
    simp only [L0]; rw [store_get_ne _ _ (by decide), hd]
  apply ExecBlock.consNormal (ExecStmt.letDecl hzero)
  interval_cases group
  · let L1 := L0.insert "fR0" (wordValue (runtimeRightF 0 b c d))
    let L2 := L1.insert "fR" (wordValue (runtimeRightF 0 b c d))
    have hcall : ExecStmt config { contract := contract, locals := L0 } evm
        (.internalCall "f4" [.var "br", .var "cr", .var "dr"] "fR0")
        (.ok { contract := contract, locals := L1 } evm) := by
      simpa [L1, runtimeRightF, wordXor_comm, wordLor_comm] using f4Call evm b c d hd32
        (evalWordVar hb0) (evalWordVar hc0) (evalWordVar hd0)
    have hfR1 : L1.get? "fR" = some (natValue 0) := by
      simp only [L1]; rw [store_get_ne _ _ (by decide)]; simp [L0]
    have hf01 : L1.get? "fR0" = some (wordValue (runtimeRightF 0 b c d)) := by simp [L1]
    have hassign := execAssignLocal (evm := evm) hfR1 (evalWordVar hf01)
    have htrue : ExecStmt config { contract := contract, locals := L0 } evm
        (.ite (.binary .eq (.var "groupR") (.intLit 0))
          [.internalCall "f4" [.var "br", .var "cr", .var "dr"] "fR0",
           .assign .localVar { base := "fR" } (.var "fR0")] [])
        (.ok { contract := contract, locals := L2 } evm) := by
      apply execGroupIfTrue "groupR" 0 _ hgroup0
      exact ExecBlock.consNormal hcall (ExecBlock.consNormal hassign ExecBlock.nil)
    apply ExecBlock.consNormal htrue
    have hg2 : L2.get? "groupR" = some (natValue 0) := by
      simp only [L2]; rw [store_get_ne _ _ (by decide)]
      simp only [L1]; rw [store_get_ne _ _ (by decide), hgroup0]
    apply ExecBlock.consNormal (execGroupIfFalse "groupR" 0 1 _ (by decide) hg2)
    apply ExecBlock.consNormal (execGroupIfFalse "groupR" 0 2 _ (by decide) hg2)
    apply ExecBlock.consNormal (execGroupIfFalse "groupR" 0 3 _ (by decide) hg2)
    apply ExecBlock.consNormal (execGroupIfFalse "groupR" 0 4 _ (by decide) hg2)
    simpa [rightFSelectionStore, L2, L1, L0] using ExecBlock.nil
  · let L1 := L0.insert "fR1" (wordValue (runtimeRightF 1 b c d))
    let L2 := L1.insert "fR" (wordValue (runtimeRightF 1 b c d))
    apply ExecBlock.consNormal (execGroupIfFalse "groupR" 1 0 _ (by decide) hgroup0)
    have hcall : ExecStmt config { contract := contract, locals := L0 } evm
        (.internalCall "f3" [.var "br", .var "cr", .var "dr"] "fR1")
        (.ok { contract := contract, locals := L1 } evm) := by
      simpa [L1, runtimeRightF, wordLand_comm, wordLor_comm] using f3Call evm b c d hd32
        (evalWordVar hb0) (evalWordVar hc0) (evalWordVar hd0)
    have hfR1 : L1.get? "fR" = some (natValue 0) := by
      simp only [L1]; rw [store_get_ne _ _ (by decide)]; simp [L0]
    have hf11 : L1.get? "fR1" = some (wordValue (runtimeRightF 1 b c d)) := by simp [L1]
    have hassign := execAssignLocal (evm := evm) hfR1 (evalWordVar hf11)
    have htrue : ExecStmt config { contract := contract, locals := L0 } evm
        (.ite (.binary .eq (.var "groupR") (.intLit 1))
          [.internalCall "f3" [.var "br", .var "cr", .var "dr"] "fR1",
           .assign .localVar { base := "fR" } (.var "fR1")] [])
        (.ok { contract := contract, locals := L2 } evm) := by
      apply execGroupIfTrue "groupR" 1 _ hgroup0
      exact ExecBlock.consNormal hcall (ExecBlock.consNormal hassign ExecBlock.nil)
    apply ExecBlock.consNormal htrue
    have hg2 : L2.get? "groupR" = some (natValue 1) := by
      simp only [L2]; rw [store_get_ne _ _ (by decide)]
      simp only [L1]; rw [store_get_ne _ _ (by decide), hgroup0]
    apply ExecBlock.consNormal (execGroupIfFalse "groupR" 1 2 _ (by decide) hg2)
    apply ExecBlock.consNormal (execGroupIfFalse "groupR" 1 3 _ (by decide) hg2)
    apply ExecBlock.consNormal (execGroupIfFalse "groupR" 1 4 _ (by decide) hg2)
    simpa [rightFSelectionStore, L2, L1, L0] using ExecBlock.nil
  · let L1 := L0.insert "fR2" (wordValue (runtimeRightF 2 b c d))
    let L2 := L1.insert "fR" (wordValue (runtimeRightF 2 b c d))
    apply ExecBlock.consNormal (execGroupIfFalse "groupR" 2 0 _ (by decide) hgroup0)
    apply ExecBlock.consNormal (execGroupIfFalse "groupR" 2 1 _ (by decide) hgroup0)
    have hcall : ExecStmt config { contract := contract, locals := L0 } evm
        (.internalCall "f2" [.var "br", .var "cr", .var "dr"] "fR2")
        (.ok { contract := contract, locals := L1 } evm) := by
      simpa [L1, runtimeRightF, wordLor_comm] using f2Call evm b c d hc32
        (evalWordVar hb0) (evalWordVar hc0) (evalWordVar hd0)
    have hfR1 : L1.get? "fR" = some (natValue 0) := by
      simp only [L1]; rw [store_get_ne _ _ (by decide)]; simp [L0]
    have hf21 : L1.get? "fR2" = some (wordValue (runtimeRightF 2 b c d)) := by simp [L1]
    have hassign := execAssignLocal (evm := evm) hfR1 (evalWordVar hf21)
    have htrue : ExecStmt config { contract := contract, locals := L0 } evm
        (.ite (.binary .eq (.var "groupR") (.intLit 2))
          [.internalCall "f2" [.var "br", .var "cr", .var "dr"] "fR2",
           .assign .localVar { base := "fR" } (.var "fR2")] [])
        (.ok { contract := contract, locals := L2 } evm) := by
      apply execGroupIfTrue "groupR" 2 _ hgroup0
      exact ExecBlock.consNormal hcall (ExecBlock.consNormal hassign ExecBlock.nil)
    apply ExecBlock.consNormal htrue
    have hg2 : L2.get? "groupR" = some (natValue 2) := by
      simp only [L2]; rw [store_get_ne _ _ (by decide)]
      simp only [L1]; rw [store_get_ne _ _ (by decide), hgroup0]
    apply ExecBlock.consNormal (execGroupIfFalse "groupR" 2 3 _ (by decide) hg2)
    apply ExecBlock.consNormal (execGroupIfFalse "groupR" 2 4 _ (by decide) hg2)
    simpa [rightFSelectionStore, L2, L1, L0] using ExecBlock.nil
  · let L1 := L0.insert "fR3" (wordValue (runtimeRightF 3 b c d))
    let L2 := L1.insert "fR" (wordValue (runtimeRightF 3 b c d))
    apply ExecBlock.consNormal (execGroupIfFalse "groupR" 3 0 _ (by decide) hgroup0)
    apply ExecBlock.consNormal (execGroupIfFalse "groupR" 3 1 _ (by decide) hgroup0)
    apply ExecBlock.consNormal (execGroupIfFalse "groupR" 3 2 _ (by decide) hgroup0)
    have hcall : ExecStmt config { contract := contract, locals := L0 } evm
        (.internalCall "f1" [.var "br", .var "cr", .var "dr"] "fR3")
        (.ok { contract := contract, locals := L1 } evm) := by
      simpa [L1, runtimeRightF, wordLand_comm, wordLor_comm] using f1Call evm b c d hb32
        (evalWordVar hb0) (evalWordVar hc0) (evalWordVar hd0)
    have hfR1 : L1.get? "fR" = some (natValue 0) := by
      simp only [L1]; rw [store_get_ne _ _ (by decide)]; simp [L0]
    have hf31 : L1.get? "fR3" = some (wordValue (runtimeRightF 3 b c d)) := by simp [L1]
    have hassign := execAssignLocal (evm := evm) hfR1 (evalWordVar hf31)
    have htrue : ExecStmt config { contract := contract, locals := L0 } evm
        (.ite (.binary .eq (.var "groupR") (.intLit 3))
          [.internalCall "f1" [.var "br", .var "cr", .var "dr"] "fR3",
           .assign .localVar { base := "fR" } (.var "fR3")] [])
        (.ok { contract := contract, locals := L2 } evm) := by
      apply execGroupIfTrue "groupR" 3 _ hgroup0
      exact ExecBlock.consNormal hcall (ExecBlock.consNormal hassign ExecBlock.nil)
    apply ExecBlock.consNormal htrue
    have hg2 : L2.get? "groupR" = some (natValue 3) := by
      simp only [L2]; rw [store_get_ne _ _ (by decide)]
      simp only [L1]; rw [store_get_ne _ _ (by decide), hgroup0]
    apply ExecBlock.consNormal (execGroupIfFalse "groupR" 3 4 _ (by decide) hg2)
    simpa [rightFSelectionStore, L2, L1, L0] using ExecBlock.nil
  · let L1 := L0.insert "fR4" (wordValue (runtimeRightF 4 b c d))
    let L2 := L1.insert "fR" (wordValue (runtimeRightF 4 b c d))
    apply ExecBlock.consNormal (execGroupIfFalse "groupR" 4 0 _ (by decide) hgroup0)
    apply ExecBlock.consNormal (execGroupIfFalse "groupR" 4 1 _ (by decide) hgroup0)
    apply ExecBlock.consNormal (execGroupIfFalse "groupR" 4 2 _ (by decide) hgroup0)
    apply ExecBlock.consNormal (execGroupIfFalse "groupR" 4 3 _ (by decide) hgroup0)
    have hcall : ExecStmt config { contract := contract, locals := L0 } evm
        (.internalCall "f0" [.var "br", .var "cr", .var "dr"] "fR4")
        (.ok { contract := contract, locals := L1 } evm) := by
      simpa [L1, runtimeRightF] using f0Call evm b c d
        (evalWordVar hb0) (evalWordVar hc0) (evalWordVar hd0)
    have hfR1 : L1.get? "fR" = some (natValue 0) := by
      simp only [L1]; rw [store_get_ne _ _ (by decide)]; simp [L0]
    have hf41 : L1.get? "fR4" = some (wordValue (runtimeRightF 4 b c d)) := by simp [L1]
    have hassign := execAssignLocal (evm := evm) hfR1 (evalWordVar hf41)
    have htrue : ExecStmt config { contract := contract, locals := L0 } evm
        (.ite (.binary .eq (.var "groupR") (.intLit 4))
          [.internalCall "f0" [.var "br", .var "cr", .var "dr"] "fR4",
           .assign .localVar { base := "fR" } (.var "fR4")] [])
        (.ok { contract := contract, locals := L2 } evm) := by
      apply execGroupIfTrue "groupR" 4 _ hgroup0
      exact ExecBlock.consNormal hcall (ExecBlock.consNormal hassign ExecBlock.nil)
    apply ExecBlock.consNormal htrue
    simpa [rightFSelectionStore, L2, L1, L0] using ExecBlock.nil

@[simp] theorem rightFSelectionStore_fR (L : Store) (group : Nat) (b c d : UInt256)
    (hg : group < 5) :
    (rightFSelectionStore L group b c d).get? "fR" =
      some (wordValue (runtimeRightF group b c d)) := by
  interval_cases group <;> simp [rightFSelectionStore]

theorem rightFSelectionStore_get_original (L : Store) (group : Nat) (b c d : UInt256)
    (hg : group < 5) (name : Ident)
    (hf : ("fR" == name) = false) (hf0 : ("fR0" == name) = false)
    (hf1 : ("fR1" == name) = false) (hf2 : ("fR2" == name) = false)
    (hf3 : ("fR3" == name) = false) (hf4 : ("fR4" == name) = false) :
    (rightFSelectionStore L group b c d).get? name = L.get? name := by
  interval_cases group
  · simp only [rightFSelectionStore]
    rw [store_get_ne _ _ hf, store_get_ne _ _ hf0, store_get_ne _ _ hf]
  · simp only [rightFSelectionStore]
    rw [store_get_ne _ _ hf, store_get_ne _ _ hf1, store_get_ne _ _ hf]
  · simp only [rightFSelectionStore]
    rw [store_get_ne _ _ hf, store_get_ne _ _ hf2, store_get_ne _ _ hf]
  · simp only [rightFSelectionStore]
    rw [store_get_ne _ _ hf, store_get_ne _ _ hf3, store_get_ne _ _ hf]
  · simp only [rightFSelectionStore]
    rw [store_get_ne _ _ hf, store_get_ne _ _ hf4, store_get_ne _ _ hf]

end Ripemd160
