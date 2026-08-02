import Examples.Ripemd160.SolmRoundControl

/-!
# RIPEMD-160 Solm round steps

Execution of the arithmetic and state-update tail shared by the authored left and right rounds.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

def RuntimeLineBound (s : RuntimeLineState) : Prop :=
  s.a.toNat < 2 ^ 32 ∧ s.b.toNat < 2 ^ 32 ∧ s.c.toNat < 2 ^ 32 ∧
    s.d.toNat < 2 ^ 32 ∧ s.e.toNat < 2 ^ 32

def leftRoundTail : List Stmt :=
  [ .letDecl "idxL" uint256Ty (.binary .mod (.var "roundL") (.intLit 16)),
    .internalCall "nibble" [.var "wordTableL", .var "idxL"] "wordIdxL",
    .internalCall "nibble" [.var "rotTableL", .var "idxL"] "shiftL",
    .letDecl "sumL" uint256Ty
      (.binary .bitAnd
        (.binary .add
          (.binary .add
            (.binary .add (.var "al") (.binary .bitAnd (.var "fL") (.var "mask32")))
            (.index (.var "words") (.var "wordIdxL")))
          (.var "kL"))
        (.var "mask32")),
    .internalCall "rotl32" [.var "sumL", .var "shiftL"] "rotatedL",
    .letDecl "nextL" uint256Ty
      (.binary .bitAnd (.binary .add (.var "rotatedL") (.var "el")) (.var "mask32")),
    .internalCall "rotl32" [.var "cl", .intLit 10] "clRot",
    .assign .localVar { base := "al" } (.var "el"),
    .assign .localVar { base := "el" } (.var "dl"),
    .assign .localVar { base := "dl" } (.var "clRot"),
    .assign .localVar { base := "cl" } (.var "bl"),
    .assign .localVar { base := "bl" } (.var "nextL") ]

def sourceRoundSum (s : RuntimeLineState) (x boolF constant : UInt256) : UInt256 :=
  UInt256.land mask32Word (s.a + UInt256.land mask32Word boolF + x + constant)

theorem sourceRoundNext_eq_sum (s : RuntimeLineState) (x : UInt256) (round : Nat)
    (rotationRow boolF constant : UInt256) :
    sourceRoundNext s x round rotationRow boolF constant =
      UInt256.land mask32Word
        (runtimeRol32 (sourceRoundSum s x boolF constant)
          (runtimeRowEntry rotationRow (UInt256.ofNat round)) + s.e) := by
  simp [sourceRoundNext, sourceRoundSum, u256_land_comm]

def leftRoundTailStore (L : Store) (s : RuntimeLineState) (x : UInt256)
    (round : Nat) (wordRow rotationRow boolF constant : UInt256) : Store :=
  let wordIdx := runtimeRowEntry wordRow (UInt256.ofNat round)
  let shift := runtimeRowEntry rotationRow (UInt256.ofNat round)
  let sum := sourceRoundSum s x boolF constant
  let rotated := runtimeRol32 sum shift
  let next := sourceRoundNext s x round rotationRow boolF constant
  let clRot := runtimeRol32 s.c ⟨10⟩
  let L1 := L.insert "idxL" (natValue round)
  let L2 := L1.insert "wordIdxL" (wordValue wordIdx)
  let L3 := L2.insert "shiftL" (wordValue shift)
  let L4 := L3.insert "sumL" (wordValue sum)
  let L5 := L4.insert "rotatedL" (wordValue rotated)
  let L6 := L5.insert "nextL" (wordValue next)
  let L7 := L6.insert "clRot" (wordValue clRot)
  let L8 := L7.insert "al" (wordValue s.e)
  let L9 := L8.insert "el" (wordValue s.d)
  let L10 := L9.insert "dl" (wordValue clRot)
  let L11 := L10.insert "cl" (wordValue s.b)
  L11.insert "bl" (wordValue next)

theorem leftRoundTailReturns {L : Store} (evm : EVM.State) (X : Fin 16 -> UInt256)
    (s : RuntimeLineState) (group round : Nat)
    (wordRow rotationRow boolF constant : UInt256)
    (hg : group < 5) (hr : round < 16) (hs : RuntimeLineBound s)
    (hX32 : ∀ i, (X i).toNat < 2 ^ 32)
    (hround : L.get? "roundL" = some (natValue round))
    (hwordRow : L.get? "wordTableL" = some (wordValue wordRow))
    (hrotRow : L.get? "rotTableL" = some (wordValue rotationRow))
    (hconstant : L.get? "kL" = some (wordValue constant))
    (hconstant32 : constant.toNat < 2 ^ 32)
    (hf : L.get? "fL" = some (wordValue boolF))
    (hmask : L.get? "mask32" = some (wordValue mask32Word))
    (hwords : L.get? "words" = some (.array (roundWords X)))
    (ha : L.get? "al" = some (wordValue s.a))
    (hb : L.get? "bl" = some (wordValue s.b))
    (hc : L.get? "cl" = some (wordValue s.c))
    (hd : L.get? "dl" = some (wordValue s.d))
    (he : L.get? "el" = some (wordValue s.e)) :
    ExecBlock config { contract := contract, locals := L } evm leftRoundTail
      (.ok { contract := contract, locals :=
        (leftRoundTailStore L s
          (X ⟨(runtimeRowEntry wordRow (UInt256.ofNat round)).toNat,
            runtimeRowEntry_lt_sixteen _ _⟩)
          round wordRow rotationRow boolF constant) } evm) := by
  let wordIdx := runtimeRowEntry wordRow (UInt256.ofNat round)
  let shift := runtimeRowEntry rotationRow (UInt256.ofNat round)
  let xi : Fin 16 := ⟨wordIdx.toNat, runtimeRowEntry_lt_sixteen _ _⟩
  let x := X xi
  let maskedF := UInt256.land mask32Word boolF
  let t0 := s.a + maskedF
  let t1 := t0 + x
  let t2 := t1 + constant
  let sum := UInt256.land mask32Word t2
  let rotated := runtimeRol32 sum shift
  let next := sourceRoundNext s x round rotationRow boolF constant
  let clRot := runtimeRol32 s.c ⟨10⟩
  rcases hs with ⟨ha32, hb32, hc32, hd32, he32⟩
  have hmaskedF32 : maskedF.toNat < 2 ^ 32 := runtimeMask32_lt _
  have hx32 : x.toNat < 2 ^ 32 := hX32 xi
  have ht0Bound : s.a.toNat + maskedF.toNat < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from by decide]; omega
  have ht0Nat : t0.toNat = s.a.toNat + maskedF.toNat := by
    simp only [t0, uadd_toNat]
    rw [show UInt256.size = 2 ^ 256 from by decide, Nat.mod_eq_of_lt]
    exact ht0Bound
  have ht1Bound : t0.toNat + x.toNat < UInt256.size := by
    rw [ht0Nat, show UInt256.size = 2 ^ 256 from by decide]; omega
  have ht1Nat : t1.toNat = t0.toNat + x.toNat := by
    simp only [t1, uadd_toNat]
    rw [show UInt256.size = 2 ^ 256 from by decide, Nat.mod_eq_of_lt]
    exact ht1Bound
  have ht2Bound : t1.toNat + constant.toNat < UInt256.size := by
    rw [ht1Nat, ht0Nat, show UInt256.size = 2 ^ 256 from by decide]; omega
  have hwordIdx : wordIdx.toNat < 16 := runtimeRowEntry_lt_sixteen _ _
  have hshift : shift.toNat < 16 := runtimeRowEntry_lt_sixteen _ _
  have hwordIdxOfNat : UInt256.ofNat wordIdx.toNat = wordIdx := u256_ofNat_toNat wordIdx
  have hshiftOfNat : UInt256.ofNat shift.toNat = shift := u256_ofNat_toNat shift
  let L1 := L.insert "idxL" (natValue round)
  have hidxEval : evalExpr? config { contract := contract, locals := L } evm
      (.binary .mod (.var "roundL") (.intLit 16)) = .ok (natValue round) := by
    have h := evalNatMod (by decide) (evalNatVar hround)
      (show evalExpr? config { contract := contract, locals := L } evm (.intLit 16) =
        .ok (natValue 16) by simp [evalExpr?, natValue, pure])
    simpa [Nat.mod_eq_of_lt hr] using h
  have hletIdx : ExecStmt config { contract := contract, locals := L } evm
      (.letDecl "idxL" uint256Ty (.binary .mod (.var "roundL") (.intLit 16)))
      (.ok { contract := contract, locals := L1 } evm) := ExecStmt.letDecl hidxEval
  have hwordRow1 : L1.get? "wordTableL" = some (wordValue wordRow) := by
    simp only [L1]; rw [store_get_ne _ _ (by decide), hwordRow]
  have hrotRow1 : L1.get? "rotTableL" = some (wordValue rotationRow) := by
    simp only [L1]; rw [store_get_ne _ _ (by decide), hrotRow]
  have hidx1 : L1.get? "idxL" = some (natValue round) := by simp [L1]
  let L2 := L1.insert "wordIdxL" (wordValue wordIdx)
  have hwordCall : ExecStmt config { contract := contract, locals := L1 } evm
      (.internalCall "nibble" [.var "wordTableL", .var "idxL"] "wordIdxL")
      (.ok { contract := contract, locals := L2 } evm) := by
    simpa [L2, wordIdx] using nibbleCall evm wordRow round hr
      (evalWordVar hwordRow1) (by
        simpa [natValue, wordValue, ulit_toNat' round (lt_trans hr (by decide))]
          using evalNatVar hidx1)
  have hrotRow2 : L2.get? "rotTableL" = some (wordValue rotationRow) := by
    simp only [L2]; rw [store_get_ne _ _ (by decide), hrotRow1]
  have hidx2 : L2.get? "idxL" = some (natValue round) := by
    simp only [L2]; rw [store_get_ne _ _ (by decide), hidx1]
  let L3 := L2.insert "shiftL" (wordValue shift)
  have hshiftCall : ExecStmt config { contract := contract, locals := L2 } evm
      (.internalCall "nibble" [.var "rotTableL", .var "idxL"] "shiftL")
      (.ok { contract := contract, locals := L3 } evm) := by
    simpa [L3, shift] using nibbleCall evm rotationRow round hr
      (evalWordVar hrotRow2) (by
        simpa [natValue, wordValue, ulit_toNat' round (lt_trans hr (by decide))]
          using evalNatVar hidx2)
  have getL3 (name : Ident) (hshiftName : ("shiftL" == name) = false)
      (hwordName : ("wordIdxL" == name) = false) (hidxName : ("idxL" == name) = false) :
      L3.get? name = L.get? name := by
    simp only [L3]; rw [store_get_ne _ _ hshiftName]
    simp only [L2]; rw [store_get_ne _ _ hwordName]
    simp only [L1]; rw [store_get_ne _ _ hidxName]
  have hwordIdx3 : L3.get? "wordIdxL" = some (wordValue wordIdx) := by
    simp only [L3]; rw [store_get_ne _ _ (by decide)]; simp [L2]
  have hwords3 : L3.get? "words" = some (.array (roundWords X)) := by
    rw [getL3 "words" (by decide) (by decide) (by decide), hwords]
  have hf3 : L3.get? "fL" = some (wordValue boolF) := by
    rw [getL3 "fL" (by decide) (by decide) (by decide), hf]
  have hmask3 : L3.get? "mask32" = some (wordValue mask32Word) := by
    rw [getL3 "mask32" (by decide) (by decide) (by decide), hmask]
  have ha3 : L3.get? "al" = some (wordValue s.a) := by
    rw [getL3 "al" (by decide) (by decide) (by decide), ha]
  have hk3 : L3.get? "kL" = some (wordValue constant) := by
    rw [getL3 "kL" (by decide) (by decide) (by decide), hconstant]
  have hwordEval : evalExpr? config { contract := contract, locals := L3 } evm
      (.index (.var "words") (.var "wordIdxL")) = .ok (wordValue x) := by
    have hidxEval' : evalExpr? config { contract := contract, locals := L3 } evm
        (.var "wordIdxL") = .ok (wordValue (UInt256.ofNat wordIdx.toNat)) := by
      rw [hwordIdxOfNat]
      exact evalWordVar hwordIdx3
    simpa [x, xi] using evalRoundWord X wordIdx.toNat hwordIdx hwords3 hidxEval'
  have hfMaskEval : evalExpr? config { contract := contract, locals := L3 } evm
      (.binary .bitAnd (.var "fL") (.var "mask32")) = .ok (wordValue maskedF) := by
    exact evalMask32 (evalWordVar hf3) (evalWordVar hmask3)
  have ht0Eval : evalExpr? config { contract := contract, locals := L3 } evm
      (.binary .add (.var "al") (.binary .bitAnd (.var "fL") (.var "mask32"))) =
      .ok (wordValue t0) := evalWordAdd ht0Bound (evalWordVar ha3) hfMaskEval
  have ht1Eval : evalExpr? config { contract := contract, locals := L3 } evm
      (.binary .add
        (.binary .add (.var "al") (.binary .bitAnd (.var "fL") (.var "mask32")))
        (.index (.var "words") (.var "wordIdxL"))) = .ok (wordValue t1) :=
    evalWordAdd ht1Bound ht0Eval hwordEval
  have ht2Eval : evalExpr? config { contract := contract, locals := L3 } evm
      (.binary .add
        (.binary .add
          (.binary .add (.var "al") (.binary .bitAnd (.var "fL") (.var "mask32")))
          (.index (.var "words") (.var "wordIdxL")))
        (.var "kL")) = .ok (wordValue t2) :=
    evalWordAdd ht2Bound ht1Eval (evalWordVar hk3)
  have hsumEval : evalExpr? config { contract := contract, locals := L3 } evm
      (.binary .bitAnd
        (.binary .add
          (.binary .add
            (.binary .add (.var "al") (.binary .bitAnd (.var "fL") (.var "mask32")))
            (.index (.var "words") (.var "wordIdxL")))
          (.var "kL"))
        (.var "mask32")) = .ok (wordValue sum) := by
    simpa [sum, sourceRoundSum, t2, t1, t0, maskedF] using
      evalMask32 ht2Eval (evalWordVar hmask3)
  let L4 := L3.insert "sumL" (wordValue sum)
  have hletSum : ExecStmt config { contract := contract, locals := L3 } evm
      (.letDecl "sumL" uint256Ty _) (.ok { contract := contract, locals := L4 } evm) :=
    ExecStmt.letDecl hsumEval
  have hsum4 : L4.get? "sumL" = some (wordValue sum) := by simp [L4]
  have hshift4 : L4.get? "shiftL" = some (wordValue shift) := by
    simp only [L4]; rw [store_get_ne _ _ (by decide)]; simp [L3]
  let L5 := L4.insert "rotatedL" (wordValue rotated)
  have hrotCall : ExecStmt config { contract := contract, locals := L4 } evm
      (.internalCall "rotl32" [.var "sumL", .var "shiftL"] "rotatedL")
      (.ok { contract := contract, locals := L5 } evm) := by
    simpa [L5, rotated, hshiftOfNat] using rotl32Call evm sum shift.toNat
      (runtimeMask32_lt _) hshift (evalWordVar hsum4) (by
        rw [hshiftOfNat]; exact evalWordVar hshift4)
  have hrotated5 : L5.get? "rotatedL" = some (wordValue rotated) := by simp [L5]
  have he5 : L5.get? "el" = some (wordValue s.e) := by
    simp only [L5]; rw [store_get_ne _ _ (by decide)]
    simp only [L4]; rw [store_get_ne _ _ (by decide)]
    rw [getL3 "el" (by decide) (by decide) (by decide), he]
  have hmask5 : L5.get? "mask32" = some (wordValue mask32Word) := by
    simp only [L5]; rw [store_get_ne _ _ (by decide)]
    simp only [L4]; rw [store_get_ne _ _ (by decide)]
    exact hmask3
  have hrotBound : rotated.toNat < 2 ^ 32 := by
    exact runtimeMask32_lt _
  have hnextAddBound : rotated.toNat + s.e.toNat < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from by decide]; omega
  have hnextAdd : evalExpr? config { contract := contract, locals := L5 } evm
      (.binary .add (.var "rotatedL") (.var "el")) =
      .ok (wordValue (rotated + s.e)) :=
    evalWordAdd (evm := evm) hnextAddBound (evalWordVar hrotated5) (evalWordVar he5)
  have hnextEq : next = UInt256.land mask32Word (rotated + s.e) := by
    simpa [next, rotated, sum, sourceRoundSum, t2, t1, t0, maskedF] using
      sourceRoundNext_eq_sum s x round rotationRow boolF constant
  have hnextEval : evalExpr? config { contract := contract, locals := L5 } evm
      (.binary .bitAnd (.binary .add (.var "rotatedL") (.var "el")) (.var "mask32")) =
      .ok (wordValue next) := by
    rw [hnextEq]
    exact evalMask32 hnextAdd (evalWordVar hmask5)
  let L6 := L5.insert "nextL" (wordValue next)
  have hletNext : ExecStmt config { contract := contract, locals := L5 } evm
      (.letDecl "nextL" uint256Ty _) (.ok { contract := contract, locals := L6 } evm) :=
    ExecStmt.letDecl hnextEval
  have hc6 : L6.get? "cl" = some (wordValue s.c) := by
    simp only [L6]; rw [store_get_ne _ _ (by decide)]
    simp only [L5]; rw [store_get_ne _ _ (by decide)]
    simp only [L4]; rw [store_get_ne _ _ (by decide)]
    rw [getL3 "cl" (by decide) (by decide) (by decide), hc]
  let L7 := L6.insert "clRot" (wordValue clRot)
  have hclCall : ExecStmt config { contract := contract, locals := L6 } evm
      (.internalCall "rotl32" [.var "cl", .intLit 10] "clRot")
      (.ok { contract := contract, locals := L7 } evm) := by
    simpa [L7, clRot] using rotl32Call evm s.c 10 hc32 (by decide)
      (evalWordVar hc6) (evalWordLit 10 (by decide))
  have original7 (name : Ident)
      (hclRotName : ("clRot" == name) = false) (hnextName : ("nextL" == name) = false)
      (hrotatedName : ("rotatedL" == name) = false) (hsumName : ("sumL" == name) = false)
      (hshiftName : ("shiftL" == name) = false)
      (hwordName : ("wordIdxL" == name) = false) (hidxName : ("idxL" == name) = false) :
      L7.get? name = L.get? name := by
    simp only [L7]; rw [store_get_ne _ _ hclRotName]
    simp only [L6]; rw [store_get_ne _ _ hnextName]
    simp only [L5]; rw [store_get_ne _ _ hrotatedName]
    simp only [L4]; rw [store_get_ne _ _ hsumName]
    exact getL3 name hshiftName hwordName hidxName
  have hal7 : L7.get? "al" = some (wordValue s.a) := by
    rw [original7 "al" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), ha]
  have hel7 : L7.get? "el" = some (wordValue s.e) := by
    rw [original7 "el" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), he]
  have hdl7 : L7.get? "dl" = some (wordValue s.d) := by
    rw [original7 "dl" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hd]
  have hcl7 : L7.get? "cl" = some (wordValue s.c) := by
    rw [original7 "cl" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hc]
  have hbl7 : L7.get? "bl" = some (wordValue s.b) := by
    rw [original7 "bl" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hb]
  have hclRot7 : L7.get? "clRot" = some (wordValue clRot) := by simp [L7]
  have hnext7 : L7.get? "nextL" = some (wordValue next) := by
    simp only [L7]; rw [store_get_ne _ _ (by decide)]; simp [L6]
  let L8 := L7.insert "al" (wordValue s.e)
  have hassignA := execAssignLocal (evm := evm) hal7 (evalWordVar hel7)
  let L9 := L8.insert "el" (wordValue s.d)
  have hdl8 : L8.get? "dl" = some (wordValue s.d) := by
    simp only [L8]; rw [store_get_ne _ _ (by decide), hdl7]
  have hel8 : L8.get? "el" = some (wordValue s.e) := by
    simp only [L8]; rw [store_get_ne _ _ (by decide), hel7]
  have hassignE := execAssignLocal (evm := evm) hel8 (evalWordVar hdl8)
  let L10 := L9.insert "dl" (wordValue clRot)
  have hdl9 : L9.get? "dl" = some (wordValue s.d) := by
    simp only [L9]; rw [store_get_ne _ _ (by decide), hdl8]
  have hclRot9 : L9.get? "clRot" = some (wordValue clRot) := by
    simp only [L9]; rw [store_get_ne _ _ (by decide)]
    simp only [L8]; rw [store_get_ne _ _ (by decide), hclRot7]
  have hassignD := execAssignLocal (evm := evm) hdl9 (evalWordVar hclRot9)
  let L11 := L10.insert "cl" (wordValue s.b)
  have hcl10 : L10.get? "cl" = some (wordValue s.c) := by
    simp only [L10]; rw [store_get_ne _ _ (by decide)]
    simp only [L9]; rw [store_get_ne _ _ (by decide)]
    simp only [L8]; rw [store_get_ne _ _ (by decide), hcl7]
  have hbl10 : L10.get? "bl" = some (wordValue s.b) := by
    simp only [L10]; rw [store_get_ne _ _ (by decide)]
    simp only [L9]; rw [store_get_ne _ _ (by decide)]
    simp only [L8]; rw [store_get_ne _ _ (by decide), hbl7]
  have hassignC := execAssignLocal (evm := evm) hcl10 (evalWordVar hbl10)
  let L12 := L11.insert "bl" (wordValue next)
  have hbl11 : L11.get? "bl" = some (wordValue s.b) := by
    simp only [L11]; rw [store_get_ne _ _ (by decide), hbl10]
  have hnext11 : L11.get? "nextL" = some (wordValue next) := by
    simp only [L11]; rw [store_get_ne _ _ (by decide)]
    simp only [L10]; rw [store_get_ne _ _ (by decide)]
    simp only [L9]; rw [store_get_ne _ _ (by decide)]
    simp only [L8]; rw [store_get_ne _ _ (by decide), hnext7]
  have hassignB := execAssignLocal (evm := evm) hbl11 (evalWordVar hnext11)
  apply ExecBlock.consNormal hletIdx
  apply ExecBlock.consNormal hwordCall
  apply ExecBlock.consNormal hshiftCall
  apply ExecBlock.consNormal hletSum
  apply ExecBlock.consNormal hrotCall
  apply ExecBlock.consNormal hletNext
  apply ExecBlock.consNormal hclCall
  apply ExecBlock.consNormal hassignA
  apply ExecBlock.consNormal hassignE
  apply ExecBlock.consNormal hassignD
  apply ExecBlock.consNormal hassignC
  apply ExecBlock.consNormal hassignB
  simpa [leftRoundTailStore, L12, L11, L10, L9, L8, L7, L6, L5, L4, L3, L2, L1,
    next, rotated, sum, t2, t1, t0, maskedF, x, xi, shift, wordIdx] using ExecBlock.nil

end Ripemd160
