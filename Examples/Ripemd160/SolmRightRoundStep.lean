import Examples.Ripemd160.SolmRoundStep

/-!
# RIPEMD-160 Solm right round step

The right compression-line arithmetic tail, obtained from the left tail by the exact local-name
renaming used in the authored source.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

def rightRoundTail : List Stmt :=
  [ .letDecl "idxR" uint256Ty (.binary .mod (.var "roundR") (.intLit 16)),
    .internalCall "nibble" [.var "wordTableR", .var "idxR"] "wordIdxR",
    .internalCall "nibble" [.var "rotTableR", .var "idxR"] "shiftR",
    .letDecl "sumR" uint256Ty
      (.binary .bitAnd
        (.binary .add
          (.binary .add
            (.binary .add (.var "ar") (.binary .bitAnd (.var "fR") (.var "mask32")))
            (.index (.var "words") (.var "wordIdxR")))
          (.var "kR"))
        (.var "mask32")),
    .internalCall "rotl32" [.var "sumR", .var "shiftR"] "rotatedR",
    .letDecl "nextR" uint256Ty
      (.binary .bitAnd (.binary .add (.var "rotatedR") (.var "er")) (.var "mask32")),
    .internalCall "rotl32" [.var "cr", .intLit 10] "crRot",
    .assign .localVar { base := "ar" } (.var "er"),
    .assign .localVar { base := "er" } (.var "dr"),
    .assign .localVar { base := "dr" } (.var "crRot"),
    .assign .localVar { base := "cr" } (.var "br"),
    .assign .localVar { base := "br" } (.var "nextR") ]

def rightRoundTailStore (L : Store) (s : RuntimeLineState) (x : UInt256)
    (round : Nat) (wordRow rotationRow boolF constant : UInt256) : Store :=
  let wordIdx := runtimeRowEntry wordRow (UInt256.ofNat round)
  let shift := runtimeRowEntry rotationRow (UInt256.ofNat round)
  let sum := sourceRoundSum s x boolF constant
  let rotated := runtimeRol32 sum shift
  let next := sourceRoundNext s x round rotationRow boolF constant
  let clRot := runtimeRol32 s.c ⟨10⟩
  let L1 := L.insert "idxR" (natValue round)
  let L2 := L1.insert "wordIdxR" (wordValue wordIdx)
  let L3 := L2.insert "shiftR" (wordValue shift)
  let L4 := L3.insert "sumR" (wordValue sum)
  let L5 := L4.insert "rotatedR" (wordValue rotated)
  let L6 := L5.insert "nextR" (wordValue next)
  let L7 := L6.insert "crRot" (wordValue clRot)
  let L8 := L7.insert "ar" (wordValue s.e)
  let L9 := L8.insert "er" (wordValue s.d)
  let L10 := L9.insert "dr" (wordValue clRot)
  let L11 := L10.insert "cr" (wordValue s.b)
  L11.insert "br" (wordValue next)

theorem rightRoundTailReturns {L : Store} (evm : EVM.State) (X : Fin 16 -> UInt256)
    (s : RuntimeLineState) (group round : Nat)
    (wordRow rotationRow boolF constant : UInt256)
    (hg : group < 5) (hr : round < 16) (hs : RuntimeLineBound s)
    (hX32 : ∀ i, (X i).toNat < 2 ^ 32)
    (hround : L.get? "roundR" = some (natValue round))
    (hwordRow : L.get? "wordTableR" = some (wordValue wordRow))
    (hrotRow : L.get? "rotTableR" = some (wordValue rotationRow))
    (hconstant : L.get? "kR" = some (wordValue constant))
    (hconstant32 : constant.toNat < 2 ^ 32)
    (hf : L.get? "fR" = some (wordValue boolF))
    (hmask : L.get? "mask32" = some (wordValue mask32Word))
    (hwords : L.get? "words" = some (.array (roundWords X)))
    (ha : L.get? "ar" = some (wordValue s.a))
    (hb : L.get? "br" = some (wordValue s.b))
    (hc : L.get? "cr" = some (wordValue s.c))
    (hd : L.get? "dr" = some (wordValue s.d))
    (he : L.get? "er" = some (wordValue s.e)) :
    ExecBlock config { contract := contract, locals := L } evm rightRoundTail
      (.ok { contract := contract, locals :=
        (rightRoundTailStore L s
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
  let L1 := L.insert "idxR" (natValue round)
  have hidxEval : evalExpr? config { contract := contract, locals := L } evm
      (.binary .mod (.var "roundR") (.intLit 16)) = .ok (natValue round) := by
    have h := evalNatMod (by decide) (evalNatVar hround)
      (show evalExpr? config { contract := contract, locals := L } evm (.intLit 16) =
        .ok (natValue 16) by simp [evalExpr?, natValue, pure])
    simpa [Nat.mod_eq_of_lt hr] using h
  have hletIdx : ExecStmt config { contract := contract, locals := L } evm
      (.letDecl "idxR" uint256Ty (.binary .mod (.var "roundR") (.intLit 16)))
      (.ok { contract := contract, locals := L1 } evm) := ExecStmt.letDecl hidxEval
  have hwordRow1 : L1.get? "wordTableR" = some (wordValue wordRow) := by
    simp only [L1]; rw [store_get_ne _ _ (by decide), hwordRow]
  have hrotRow1 : L1.get? "rotTableR" = some (wordValue rotationRow) := by
    simp only [L1]; rw [store_get_ne _ _ (by decide), hrotRow]
  have hidx1 : L1.get? "idxR" = some (natValue round) := by simp [L1]
  let L2 := L1.insert "wordIdxR" (wordValue wordIdx)
  have hwordCall : ExecStmt config { contract := contract, locals := L1 } evm
      (.internalCall "nibble" [.var "wordTableR", .var "idxR"] "wordIdxR")
      (.ok { contract := contract, locals := L2 } evm) := by
    simpa [L2, wordIdx] using nibbleCall evm wordRow round hr
      (evalWordVar hwordRow1) (by
        simpa [natValue, wordValue, ulit_toNat' round (lt_trans hr (by decide))]
          using evalNatVar hidx1)
  have hrotRow2 : L2.get? "rotTableR" = some (wordValue rotationRow) := by
    simp only [L2]; rw [store_get_ne _ _ (by decide), hrotRow1]
  have hidx2 : L2.get? "idxR" = some (natValue round) := by
    simp only [L2]; rw [store_get_ne _ _ (by decide), hidx1]
  let L3 := L2.insert "shiftR" (wordValue shift)
  have hshiftCall : ExecStmt config { contract := contract, locals := L2 } evm
      (.internalCall "nibble" [.var "rotTableR", .var "idxR"] "shiftR")
      (.ok { contract := contract, locals := L3 } evm) := by
    simpa [L3, shift] using nibbleCall evm rotationRow round hr
      (evalWordVar hrotRow2) (by
        simpa [natValue, wordValue, ulit_toNat' round (lt_trans hr (by decide))]
          using evalNatVar hidx2)
  have getL3 (name : Ident) (hshiftName : ("shiftR" == name) = false)
      (hwordName : ("wordIdxR" == name) = false) (hidxName : ("idxR" == name) = false) :
      L3.get? name = L.get? name := by
    simp only [L3]; rw [store_get_ne _ _ hshiftName]
    simp only [L2]; rw [store_get_ne _ _ hwordName]
    simp only [L1]; rw [store_get_ne _ _ hidxName]
  have hwordIdx3 : L3.get? "wordIdxR" = some (wordValue wordIdx) := by
    simp only [L3]; rw [store_get_ne _ _ (by decide)]; simp [L2]
  have hwords3 : L3.get? "words" = some (.array (roundWords X)) := by
    rw [getL3 "words" (by decide) (by decide) (by decide), hwords]
  have hf3 : L3.get? "fR" = some (wordValue boolF) := by
    rw [getL3 "fR" (by decide) (by decide) (by decide), hf]
  have hmask3 : L3.get? "mask32" = some (wordValue mask32Word) := by
    rw [getL3 "mask32" (by decide) (by decide) (by decide), hmask]
  have ha3 : L3.get? "ar" = some (wordValue s.a) := by
    rw [getL3 "ar" (by decide) (by decide) (by decide), ha]
  have hk3 : L3.get? "kR" = some (wordValue constant) := by
    rw [getL3 "kR" (by decide) (by decide) (by decide), hconstant]
  have hwordEval : evalExpr? config { contract := contract, locals := L3 } evm
      (.index (.var "words") (.var "wordIdxR")) = .ok (wordValue x) := by
    have hidxEval' : evalExpr? config { contract := contract, locals := L3 } evm
        (.var "wordIdxR") = .ok (wordValue (UInt256.ofNat wordIdx.toNat)) := by
      rw [hwordIdxOfNat]
      exact evalWordVar hwordIdx3
    simpa [x, xi] using evalRoundWord X wordIdx.toNat hwordIdx hwords3 hidxEval'
  have hfMaskEval : evalExpr? config { contract := contract, locals := L3 } evm
      (.binary .bitAnd (.var "fR") (.var "mask32")) = .ok (wordValue maskedF) := by
    exact evalMask32 (evalWordVar hf3) (evalWordVar hmask3)
  have ht0Eval : evalExpr? config { contract := contract, locals := L3 } evm
      (.binary .add (.var "ar") (.binary .bitAnd (.var "fR") (.var "mask32"))) =
      .ok (wordValue t0) := evalWordAdd ht0Bound (evalWordVar ha3) hfMaskEval
  have ht1Eval : evalExpr? config { contract := contract, locals := L3 } evm
      (.binary .add
        (.binary .add (.var "ar") (.binary .bitAnd (.var "fR") (.var "mask32")))
        (.index (.var "words") (.var "wordIdxR"))) = .ok (wordValue t1) :=
    evalWordAdd ht1Bound ht0Eval hwordEval
  have ht2Eval : evalExpr? config { contract := contract, locals := L3 } evm
      (.binary .add
        (.binary .add
          (.binary .add (.var "ar") (.binary .bitAnd (.var "fR") (.var "mask32")))
          (.index (.var "words") (.var "wordIdxR")))
        (.var "kR")) = .ok (wordValue t2) :=
    evalWordAdd ht2Bound ht1Eval (evalWordVar hk3)
  have hsumEval : evalExpr? config { contract := contract, locals := L3 } evm
      (.binary .bitAnd
        (.binary .add
          (.binary .add
            (.binary .add (.var "ar") (.binary .bitAnd (.var "fR") (.var "mask32")))
            (.index (.var "words") (.var "wordIdxR")))
          (.var "kR"))
        (.var "mask32")) = .ok (wordValue sum) := by
    simpa [sum, sourceRoundSum, t2, t1, t0, maskedF] using
      evalMask32 ht2Eval (evalWordVar hmask3)
  let L4 := L3.insert "sumR" (wordValue sum)
  have hletSum : ExecStmt config { contract := contract, locals := L3 } evm
      (.letDecl "sumR" uint256Ty _) (.ok { contract := contract, locals := L4 } evm) :=
    ExecStmt.letDecl hsumEval
  have hsum4 : L4.get? "sumR" = some (wordValue sum) := by simp [L4]
  have hshift4 : L4.get? "shiftR" = some (wordValue shift) := by
    simp only [L4]; rw [store_get_ne _ _ (by decide)]; simp [L3]
  let L5 := L4.insert "rotatedR" (wordValue rotated)
  have hrotCall : ExecStmt config { contract := contract, locals := L4 } evm
      (.internalCall "rotl32" [.var "sumR", .var "shiftR"] "rotatedR")
      (.ok { contract := contract, locals := L5 } evm) := by
    simpa [L5, rotated, hshiftOfNat] using rotl32Call evm sum shift.toNat
      (runtimeMask32_lt _) hshift (evalWordVar hsum4) (by
        rw [hshiftOfNat]; exact evalWordVar hshift4)
  have hrotated5 : L5.get? "rotatedR" = some (wordValue rotated) := by simp [L5]
  have he5 : L5.get? "er" = some (wordValue s.e) := by
    simp only [L5]; rw [store_get_ne _ _ (by decide)]
    simp only [L4]; rw [store_get_ne _ _ (by decide)]
    rw [getL3 "er" (by decide) (by decide) (by decide), he]
  have hmask5 : L5.get? "mask32" = some (wordValue mask32Word) := by
    simp only [L5]; rw [store_get_ne _ _ (by decide)]
    simp only [L4]; rw [store_get_ne _ _ (by decide)]
    exact hmask3
  have hrotBound : rotated.toNat < 2 ^ 32 := by
    exact runtimeMask32_lt _
  have hnextAddBound : rotated.toNat + s.e.toNat < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from by decide]; omega
  have hnextAdd : evalExpr? config { contract := contract, locals := L5 } evm
      (.binary .add (.var "rotatedR") (.var "er")) =
      .ok (wordValue (rotated + s.e)) :=
    evalWordAdd (evm := evm) hnextAddBound (evalWordVar hrotated5) (evalWordVar he5)
  have hnextEq : next = UInt256.land mask32Word (rotated + s.e) := by
    simpa [next, rotated, sum, sourceRoundSum, t2, t1, t0, maskedF] using
      sourceRoundNext_eq_sum s x round rotationRow boolF constant
  have hnextEval : evalExpr? config { contract := contract, locals := L5 } evm
      (.binary .bitAnd (.binary .add (.var "rotatedR") (.var "er")) (.var "mask32")) =
      .ok (wordValue next) := by
    rw [hnextEq]
    exact evalMask32 hnextAdd (evalWordVar hmask5)
  let L6 := L5.insert "nextR" (wordValue next)
  have hletNext : ExecStmt config { contract := contract, locals := L5 } evm
      (.letDecl "nextR" uint256Ty _) (.ok { contract := contract, locals := L6 } evm) :=
    ExecStmt.letDecl hnextEval
  have hc6 : L6.get? "cr" = some (wordValue s.c) := by
    simp only [L6]; rw [store_get_ne _ _ (by decide)]
    simp only [L5]; rw [store_get_ne _ _ (by decide)]
    simp only [L4]; rw [store_get_ne _ _ (by decide)]
    rw [getL3 "cr" (by decide) (by decide) (by decide), hc]
  let L7 := L6.insert "crRot" (wordValue clRot)
  have hclCall : ExecStmt config { contract := contract, locals := L6 } evm
      (.internalCall "rotl32" [.var "cr", .intLit 10] "crRot")
      (.ok { contract := contract, locals := L7 } evm) := by
    simpa [L7, clRot] using rotl32Call evm s.c 10 hc32 (by decide)
      (evalWordVar hc6) (evalWordLit 10 (by decide))
  have original7 (name : Ident)
      (hclRotName : ("crRot" == name) = false) (hnextName : ("nextR" == name) = false)
      (hrotatedName : ("rotatedR" == name) = false) (hsumName : ("sumR" == name) = false)
      (hshiftName : ("shiftR" == name) = false)
      (hwordName : ("wordIdxR" == name) = false) (hidxName : ("idxR" == name) = false) :
      L7.get? name = L.get? name := by
    simp only [L7]; rw [store_get_ne _ _ hclRotName]
    simp only [L6]; rw [store_get_ne _ _ hnextName]
    simp only [L5]; rw [store_get_ne _ _ hrotatedName]
    simp only [L4]; rw [store_get_ne _ _ hsumName]
    exact getL3 name hshiftName hwordName hidxName
  have hal7 : L7.get? "ar" = some (wordValue s.a) := by
    rw [original7 "ar" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), ha]
  have hel7 : L7.get? "er" = some (wordValue s.e) := by
    rw [original7 "er" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), he]
  have hdl7 : L7.get? "dr" = some (wordValue s.d) := by
    rw [original7 "dr" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hd]
  have hcl7 : L7.get? "cr" = some (wordValue s.c) := by
    rw [original7 "cr" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hc]
  have hbl7 : L7.get? "br" = some (wordValue s.b) := by
    rw [original7 "br" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hb]
  have hclRot7 : L7.get? "crRot" = some (wordValue clRot) := by simp [L7]
  have hnext7 : L7.get? "nextR" = some (wordValue next) := by
    simp only [L7]; rw [store_get_ne _ _ (by decide)]; simp [L6]
  let L8 := L7.insert "ar" (wordValue s.e)
  have hassignA := execAssignLocal (evm := evm) hal7 (evalWordVar hel7)
  let L9 := L8.insert "er" (wordValue s.d)
  have hdl8 : L8.get? "dr" = some (wordValue s.d) := by
    simp only [L8]; rw [store_get_ne _ _ (by decide), hdl7]
  have hel8 : L8.get? "er" = some (wordValue s.e) := by
    simp only [L8]; rw [store_get_ne _ _ (by decide), hel7]
  have hassignE := execAssignLocal (evm := evm) hel8 (evalWordVar hdl8)
  let L10 := L9.insert "dr" (wordValue clRot)
  have hdl9 : L9.get? "dr" = some (wordValue s.d) := by
    simp only [L9]; rw [store_get_ne _ _ (by decide), hdl8]
  have hclRot9 : L9.get? "crRot" = some (wordValue clRot) := by
    simp only [L9]; rw [store_get_ne _ _ (by decide)]
    simp only [L8]; rw [store_get_ne _ _ (by decide), hclRot7]
  have hassignD := execAssignLocal (evm := evm) hdl9 (evalWordVar hclRot9)
  let L11 := L10.insert "cr" (wordValue s.b)
  have hcl10 : L10.get? "cr" = some (wordValue s.c) := by
    simp only [L10]; rw [store_get_ne _ _ (by decide)]
    simp only [L9]; rw [store_get_ne _ _ (by decide)]
    simp only [L8]; rw [store_get_ne _ _ (by decide), hcl7]
  have hbl10 : L10.get? "br" = some (wordValue s.b) := by
    simp only [L10]; rw [store_get_ne _ _ (by decide)]
    simp only [L9]; rw [store_get_ne _ _ (by decide)]
    simp only [L8]; rw [store_get_ne _ _ (by decide), hbl7]
  have hassignC := execAssignLocal (evm := evm) hcl10 (evalWordVar hbl10)
  let L12 := L11.insert "br" (wordValue next)
  have hbl11 : L11.get? "br" = some (wordValue s.b) := by
    simp only [L11]; rw [store_get_ne _ _ (by decide), hbl10]
  have hnext11 : L11.get? "nextR" = some (wordValue next) := by
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
  simpa [rightRoundTailStore, L12, L11, L10, L9, L8, L7, L6, L5, L4, L3, L2, L1,
    next, rotated, sum, t2, t1, t0, maskedF, x, xi, shift, wordIdx] using ExecBlock.nil


end Ripemd160
