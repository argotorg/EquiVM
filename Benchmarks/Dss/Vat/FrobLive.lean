import Benchmarks.Dss.Vat.FrobLiveSuccess

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Vat

suppress_compilation

def frobLiveAddArithmeticGuards (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.gt (frobDinkWord I + solcSlotWord σ I (frobUrnInkSlot I))
      (solcSlotWord σ I (frobUrnInkSlot I)) = ⟨0⟩) ∧
  (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.lt (frobDinkWord I + solcSlotWord σ I (frobUrnInkSlot I))
      (solcSlotWord σ I (frobUrnInkSlot I)) = ⟨0⟩) ∧
  (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.gt (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I))
      (solcSlotWord σ I (frobUrnArtSlot I)) = ⟨0⟩) ∧
  (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.lt (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I))
      (solcSlotWord σ I (frobUrnArtSlot I)) = ⟨0⟩) ∧
  (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.gt (frobDartWord I + solcSlotWord σ I (frobIlkArtSlot I))
      (solcSlotWord σ I (frobIlkArtSlot I)) = ⟨0⟩) ∧
  (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.lt (frobDartWord I + solcSlotWord σ I (frobIlkArtSlot I))
      (solcSlotWord σ I (frobIlkArtSlot I)) = ⟨0⟩)

def frobLiveMulArithmeticGuards (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  UInt256.slt (solcSlotWord σ I (frobIlkRateSlot I)) ⟨0⟩ = ⟨0⟩ ∧
  (frobDartWord I = ⟨0⟩ ∨
    UInt256.eq
      (UInt256.sdiv
        (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)))
        (frobDartWord I))
      (solcSlotWord σ I (frobIlkRateSlot I)) ≠ ⟨0⟩) ∧
  ((frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I)) = ⟨0⟩ ∨
    UInt256.eq
      (UInt256.div
        (UInt256.mul (solcSlotWord σ I (frobIlkRateSlot I))
          (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I)))
        (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I)))
      (solcSlotWord σ I (frobIlkRateSlot I)) ≠ ⟨0⟩)

def frobLiveArithmeticPrefixGuards (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.gt (frobDinkWord I + solcSlotWord σ I (frobUrnInkSlot I))
      (solcSlotWord σ I (frobUrnInkSlot I)) = ⟨0⟩) ∧
  (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.lt (frobDinkWord I + solcSlotWord σ I (frobUrnInkSlot I))
      (solcSlotWord σ I (frobUrnInkSlot I)) = ⟨0⟩) ∧
  (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.gt (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I))
      (solcSlotWord σ I (frobUrnArtSlot I)) = ⟨0⟩) ∧
  (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.lt (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I))
      (solcSlotWord σ I (frobUrnArtSlot I)) = ⟨0⟩) ∧
  (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.gt (frobDartWord I + solcSlotWord σ I (frobIlkArtSlot I))
      (solcSlotWord σ I (frobIlkArtSlot I)) = ⟨0⟩) ∧
  (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.lt (frobDartWord I + solcSlotWord σ I (frobIlkArtSlot I))
      (solcSlotWord σ I (frobIlkArtSlot I)) = ⟨0⟩) ∧
  UInt256.slt (solcSlotWord σ I (frobIlkRateSlot I)) ⟨0⟩ = ⟨0⟩ ∧
  (frobDartWord I = ⟨0⟩ ∨
    UInt256.eq
      (UInt256.sdiv
        (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)))
        (frobDartWord I))
      (solcSlotWord σ I (frobIlkRateSlot I)) ≠ ⟨0⟩) ∧
  ((frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I)) = ⟨0⟩ ∨
    UInt256.eq
      (UInt256.div
        (UInt256.mul (solcSlotWord σ I (frobIlkRateSlot I))
          (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I)))
        (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I)))
      (solcSlotWord σ I (frobIlkRateSlot I)) ≠ ⟨0⟩)

def frobLiveDebtCeilingSafetyGuards (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  (UInt256.slt
      (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)))
      ⟨0⟩ = ⟨0⟩ ∨
    UInt256.gt
      (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)) +
        solcSlotWord σ I foldDebtSlot)
      (solcSlotWord σ I foldDebtSlot) = ⟨0⟩) ∧
  (UInt256.sgt
      (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)))
      ⟨0⟩ = ⟨0⟩ ∨
    UInt256.lt
      (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)) +
        solcSlotWord σ I foldDebtSlot)
      (solcSlotWord σ I foldDebtSlot) = ⟨0⟩) ∧
  (solcSlotWord σ I (frobIlkRateSlot I) = ⟨0⟩ ∨
    UInt256.eq
      (UInt256.div
        (UInt256.mul
          (frobDartWord I + solcSlotWord σ I (frobIlkArtSlot I))
          (solcSlotWord σ I (frobIlkRateSlot I)))
        (solcSlotWord σ I (frobIlkRateSlot I)))
      (frobDartWord I + solcSlotWord σ I (frobIlkArtSlot I)) ≠ ⟨0⟩) ∧
  UInt256.lor
    (UInt256.land
      (UInt256.isZero
        (UInt256.gt
          (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)) +
            solcSlotWord σ I foldDebtSlot)
          (solcSlotWord σ I ⟨9⟩)))
      (UInt256.isZero
        (UInt256.gt
          (UInt256.mul
            (frobDartWord I + solcSlotWord σ I (frobIlkArtSlot I))
            (solcSlotWord σ I (frobIlkRateSlot I)))
          (solcSlotWord σ I (frobIlkLineSlot I)))))
    (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) ≠ ⟨0⟩ ∧
  (((sstoreAccountMap I.codeOwner σ foldDebtSlot
    (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)) +
      solcSlotWord σ I foldDebtSlot)).find? I.codeOwner |>.option ⟨0⟩
      (fun acc => acc.storage.findD (⟨7⟩ : UInt256) ⟨0⟩)) =
    UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)) +
      solcSlotWord σ I foldDebtSlot) ∧
  (solcSlotWord σ I (frobIlkSpotSlot I) = ⟨0⟩ ∨
    UInt256.eq
      (UInt256.div
        (UInt256.mul
          (frobDinkWord I + solcSlotWord σ I (frobUrnInkSlot I))
          (solcSlotWord σ I (frobIlkSpotSlot I)))
        (solcSlotWord σ I (frobIlkSpotSlot I)))
      (frobDinkWord I + solcSlotWord σ I (frobUrnInkSlot I)) ≠ ⟨0⟩) ∧
  UInt256.lor
    (UInt256.isZero
      (UInt256.gt
        (UInt256.mul (solcSlotWord σ I (frobIlkRateSlot I))
          (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I)))
        (UInt256.mul
          (frobDinkWord I + solcSlotWord σ I (frobUrnInkSlot I))
          (solcSlotWord σ I (frobIlkSpotSlot I)))))
    (UInt256.land
      (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
      (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) ≠ ⟨0⟩

def frobLiveWishAuthDustGuards (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  UInt256.lor
    (UInt256.lor
      (UInt256.eq (vatSlotWord (frobUWishSlot I)
        (sstoreAccountMap I.codeOwner σ foldDebtSlot
          (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)) +
            solcSlotWord σ I foldDebtSlot)) I) ⟨1⟩)
      (UInt256.eq (frobUMaskedWord I) (hopeSourceWord I)))
    (UInt256.land
      (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
      (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) ≠ ⟨0⟩ ∧
  UInt256.lor
    (UInt256.lor
      (UInt256.eq (vatSlotWord (frobVWishSlot I)
        (sstoreAccountMap I.codeOwner σ foldDebtSlot
          (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)) +
            solcSlotWord σ I foldDebtSlot)) I) ⟨1⟩)
      (UInt256.eq (frobVMaskedWord I) (hopeSourceWord I)))
    (UInt256.isZero (UInt256.sgt (frobDinkWord I) ⟨0⟩)) ≠ ⟨0⟩ ∧
  UInt256.lor
    (UInt256.lor
      (UInt256.eq (vatSlotWord (frobWWishSlot I)
        (sstoreAccountMap I.codeOwner σ foldDebtSlot
          (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)) +
            solcSlotWord σ I foldDebtSlot)) I) ⟨1⟩)
      (UInt256.eq (frobWMaskedWord I) (hopeSourceWord I)))
    (UInt256.isZero (UInt256.slt (frobDartWord I) ⟨0⟩)) ≠ ⟨0⟩ ∧
  UInt256.lor
    (UInt256.isZero
      (UInt256.lt
        (UInt256.mul (solcSlotWord σ I (frobIlkRateSlot I))
          (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I)))
        (solcSlotWord σ I (frobIlkDustSlot I))))
    (UInt256.eq ⟨0⟩
      (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I))) ≠ ⟨0⟩

def frobLiveFinalArithmeticGuards (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.gt (frobGemNew σ I)
      (solcSlotWord (frobAfterDebt σ I) I (frobGemVSlot I)) = ⟨0⟩) ∧
  (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.lt (frobGemNew σ I)
      (solcSlotWord (frobAfterDebt σ I) I (frobGemVSlot I)) = ⟨0⟩) ∧
  (UInt256.slt (frobDtabWord σ I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.gt (frobDaiNew σ I)
      (solcSlotWord (frobAfterGem σ I) I (frobDaiWSlot I)) = ⟨0⟩) ∧
  (UInt256.sgt (frobDtabWord σ I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.lt (frobDaiNew σ I)
      (solcSlotWord (frobAfterGem σ I) I (frobDaiWSlot I)) = ⟨0⟩)

theorem frobLiveSuccessGuards_of_groups {σ : AccountMap} {I : ExecutionEnv}
    (hArithmetic : frobLiveArithmeticPrefixGuards σ I)
    (hDebtSafety : frobLiveDebtCeilingSafetyGuards σ I)
    (hWishDust : frobLiveWishAuthDustGuards σ I)
    (hFinalArithmetic : frobLiveFinalArithmeticGuards σ I) :
    frobLiveSuccessGuards σ I := by
  unfold frobLiveArithmeticPrefixGuards at hArithmetic
  unfold frobLiveDebtCeilingSafetyGuards at hDebtSafety
  unfold frobLiveWishAuthDustGuards at hWishDust
  unfold frobLiveFinalArithmeticGuards at hFinalArithmetic
  unfold frobLiveSuccessGuards
  rcases hArithmetic with
    ⟨hInkNeg, hInkPos, hArtNeg, hArtPos, hIlkNeg, hIlkPos, hRateMax,
      hDtabMul, hTabMul⟩
  rcases hDebtSafety with
    ⟨hDebtNeg, hDebtPos, hCeilingMul, hCeilingOk, hDebtLoadStore, hInkMul,
      hSafetyOk⟩
  rcases hWishDust with ⟨hU, hV, hW, hDust⟩
  rcases hFinalArithmetic with ⟨hGemPos, hGemNeg, hDaiNeg, hDaiPos⟩
  exact
    ⟨hInkNeg, hInkPos, hArtNeg, hArtPos, hIlkNeg, hIlkPos, hRateMax,
      hDtabMul, hTabMul, hDebtNeg, hDebtPos, hCeilingMul, hCeilingOk,
      hDebtLoadStore, hInkMul, hSafetyOk, hU, hV, hW, hDust, hGemPos, hGemNeg,
      hDaiNeg, hDaiPos⟩

theorem frobLiveArithmeticPrefixGuards_of_add_mul {σ : AccountMap} {I : ExecutionEnv}
    (hAdd : frobLiveAddArithmeticGuards σ I)
    (hMul : frobLiveMulArithmeticGuards σ I) :
    frobLiveArithmeticPrefixGuards σ I := by
  unfold frobLiveAddArithmeticGuards at hAdd
  unfold frobLiveMulArithmeticGuards at hMul
  unfold frobLiveArithmeticPrefixGuards
  rcases hAdd with ⟨hInkNeg, hInkPos, hArtNeg, hArtPos, hIlkNeg, hIlkPos⟩
  rcases hMul with ⟨hRateMax, hDtabMul, hTabMul⟩
  exact
    ⟨hInkNeg, hInkPos, hArtNeg, hArtPos, hIlkNeg, hIlkPos, hRateMax,
      hDtabMul, hTabMul⟩

theorem frobLiveAddMulGuards_of_arithmeticPrefix {σ : AccountMap} {I : ExecutionEnv}
    (hArithmetic : frobLiveArithmeticPrefixGuards σ I) :
    frobLiveAddArithmeticGuards σ I ∧ frobLiveMulArithmeticGuards σ I := by
  unfold frobLiveArithmeticPrefixGuards at hArithmetic
  unfold frobLiveAddArithmeticGuards
  unfold frobLiveMulArithmeticGuards
  rcases hArithmetic with
    ⟨hInkNeg, hInkPos, hArtNeg, hArtPos, hIlkNeg, hIlkPos, hRateMax,
      hDtabMul, hTabMul⟩
  exact
    ⟨⟨hInkNeg, hInkPos, hArtNeg, hArtPos, hIlkNeg, hIlkPos⟩,
      ⟨hRateMax, hDtabMul, hTabMul⟩⟩

theorem hsourceRevertFromPrefix {evm : EVM.State} {I : ExecutionEnv}
    {p tail : List Stmt}
    (hbody : frobTransition.body = p ++ tail)
    (hsrcPrefixRevert :
      ExecBlock config { contract := contract, locals := frobStore I } evm p
        .reverted) :
    ExecTransitionBody config contract evm (frobStore I) frobTransition.body
      .reverted := by
  have hblock :
      ExecBlock config { contract := contract, locals := frobStore I } evm
        frobTransition.body .reverted := by
    rw [hbody]
    exact Reasoning.Refinement.execBlock_append_term (s2 := tail) hsrcPrefixRevert
      (by intro f e h; cases h)
  exact ExecFuncBody.execBlockRevert hblock

theorem hsourceRevertFromUrnInkAdd {evm : EVM.State} {I : ExecutionEnv}
    (hsrcPrefixRevert :
      ExecBlock config { contract := contract, locals := frobStore I } evm
        ((nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
          checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink"))
        .reverted) :
    ExecTransitionBody config contract evm (frobStore I) frobTransition.body
      .reverted := by
  exact hsourceRevertFromPrefix
    (tail :=
      checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
      checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
      checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
      checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
      checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
      [ .assign .storage debtRef (.var "debtNew") ] ++
      checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
      checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
      [ .require
          (eitherExpr
            (.binary .le (.var "dart") (.intLit 0))
            (bothExpr
              (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
              (.binary .le (.var "debtNew") (.storage LineRef)))),
        .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
      [ .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (wishExpr (.var "u") sender)),
        .require
          (eitherExpr (.binary .le (.var "dink") (.intLit 0))
            (wishExpr (.var "v") sender)),
        .require
          (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
            (wishExpr (.var "w") sender)),
        .require
          (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
            (.binary .ge (.var "tab") (.var "ilkDust"))) ] ++
      checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
      checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
      [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
        .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
        .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
        .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
        .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
        .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
    (by simp [frobTransition, List.append_assoc])
    hsrcPrefixRevert
theorem hsourceRevertFromUrnArtAdd {evm : EVM.State} {I : ExecutionEnv}
    (hsrcPrefixRevert :
      ExecBlock config { contract := contract, locals := frobStore I } evm
        ((nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
          checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
          checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart"))
        .reverted) :
    ExecTransitionBody config contract evm (frobStore I) frobTransition.body
      .reverted := by
  exact hsourceRevertFromPrefix
    (tail :=
      checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
      checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
      checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
      checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
      [ .assign .storage debtRef (.var "debtNew") ] ++
      checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
      checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
      [ .require
          (eitherExpr
            (.binary .le (.var "dart") (.intLit 0))
            (bothExpr
              (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
              (.binary .le (.var "debtNew") (.storage LineRef)))),
        .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
      [ .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (wishExpr (.var "u") sender)),
        .require
          (eitherExpr (.binary .le (.var "dink") (.intLit 0))
            (wishExpr (.var "v") sender)),
        .require
          (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
            (wishExpr (.var "w") sender)),
        .require
          (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
            (.binary .ge (.var "tab") (.var "ilkDust"))) ] ++
      checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
      checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
      [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
        .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
        .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
        .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
        .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
        .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
    (by simp [frobTransition, List.append_assoc])
    hsrcPrefixRevert
theorem hsourceRevertFromIlkArtAdd {evm : EVM.State} {I : ExecutionEnv}
    (hsrcPrefixRevert :
      ExecBlock config { contract := contract, locals := frobStore I } evm
        ((nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
          checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
          checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
          checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart"))
        .reverted) :
    ExecTransitionBody config contract evm (frobStore I) frobTransition.body
      .reverted := by
  exact hsourceRevertFromPrefix
    (tail :=
      checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
      checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
      checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
      [ .assign .storage debtRef (.var "debtNew") ] ++
      checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
      checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
      [ .require
          (eitherExpr
            (.binary .le (.var "dart") (.intLit 0))
            (bothExpr
              (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
              (.binary .le (.var "debtNew") (.storage LineRef)))),
        .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
      [ .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (wishExpr (.var "u") sender)),
        .require
          (eitherExpr (.binary .le (.var "dink") (.intLit 0))
            (wishExpr (.var "v") sender)),
        .require
          (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
            (wishExpr (.var "w") sender)),
        .require
          (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
            (.binary .ge (.var "tab") (.var "ilkDust"))) ] ++
      checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
      checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
      [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
        .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
        .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
        .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
        .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
        .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
    (by simp [frobTransition, List.append_assoc])
    hsrcPrefixRevert
theorem hsourceRevertFromDtabMul {evm : EVM.State} {I : ExecutionEnv}
    (hsrcPrefixRevert :
      ExecBlock config { contract := contract, locals := frobStore I } evm
        ((nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
          checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
          checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
          checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
          checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart"))
        .reverted) :
    ExecTransitionBody config contract evm (frobStore I) frobTransition.body
      .reverted := by
  exact hsourceRevertFromPrefix
    (tail :=
      checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
      checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
      [ .assign .storage debtRef (.var "debtNew") ] ++
      checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
      checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
      [ .require
          (eitherExpr
            (.binary .le (.var "dart") (.intLit 0))
            (bothExpr
              (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
              (.binary .le (.var "debtNew") (.storage LineRef)))),
        .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
      [ .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (wishExpr (.var "u") sender)),
        .require
          (eitherExpr (.binary .le (.var "dink") (.intLit 0))
            (wishExpr (.var "v") sender)),
        .require
          (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
            (wishExpr (.var "w") sender)),
        .require
          (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
            (.binary .ge (.var "tab") (.var "ilkDust"))) ] ++
      checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
      checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
      [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
        .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
        .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
        .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
        .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
        .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
    (by simp [frobTransition, List.append_assoc])
    hsrcPrefixRevert
theorem hsourceRevertFromTabMul {evm : EVM.State} {I : ExecutionEnv}
    (hsrcPrefixRevert :
      ExecBlock config { contract := contract, locals := frobStore I } evm
        ((nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
          checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
          checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
          checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
          checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
          checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew"))
        .reverted) :
    ExecTransitionBody config contract evm (frobStore I) frobTransition.body
      .reverted := by
  exact hsourceRevertFromPrefix
    (tail :=
      checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
      [ .assign .storage debtRef (.var "debtNew") ] ++
      checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
      checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
      [ .require
          (eitherExpr
            (.binary .le (.var "dart") (.intLit 0))
            (bothExpr
              (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
              (.binary .le (.var "debtNew") (.storage LineRef)))),
        .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
      [ .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (wishExpr (.var "u") sender)),
        .require
          (eitherExpr (.binary .le (.var "dink") (.intLit 0))
            (wishExpr (.var "v") sender)),
        .require
          (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
            (wishExpr (.var "w") sender)),
        .require
          (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
            (.binary .ge (.var "tab") (.var "ilkDust"))) ] ++
      checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
      checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
      [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
        .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
        .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
        .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
        .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
        .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
    (by simp [frobTransition, List.append_assoc])
    hsrcPrefixRevert
theorem hsourceRevertFromDebtAdd {evm : EVM.State} {I : ExecutionEnv}
    (hsrcPrefixRevert :
      ExecBlock config { contract := contract, locals := frobStore I } evm
        ((nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
          checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
          checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
          checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
          checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
          checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
          checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab"))
        .reverted) :
    ExecTransitionBody config contract evm (frobStore I) frobTransition.body
      .reverted := by
  exact hsourceRevertFromPrefix
    (tail :=
      [ .assign .storage debtRef (.var "debtNew") ] ++
      checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
      checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
      [ .require
          (eitherExpr
            (.binary .le (.var "dart") (.intLit 0))
            (bothExpr
              (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
              (.binary .le (.var "debtNew") (.storage LineRef)))),
        .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
      [ .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (wishExpr (.var "u") sender)),
        .require
          (eitherExpr (.binary .le (.var "dink") (.intLit 0))
            (wishExpr (.var "v") sender)),
        .require
          (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
            (wishExpr (.var "w") sender)),
        .require
          (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
            (.binary .ge (.var "tab") (.var "ilkDust"))) ] ++
      checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
      checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
      [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
        .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
        .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
        .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
        .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
        .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
    (by simp [frobTransition, List.append_assoc])
    hsrcPrefixRevert
theorem hsourceRevertFromCeilingMul {evm : EVM.State} {I : ExecutionEnv}
    (hsrcPrefixRevert :
      ExecBlock config { contract := contract, locals := frobStore I } evm
        ((nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
          checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
          checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
          checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
          checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
          checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
          checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
          [ .assign .storage debtRef (.var "debtNew") ] ++
          checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate"))
        .reverted) :
    ExecTransitionBody config contract evm (frobStore I) frobTransition.body
      .reverted := by
  exact hsourceRevertFromPrefix
    (tail :=
      checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
      [ .require
          (eitherExpr
            (.binary .le (.var "dart") (.intLit 0))
            (bothExpr
              (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
              (.binary .le (.var "debtNew") (.storage LineRef)))),
        .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
      [ .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (wishExpr (.var "u") sender)),
        .require
          (eitherExpr (.binary .le (.var "dink") (.intLit 0))
            (wishExpr (.var "v") sender)),
        .require
          (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
            (wishExpr (.var "w") sender)),
        .require
          (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
            (.binary .ge (.var "tab") (.var "ilkDust"))) ] ++
      checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
      checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
      [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
        .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
        .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
        .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
        .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
        .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
    (by simp [frobTransition, List.append_assoc])
    hsrcPrefixRevert
theorem hsourceRevertFromInkSpotMul {evm : EVM.State} {I : ExecutionEnv}
    (hsrcPrefixRevert :
      ExecBlock config { contract := contract, locals := frobStore I } evm
        ((nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
          checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
          checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
          checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
          checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
          checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
          checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
          [ .assign .storage debtRef (.var "debtNew") ] ++
          checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot"))
        .reverted) :
    ExecTransitionBody config contract evm (frobStore I) frobTransition.body
      .reverted := by
  exact hsourceRevertFromPrefix
    (tail :=
      [ .require
          (eitherExpr
            (.binary .le (.var "dart") (.intLit 0))
            (bothExpr
              (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
              (.binary .le (.var "debtNew") (.storage LineRef)))),
        .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
      [ .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (wishExpr (.var "u") sender)),
        .require
          (eitherExpr (.binary .le (.var "dink") (.intLit 0))
            (wishExpr (.var "v") sender)),
        .require
          (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
            (wishExpr (.var "w") sender)),
        .require
          (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
            (.binary .ge (.var "tab") (.var "ilkDust"))) ] ++
      checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
      checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
      [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
        .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
        .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
        .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
        .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
        .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
    (by simp [frobTransition, List.append_assoc])
    hsrcPrefixRevert
theorem hsourceRevertFromCeilingRequire {evm : EVM.State} {I : ExecutionEnv}
    (hsrcPrefixRevert :
      ExecBlock config { contract := contract, locals := frobStore I } evm
        ((nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
          checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
          checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
          checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
          checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
          checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
          checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
          [ .assign .storage debtRef (.var "debtNew") ] ++
          checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
          [ .require
              (eitherExpr
                (.binary .le (.var "dart") (.intLit 0))
                (bothExpr
                  (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                  (.binary .le (.var "debtNew") (.storage LineRef)))) ])
        .reverted) :
    ExecTransitionBody config contract evm (frobStore I) frobTransition.body
      .reverted := by
  exact hsourceRevertFromPrefix
    (tail :=
      [ .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
      [ .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (wishExpr (.var "u") sender)),
        .require
          (eitherExpr (.binary .le (.var "dink") (.intLit 0))
            (wishExpr (.var "v") sender)),
        .require
          (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
            (wishExpr (.var "w") sender)),
        .require
          (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
            (.binary .ge (.var "tab") (.var "ilkDust"))) ] ++
      checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
      checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
      [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
        .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
        .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
        .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
        .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
        .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
    (by simp [frobTransition, List.append_assoc])
    hsrcPrefixRevert
theorem hsourceRevertFromSafetyRequire {evm : EVM.State} {I : ExecutionEnv}
    (hsrcPrefixRevert :
      ExecBlock config { contract := contract, locals := frobStore I } evm
        ((nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
          checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
          checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
          checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
          checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
          checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
          checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
          [ .assign .storage debtRef (.var "debtNew") ] ++
          checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
          [ .require
              (eitherExpr
                (.binary .le (.var "dart") (.intLit 0))
                (bothExpr
                  (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                  (.binary .le (.var "debtNew") (.storage LineRef)))),
            .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (.binary .le (.var "tab") (.var "inkSpot"))) ])
        .reverted) :
    ExecTransitionBody config contract evm (frobStore I) frobTransition.body
      .reverted := by
  exact hsourceRevertFromPrefix
    (tail :=
      [ .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (wishExpr (.var "u") sender)),
        .require
          (eitherExpr (.binary .le (.var "dink") (.intLit 0))
            (wishExpr (.var "v") sender)),
        .require
          (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
            (wishExpr (.var "w") sender)),
        .require
          (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
            (.binary .ge (.var "tab") (.var "ilkDust"))) ] ++
      checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
      checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
      [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
        .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
        .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
        .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
        .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
        .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
    (by simp [frobTransition, List.append_assoc])
    hsrcPrefixRevert
theorem hsourceRevertFromAuthorizationDust {evm : EVM.State} {I : ExecutionEnv}
    (hsrcPrefixRevert :
      ExecBlock config { contract := contract, locals := frobStore I } evm
        ((nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
          checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
          checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
          checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
          checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
          checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
          checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
          [ .assign .storage debtRef (.var "debtNew") ] ++
          checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
          [ .require
              (eitherExpr
                (.binary .le (.var "dart") (.intLit 0))
                (bothExpr
                  (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                  (.binary .le (.var "debtNew") (.storage LineRef)))),
            .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
          [ .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (wishExpr (.var "u") sender)),
            .require
              (eitherExpr (.binary .le (.var "dink") (.intLit 0))
                (wishExpr (.var "v") sender)),
            .require
              (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
                (wishExpr (.var "w") sender)),
            .require
              (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
                (.binary .ge (.var "tab") (.var "ilkDust"))) ])
        .reverted) :
    ExecTransitionBody config contract evm (frobStore I) frobTransition.body
      .reverted := by
  exact hsourceRevertFromPrefix
    (tail :=
      checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
      checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
      [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
        .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
        .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
        .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
        .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
        .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
    (by simp [frobTransition, List.append_assoc])
    hsrcPrefixRevert

theorem hsourceRevertFromFinalStoreTail {evm evmDebt : EVM.State} {I : ExecutionEnv}
    {localsSafe : Store}
    (hsourceDust :
      ExecBlock config { contract := contract, locals := frobStore I } evm
        ((nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
          checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
          checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
          checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
          checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
          checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
          checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
          [ .assign .storage debtRef (.var "debtNew") ] ++
          checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
          [ .require
              (eitherExpr
                (.binary .le (.var "dart") (.intLit 0))
                (bothExpr
                  (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                  (.binary .le (.var "debtNew") (.storage LineRef)))),
            .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
          [ .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (wishExpr (.var "u") sender)),
            .require
              (eitherExpr (.binary .le (.var "dink") (.intLit 0))
                (wishExpr (.var "v") sender)),
            .require
              (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
                (wishExpr (.var "w") sender)),
            .require
              (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
                (.binary .ge (.var "tab") (.var "ilkDust"))) ])
        (.ok { contract := contract, locals := localsSafe } evmDebt))
    (htail :
      ExecBlock config { contract := contract, locals := localsSafe } evmDebt
        (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
          (.var "dink") ++
          [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
          checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
          [ .assign .storage (daiRef (.var "w")) (.var "daiNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
            .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
            .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
            .assign .storage (ilksF (.var "i") "rate") (.var "ilkRate"),
            .assign .storage (ilksF (.var "i") "spot") (.var "ilkSpot"),
            .assign .storage (ilksF (.var "i") "line") (.var "ilkLine"),
            .assign .storage (ilksF (.var "i") "dust") (.var "ilkDust") ])
        .reverted) :
    ExecTransitionBody config contract evm (frobStore I) frobTransition.body
      .reverted := by
  have hblock := Reasoning.Refinement.execBlock_append hsourceDust htail
  exact ExecFuncBody.execBlockRevert (by
    simpa [ExecTransitionBody, frobTransition, List.append_assoc] using hblock)

set_option maxHeartbeats 0 in
theorem frobConstructedLocalsAuthDustExtras {I : ExecutionEnv}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (dtab : Int) (debtOld dtabWord : UInt256) :
    let localsLoaded :=
      frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
    let urnInkNew := frobDinkWord I + urnInk
    let urnArtNew := frobDartWord I + urnArt
    let ilkArtNew := frobDartWord I + ilkArt
    let localsIlk :=
      (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
          "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat)))
    let localsDtab := localsIlk.insert "dtab" (.int dtab)
    let tab := UInt256.mul ilkRate urnArtNew
    let debtNew := dtabWord + debtOld
    let localsDebt :=
      (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).insert
        "debtNew" (.int (Int.ofNat debtNew.toNat))
    let ceilingDebt := UInt256.mul ilkArtNew ilkRate
    let inkSpot := UInt256.mul urnInkNew ilkSpot
    let localsSafe :=
      (localsDebt.insert "ceilingDebt"
        (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
        (.int (Int.ofNat inkSpot.toNat))
    localsSafe.get? "dart" = some (frobDartValue I) ∧
    localsSafe.get? "tab" = some (.int (Int.ofNat tab.toNat)) ∧
    localsSafe.get? "can" = none := by
  intro localsLoaded urnInkNew urnArtNew ilkArtNew localsIlk localsDtab tab debtNew
    localsDebt ceilingDebt inkSpot localsSafe
  exact ⟨
    (by
      change
        ((((((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
          "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))).get? "dart" =
          some (frobDartValue I)
      repeat rw [store_get_ne _ _ (by decide)]
      simp),
    (by
      change
        ((((((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
          "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))).get? "tab" =
          some (.int (Int.ofNat tab.toNat))
      rw [store_get_ne _ _ (by decide)]
      rw [store_get_ne _ _ (by decide)]
      rw [store_get_ne _ _ (by decide)]
      rw [store_get_self]),
    (by
      change
        ((((((((localsLoaded.insert "urnInkNew"
          (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
          (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
          (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
          "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
          (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
          (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
          (.int (Int.ofNat inkSpot.toNat))).get? "can" = none
      repeat rw [store_get_ne _ _ (by decide)]
      simp)⟩


set_option maxHeartbeats 0 in
theorem vatFrobBodyCoreLiveRateZeroRevert
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (vatSelBytes 11))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz196 : 196 ≤ I.calldata.size)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (frobTransition.params.map Param.name)
        (transitionSignature frobTransition).paramTypes I.calldata = some (frobStore I))
    (hdecoded :
      ∃ k C,
        RD vatBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2975⟩
          [frobDartWord I, frobDinkWord I, frobWMaskedWord I, frobVMaskedWord I,
            frobUMaskedWord I, frobIWord I, ⟨524⟩, vatSelWord I]
          solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hlive : vatSlotWord ⟨10⟩ σ_evm I = ⟨1⟩)
    (hrateZeroEvm : solcSlotWord σ_evm I (frobIlkRateSlot I) = ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, hafterLive⟩ := vatFrobLiveOk
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (sel := vatSelWord I) hlive hdecoded
  let urnInk := vatSlotWord (frobUrnInkSlot I) σ_solm I
  let urnArt := vatSlotWord (frobUrnArtSlot I) σ_solm I
  let ilkArt := vatSlotWord (frobIlkArtSlot I) σ_solm I
  let ilkRate := vatSlotWord (frobIlkRateSlot I) σ_solm I
  let ilkSpot := vatSlotWord (frobIlkSpotSlot I) σ_solm I
  let ilkLine := vatSlotWord (frobIlkLineSlot I) σ_solm I
  let ilkDust := vatSlotWord (frobIlkDustSlot I) σ_solm I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveWord : vatSlotWord ⟨10⟩ σ_evm I = vatSlotWord ⟨10⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨10⟩ ⟨0⟩
  have hliveSolm : vatSlotWord ⟨10⟩ σ_solm I = ⟨1⟩ := by
    rw [← hliveWord]
    exact hlive
  have hrateWord :
      vatSlotWord (frobIlkRateSlot I) σ_solm I = ⟨0⟩ := by
    have heq :
        vatSlotWord (frobIlkRateSlot I) σ_evm I =
          vatSlotWord (frobIlkRateSlot I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (frobIlkRateSlot I) ⟨0⟩
    rw [← heq]
    simpa [vatSlotWord] using hrateZeroEvm
  have hbodyRaw :
      let locals := frobStore I
      let evm0' := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      ExecTransitionBody config contract evm0' locals frobTransition.body
        .reverted := by
    exact vatFrobSourceBodyRateZero
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := g)
        (urnInk := urnInk) (urnArt := urnArt) (ilkArt := ilkArt)
        (ilkRate := ilkRate) (ilkSpot := ilkSpot) (ilkLine := ilkLine)
        (ilkDust := ilkDust)
        hwv hsz196 hliveSolm
        (by simpa [urnInk] using
          (frobSourceLoad_urnInk (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [urnArt] using
          (frobSourceLoad_urnArt (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkArt] using
          (frobSourceLoad_ilkArt (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkRate] using
          (frobSourceLoad_ilkRate (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkSpot] using
          (frobSourceLoad_ilkSpot (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkLine] using
          (frobSourceLoad_ilkLine (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkDust] using
          (frobSourceLoad_ilkDust (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by
          rw [show ilkRate = vatSlotWord (frobIlkRateSlot I) σ_solm I from rfl,
            hrateWord]
          native_decide)
  have hbody :
      ExecTransitionBody config contract evm0 (frobStore I) frobTransition.body
        .reverted := by
    simpa [evm0] using hbodyRaw
  obtain ⟨_, _, hafterUrn⟩ := RD.vatFrobUrnLoads hafterLive
  have hrev := RD.vatFrobIlkLoadsRateZero hafterUrn hrateZeroEvm
  exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel) hdecode hbody


set_option maxHeartbeats 0 in
theorem frobDtabBadRangeOfMulGuardFail {σ : AccountMap} {I : ExecutionEnv}
    {ilkRate : UInt256}
    (hIlkRateEq : solcSlotWord σ I (frobIlkRateSlot I) = ilkRate)
    (hDtabMul :
      ¬ (frobDartWord I = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.sdiv
            (UInt256.mul (frobDartWord I)
              (solcSlotWord σ I (frobIlkRateSlot I)))
            (frobDartWord I))
          (solcSlotWord σ I (frobIlkRateSlot I)) ≠ ⟨0⟩)) :
    let dtab : Int := Int.ofNat ilkRate.toNat * frobDartInt I
    dtab < -((2 : Int) ^ 255) ∨ dtab ≥ (2 : Int) ^ 255 := by
  intro dtab
  have hDtabMulSourceFail :
      ¬ (frobDartWord I = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.sdiv (UInt256.mul (frobDartWord I) ilkRate)
            (frobDartWord I)) ilkRate ≠ ⟨0⟩) := by
    intro hsrc
    exact hDtabMul (by
      simpa [hIlkRateEq] using hsrc)
  by_contra hbadRange
  have hdtabLo : -((2 : Int) ^ 255) ≤ dtab :=
    not_lt.mp (fun h => hbadRange (Or.inl h))
  have hdtabHi : dtab < (2 : Int) ^ 255 :=
    not_le.mp (fun h => hbadRange (Or.inr h))
  have hprodHi :
      Int.ofNat ilkRate.toNat * frobDartInt I < (2 : Int) ^ 255 := by
    change Int.ofNat ilkRate.toNat * frobDartInt I < (2 : Int) ^ 255 at hdtabHi
    exact hdtabHi
  have hdartWordNe : frobDartWord I ≠ ⟨0⟩ := by
    intro hzero
    exact hDtabMulSourceFail (Or.inl hzero)
  by_cases hdartLow : (frobDartWord I).toNat < EVM.twoPow 255
  · have hguardTrue :
        frobDartWord I = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.sdiv
              (UInt256.mul (frobDartWord I) ilkRate)
              (frobDartWord I)) ilkRate ≠ ⟨0⟩ := by
      simpa [grabDartWord, frobDartWord, grabDartInt, frobDartInt] using
        grab_dtab_word_guard_true_of_range_pos I
          (rate := ilkRate) hdartLow hdartWordNe hprodHi
    exact hDtabMulSourceFail hguardTrue
  · have hprodLo :
        -((2 : Int) ^ 255) ≤
          Int.ofNat ilkRate.toNat * frobDartInt I := by
      change -((2 : Int) ^ 255) ≤ Int.ofNat ilkRate.toNat * frobDartInt I at hdtabLo
      exact hdtabLo
    have hrateNe : ilkRate ≠ ⟨0⟩ := by
      intro hzero
      exact hDtabMulSourceFail
        (by
          simpa [grabDartWord, frobDartWord] using
            grab_dtab_word_guard_true_of_rate_zero I (rate := ilkRate) hzero)
    have hguardTrue :
        frobDartWord I = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.sdiv
              (UInt256.mul (frobDartWord I) ilkRate)
              (frobDartWord I)) ilkRate ≠ ⟨0⟩ := by
      simpa [grabDartWord, frobDartWord, grabDartInt, frobDartInt] using
        grab_dtab_word_guard_true_of_range_neg I
          (rate := ilkRate) (not_lt.mp hdartLow) hrateNe hprodLo
    exact hDtabMulSourceFail hguardTrue

theorem frobDtabRangeOfMulGuard {I : ExecutionEnv} {ilkRate : UInt256}
    (hRateMax : UInt256.slt ilkRate ⟨0⟩ = ⟨0⟩)
    (hDtabMul :
      frobDartWord I = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.sdiv (UInt256.mul (frobDartWord I) ilkRate)
            (frobDartWord I)) ilkRate ≠ ⟨0⟩) :
    -((2 : Int) ^ 255) ≤ Int.ofNat ilkRate.toNat * frobDartInt I ∧
      Int.ofNat ilkRate.toNat * frobDartInt I < (2 : Int) ^ 255 := by
  have hRateLow : ilkRate.toNat < EVM.twoPow 255 :=
    u256_toNat_lt_sign_of_slt_zero hRateMax
  have hMulGuardEq :
      frobDartWord I = ⟨0⟩ ∨
        UInt256.sdiv (UInt256.mul (frobDartWord I) ilkRate)
          (frobDartWord I) = ilkRate := by
    cases hDtabMul with
    | inl hzero => exact Or.inl hzero
    | inr hne => exact Or.inr (u256_eq_ne_zero_to_eq hne)
  exact frob_dtab_product_range_of_guard I hRateLow hMulGuardEq

theorem evalFrobDtabSourceGuardsTrue {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store} {ilkRate : UInt256} {dtab : Int}
    (hrate : locals.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)))
    (hdart : locals.get? "dart" = some (frobDartValue I))
    (hdtab : dtab = Int.ofNat ilkRate.toNat * frobDartInt I)
    (hRateMax : UInt256.slt ilkRate ⟨0⟩ = ⟨0⟩) :
    evalExpr? config
      { contract := contract, locals := locals.insert "dtab" (.int dtab) }
      evm (.binary .le (.var "ilkRate") (.intLit maxInt256)) =
      .ok (.bool true) ∧
    evalExpr? config
      { contract := contract, locals := locals.insert "dtab" (.int dtab) }
      evm
      (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
        (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
          (.var "ilkRate"))) =
      .ok (.bool true) := by
  have hrateEval :
      evalExpr? config
        { contract := contract, locals := locals.insert "dtab" (.int dtab) }
        evm (.var "ilkRate") = .ok (.int (Int.ofNat ilkRate.toNat)) := by
    exact vatEvalExpr_varUInt256 (by
      rw [store_get_ne _ _ (by decide)]
      exact hrate)
  have hMaxLit :
      evalExpr? config
        { contract := contract, locals := locals.insert "dtab" (.int dtab) }
        evm (.intLit maxInt256) = .ok (.int maxInt256) := by
    simp [evalExpr?, pure]
  have hguardMax :
      evalExpr? config
        { contract := contract, locals := locals.insert "dtab" (.int dtab) }
        evm (.binary .le (.var "ilkRate") (.intLit maxInt256)) =
        .ok (.bool true) :=
    vatEvalExpr_le_int_true hrateEval hMaxLit
      (uintWordLeMaxInt256_of_slt_zero hRateMax)
  have hguardMul :
      evalExpr? config
        { contract := contract, locals := locals.insert "dtab" (.int dtab) }
        evm
        (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
          (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
            (.var "ilkRate"))) =
        .ok (.bool true) := by
    by_cases hwordZero : frobDartWord I = ⟨0⟩
    · exact evalExpr_frob_dtab_mul_guard_dart_zero_true
        (evm := evm) (locals := locals) I hdart
        (frobDartInt_zero_of_word_zero I hwordZero)
    · have hdartNe : frobDartInt I ≠ 0 :=
        frobDartInt_ne_zero_of_word_ne I hwordZero
      have hdiv : dtab / frobDartInt I = Int.ofNat ilkRate.toNat := by
        rw [hdtab]
        exact Int.mul_ediv_cancel (Int.ofNat ilkRate.toNat) hdartNe
      exact evalExpr_frob_dtab_mul_guard_exact_true
        (evm := evm) (locals := locals) (rate := ilkRate) I hdart hrate
        hdartNe hdiv
  exact ⟨hguardMax, hguardMul⟩

theorem execFrobLoadedPrefixDtabMulRevertRange {evm : EVM.State}
    {I : ExecutionEnv} {pre : List Stmt}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (dtab : Int)
    (hprefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm pre
        (.ok
          { contract := contract,
            locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot
              ilkLine ilkDust }
          evm))
    (hInkNeg : 0 ≤ frobDinkInt I ∨
      (frobDinkWord I + urnInk).toNat ≤ urnInk.toNat)
    (hInkPos : frobDinkInt I ≤ 0 ∨
      urnInk.toNat ≤ (frobDinkWord I + urnInk).toNat)
    (hArtNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + urnArt).toNat ≤ urnArt.toNat)
    (hArtPos : frobDartInt I ≤ 0 ∨
      urnArt.toNat ≤ (frobDartWord I + urnArt).toNat)
    (hIlkNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + ilkArt).toNat ≤ ilkArt.toNat)
    (hIlkPos : frobDartInt I ≤ 0 ∨
      ilkArt.toNat ≤ (frobDartWord I + ilkArt).toNat)
    (hdtab : dtab = Int.ofNat ilkRate.toNat * frobDartInt I)
    (hbad : dtab < -((2 : Int) ^ 255) ∨ dtab ≥ (2 : Int) ^ 255) :
    ExecBlock config { contract := contract, locals := frobStore I } evm
      (pre ++
        checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
        checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
        checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
        checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart"))
      .reverted := by
  let localsLoaded :=
    frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
  let urnInkNew := frobDinkWord I + urnInk
  let urnArtNew := frobDartWord I + urnArt
  let ilkArtNew := frobDartWord I + ilkArt
  let localsIlk :=
    (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
        "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat)))
  have hthree :=
    execFrobLoadedPrefixThreeAdds
      (evm := evm) (I := I) (pre := pre)
      urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust hprefix
      hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
  have hrateGet :
      localsIlk.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)) := by
    change (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
        "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat))).get? "ilkRate" =
        some (.int (Int.ofNat ilkRate.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_rate I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hdartGet : localsIlk.get? "dart" = some (frobDartValue I) := by
    change (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
        "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat))).get? "dart" = some (frobDartValue I)
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_dart I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hdtabBlock :
      ExecBlock config { contract := contract, locals := localsIlk } evm
        (checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart"))
        .reverted :=
    execFrobDtabMulCheckedRevertRange
      (evm := evm) (I := I) localsIlk ilkRate dtab hrateGet hdartGet hdtab hbad
  have hfull := Reasoning.Refinement.execBlock_append
    (by simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk] using hthree)
    hdtabBlock
  simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
    List.append_assoc] using hfull

theorem execFrobLoadedPrefixDtabMulRevertMaxSlt {evm : EVM.State}
    {I : ExecutionEnv} {pre : List Stmt}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (dtab : Int)
    (hprefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm pre
        (.ok
          { contract := contract,
            locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot
              ilkLine ilkDust }
          evm))
    (hInkNeg : 0 ≤ frobDinkInt I ∨
      (frobDinkWord I + urnInk).toNat ≤ urnInk.toNat)
    (hInkPos : frobDinkInt I ≤ 0 ∨
      urnInk.toNat ≤ (frobDinkWord I + urnInk).toNat)
    (hArtNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + urnArt).toNat ≤ urnArt.toNat)
    (hArtPos : frobDartInt I ≤ 0 ∨
      urnArt.toNat ≤ (frobDartWord I + urnArt).toNat)
    (hIlkNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + ilkArt).toNat ≤ ilkArt.toNat)
    (hIlkPos : frobDartInt I ≤ 0 ∨
      ilkArt.toNat ≤ (frobDartWord I + ilkArt).toNat)
    (hdtab : dtab = Int.ofNat ilkRate.toNat * frobDartInt I)
    (hRateMaxFail : UInt256.slt ilkRate ⟨0⟩ ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := frobStore I } evm
      (pre ++
        checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
        checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
        checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
        checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart"))
      .reverted := by
  by_cases hbad : dtab < -((2 : Int) ^ 255) ∨ dtab ≥ (2 : Int) ^ 255
  · exact execFrobLoadedPrefixDtabMulRevertRange
      (evm := evm) (I := I) (pre := pre)
      urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust dtab hprefix
      hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos hdtab hbad
  · let localsLoaded :=
      frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
    let urnInkNew := frobDinkWord I + urnInk
    let urnArtNew := frobDartWord I + urnArt
    let ilkArtNew := frobDartWord I + ilkArt
    let localsIlk :=
      (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
          "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat)))
    have hthree :=
      execFrobLoadedPrefixThreeAdds
        (evm := evm) (I := I) (pre := pre)
        urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust hprefix
        hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
    have hrateGet :
        localsIlk.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)) := by
      change (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
          "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).get? "ilkRate" =
          some (.int (Int.ofNat ilkRate.toNat))
      rw [store_get_ne _ _ (by decide)]
      rw [store_get_ne _ _ (by decide)]
      rw [store_get_ne _ _ (by decide)]
      simpa [localsLoaded] using
        frobStoreIlkDust_get_rate I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
          ilkDust
    have hdartGet : localsIlk.get? "dart" = some (frobDartValue I) := by
      change (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
          "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).get? "dart" = some (frobDartValue I)
      rw [store_get_ne _ _ (by decide)]
      rw [store_get_ne _ _ (by decide)]
      rw [store_get_ne _ _ (by decide)]
      simpa [localsLoaded] using
        frobStoreIlkDust_get_dart I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
          ilkDust
    have hdtabLo : -((2 : Int) ^ 255) ≤ dtab :=
      not_lt.mp (fun h => hbad (Or.inl h))
    have hdtabHi : dtab < (2 : Int) ^ 255 :=
      not_le.mp (fun h => hbad (Or.inr h))
    have hdtabBlock :
        ExecBlock config { contract := contract, locals := localsIlk } evm
          (checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart"))
          .reverted :=
      execFrobDtabMulCheckedRevertMaxSlt
        (evm := evm) (I := I) localsIlk ilkRate dtab hrateGet hdartGet hdtab
        hdtabLo hdtabHi hRateMaxFail
    have hfull := Reasoning.Refinement.execBlock_append
      (by simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk] using hthree)
      hdtabBlock
    simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
      List.append_assoc] using hfull

theorem execFrobLoadedPrefixTabMulRevertOverflow {evm : EVM.State}
    {I : ExecutionEnv} {pre : List Stmt}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (dtab : Int)
    (hprefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm pre
        (.ok
          { contract := contract,
            locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot
              ilkLine ilkDust }
          evm))
    (hInkNeg : 0 ≤ frobDinkInt I ∨
      (frobDinkWord I + urnInk).toNat ≤ urnInk.toNat)
    (hInkPos : frobDinkInt I ≤ 0 ∨
      urnInk.toNat ≤ (frobDinkWord I + urnInk).toNat)
    (hArtNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + urnArt).toNat ≤ urnArt.toNat)
    (hArtPos : frobDartInt I ≤ 0 ∨
      urnArt.toNat ≤ (frobDartWord I + urnArt).toNat)
    (hIlkNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + ilkArt).toNat ≤ ilkArt.toNat)
    (hIlkPos : frobDartInt I ≤ 0 ∨
      ilkArt.toNat ≤ (frobDartWord I + ilkArt).toNat)
    (hdtab : dtab = Int.ofNat ilkRate.toNat * frobDartInt I)
    (hRateMax : UInt256.slt ilkRate ⟨0⟩ = ⟨0⟩)
    (hDtabMul :
      frobDartWord I = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.sdiv (UInt256.mul (frobDartWord I) ilkRate)
            (frobDartWord I)) ilkRate ≠ ⟨0⟩)
    (htabOverflow : UInt256.size ≤ ilkRate.toNat *
      (frobDartWord I + urnArt).toNat) :
    ExecBlock config { contract := contract, locals := frobStore I } evm
      (pre ++
        checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
        checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
        checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
        checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
        checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew"))
      .reverted := by
  let localsLoaded :=
    frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
  let urnInkNew := frobDinkWord I + urnInk
  let urnArtNew := frobDartWord I + urnArt
  let ilkArtNew := frobDartWord I + ilkArt
  let localsIlk :=
    (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
        "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat)))
  have hthree :=
    execFrobLoadedPrefixThreeAdds
      (evm := evm) (I := I) (pre := pre)
      urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust hprefix
      hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
  have hrateGetIlk :
      localsIlk.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)) := by
    change (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
        "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat))).get? "ilkRate" =
        some (.int (Int.ofNat ilkRate.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_rate I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hdartGet : localsIlk.get? "dart" = some (frobDartValue I) := by
    change (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
        "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat))).get? "dart" = some (frobDartValue I)
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_dart I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hdtabRange := frobDtabRangeOfMulGuard (I := I) hRateMax hDtabMul
  have hdtabGuards :=
    evalFrobDtabSourceGuardsTrue
      (evm := evm) (I := I) (locals := localsIlk) (ilkRate := ilkRate)
      (dtab := dtab) hrateGetIlk hdartGet hdtab hRateMax
  have hdtabLo : -((2 : Int) ^ 255) ≤ dtab := by
    rw [hdtab]
    exact hdtabRange.1
  have hdtabHi : dtab < (2 : Int) ^ 255 := by
    rw [hdtab]
    exact hdtabRange.2
  have hdtabBlock :
      ExecBlock config { contract := contract, locals := localsIlk } evm
        (checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart"))
        (.ok
          { contract := contract,
            locals := (localsIlk.insert "dtab" (.int dtab)) }
          evm) :=
    execFrobDtabMulCheckedOk
      (evm := evm) (I := I) localsIlk ilkRate dtab hrateGetIlk hdartGet
      hdtab hdtabLo hdtabHi hdtabGuards.1 hdtabGuards.2
  have hsourceDtab := Reasoning.Refinement.execBlock_append
    (by simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk] using hthree)
    hdtabBlock
  have hrateGetDtab :
      (localsIlk.insert "dtab" (.int dtab)).get? "ilkRate" =
        some (.int (Int.ofNat ilkRate.toNat)) := by
    rw [store_get_ne _ _ (by decide)]
    exact hrateGetIlk
  have hurnArtNewGet :
      (localsIlk.insert "dtab" (.int dtab)).get? "urnArtNew" =
        some (.int (Int.ofNat urnArtNew.toNat)) := by
    change ((((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
        "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).get?
        "urnArtNew" = some (.int (Int.ofNat urnArtNew.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_self]
  have htabBlock :
      ExecBlock config
        { contract := contract, locals := (localsIlk.insert "dtab" (.int dtab)) } evm
        (checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew"))
        .reverted := by
    exact execFrobTabMulCheckedRevertOverflow
      (evm := evm) (locals := localsIlk.insert "dtab" (.int dtab))
      ilkRate urnArtNew hrateGetDtab hurnArtNewGet
      (by simpa [urnArtNew] using htabOverflow)
  have hfull := Reasoning.Refinement.execBlock_append
    (by simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
      List.append_assoc] using hsourceDtab)
    htabBlock
  simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
    List.append_assoc] using hfull
theorem execFrobLoadedPrefixThroughTabOk {evm : EVM.State}
    {I : ExecutionEnv} {pre : List Stmt}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (dtab : Int)
    (hprefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm pre
        (.ok
          { contract := contract,
            locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot
              ilkLine ilkDust }
          evm))
    (hInkNeg : 0 ≤ frobDinkInt I ∨
      (frobDinkWord I + urnInk).toNat ≤ urnInk.toNat)
    (hInkPos : frobDinkInt I ≤ 0 ∨
      urnInk.toNat ≤ (frobDinkWord I + urnInk).toNat)
    (hArtNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + urnArt).toNat ≤ urnArt.toNat)
    (hArtPos : frobDartInt I ≤ 0 ∨
      urnArt.toNat ≤ (frobDartWord I + urnArt).toNat)
    (hIlkNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + ilkArt).toNat ≤ ilkArt.toNat)
    (hIlkPos : frobDartInt I ≤ 0 ∨
      ilkArt.toNat ≤ (frobDartWord I + ilkArt).toNat)
    (hdtab : dtab = Int.ofNat ilkRate.toNat * frobDartInt I)
    (hRateMax : UInt256.slt ilkRate ⟨0⟩ = ⟨0⟩)
    (hDtabMul :
      frobDartWord I = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.sdiv (UInt256.mul (frobDartWord I) ilkRate)
            (frobDartWord I)) ilkRate ≠ ⟨0⟩)
    (hTabMul :
      (frobDartWord I + urnArt) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div (UInt256.mul ilkRate (frobDartWord I + urnArt))
            (frobDartWord I + urnArt)) ilkRate ≠ ⟨0⟩) :
    let localsLoaded :=
      frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
    let urnInkNew := frobDinkWord I + urnInk
    let urnArtNew := frobDartWord I + urnArt
    let ilkArtNew := frobDartWord I + ilkArt
    let localsIlk :=
      (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
          "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat)))
    let localsDtab := localsIlk.insert "dtab" (.int dtab)
    let tab := UInt256.mul ilkRate urnArtNew
    ExecBlock config { contract := contract, locals := frobStore I } evm
      (pre ++
        checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
        checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
        checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
        checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
        checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew"))
      (.ok
        { contract := contract,
          locals := localsDtab.insert "tab" (.int (Int.ofNat tab.toNat)) }
        evm) := by
  intro localsLoaded urnInkNew urnArtNew ilkArtNew localsIlk localsDtab tab
  have hthree :=
    execFrobLoadedPrefixThreeAdds
      (evm := evm) (I := I) (pre := pre)
      urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust hprefix
      hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
  have hrateGetIlk :
      localsIlk.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)) := by
    change (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
        "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat))).get? "ilkRate" =
        some (.int (Int.ofNat ilkRate.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_rate I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hdartGet : localsIlk.get? "dart" = some (frobDartValue I) := by
    change (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
        "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat))).get? "dart" = some (frobDartValue I)
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_dart I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hdtabRange := frobDtabRangeOfMulGuard (I := I) hRateMax hDtabMul
  have hdtabGuards :=
    evalFrobDtabSourceGuardsTrue
      (evm := evm) (I := I) (locals := localsIlk) (ilkRate := ilkRate)
      (dtab := dtab) hrateGetIlk hdartGet hdtab hRateMax
  have hdtabLo : -((2 : Int) ^ 255) ≤ dtab := by
    rw [hdtab]
    exact hdtabRange.1
  have hdtabHi : dtab < (2 : Int) ^ 255 := by
    rw [hdtab]
    exact hdtabRange.2
  have hdtabBlock :
      ExecBlock config { contract := contract, locals := localsIlk } evm
        (checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart"))
        (.ok { contract := contract, locals := localsDtab } evm) := by
    simpa [localsDtab] using
      execFrobDtabMulCheckedOk
        (evm := evm) (I := I) localsIlk ilkRate dtab hrateGetIlk hdartGet
        hdtab hdtabLo hdtabHi hdtabGuards.1 hdtabGuards.2
  have hsourceDtab := Reasoning.Refinement.execBlock_append
    (by simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk] using hthree)
    hdtabBlock
  have hTabMulS :
      urnArtNew = ⟨0⟩ ∨
        UInt256.eq (UInt256.div (UInt256.mul ilkRate urnArtNew) urnArtNew)
          ilkRate ≠ ⟨0⟩ := by
    simpa [urnArtNew] using hTabMul
  have htabFitGuard := uintCheckedMulGuard_to_fit_and_source_guard hTabMulS
  have hrateGetDtab :
      localsDtab.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)) := by
    change (localsIlk.insert "dtab" (.int dtab)).get? "ilkRate" =
      some (.int (Int.ofNat ilkRate.toNat))
    rw [store_get_ne _ _ (by decide)]
    exact hrateGetIlk
  have hurnArtNewGet :
      localsDtab.get? "urnArtNew" = some (.int (Int.ofNat urnArtNew.toNat)) := by
    change ((((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
        "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).get?
        "urnArtNew" = some (.int (Int.ofNat urnArtNew.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_self]
  have htabBlock :
      ExecBlock config { contract := contract, locals := localsDtab } evm
        (checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew"))
        (.ok
          { contract := contract,
            locals := localsDtab.insert "tab" (.int (Int.ofNat tab.toNat)) }
          evm) := by
    exact execFrobTabMulCheckedOk (evm := evm) (locals := localsDtab)
      ilkRate urnArtNew tab hrateGetDtab hurnArtNewGet (by rfl)
      htabFitGuard.1 htabFitGuard.2
  have hfull := Reasoning.Refinement.execBlock_append
    (by simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
      localsDtab, List.append_assoc] using hsourceDtab)
    htabBlock
  simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk, localsDtab,
    tab, List.append_assoc] using hfull

theorem execFrobLoadedPrefixThroughDebtOk {evm : EVM.State}
    {I : ExecutionEnv} {pre : List Stmt}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (dtab : Int) (debtOld debtNew dtabWord : UInt256)
    (hprefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm pre
        (.ok
          { contract := contract,
            locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot
              ilkLine ilkDust }
          evm))
    (hInkNeg : 0 ≤ frobDinkInt I ∨
      (frobDinkWord I + urnInk).toNat ≤ urnInk.toNat)
    (hInkPos : frobDinkInt I ≤ 0 ∨
      urnInk.toNat ≤ (frobDinkWord I + urnInk).toNat)
    (hArtNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + urnArt).toNat ≤ urnArt.toNat)
    (hArtPos : frobDartInt I ≤ 0 ∨
      urnArt.toNat ≤ (frobDartWord I + urnArt).toNat)
    (hIlkNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + ilkArt).toNat ≤ ilkArt.toNat)
    (hIlkPos : frobDartInt I ≤ 0 ∨
      ilkArt.toNat ≤ (frobDartWord I + ilkArt).toNat)
    (hdtab : dtab = Int.ofNat ilkRate.toNat * frobDartInt I)
    (hRateMax : UInt256.slt ilkRate ⟨0⟩ = ⟨0⟩)
    (hDtabMul :
      frobDartWord I = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.sdiv (UInt256.mul (frobDartWord I) ilkRate)
            (frobDartWord I)) ilkRate ≠ ⟨0⟩)
    (hTabMul :
      (frobDartWord I + urnArt) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div (UInt256.mul ilkRate (frobDartWord I + urnArt))
            (frobDartWord I + urnArt)) ilkRate ≠ ⟨0⟩)
    (hdebtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner foldDebtSlot = debtOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : debtNew = dtabWord + debtOld)
    (hDebtNeg :
      UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨ UInt256.gt debtNew debtOld = ⟨0⟩)
    (hDebtPos :
      UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨ UInt256.lt debtNew debtOld = ⟨0⟩) :
    let localsLoaded :=
      frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
    let urnInkNew := frobDinkWord I + urnInk
    let urnArtNew := frobDartWord I + urnArt
    let ilkArtNew := frobDartWord I + ilkArt
    let localsIlk :=
      (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
          "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat)))
    let localsDtab := localsIlk.insert "dtab" (.int dtab)
    let tab := UInt256.mul ilkRate urnArtNew
    let localsTab := localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))
    ExecBlock config { contract := contract, locals := frobStore I } evm
      (pre ++
        checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
        checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
        checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
        checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
        checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
        checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
        [ .assign .storage debtRef (.var "debtNew") ])
      (.ok
        { contract := contract,
          locals := localsTab.insert "debtNew" (.int (Int.ofNat debtNew.toNat)) }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner foldDebtSlot
          debtNew)) := by
  intro localsLoaded urnInkNew urnArtNew ilkArtNew localsIlk localsDtab tab localsTab
  have hsourceTab :=
    execFrobLoadedPrefixThroughTabOk
      (evm := evm) (I := I) (pre := pre)
      urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust dtab hprefix
      hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos hdtab hRateMax hDtabMul
      hTabMul
  have hdtabRange := frobDtabRangeOfMulGuard (I := I) hRateMax hDtabMul
  have hdtabLo : -((2 : Int) ^ 255) ≤ dtab := by
    rw [hdtab]
    exact hdtabRange.1
  have hdtabHi : dtab < (2 : Int) ^ 255 := by
    rw [hdtab]
    exact hdtabRange.2
  have hbaseDebt : localsTab.get? "debt" = none := by
    change (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).get?
      "debt" = none
    rw [store_get_ne _ _ (by decide)]
    change (localsIlk.insert "dtab" (.int dtab)).get? "debt" = none
    rw [store_get_ne _ _ (by decide)]
    change (((localsLoaded.insert "urnInkNew"
      (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
      (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat))).get? "debt" = none
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simp [localsLoaded, frobStoreIlkDust, frobStore]
  have hdtabGet : localsTab.get? "dtab" = some (.int dtab) := by
    change (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).get? "dtab" =
      some (.int dtab)
    rw [store_get_ne _ _ (by decide)]
    simp [localsDtab]
  have hdebtBlock :
      ExecBlock config { contract := contract, locals := localsTab } evm
        (checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
          [ .assign .storage debtRef (.var "debtNew") ])
        (.ok
          { contract := contract,
            locals := localsTab.insert "debtNew" (.int (Int.ofNat debtNew.toNat)) }
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner foldDebtSlot
            debtNew)) := by
    exact execFrobDebtAddStoreOk
      (evm := evm) (locals := localsTab)
      debtOld debtNew dtabWord dtab hbaseDebt hdtabGet hdebtLoad hdtabMod hnew
      (signedAddGuardNegCond_of_word hdtabLo hdtabHi hdtabMod hDebtNeg)
      (signedAddGuardPosCond_of_word hdtabLo hdtabHi hdtabMod hDebtPos)
  have hfull := Reasoning.Refinement.execBlock_append
    (by simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
      localsDtab, tab, localsTab, List.append_assoc] using hsourceTab)
    hdebtBlock
  simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk, localsDtab,
    tab, localsTab, List.append_assoc] using hfull

theorem execFrobLoadedPrefixDebtAddRevertGuardNeg {evm : EVM.State}
    {I : ExecutionEnv} {pre : List Stmt}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (dtab : Int) (debtOld debtNew dtabWord : UInt256)
    (hprefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm pre
        (.ok
          { contract := contract,
            locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot
              ilkLine ilkDust }
          evm))
    (hInkNeg : 0 ≤ frobDinkInt I ∨
      (frobDinkWord I + urnInk).toNat ≤ urnInk.toNat)
    (hInkPos : frobDinkInt I ≤ 0 ∨
      urnInk.toNat ≤ (frobDinkWord I + urnInk).toNat)
    (hArtNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + urnArt).toNat ≤ urnArt.toNat)
    (hArtPos : frobDartInt I ≤ 0 ∨
      urnArt.toNat ≤ (frobDartWord I + urnArt).toNat)
    (hIlkNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + ilkArt).toNat ≤ ilkArt.toNat)
    (hIlkPos : frobDartInt I ≤ 0 ∨
      ilkArt.toNat ≤ (frobDartWord I + ilkArt).toNat)
    (hdtab : dtab = Int.ofNat ilkRate.toNat * frobDartInt I)
    (hRateMax : UInt256.slt ilkRate ⟨0⟩ = ⟨0⟩)
    (hDtabMul :
      frobDartWord I = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.sdiv (UInt256.mul (frobDartWord I) ilkRate)
            (frobDartWord I)) ilkRate ≠ ⟨0⟩)
    (hTabMul :
      (frobDartWord I + urnArt) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div (UInt256.mul ilkRate (frobDartWord I + urnArt))
            (frobDartWord I + urnArt)) ilkRate ≠ ⟨0⟩)
    (hdebtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner foldDebtSlot = debtOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : debtNew = dtabWord + debtOld)
    (hDebtNegFail :
      ¬ (UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨ UInt256.gt debtNew debtOld = ⟨0⟩)) :
    ExecBlock config { contract := contract, locals := frobStore I } evm
      (pre ++
        checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
        checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
        checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
        checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
        checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
        checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab"))
      .reverted := by
  let localsLoaded :=
    frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
  let urnInkNew := frobDinkWord I + urnInk
  let urnArtNew := frobDartWord I + urnArt
  let ilkArtNew := frobDartWord I + ilkArt
  let localsIlk :=
    (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
        "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat)))
  let localsDtab := localsIlk.insert "dtab" (.int dtab)
  let tab := UInt256.mul ilkRate urnArtNew
  let localsTab := localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))
  have hsourceTab :=
    execFrobLoadedPrefixThroughTabOk
      (evm := evm) (I := I) (pre := pre)
      urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust dtab hprefix
      hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos hdtab hRateMax hDtabMul
      hTabMul
  have hdtabRange := frobDtabRangeOfMulGuard (I := I) hRateMax hDtabMul
  have hdtabLo : -((2 : Int) ^ 255) ≤ dtab := by
    rw [hdtab]
    exact hdtabRange.1
  have hdtabHi : dtab < (2 : Int) ^ 255 := by
    rw [hdtab]
    exact hdtabRange.2
  have hbaseDebt : localsTab.get? "debt" = none := by
    change (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).get?
      "debt" = none
    rw [store_get_ne _ _ (by decide)]
    change (localsIlk.insert "dtab" (.int dtab)).get? "debt" = none
    rw [store_get_ne _ _ (by decide)]
    change (((localsLoaded.insert "urnInkNew"
      (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
      (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat))).get? "debt" = none
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simp [localsLoaded, frobStoreIlkDust, frobStore]
  have hdtabGet : localsTab.get? "dtab" = some (.int dtab) := by
    change (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).get? "dtab" =
      some (.int dtab)
    rw [store_get_ne _ _ (by decide)]
    simp [localsDtab]
  have hdebtBlock :
      ExecBlock config { contract := contract, locals := localsTab } evm
        (checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab"))
        .reverted := by
    exact execFrobDebtAddCheckedRevertGuardNeg
      (evm := evm) (locals := localsTab)
      debtOld debtNew dtabWord dtab hbaseDebt hdtabGet hdebtLoad hdtabMod hnew
      (signedAddGuardNegFalseCond_of_word hdtabLo hdtabHi hdtabMod
        hDebtNegFail)
  have hfull := Reasoning.Refinement.execBlock_append
    (by simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
      localsDtab, tab, localsTab, List.append_assoc] using hsourceTab)
    hdebtBlock
  simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk, localsDtab,
    tab, localsTab, List.append_assoc] using hfull

theorem execFrobLoadedPrefixDebtAddRevertGuardPos {evm : EVM.State}
    {I : ExecutionEnv} {pre : List Stmt}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (dtab : Int) (debtOld debtNew dtabWord : UInt256)
    (hprefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm pre
        (.ok
          { contract := contract,
            locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot
              ilkLine ilkDust }
          evm))
    (hInkNeg : 0 ≤ frobDinkInt I ∨
      (frobDinkWord I + urnInk).toNat ≤ urnInk.toNat)
    (hInkPos : frobDinkInt I ≤ 0 ∨
      urnInk.toNat ≤ (frobDinkWord I + urnInk).toNat)
    (hArtNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + urnArt).toNat ≤ urnArt.toNat)
    (hArtPos : frobDartInt I ≤ 0 ∨
      urnArt.toNat ≤ (frobDartWord I + urnArt).toNat)
    (hIlkNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + ilkArt).toNat ≤ ilkArt.toNat)
    (hIlkPos : frobDartInt I ≤ 0 ∨
      ilkArt.toNat ≤ (frobDartWord I + ilkArt).toNat)
    (hdtab : dtab = Int.ofNat ilkRate.toNat * frobDartInt I)
    (hRateMax : UInt256.slt ilkRate ⟨0⟩ = ⟨0⟩)
    (hDtabMul :
      frobDartWord I = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.sdiv (UInt256.mul (frobDartWord I) ilkRate)
            (frobDartWord I)) ilkRate ≠ ⟨0⟩)
    (hTabMul :
      (frobDartWord I + urnArt) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div (UInt256.mul ilkRate (frobDartWord I + urnArt))
            (frobDartWord I + urnArt)) ilkRate ≠ ⟨0⟩)
    (hdebtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner foldDebtSlot = debtOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : debtNew = dtabWord + debtOld)
    (hDebtNeg :
      UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨ UInt256.gt debtNew debtOld = ⟨0⟩)
    (hDebtPosFail :
      ¬ (UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨ UInt256.lt debtNew debtOld = ⟨0⟩)) :
    ExecBlock config { contract := contract, locals := frobStore I } evm
      (pre ++
        checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
        checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
        checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
        checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
        checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
        checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab"))
      .reverted := by
  let localsLoaded :=
    frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
  let urnInkNew := frobDinkWord I + urnInk
  let urnArtNew := frobDartWord I + urnArt
  let ilkArtNew := frobDartWord I + ilkArt
  let localsIlk :=
    (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
        "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat)))
  let localsDtab := localsIlk.insert "dtab" (.int dtab)
  let tab := UInt256.mul ilkRate urnArtNew
  let localsTab := localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))
  have hsourceTab :=
    execFrobLoadedPrefixThroughTabOk
      (evm := evm) (I := I) (pre := pre)
      urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust dtab hprefix
      hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos hdtab hRateMax hDtabMul
      hTabMul
  have hdtabRange := frobDtabRangeOfMulGuard (I := I) hRateMax hDtabMul
  have hdtabLo : -((2 : Int) ^ 255) ≤ dtab := by
    rw [hdtab]
    exact hdtabRange.1
  have hdtabHi : dtab < (2 : Int) ^ 255 := by
    rw [hdtab]
    exact hdtabRange.2
  have hbaseDebt : localsTab.get? "debt" = none := by
    change (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).get?
      "debt" = none
    rw [store_get_ne _ _ (by decide)]
    change (localsIlk.insert "dtab" (.int dtab)).get? "debt" = none
    rw [store_get_ne _ _ (by decide)]
    change (((localsLoaded.insert "urnInkNew"
      (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
      (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat))).get? "debt" = none
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simp [localsLoaded, frobStoreIlkDust, frobStore]
  have hdtabGet : localsTab.get? "dtab" = some (.int dtab) := by
    change (localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))).get? "dtab" =
      some (.int dtab)
    rw [store_get_ne _ _ (by decide)]
    simp [localsDtab]
  have hdebtBlock :
      ExecBlock config { contract := contract, locals := localsTab } evm
        (checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab"))
        .reverted := by
    exact execFrobDebtAddCheckedRevertGuardPos
      (evm := evm) (locals := localsTab)
      debtOld debtNew dtabWord dtab hbaseDebt hdtabGet hdebtLoad hdtabMod hnew
      (signedAddGuardNegCond_of_word hdtabLo hdtabHi hdtabMod hDebtNeg)
      (signedAddGuardPosFalseCond_of_word hdtabLo hdtabHi hdtabMod
        hDebtPosFail)
  have hfull := Reasoning.Refinement.execBlock_append
    (by simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
      localsDtab, tab, localsTab, List.append_assoc] using hsourceTab)
    hdebtBlock
  simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk, localsDtab,
    tab, localsTab, List.append_assoc] using hfull

theorem execFrobLoadedPrefixThroughSafetyOk {evm : EVM.State}
    {I : ExecutionEnv} {pre : List Stmt}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (dtab : Int) (debtOld debtNew dtabWord Line : UInt256)
    (hprefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm pre
        (.ok
          { contract := contract,
            locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot
              ilkLine ilkDust }
          evm))
    (hInkNeg : 0 ≤ frobDinkInt I ∨
      (frobDinkWord I + urnInk).toNat ≤ urnInk.toNat)
    (hInkPos : frobDinkInt I ≤ 0 ∨
      urnInk.toNat ≤ (frobDinkWord I + urnInk).toNat)
    (hArtNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + urnArt).toNat ≤ urnArt.toNat)
    (hArtPos : frobDartInt I ≤ 0 ∨
      urnArt.toNat ≤ (frobDartWord I + urnArt).toNat)
    (hIlkNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + ilkArt).toNat ≤ ilkArt.toNat)
    (hIlkPos : frobDartInt I ≤ 0 ∨
      ilkArt.toNat ≤ (frobDartWord I + ilkArt).toNat)
    (hdtab : dtab = Int.ofNat ilkRate.toNat * frobDartInt I)
    (hRateMax : UInt256.slt ilkRate ⟨0⟩ = ⟨0⟩)
    (hDtabMul :
      frobDartWord I = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.sdiv (UInt256.mul (frobDartWord I) ilkRate)
            (frobDartWord I)) ilkRate ≠ ⟨0⟩)
    (hTabMul :
      (frobDartWord I + urnArt) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div (UInt256.mul ilkRate (frobDartWord I + urnArt))
            (frobDartWord I + urnArt)) ilkRate ≠ ⟨0⟩)
    (hdebtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner foldDebtSlot = debtOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : debtNew = dtabWord + debtOld)
    (hDebtNeg :
      UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨ UInt256.gt debtNew debtOld = ⟨0⟩)
    (hDebtPos :
      UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨ UInt256.lt debtNew debtOld = ⟨0⟩)
    (hlineLoad :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner foldDebtSlot debtNew)
          evm.executionEnv.codeOwner ⟨9⟩ =
        Line)
    (hCeilingMul :
      ilkRate = ⟨0⟩ ∨
        UInt256.eq (UInt256.div
          (UInt256.mul (frobDartWord I + ilkArt) ilkRate) ilkRate)
          (frobDartWord I + ilkArt) ≠ ⟨0⟩)
    (hCeilingReq :
      frobDartInt I ≤ 0 ∨
        ((UInt256.mul (frobDartWord I + ilkArt) ilkRate).toNat ≤
            ilkLine.toNat ∧
          debtNew.toNat ≤ Line.toNat))
    (hInkMul :
      ilkSpot = ⟨0⟩ ∨
        UInt256.eq (UInt256.div
          (UInt256.mul (frobDinkWord I + urnInk) ilkSpot) ilkSpot)
          (frobDinkWord I + urnInk) ≠ ⟨0⟩)
    (hSafetyReq :
      (frobDartInt I ≤ 0 ∧ 0 ≤ frobDinkInt I) ∨
        (UInt256.mul ilkRate (frobDartWord I + urnArt)).toNat ≤
          (UInt256.mul (frobDinkWord I + urnInk) ilkSpot).toNat) :
    let localsLoaded :=
      frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
    let urnInkNew := frobDinkWord I + urnInk
    let urnArtNew := frobDartWord I + urnArt
    let ilkArtNew := frobDartWord I + ilkArt
    let localsIlk :=
      (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
          "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat)))
    let localsDtab := localsIlk.insert "dtab" (.int dtab)
    let tab := UInt256.mul ilkRate urnArtNew
    let localsTab := localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))
    let localsDebt := localsTab.insert "debtNew" (.int (Int.ofNat debtNew.toNat))
    let evmDebt :=
      Solm.EVM.storageStore evm evm.executionEnv.codeOwner foldDebtSlot debtNew
    let ceilingDebt := UInt256.mul ilkArtNew ilkRate
    let inkSpot := UInt256.mul urnInkNew ilkSpot
    ExecBlock config { contract := contract, locals := frobStore I } evm
      (pre ++
        checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
        checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
        checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
        checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
        checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
        checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
        [ .assign .storage debtRef (.var "debtNew") ] ++
        checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
        checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
        [ .require
            (eitherExpr
              (.binary .le (.var "dart") (.intLit 0))
              (bothExpr
                (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                (.binary .le (.var "debtNew") (.storage LineRef)))),
          .require
            (eitherExpr
              (bothExpr
                (.binary .le (.var "dart") (.intLit 0))
                (.binary .ge (.var "dink") (.intLit 0)))
              (.binary .le (.var "tab") (.var "inkSpot"))) ])
      (.ok
        { contract := contract,
          locals :=
            (localsDebt.insert "ceilingDebt"
              (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
              (.int (Int.ofNat inkSpot.toNat)) }
        evmDebt) := by
  intro localsLoaded urnInkNew urnArtNew ilkArtNew localsIlk localsDtab tab
    localsTab localsDebt evmDebt ceilingDebt inkSpot
  have hsourceDebt :=
    execFrobLoadedPrefixThroughDebtOk
      (evm := evm) (I := I) (pre := pre)
      urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust dtab debtOld debtNew
      dtabWord hprefix hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos hdtab
      hRateMax hDtabMul hTabMul hdebtLoad hdtabMod hnew hDebtNeg hDebtPos
  have hCeilingFitGuard :=
    uintCheckedMulGuard_to_fit_and_source_guard hCeilingMul
  have hInkFitGuard :=
    uintCheckedMulGuard_to_fit_and_source_guard hInkMul
  have hlocalsDebtIlkArtNew :
      localsDebt.get? "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "ilkArtNew" =
          some (.int (Int.ofNat ilkArtNew.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_self]
  have hlocalsDebtRate :
      localsDebt.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "ilkRate" =
          some (.int (Int.ofNat ilkRate.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_rate I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hlocalsDebtUrnInkNew :
      localsDebt.get? "urnInkNew" = some (.int (Int.ofNat urnInkNew.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "urnInkNew" =
          some (.int (Int.ofNat urnInkNew.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_self]
  have hlocalsDebtSpot :
      localsDebt.get? "ilkSpot" = some (.int (Int.ofNat ilkSpot.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "ilkSpot" =
          some (.int (Int.ofNat ilkSpot.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_spot I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hlocalsDebtDart : localsDebt.get? "dart" = some (frobDartValue I) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "dart" = some (frobDartValue I)
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_dart I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hlocalsDebtDink : localsDebt.get? "dink" = some (frobDinkValue I) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "dink" = some (frobDinkValue I)
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_dink I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hlocalsDebtLine :
      localsDebt.get? "ilkLine" = some (.int (Int.ofNat ilkLine.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "ilkLine" =
          some (.int (Int.ofNat ilkLine.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_line I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hlocalsDebtDebtNew :
      localsDebt.get? "debtNew" = some (.int (Int.ofNat debtNew.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "debtNew" =
          some (.int (Int.ofNat debtNew.toNat))
    rw [store_get_self]
  have hlocalsDebtTab :
      localsDebt.get? "tab" = some (.int (Int.ofNat tab.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "tab" =
          some (.int (Int.ofNat tab.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_self]
  have hlocalsDebtLineBase : localsDebt.get? "Line" = none := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "Line" = none
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simp [localsLoaded, frobStoreIlkDust, frobStore]
  have hlineLoadDebt :
      Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner ⟨9⟩ = Line := by
    simpa [evmDebt, storageStore_executionEnv] using hlineLoad
  have hceilingReqEval :
      evalExpr? config
        { contract := contract,
          locals :=
            (localsDebt.insert "ceilingDebt"
              (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
              (.int (Int.ofNat inkSpot.toNat)) }
        evmDebt
        (eitherExpr
          (.binary .le (.var "dart") (.intLit 0))
          (bothExpr
            (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
            (.binary .le (.var "debtNew") (.storage LineRef)))) =
        .ok (.bool true) := by
    exact evalExpr_frob_ceiling_req_true
      (evm := evmDebt) (I := I)
      (ceilingDebt := ceilingDebt) (ilkLine := ilkLine)
      (debtNew := debtNew) (Line := Line)
      (by
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        exact hlocalsDebtDart)
      (by
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_self])
      (by
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        exact hlocalsDebtLine)
      (by
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        exact hlocalsDebtDebtNew)
      (by
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        exact hlocalsDebtLineBase)
      hlineLoadDebt
      (by simpa [ceilingDebt, ilkArtNew] using hCeilingReq)
  have hsafetyReqEval :
      evalExpr? config
        { contract := contract,
          locals :=
            (localsDebt.insert "ceilingDebt"
              (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
              (.int (Int.ofNat inkSpot.toNat)) }
        evmDebt
        (eitherExpr
          (bothExpr
            (.binary .le (.var "dart") (.intLit 0))
            (.binary .ge (.var "dink") (.intLit 0)))
          (.binary .le (.var "tab") (.var "inkSpot"))) =
        .ok (.bool true) := by
    exact evalExpr_frob_safety_req_true
      (evm := evmDebt) (I := I) (tab := tab) (inkSpot := inkSpot)
      (by
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        exact hlocalsDebtDart)
      (by
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        exact hlocalsDebtDink)
      (by
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        exact hlocalsDebtTab)
      (by
        rw [store_get_self])
      (by simpa [tab, inkSpot, urnInkNew, urnArtNew] using hSafetyReq)
  have hsafeBlock :
      ExecBlock config { contract := contract, locals := localsDebt } evmDebt
        (checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
          [ .require
              (eitherExpr
                (.binary .le (.var "dart") (.intLit 0))
                (bothExpr
                  (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                  (.binary .le (.var "debtNew") (.storage LineRef)))),
            .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (.binary .le (.var "tab") (.var "inkSpot"))) ])
        (.ok
          { contract := contract,
            locals :=
              (localsDebt.insert "ceilingDebt"
                (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
                (.int (Int.ofNat inkSpot.toNat)) }
          evmDebt) := by
    exact execFrobCeilingSafetyOk
      (evm := evmDebt) (locals := localsDebt)
      ilkArtNew ilkRate ceilingDebt urnInkNew ilkSpot inkSpot
      hlocalsDebtIlkArtNew hlocalsDebtRate hlocalsDebtUrnInkNew hlocalsDebtSpot
      (by rfl) hCeilingFitGuard.1 hCeilingFitGuard.2
      (by rfl) hInkFitGuard.1 hInkFitGuard.2
      hceilingReqEval hsafetyReqEval
  have hfull := Reasoning.Refinement.execBlock_append
    (by simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
      localsDtab, tab, localsTab, localsDebt, evmDebt, List.append_assoc]
      using hsourceDebt)
    hsafeBlock
  simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk, localsDtab,
    tab, localsTab, localsDebt, evmDebt, ceilingDebt, inkSpot, List.append_assoc]
    using hfull

theorem execFrobLoadedPrefixCeilingMulRevertOverflow {evm : EVM.State}
    {I : ExecutionEnv} {pre : List Stmt}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (dtab : Int) (debtOld debtNew dtabWord : UInt256)
    (hprefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm pre
        (.ok
          { contract := contract,
            locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot
              ilkLine ilkDust }
          evm))
    (hInkNeg : 0 ≤ frobDinkInt I ∨
      (frobDinkWord I + urnInk).toNat ≤ urnInk.toNat)
    (hInkPos : frobDinkInt I ≤ 0 ∨
      urnInk.toNat ≤ (frobDinkWord I + urnInk).toNat)
    (hArtNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + urnArt).toNat ≤ urnArt.toNat)
    (hArtPos : frobDartInt I ≤ 0 ∨
      urnArt.toNat ≤ (frobDartWord I + urnArt).toNat)
    (hIlkNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + ilkArt).toNat ≤ ilkArt.toNat)
    (hIlkPos : frobDartInt I ≤ 0 ∨
      ilkArt.toNat ≤ (frobDartWord I + ilkArt).toNat)
    (hdtab : dtab = Int.ofNat ilkRate.toNat * frobDartInt I)
    (hRateMax : UInt256.slt ilkRate ⟨0⟩ = ⟨0⟩)
    (hDtabMul :
      frobDartWord I = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.sdiv (UInt256.mul (frobDartWord I) ilkRate)
            (frobDartWord I)) ilkRate ≠ ⟨0⟩)
    (hTabMul :
      (frobDartWord I + urnArt) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div (UInt256.mul ilkRate (frobDartWord I + urnArt))
            (frobDartWord I + urnArt)) ilkRate ≠ ⟨0⟩)
    (hdebtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner foldDebtSlot = debtOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : debtNew = dtabWord + debtOld)
    (hDebtNeg :
      UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨ UInt256.gt debtNew debtOld = ⟨0⟩)
    (hDebtPos :
      UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨ UInt256.lt debtNew debtOld = ⟨0⟩)
    (hover :
      UInt256.size ≤ (frobDartWord I + ilkArt).toNat * ilkRate.toNat) :
    ExecBlock config { contract := contract, locals := frobStore I } evm
      (pre ++
        checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
        checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
        checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
        checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
        checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
        checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
        [ .assign .storage debtRef (.var "debtNew") ] ++
        checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate"))
      .reverted := by
  let localsLoaded :=
    frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
  let urnInkNew := frobDinkWord I + urnInk
  let urnArtNew := frobDartWord I + urnArt
  let ilkArtNew := frobDartWord I + ilkArt
  let localsIlk :=
    (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
        "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat)))
  let localsDtab := localsIlk.insert "dtab" (.int dtab)
  let tab := UInt256.mul ilkRate urnArtNew
  let localsTab := localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))
  let localsDebt := localsTab.insert "debtNew" (.int (Int.ofNat debtNew.toNat))
  let evmDebt :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner foldDebtSlot debtNew
  have hsourceDebt :=
    execFrobLoadedPrefixThroughDebtOk
      (evm := evm) (I := I) (pre := pre)
      urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust dtab debtOld debtNew
      dtabWord hprefix hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos hdtab
      hRateMax hDtabMul hTabMul hdebtLoad hdtabMod hnew hDebtNeg hDebtPos
  have hlocalsDebtIlkArtNew :
      localsDebt.get? "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "ilkArtNew" =
          some (.int (Int.ofNat ilkArtNew.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_self]
  have hlocalsDebtRate :
      localsDebt.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "ilkRate" =
          some (.int (Int.ofNat ilkRate.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_rate I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hceilBlock :
      ExecBlock config { contract := contract, locals := localsDebt } evmDebt
        (checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate"))
        .reverted := by
    exact execFrobCeilingDebtCheckedRevertOverflow
      (evm := evmDebt) (locals := localsDebt)
      ilkArtNew ilkRate hlocalsDebtIlkArtNew hlocalsDebtRate
      (by simpa [ilkArtNew] using hover)
  have hfull := Reasoning.Refinement.execBlock_append
    (by simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
      localsDtab, tab, localsTab, localsDebt, evmDebt, List.append_assoc]
      using hsourceDebt)
    hceilBlock
  simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk, localsDtab,
    tab, localsTab, localsDebt, evmDebt, List.append_assoc] using hfull

theorem execFrobLoadedPrefixInkSpotMulRevertOverflow {evm : EVM.State}
    {I : ExecutionEnv} {pre : List Stmt}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (dtab : Int) (debtOld debtNew dtabWord : UInt256)
    (hprefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm pre
        (.ok
          { contract := contract,
            locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot
              ilkLine ilkDust }
          evm))
    (hInkNeg : 0 ≤ frobDinkInt I ∨
      (frobDinkWord I + urnInk).toNat ≤ urnInk.toNat)
    (hInkPos : frobDinkInt I ≤ 0 ∨
      urnInk.toNat ≤ (frobDinkWord I + urnInk).toNat)
    (hArtNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + urnArt).toNat ≤ urnArt.toNat)
    (hArtPos : frobDartInt I ≤ 0 ∨
      urnArt.toNat ≤ (frobDartWord I + urnArt).toNat)
    (hIlkNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + ilkArt).toNat ≤ ilkArt.toNat)
    (hIlkPos : frobDartInt I ≤ 0 ∨
      ilkArt.toNat ≤ (frobDartWord I + ilkArt).toNat)
    (hdtab : dtab = Int.ofNat ilkRate.toNat * frobDartInt I)
    (hRateMax : UInt256.slt ilkRate ⟨0⟩ = ⟨0⟩)
    (hDtabMul :
      frobDartWord I = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.sdiv (UInt256.mul (frobDartWord I) ilkRate)
            (frobDartWord I)) ilkRate ≠ ⟨0⟩)
    (hTabMul :
      (frobDartWord I + urnArt) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div (UInt256.mul ilkRate (frobDartWord I + urnArt))
            (frobDartWord I + urnArt)) ilkRate ≠ ⟨0⟩)
    (hdebtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner foldDebtSlot = debtOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : debtNew = dtabWord + debtOld)
    (hDebtNeg :
      UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨ UInt256.gt debtNew debtOld = ⟨0⟩)
    (hDebtPos :
      UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨ UInt256.lt debtNew debtOld = ⟨0⟩)
    (hCeilingMul :
      ilkRate = ⟨0⟩ ∨
        UInt256.eq (UInt256.div
          (UInt256.mul (frobDartWord I + ilkArt) ilkRate) ilkRate)
          (frobDartWord I + ilkArt) ≠ ⟨0⟩)
    (hover :
      UInt256.size ≤ (frobDinkWord I + urnInk).toNat * ilkSpot.toNat) :
    ExecBlock config { contract := contract, locals := frobStore I } evm
      (pre ++
        checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
        checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
        checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
        checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
        checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
        checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
        [ .assign .storage debtRef (.var "debtNew") ] ++
        checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
        checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot"))
      .reverted := by
  let localsLoaded :=
    frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
  let urnInkNew := frobDinkWord I + urnInk
  let urnArtNew := frobDartWord I + urnArt
  let ilkArtNew := frobDartWord I + ilkArt
  let localsIlk :=
    (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
        "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat)))
  let localsDtab := localsIlk.insert "dtab" (.int dtab)
  let tab := UInt256.mul ilkRate urnArtNew
  let localsTab := localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))
  let localsDebt := localsTab.insert "debtNew" (.int (Int.ofNat debtNew.toNat))
  let evmDebt :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner foldDebtSlot debtNew
  let ceilingDebt := UInt256.mul ilkArtNew ilkRate
  have hsourceDebt :=
    execFrobLoadedPrefixThroughDebtOk
      (evm := evm) (I := I) (pre := pre)
      urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust dtab debtOld debtNew
      dtabWord hprefix hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos hdtab
      hRateMax hDtabMul hTabMul hdebtLoad hdtabMod hnew hDebtNeg hDebtPos
  have hCeilingFitGuard :=
    uintCheckedMulGuard_to_fit_and_source_guard hCeilingMul
  have hlocalsDebtIlkArtNew :
      localsDebt.get? "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "ilkArtNew" =
          some (.int (Int.ofNat ilkArtNew.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_self]
  have hlocalsDebtRate :
      localsDebt.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "ilkRate" =
          some (.int (Int.ofNat ilkRate.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_rate I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hlocalsDebtUrnInkNew :
      localsDebt.get? "urnInkNew" = some (.int (Int.ofNat urnInkNew.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "urnInkNew" =
          some (.int (Int.ofNat urnInkNew.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_self]
  have hlocalsDebtSpot :
      localsDebt.get? "ilkSpot" = some (.int (Int.ofNat ilkSpot.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "ilkSpot" =
          some (.int (Int.ofNat ilkSpot.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_spot I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hceilBlock :
      ExecBlock config { contract := contract, locals := localsDebt } evmDebt
        (checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate"))
        (.ok
          { contract := contract,
            locals := localsDebt.insert "ceilingDebt"
              (.int (Int.ofNat ceilingDebt.toNat)) }
          evmDebt) := by
    exact execFrobCeilingDebtCheckedOk
      (evm := evmDebt) (locals := localsDebt)
      ilkArtNew ilkRate ceilingDebt hlocalsDebtIlkArtNew hlocalsDebtRate
      (by rfl) hCeilingFitGuard.1 hCeilingFitGuard.2
  have hinkBlock :
      ExecBlock config
        { contract := contract,
          locals := localsDebt.insert "ceilingDebt"
            (.int (Int.ofNat ceilingDebt.toNat)) }
        evmDebt
        (checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot"))
        .reverted := by
    exact execFrobInkSpotCheckedRevertOverflow
      (evm := evmDebt)
      (locals := localsDebt.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat)))
      urnInkNew ilkSpot
      (by
        rw [store_get_ne _ _ (by decide)]
        exact hlocalsDebtUrnInkNew)
      (by
        rw [store_get_ne _ _ (by decide)]
        exact hlocalsDebtSpot)
      (by simpa [urnInkNew] using hover)
  have hmulRevert := Reasoning.Refinement.execBlock_append hceilBlock hinkBlock
  have hfull := Reasoning.Refinement.execBlock_append
    (by simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
      localsDtab, tab, localsTab, localsDebt, evmDebt, List.append_assoc]
      using hsourceDebt)
    (by simpa [localsDebt, evmDebt, ceilingDebt, List.append_assoc]
      using hmulRevert)
  simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk, localsDtab,
    tab, localsTab, localsDebt, evmDebt, ceilingDebt, List.append_assoc] using hfull

theorem execFrobLoadedPrefixCeilingRequireRevert {evm : EVM.State}
    {I : ExecutionEnv} {pre : List Stmt}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (dtab : Int) (debtOld debtNew dtabWord Line : UInt256)
    (hprefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm pre
        (.ok
          { contract := contract,
            locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot
              ilkLine ilkDust }
          evm))
    (hInkNeg : 0 ≤ frobDinkInt I ∨
      (frobDinkWord I + urnInk).toNat ≤ urnInk.toNat)
    (hInkPos : frobDinkInt I ≤ 0 ∨
      urnInk.toNat ≤ (frobDinkWord I + urnInk).toNat)
    (hArtNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + urnArt).toNat ≤ urnArt.toNat)
    (hArtPos : frobDartInt I ≤ 0 ∨
      urnArt.toNat ≤ (frobDartWord I + urnArt).toNat)
    (hIlkNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + ilkArt).toNat ≤ ilkArt.toNat)
    (hIlkPos : frobDartInt I ≤ 0 ∨
      ilkArt.toNat ≤ (frobDartWord I + ilkArt).toNat)
    (hdtab : dtab = Int.ofNat ilkRate.toNat * frobDartInt I)
    (hRateMax : UInt256.slt ilkRate ⟨0⟩ = ⟨0⟩)
    (hDtabMul :
      frobDartWord I = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.sdiv (UInt256.mul (frobDartWord I) ilkRate)
            (frobDartWord I)) ilkRate ≠ ⟨0⟩)
    (hTabMul :
      (frobDartWord I + urnArt) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div (UInt256.mul ilkRate (frobDartWord I + urnArt))
            (frobDartWord I + urnArt)) ilkRate ≠ ⟨0⟩)
    (hdebtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner foldDebtSlot = debtOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : debtNew = dtabWord + debtOld)
    (hDebtNeg :
      UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨ UInt256.gt debtNew debtOld = ⟨0⟩)
    (hDebtPos :
      UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨ UInt256.lt debtNew debtOld = ⟨0⟩)
    (hlineLoad :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner foldDebtSlot debtNew)
          evm.executionEnv.codeOwner ⟨9⟩ =
        Line)
    (hCeilingMul :
      ilkRate = ⟨0⟩ ∨
        UInt256.eq (UInt256.div
          (UInt256.mul (frobDartWord I + ilkArt) ilkRate) ilkRate)
          (frobDartWord I + ilkArt) ≠ ⟨0⟩)
    (hInkMul :
      ilkSpot = ⟨0⟩ ∨
        UInt256.eq (UInt256.div
          (UInt256.mul (frobDinkWord I + urnInk) ilkSpot) ilkSpot)
          (frobDinkWord I + urnInk) ≠ ⟨0⟩)
    (hCeilingBad :
      0 < frobDartInt I ∧
        ¬ ((UInt256.mul (frobDartWord I + ilkArt) ilkRate).toNat ≤
              ilkLine.toNat ∧
            debtNew.toNat ≤ Line.toNat)) :
    ExecBlock config { contract := contract, locals := frobStore I } evm
      (pre ++
        checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
        checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
        checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
        checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
        checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
        checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
        [ .assign .storage debtRef (.var "debtNew") ] ++
        checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
        checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
        [ .require
            (eitherExpr
              (.binary .le (.var "dart") (.intLit 0))
              (bothExpr
                (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                (.binary .le (.var "debtNew") (.storage LineRef)))) ])
      .reverted := by
  let localsLoaded :=
    frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
  let urnInkNew := frobDinkWord I + urnInk
  let urnArtNew := frobDartWord I + urnArt
  let ilkArtNew := frobDartWord I + ilkArt
  let localsIlk :=
    (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
        "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat)))
  let localsDtab := localsIlk.insert "dtab" (.int dtab)
  let tab := UInt256.mul ilkRate urnArtNew
  let localsTab := localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))
  let localsDebt := localsTab.insert "debtNew" (.int (Int.ofNat debtNew.toNat))
  let evmDebt :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner foldDebtSlot debtNew
  let ceilingDebt := UInt256.mul ilkArtNew ilkRate
  let inkSpot := UInt256.mul urnInkNew ilkSpot
  have hsourceDebt :=
    execFrobLoadedPrefixThroughDebtOk
      (evm := evm) (I := I) (pre := pre)
      urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust dtab debtOld debtNew
      dtabWord hprefix hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos hdtab
      hRateMax hDtabMul hTabMul hdebtLoad hdtabMod hnew hDebtNeg hDebtPos
  have hCeilingFitGuard :=
    uintCheckedMulGuard_to_fit_and_source_guard hCeilingMul
  have hInkFitGuard :=
    uintCheckedMulGuard_to_fit_and_source_guard hInkMul
  have hlocalsDebtIlkArtNew :
      localsDebt.get? "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "ilkArtNew" =
          some (.int (Int.ofNat ilkArtNew.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_self]
  have hlocalsDebtRate :
      localsDebt.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "ilkRate" =
          some (.int (Int.ofNat ilkRate.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_rate I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hlocalsDebtUrnInkNew :
      localsDebt.get? "urnInkNew" = some (.int (Int.ofNat urnInkNew.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "urnInkNew" =
          some (.int (Int.ofNat urnInkNew.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_self]
  have hlocalsDebtSpot :
      localsDebt.get? "ilkSpot" = some (.int (Int.ofNat ilkSpot.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "ilkSpot" =
          some (.int (Int.ofNat ilkSpot.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_spot I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hlocalsDebtDart : localsDebt.get? "dart" = some (frobDartValue I) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "dart" = some (frobDartValue I)
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_dart I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hlocalsDebtLine :
      localsDebt.get? "ilkLine" = some (.int (Int.ofNat ilkLine.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "ilkLine" =
          some (.int (Int.ofNat ilkLine.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_line I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hlocalsDebtDebtNew :
      localsDebt.get? "debtNew" = some (.int (Int.ofNat debtNew.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "debtNew" =
          some (.int (Int.ofNat debtNew.toNat))
    rw [store_get_self]
  have hlocalsDebtLineBase : localsDebt.get? "Line" = none := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "Line" = none
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simp [localsLoaded, frobStoreIlkDust, frobStore]
  have hlineLoadDebt :
      Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner ⟨9⟩ = Line := by
    simpa [evmDebt, storageStore_executionEnv] using hlineLoad
  have hceilingReqEval :
      evalExpr? config
        { contract := contract,
          locals :=
            (localsDebt.insert "ceilingDebt"
              (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
              (.int (Int.ofNat inkSpot.toNat)) }
        evmDebt
        (eitherExpr
          (.binary .le (.var "dart") (.intLit 0))
          (bothExpr
            (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
            (.binary .le (.var "debtNew") (.storage LineRef)))) =
        .ok (.bool false) := by
    exact evalExpr_frob_ceiling_req_false
      (evm := evmDebt) (I := I)
      (ceilingDebt := ceilingDebt) (ilkLine := ilkLine)
      (debtNew := debtNew) (Line := Line)
      (by
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        exact hlocalsDebtDart)
      (by
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_self])
      (by
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        exact hlocalsDebtLine)
      (by
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        exact hlocalsDebtDebtNew)
      (by
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        exact hlocalsDebtLineBase)
      hlineLoadDebt hCeilingBad.1
      (by simpa [ceilingDebt, ilkArtNew] using hCeilingBad.2)
  have hblock :
      ExecBlock config { contract := contract, locals := localsDebt } evmDebt
        (checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
          [ .require
              (eitherExpr
                (.binary .le (.var "dart") (.intLit 0))
                (bothExpr
                  (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                  (.binary .le (.var "debtNew") (.storage LineRef)))) ])
        .reverted := by
    exact execFrobCeilingRequireRevert
      (evm := evmDebt) (locals := localsDebt)
      ilkArtNew ilkRate ceilingDebt urnInkNew ilkSpot inkSpot
      hlocalsDebtIlkArtNew hlocalsDebtRate hlocalsDebtUrnInkNew hlocalsDebtSpot
      (by rfl) hCeilingFitGuard.1 hCeilingFitGuard.2
      (by rfl) hInkFitGuard.1 hInkFitGuard.2
      hceilingReqEval
  have hfull := Reasoning.Refinement.execBlock_append
    (by simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
      localsDtab, tab, localsTab, localsDebt, evmDebt, List.append_assoc]
      using hsourceDebt)
    hblock
  simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk, localsDtab,
    tab, localsTab, localsDebt, evmDebt, ceilingDebt, inkSpot, List.append_assoc]
    using hfull

theorem execFrobLoadedPrefixSafetyRequireRevert {evm : EVM.State}
    {I : ExecutionEnv} {pre : List Stmt}
    (urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust : UInt256)
    (dtab : Int) (debtOld debtNew dtabWord Line : UInt256)
    (hprefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm pre
        (.ok
          { contract := contract,
            locals := frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot
              ilkLine ilkDust }
          evm))
    (hInkNeg : 0 ≤ frobDinkInt I ∨
      (frobDinkWord I + urnInk).toNat ≤ urnInk.toNat)
    (hInkPos : frobDinkInt I ≤ 0 ∨
      urnInk.toNat ≤ (frobDinkWord I + urnInk).toNat)
    (hArtNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + urnArt).toNat ≤ urnArt.toNat)
    (hArtPos : frobDartInt I ≤ 0 ∨
      urnArt.toNat ≤ (frobDartWord I + urnArt).toNat)
    (hIlkNeg : 0 ≤ frobDartInt I ∨
      (frobDartWord I + ilkArt).toNat ≤ ilkArt.toNat)
    (hIlkPos : frobDartInt I ≤ 0 ∨
      ilkArt.toNat ≤ (frobDartWord I + ilkArt).toNat)
    (hdtab : dtab = Int.ofNat ilkRate.toNat * frobDartInt I)
    (hRateMax : UInt256.slt ilkRate ⟨0⟩ = ⟨0⟩)
    (hDtabMul :
      frobDartWord I = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.sdiv (UInt256.mul (frobDartWord I) ilkRate)
            (frobDartWord I)) ilkRate ≠ ⟨0⟩)
    (hTabMul :
      (frobDartWord I + urnArt) = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.div (UInt256.mul ilkRate (frobDartWord I + urnArt))
            (frobDartWord I + urnArt)) ilkRate ≠ ⟨0⟩)
    (hdebtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner foldDebtSlot = debtOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : debtNew = dtabWord + debtOld)
    (hDebtNeg :
      UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨ UInt256.gt debtNew debtOld = ⟨0⟩)
    (hDebtPos :
      UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨ UInt256.lt debtNew debtOld = ⟨0⟩)
    (hlineLoad :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner foldDebtSlot debtNew)
          evm.executionEnv.codeOwner ⟨9⟩ =
        Line)
    (hCeilingMul :
      ilkRate = ⟨0⟩ ∨
        UInt256.eq (UInt256.div
          (UInt256.mul (frobDartWord I + ilkArt) ilkRate) ilkRate)
          (frobDartWord I + ilkArt) ≠ ⟨0⟩)
    (hCeilingReq :
      frobDartInt I ≤ 0 ∨
        ((UInt256.mul (frobDartWord I + ilkArt) ilkRate).toNat ≤
            ilkLine.toNat ∧
          debtNew.toNat ≤ Line.toNat))
    (hInkMul :
      ilkSpot = ⟨0⟩ ∨
        UInt256.eq (UInt256.div
          (UInt256.mul (frobDinkWord I + urnInk) ilkSpot) ilkSpot)
          (frobDinkWord I + urnInk) ≠ ⟨0⟩)
    (hSafetyBad :
      ¬ (frobDartInt I ≤ 0 ∧ 0 ≤ frobDinkInt I) ∧
        (UInt256.mul (frobDinkWord I + urnInk) ilkSpot).toNat <
          (UInt256.mul ilkRate (frobDartWord I + urnArt)).toNat) :
    ExecBlock config { contract := contract, locals := frobStore I } evm
      (pre ++
        checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
        checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
        checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
        checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
        checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
        checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
        [ .assign .storage debtRef (.var "debtNew") ] ++
        checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
        checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
        [ .require
            (eitherExpr
              (.binary .le (.var "dart") (.intLit 0))
              (bothExpr
                (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                (.binary .le (.var "debtNew") (.storage LineRef)))),
          .require
            (eitherExpr
              (bothExpr
                (.binary .le (.var "dart") (.intLit 0))
                (.binary .ge (.var "dink") (.intLit 0)))
              (.binary .le (.var "tab") (.var "inkSpot"))) ])
      .reverted := by
  let localsLoaded :=
    frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
  let urnInkNew := frobDinkWord I + urnInk
  let urnArtNew := frobDartWord I + urnArt
  let ilkArtNew := frobDartWord I + ilkArt
  let localsIlk :=
    (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
        "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat)))
  let localsDtab := localsIlk.insert "dtab" (.int dtab)
  let tab := UInt256.mul ilkRate urnArtNew
  let localsTab := localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))
  let localsDebt := localsTab.insert "debtNew" (.int (Int.ofNat debtNew.toNat))
  let evmDebt :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner foldDebtSlot debtNew
  let ceilingDebt := UInt256.mul ilkArtNew ilkRate
  let inkSpot := UInt256.mul urnInkNew ilkSpot
  have hsourceDebt :=
    execFrobLoadedPrefixThroughDebtOk
      (evm := evm) (I := I) (pre := pre)
      urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust dtab debtOld debtNew
      dtabWord hprefix hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos hdtab
      hRateMax hDtabMul hTabMul hdebtLoad hdtabMod hnew hDebtNeg hDebtPos
  have hCeilingFitGuard :=
    uintCheckedMulGuard_to_fit_and_source_guard hCeilingMul
  have hInkFitGuard :=
    uintCheckedMulGuard_to_fit_and_source_guard hInkMul
  have hlocalsDebtIlkArtNew :
      localsDebt.get? "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "ilkArtNew" =
          some (.int (Int.ofNat ilkArtNew.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_self]
  have hlocalsDebtRate :
      localsDebt.get? "ilkRate" = some (.int (Int.ofNat ilkRate.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "ilkRate" =
          some (.int (Int.ofNat ilkRate.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_rate I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hlocalsDebtUrnInkNew :
      localsDebt.get? "urnInkNew" = some (.int (Int.ofNat urnInkNew.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "urnInkNew" =
          some (.int (Int.ofNat urnInkNew.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_self]
  have hlocalsDebtSpot :
      localsDebt.get? "ilkSpot" = some (.int (Int.ofNat ilkSpot.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "ilkSpot" =
          some (.int (Int.ofNat ilkSpot.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_spot I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hlocalsDebtDart : localsDebt.get? "dart" = some (frobDartValue I) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "dart" = some (frobDartValue I)
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_dart I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hlocalsDebtDink : localsDebt.get? "dink" = some (frobDinkValue I) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "dink" = some (frobDinkValue I)
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_dink I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hlocalsDebtLine :
      localsDebt.get? "ilkLine" = some (.int (Int.ofNat ilkLine.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "ilkLine" =
          some (.int (Int.ofNat ilkLine.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_line I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine
        ilkDust
  have hlocalsDebtDebtNew :
      localsDebt.get? "debtNew" = some (.int (Int.ofNat debtNew.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "debtNew" =
          some (.int (Int.ofNat debtNew.toNat))
    rw [store_get_self]
  have hlocalsDebtTab :
      localsDebt.get? "tab" = some (.int (Int.ofNat tab.toNat)) := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "tab" =
          some (.int (Int.ofNat tab.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_self]
  have hlocalsDebtLineBase : localsDebt.get? "Line" = none := by
    change
      ((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).get? "Line" = none
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simp [localsLoaded, frobStoreIlkDust, frobStore]
  have hlineLoadDebt :
      Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner ⟨9⟩ = Line := by
    simpa [evmDebt, storageStore_executionEnv] using hlineLoad
  have hceilingReqEval :
      evalExpr? config
        { contract := contract,
          locals :=
            (localsDebt.insert "ceilingDebt"
              (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
              (.int (Int.ofNat inkSpot.toNat)) }
        evmDebt
        (eitherExpr
          (.binary .le (.var "dart") (.intLit 0))
          (bothExpr
            (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
            (.binary .le (.var "debtNew") (.storage LineRef)))) =
        .ok (.bool true) := by
    exact evalExpr_frob_ceiling_req_true
      (evm := evmDebt) (I := I)
      (ceilingDebt := ceilingDebt) (ilkLine := ilkLine)
      (debtNew := debtNew) (Line := Line)
      (by
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        exact hlocalsDebtDart)
      (by
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_self])
      (by
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        exact hlocalsDebtLine)
      (by
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        exact hlocalsDebtDebtNew)
      (by
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        exact hlocalsDebtLineBase)
      hlineLoadDebt
      (by simpa [ceilingDebt, ilkArtNew] using hCeilingReq)
  have hsafetyReqEval :
      evalExpr? config
        { contract := contract,
          locals :=
            (localsDebt.insert "ceilingDebt"
              (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
              (.int (Int.ofNat inkSpot.toNat)) }
        evmDebt
        (eitherExpr
          (bothExpr
            (.binary .le (.var "dart") (.intLit 0))
            (.binary .ge (.var "dink") (.intLit 0)))
          (.binary .le (.var "tab") (.var "inkSpot"))) =
        .ok (.bool false) := by
    exact evalExpr_frob_safety_req_false
      (evm := evmDebt) (I := I) (tab := tab) (inkSpot := inkSpot)
      (by
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        exact hlocalsDebtDart)
      (by
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        exact hlocalsDebtDink)
      (by
        rw [store_get_ne _ _ (by decide)]
        rw [store_get_ne _ _ (by decide)]
        exact hlocalsDebtTab)
      (by
        rw [store_get_self])
      hSafetyBad.1
      (by simpa [tab, inkSpot, urnInkNew, urnArtNew] using hSafetyBad.2)
  have hblock :
      ExecBlock config { contract := contract, locals := localsDebt } evmDebt
        (checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
          [ .require
              (eitherExpr
                (.binary .le (.var "dart") (.intLit 0))
                (bothExpr
                  (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                  (.binary .le (.var "debtNew") (.storage LineRef)))),
            .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (.binary .le (.var "tab") (.var "inkSpot"))) ])
        .reverted := by
    exact execFrobSafetyRequireRevert
      (evm := evmDebt) (locals := localsDebt)
      ilkArtNew ilkRate ceilingDebt urnInkNew ilkSpot inkSpot
      hlocalsDebtIlkArtNew hlocalsDebtRate hlocalsDebtUrnInkNew hlocalsDebtSpot
      (by rfl) hCeilingFitGuard.1 hCeilingFitGuard.2
      (by rfl) hInkFitGuard.1 hInkFitGuard.2
      hceilingReqEval hsafetyReqEval
  have hfull := Reasoning.Refinement.execBlock_append
    (by simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk,
      localsDtab, tab, localsTab, localsDebt, evmDebt, List.append_assoc]
      using hsourceDebt)
    hblock
  simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk, localsDtab,
    tab, localsTab, localsDebt, evmDebt, ceilingDebt, inkSpot, List.append_assoc]
    using hfull
set_option maxHeartbeats 0 in
theorem vatFrobBodyCoreLiveAddOverflowReverts
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (vatSelBytes 11))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz196 : 196 ≤ I.calldata.size)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (frobTransition.params.map Param.name)
        (transitionSignature frobTransition).paramTypes I.calldata = some (frobStore I))
    (hdecoded :
      ∃ k C,
        RD vatBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2975⟩
          [frobDartWord I, frobDinkWord I, frobWMaskedWord I, frobVMaskedWord I,
            frobUMaskedWord I, frobIWord I, ⟨524⟩, vatSelWord I]
          solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hlive : vatSlotWord ⟨10⟩ σ_evm I = ⟨1⟩)
    (hrateZeroEvm : ¬ solcSlotWord σ_evm I (frobIlkRateSlot I) = ⟨0⟩)
    (hAddFail : ¬ frobLiveAddArithmeticGuards σ_evm I) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, hafterLive⟩ := vatFrobLiveOk
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (sel := vatSelWord I) hlive hdecoded
  let urnInk := vatSlotWord (frobUrnInkSlot I) σ_solm I
  let urnArt := vatSlotWord (frobUrnArtSlot I) σ_solm I
  let ilkArt := vatSlotWord (frobIlkArtSlot I) σ_solm I
  let ilkRate := vatSlotWord (frobIlkRateSlot I) σ_solm I
  let ilkSpot := vatSlotWord (frobIlkSpotSlot I) σ_solm I
  let ilkLine := vatSlotWord (frobIlkLineSlot I) σ_solm I
  let ilkDust := vatSlotWord (frobIlkDustSlot I) σ_solm I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveWord : vatSlotWord ⟨10⟩ σ_evm I = vatSlotWord ⟨10⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨10⟩ ⟨0⟩
  have hliveSolm : vatSlotWord ⟨10⟩ σ_solm I = ⟨1⟩ := by
    rw [← hliveWord]
    exact hlive
  have hrateWordNe :
      vatSlotWord (frobIlkRateSlot I) σ_solm I ≠ ⟨0⟩ := by
    intro hzeroSolm
    apply hrateZeroEvm
    have heq :
        vatSlotWord (frobIlkRateSlot I) σ_evm I =
          vatSlotWord (frobIlkRateSlot I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (frobIlkRateSlot I) ⟨0⟩
    simpa [vatSlotWord, hzeroSolm] using heq.trans hzeroSolm
  have hratePos : 0 < ilkRate.toNat := by
    have hnat : ilkRate.toNat ≠ 0 := by
      intro hzeroNat
      apply hrateWordNe
      apply u256_inj
      simp [ilkRate, hzeroNat]
    exact Nat.pos_of_ne_zero hnat
  have hsourcePrefixRaw :
      let locals := frobStore I
      let evm0' := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      ExecBlock config { contract := contract, locals := locals } evm0'
        (nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ])
        (.ok
          { contract := contract,
            locals :=
              frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust }
          evm0') := by
    exact vatFrobSourceRateNonzeroPrefix
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := g)
        (urnInk := urnInk) (urnArt := urnArt) (ilkArt := ilkArt)
        (ilkRate := ilkRate) (ilkSpot := ilkSpot) (ilkLine := ilkLine)
        (ilkDust := ilkDust)
        hwv hsz196 hliveSolm
        (by simpa [urnInk] using
          (frobSourceLoad_urnInk (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [urnArt] using
          (frobSourceLoad_urnArt (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkArt] using
          (frobSourceLoad_ilkArt (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkRate] using
          (frobSourceLoad_ilkRate (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkSpot] using
          (frobSourceLoad_ilkSpot (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkLine] using
          (frobSourceLoad_ilkLine (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkDust] using
          (frobSourceLoad_ilkDust (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        hratePos
  have hsourcePrefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm0
        (nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ])
        (.ok
          { contract := contract,
            locals :=
              frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust }
          evm0) := by
    simpa [evm0] using hsourcePrefixRaw
  obtain ⟨_, _, hafterUrn⟩ := RD.vatFrobUrnLoads hafterLive
  obtain ⟨_, _, hafterRateNonzero⟩ :=
    RD.vatFrobIlkLoadsRateNonzero hafterUrn hrateZeroEvm
  have hthreeAddsEvm :
      (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
          (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
      (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
          (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
      (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
          (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
      (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
          (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
      (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
          (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
      (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
          (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
      ∃ k' C',
        RD vatBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3306⟩
          [frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I),
            ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
            frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I,
            frobIWord I, ⟨524⟩, vatSelWord I]
          (frobUrnArtUpdatedMem σ_evm I
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
          (UInt256.ofNat 18) ByteArray.empty (cA, σ_evm) k' C' := by
    intro hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
    obtain ⟨_, _, hInk⟩ :=
      RD.vatFrobUrnInkAddSuccess (h := hafterRateNonzero) hInkNeg hInkPos
    obtain ⟨_, _, hArt⟩ :=
      RD.vatFrobUrnArtAddSuccess (h := by simpa using hInk) hArtNeg hArtPos
    obtain ⟨_, _, hIlk⟩ :=
      RD.vatFrobIlkArtAddSuccess (h := by simpa using hArt) hIlkNeg hIlkPos
    exact ⟨_, _, by simpa using hIlk⟩
  have hUrnInkEq :
      solcSlotWord σ_evm I (frobUrnInkSlot I) =
        solcSlotWord σ_solm I (frobUrnInkSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobUrnInkSlot I) ⟨0⟩
  have hUrnArtEq :
      solcSlotWord σ_evm I (frobUrnArtSlot I) =
        solcSlotWord σ_solm I (frobUrnArtSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobUrnArtSlot I) ⟨0⟩
  have hIlkArtEq :
      solcSlotWord σ_evm I (frobIlkArtSlot I) =
        solcSlotWord σ_solm I (frobIlkArtSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkArtSlot I) ⟨0⟩
  classical
  by_cases hInkNeg :
      UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
          (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩
  · by_cases hInkPos :
        UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩
    · by_cases hArtNeg :
          UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
            UInt256.gt
              (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
              (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩
      · by_cases hArtPos :
            UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
              UInt256.lt
                (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
                (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩
        · by_cases hIlkNeg :
              UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                UInt256.gt
                  (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
                  (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩
          · by_cases hIlkPos :
                UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                  UInt256.lt
                    (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
                    (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩
            · exact False.elim (hAddFail (by
                unfold frobLiveAddArithmeticGuards
                exact ⟨hInkNeg, hInkPos, hArtNeg, hArtPos, hIlkNeg, hIlkPos⟩))
            · have hInkNegSource :
                  UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                    UInt256.gt (frobDinkWord I + urnInk) urnInk = ⟨0⟩ := by
                simpa [urnInk, vatSlotWord, hUrnInkEq] using hInkNeg
              have hInkPosSource :
                  UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                    UInt256.lt (frobDinkWord I + urnInk) urnInk = ⟨0⟩ := by
                simpa [urnInk, vatSlotWord, hUrnInkEq] using hInkPos
              have hArtNegSource :
                  UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                    UInt256.gt (frobDartWord I + urnArt) urnArt = ⟨0⟩ := by
                simpa [urnArt, vatSlotWord, hUrnArtEq] using hArtNeg
              have hArtPosSource :
                  UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                    UInt256.lt (frobDartWord I + urnArt) urnArt = ⟨0⟩ := by
                simpa [urnArt, vatSlotWord, hUrnArtEq] using hArtPos
              have hIlkNegSource :
                  UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                    UInt256.gt (frobDartWord I + ilkArt) ilkArt = ⟨0⟩ := by
                simpa [ilkArt, vatSlotWord, hIlkArtEq] using hIlkNeg
              have hIlkPosSource :
                  ¬ (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                    UInt256.lt (frobDartWord I + ilkArt) ilkArt = ⟨0⟩) := by
                intro hsrc
                exact hIlkPos (by
                  simpa [ilkArt, vatSlotWord, hIlkArtEq] using hsrc)
              have hsrcPrefixRevert :
                  ExecBlock config { contract := contract, locals := frobStore I } evm0
                    ((nonpayable ++ requireLive ++
                      [ .letDecl "urnInk" (some uint256)
                          (.storage (urnsF (.var "i") (.var "u") "ink")),
                        .letDecl "urnArt" (some uint256)
                          (.storage (urnsF (.var "i") (.var "u") "art")),
                        .letDecl "ilkArt" (some uint256)
                          (.storage (ilksF (.var "i") "Art")),
                        .letDecl "ilkRate" (some uint256)
                          (.storage (ilksF (.var "i") "rate")),
                        .letDecl "ilkSpot" (some uint256)
                          (.storage (ilksF (.var "i") "spot")),
                        .letDecl "ilkLine" (some uint256)
                          (.storage (ilksF (.var "i") "line")),
                        .letDecl "ilkDust" (some uint256)
                          (.storage (ilksF (.var "i") "dust")),
                        .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
                      checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
                      checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
                      checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart"))
                    .reverted := by
                exact execFrobLoadedPrefixIlkArtRevertGuardPos
                  (evm := evm0) (I := I)
                  urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
                  hsourcePrefix
                  (frobDinkAddGuardNegCond hInkNegSource)
                  (frobDinkAddGuardPosCond hInkPosSource)
                  (frobDartAddGuardNegCond hArtNegSource)
                  (frobDartAddGuardPosCond hArtPosSource)
                  (frobDartAddGuardNegCond hIlkNegSource)
                  (frobDartAddGuardPosFailCond hIlkPosSource)
              have hsrcFullRevert := hsourceRevertFromIlkArtAdd hsrcPrefixRevert
              obtain ⟨_, _, hInkDone⟩ :=
                RD.vatFrobUrnInkAddSuccess (h := hafterRateNonzero) hInkNeg hInkPos
              obtain ⟨_, _, hArtDone⟩ :=
                RD.vatFrobUrnArtAddSuccess (h := by simpa using hInkDone)
                  hArtNeg hArtPos
              have hrev := RD.vatFrobIlkArtAddRevert
                (h := by simpa using hArtDone)
                (Or.inr ⟨hIlkNeg, hIlkPos⟩)
              exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel) hdecode
                hsrcFullRevert
          · have hInkNegSource :
                UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                  UInt256.gt (frobDinkWord I + urnInk) urnInk = ⟨0⟩ := by
              simpa [urnInk, vatSlotWord, hUrnInkEq] using hInkNeg
            have hInkPosSource :
                UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                  UInt256.lt (frobDinkWord I + urnInk) urnInk = ⟨0⟩ := by
              simpa [urnInk, vatSlotWord, hUrnInkEq] using hInkPos
            have hArtNegSource :
                UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                  UInt256.gt (frobDartWord I + urnArt) urnArt = ⟨0⟩ := by
              simpa [urnArt, vatSlotWord, hUrnArtEq] using hArtNeg
            have hArtPosSource :
                UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                  UInt256.lt (frobDartWord I + urnArt) urnArt = ⟨0⟩ := by
              simpa [urnArt, vatSlotWord, hUrnArtEq] using hArtPos
            have hIlkNegSource :
                ¬ (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                  UInt256.gt (frobDartWord I + ilkArt) ilkArt = ⟨0⟩) := by
              intro hsrc
              exact hIlkNeg (by
                simpa [ilkArt, vatSlotWord, hIlkArtEq] using hsrc)
            have hsrcPrefixRevert :
                ExecBlock config { contract := contract, locals := frobStore I } evm0
                  ((nonpayable ++ requireLive ++
                    [ .letDecl "urnInk" (some uint256)
                        (.storage (urnsF (.var "i") (.var "u") "ink")),
                      .letDecl "urnArt" (some uint256)
                        (.storage (urnsF (.var "i") (.var "u") "art")),
                      .letDecl "ilkArt" (some uint256)
                        (.storage (ilksF (.var "i") "Art")),
                      .letDecl "ilkRate" (some uint256)
                        (.storage (ilksF (.var "i") "rate")),
                      .letDecl "ilkSpot" (some uint256)
                        (.storage (ilksF (.var "i") "spot")),
                      .letDecl "ilkLine" (some uint256)
                        (.storage (ilksF (.var "i") "line")),
                      .letDecl "ilkDust" (some uint256)
                        (.storage (ilksF (.var "i") "dust")),
                      .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
                    checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
                    checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
                    checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart"))
                  .reverted := by
              exact execFrobLoadedPrefixIlkArtRevertGuardNeg
                (evm := evm0) (I := I)
                urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
                hsourcePrefix
                (frobDinkAddGuardNegCond hInkNegSource)
                (frobDinkAddGuardPosCond hInkPosSource)
                (frobDartAddGuardNegCond hArtNegSource)
                (frobDartAddGuardPosCond hArtPosSource)
                (frobDartAddGuardNegFailCond hIlkNegSource)
            have hsrcFullRevert := hsourceRevertFromIlkArtAdd hsrcPrefixRevert
            obtain ⟨_, _, hInkDone⟩ :=
              RD.vatFrobUrnInkAddSuccess (h := hafterRateNonzero) hInkNeg hInkPos
            obtain ⟨_, _, hArtDone⟩ :=
              RD.vatFrobUrnArtAddSuccess (h := by simpa using hInkDone)
                hArtNeg hArtPos
            have hrev := RD.vatFrobIlkArtAddRevert
              (h := by simpa using hArtDone)
              (Or.inl hIlkNeg)
            exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel) hdecode
              hsrcFullRevert
        · have hInkNegSource :
              UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                UInt256.gt (frobDinkWord I + urnInk) urnInk = ⟨0⟩ := by
            simpa [urnInk, vatSlotWord, hUrnInkEq] using hInkNeg
          have hInkPosSource :
              UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                UInt256.lt (frobDinkWord I + urnInk) urnInk = ⟨0⟩ := by
            simpa [urnInk, vatSlotWord, hUrnInkEq] using hInkPos
          have hArtNegSource :
              UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                UInt256.gt (frobDartWord I + urnArt) urnArt = ⟨0⟩ := by
            simpa [urnArt, vatSlotWord, hUrnArtEq] using hArtNeg
          have hArtPosSource :
              ¬ (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
                UInt256.lt (frobDartWord I + urnArt) urnArt = ⟨0⟩) := by
            intro hsrc
            exact hArtPos (by
              simpa [urnArt, vatSlotWord, hUrnArtEq] using hsrc)
          have hsrcPrefixRevert :
              ExecBlock config { contract := contract, locals := frobStore I } evm0
                ((nonpayable ++ requireLive ++
                  [ .letDecl "urnInk" (some uint256)
                      (.storage (urnsF (.var "i") (.var "u") "ink")),
                    .letDecl "urnArt" (some uint256)
                      (.storage (urnsF (.var "i") (.var "u") "art")),
                    .letDecl "ilkArt" (some uint256)
                      (.storage (ilksF (.var "i") "Art")),
                    .letDecl "ilkRate" (some uint256)
                      (.storage (ilksF (.var "i") "rate")),
                    .letDecl "ilkSpot" (some uint256)
                      (.storage (ilksF (.var "i") "spot")),
                    .letDecl "ilkLine" (some uint256)
                      (.storage (ilksF (.var "i") "line")),
                    .letDecl "ilkDust" (some uint256)
                      (.storage (ilksF (.var "i") "dust")),
                    .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
                  checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
                  checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart"))
                .reverted := by
            exact execFrobLoadedPrefixUrnArtRevertGuardPos
              (evm := evm0) (I := I)
              urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
              hsourcePrefix
              (frobDinkAddGuardNegCond hInkNegSource)
              (frobDinkAddGuardPosCond hInkPosSource)
              (frobDartAddGuardNegCond hArtNegSource)
              (frobDartAddGuardPosFailCond hArtPosSource)
          have hsrcFullRevert := hsourceRevertFromUrnArtAdd hsrcPrefixRevert
          obtain ⟨_, _, hInkDone⟩ :=
            RD.vatFrobUrnInkAddSuccess (h := hafterRateNonzero) hInkNeg hInkPos
          have hrev := RD.vatFrobUrnArtAddRevert
            (h := by simpa using hInkDone)
            (Or.inr ⟨hArtNeg, hArtPos⟩)
          exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel) hdecode
            hsrcFullRevert
      · have hInkNegSource :
            UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
              UInt256.gt (frobDinkWord I + urnInk) urnInk = ⟨0⟩ := by
          simpa [urnInk, vatSlotWord, hUrnInkEq] using hInkNeg
        have hInkPosSource :
            UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
              UInt256.lt (frobDinkWord I + urnInk) urnInk = ⟨0⟩ := by
          simpa [urnInk, vatSlotWord, hUrnInkEq] using hInkPos
        have hArtNegSource :
            ¬ (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
              UInt256.gt (frobDartWord I + urnArt) urnArt = ⟨0⟩) := by
          intro hsrc
          exact hArtNeg (by
            simpa [urnArt, vatSlotWord, hUrnArtEq] using hsrc)
        have hsrcPrefixRevert :
            ExecBlock config { contract := contract, locals := frobStore I } evm0
              ((nonpayable ++ requireLive ++
                [ .letDecl "urnInk" (some uint256)
                    (.storage (urnsF (.var "i") (.var "u") "ink")),
                  .letDecl "urnArt" (some uint256)
                    (.storage (urnsF (.var "i") (.var "u") "art")),
                  .letDecl "ilkArt" (some uint256)
                    (.storage (ilksF (.var "i") "Art")),
                  .letDecl "ilkRate" (some uint256)
                    (.storage (ilksF (.var "i") "rate")),
                  .letDecl "ilkSpot" (some uint256)
                    (.storage (ilksF (.var "i") "spot")),
                  .letDecl "ilkLine" (some uint256)
                    (.storage (ilksF (.var "i") "line")),
                  .letDecl "ilkDust" (some uint256)
                    (.storage (ilksF (.var "i") "dust")),
                  .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
                checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
                checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart"))
              .reverted := by
          exact execFrobLoadedPrefixUrnArtRevertGuardNeg
            (evm := evm0) (I := I)
            urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
            hsourcePrefix
            (frobDinkAddGuardNegCond hInkNegSource)
            (frobDinkAddGuardPosCond hInkPosSource)
            (frobDartAddGuardNegFailCond hArtNegSource)
        have hsrcFullRevert := hsourceRevertFromUrnArtAdd hsrcPrefixRevert
        obtain ⟨_, _, hInkDone⟩ :=
          RD.vatFrobUrnInkAddSuccess (h := hafterRateNonzero) hInkNeg hInkPos
        have hrev := RD.vatFrobUrnArtAddRevert
          (h := by simpa using hInkDone)
          (Or.inl hArtNeg)
        exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel) hdecode
          hsrcFullRevert
    · have hInkPosSource :
          ¬ (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
            UInt256.lt (frobDinkWord I + urnInk) urnInk = ⟨0⟩) := by
        intro hsrc
        exact hInkPos (by
          simpa [urnInk, vatSlotWord, hUrnInkEq] using hsrc)
      have hInkNegSource :
          UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
            UInt256.gt (frobDinkWord I + urnInk) urnInk = ⟨0⟩ := by
        simpa [urnInk, vatSlotWord, hUrnInkEq] using hInkNeg
      have hsrcPrefixRevert :
          ExecBlock config { contract := contract, locals := frobStore I } evm0
            ((nonpayable ++ requireLive ++
              [ .letDecl "urnInk" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "ink")),
                .letDecl "urnArt" (some uint256)
                  (.storage (urnsF (.var "i") (.var "u") "art")),
                .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
                .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
                .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
                .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
                .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
                .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
              checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink"))
            .reverted := by
        exact execFrobLoadedPrefixUrnInkRevertGuardPos
          (evm := evm0) (I := I)
          urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
          hsourcePrefix
          (frobDinkAddGuardNegCond hInkNegSource)
          (frobDinkAddGuardPosFailCond hInkPosSource)
      have hsrcFullRevert := hsourceRevertFromUrnInkAdd hsrcPrefixRevert
      have hrev := RD.vatFrobUrnInkAddRevert
        (h := by simpa using hafterRateNonzero)
        (Or.inr ⟨hInkNeg, hInkPos⟩)
      exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel) hdecode
        hsrcFullRevert
  · have hInkNegSource :
        ¬ (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt (frobDinkWord I + urnInk) urnInk = ⟨0⟩) := by
      intro hsrc
      exact hInkNeg (by
        simpa [urnInk, vatSlotWord, hUrnInkEq] using hsrc)
    have hsrcPrefixRevert :
        ExecBlock config { contract := contract, locals := frobStore I } evm0
          ((nonpayable ++ requireLive ++
            [ .letDecl "urnInk" (some uint256)
                (.storage (urnsF (.var "i") (.var "u") "ink")),
              .letDecl "urnArt" (some uint256)
                (.storage (urnsF (.var "i") (.var "u") "art")),
              .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
              .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
              .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
              .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
              .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
              .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
            checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink"))
          .reverted := by
      exact execFrobLoadedPrefixUrnInkRevertGuardNeg
        (evm := evm0) (I := I)
        urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
        hsourcePrefix
        (frobDinkAddGuardNegFailCond hInkNegSource)
    have hsrcFullRevert := hsourceRevertFromUrnInkAdd hsrcPrefixRevert
    have hrev := RD.vatFrobUrnInkAddRevert
      (h := by simpa using hafterRateNonzero)
      (Or.inl hInkNeg)
    exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel) hdecode
      hsrcFullRevert

/- The former monolithic live proof was removed; the live proof is split into branch theorems below. -/

set_option maxHeartbeats 0 in
theorem vatFrobBodyCoreLiveMulOverflowReverts
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (vatSelBytes 11))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz196 : 196 ≤ I.calldata.size)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (frobTransition.params.map Param.name)
        (transitionSignature frobTransition).paramTypes I.calldata = some (frobStore I))
    (hdecoded :
      ∃ k C,
        RD vatBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2975⟩
          [frobDartWord I, frobDinkWord I, frobWMaskedWord I, frobVMaskedWord I,
            frobUMaskedWord I, frobIWord I, ⟨524⟩, vatSelWord I]
          solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hlive : vatSlotWord ⟨10⟩ σ_evm I = ⟨1⟩)
    (hrateZeroEvm : ¬ solcSlotWord σ_evm I (frobIlkRateSlot I) = ⟨0⟩)
    (hAdd : frobLiveAddArithmeticGuards σ_evm I)
    (hMulFail : ¬ frobLiveMulArithmeticGuards σ_evm I) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, hafterLive⟩ := vatFrobLiveOk
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (sel := vatSelWord I) hlive hdecoded
  let urnInk := vatSlotWord (frobUrnInkSlot I) σ_solm I
  let urnArt := vatSlotWord (frobUrnArtSlot I) σ_solm I
  let ilkArt := vatSlotWord (frobIlkArtSlot I) σ_solm I
  let ilkRate := vatSlotWord (frobIlkRateSlot I) σ_solm I
  let ilkSpot := vatSlotWord (frobIlkSpotSlot I) σ_solm I
  let ilkLine := vatSlotWord (frobIlkLineSlot I) σ_solm I
  let ilkDust := vatSlotWord (frobIlkDustSlot I) σ_solm I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveWord : vatSlotWord ⟨10⟩ σ_evm I = vatSlotWord ⟨10⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨10⟩ ⟨0⟩
  have hliveSolm : vatSlotWord ⟨10⟩ σ_solm I = ⟨1⟩ := by
    rw [← hliveWord]
    exact hlive
  have hrateWordNe :
      vatSlotWord (frobIlkRateSlot I) σ_solm I ≠ ⟨0⟩ := by
    intro hzeroSolm
    apply hrateZeroEvm
    have heq :
        vatSlotWord (frobIlkRateSlot I) σ_evm I =
          vatSlotWord (frobIlkRateSlot I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (frobIlkRateSlot I) ⟨0⟩
    simpa [vatSlotWord, hzeroSolm] using heq.trans hzeroSolm
  have hratePos : 0 < ilkRate.toNat := by
    have hnat : ilkRate.toNat ≠ 0 := by
      intro hzeroNat
      apply hrateWordNe
      apply u256_inj
      simp [ilkRate, hzeroNat]
    exact Nat.pos_of_ne_zero hnat
  have hsourcePrefixRaw :
      let locals := frobStore I
      let evm0' := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      ExecBlock config { contract := contract, locals := locals } evm0'
        (nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ])
        (.ok
          { contract := contract,
            locals :=
              frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust }
          evm0') := by
    exact vatFrobSourceRateNonzeroPrefix
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := g)
        (urnInk := urnInk) (urnArt := urnArt) (ilkArt := ilkArt)
        (ilkRate := ilkRate) (ilkSpot := ilkSpot) (ilkLine := ilkLine)
        (ilkDust := ilkDust)
        hwv hsz196 hliveSolm
        (by simpa [urnInk] using
          (frobSourceLoad_urnInk (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [urnArt] using
          (frobSourceLoad_urnArt (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkArt] using
          (frobSourceLoad_ilkArt (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkRate] using
          (frobSourceLoad_ilkRate (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkSpot] using
          (frobSourceLoad_ilkSpot (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkLine] using
          (frobSourceLoad_ilkLine (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkDust] using
          (frobSourceLoad_ilkDust (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        hratePos
  have hsourcePrefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm0
        (nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ])
        (.ok
          { contract := contract,
            locals :=
              frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust }
          evm0) := by
    simpa [evm0] using hsourcePrefixRaw
  obtain ⟨_, _, hafterUrn⟩ := RD.vatFrobUrnLoads hafterLive
  obtain ⟨_, _, hafterRateNonzero⟩ :=
    RD.vatFrobIlkLoadsRateNonzero hafterUrn hrateZeroEvm
  have hthreeAddsEvm :
      (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
          (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
      (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
          (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
      (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
          (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
      (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
          (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
      (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
          (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
      (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
          (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
      ∃ k' C',
        RD vatBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3306⟩
          [frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I),
            ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
            frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I,
            frobIWord I, ⟨524⟩, vatSelWord I]
          (frobUrnArtUpdatedMem σ_evm I
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
          (UInt256.ofNat 18) ByteArray.empty (cA, σ_evm) k' C' := by
    intro hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
    obtain ⟨_, _, hInk⟩ :=
      RD.vatFrobUrnInkAddSuccess (h := hafterRateNonzero) hInkNeg hInkPos
    obtain ⟨_, _, hArt⟩ :=
      RD.vatFrobUrnArtAddSuccess (h := by simpa using hInk) hArtNeg hArtPos
    obtain ⟨_, _, hIlk⟩ :=
      RD.vatFrobIlkArtAddSuccess (h := by simpa using hArt) hIlkNeg hIlkPos
    exact ⟨_, _, by simpa using hIlk⟩
  have hthroughDtabEvm :
      (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
          (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
      (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
          (solcSlotWord σ_evm I (frobUrnInkSlot I)) = ⟨0⟩) →
      (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
          (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
      (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
          (solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩) →
      (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
          (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
      (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
          (solcSlotWord σ_evm I (frobIlkArtSlot I)) = ⟨0⟩) →
      UInt256.slt (solcSlotWord σ_evm I (frobIlkRateSlot I)) ⟨0⟩ = ⟨0⟩ →
      (frobDartWord I = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.sdiv
            (UInt256.mul (frobDartWord I)
              (solcSlotWord σ_evm I (frobIlkRateSlot I)))
            (frobDartWord I))
          (solcSlotWord σ_evm I (frobIlkRateSlot I)) ≠ ⟨0⟩) →
      ∃ k' C',
        RD vatBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3329⟩
          [UInt256.mul (frobDartWord I)
              (solcSlotWord σ_evm I (frobIlkRateSlot I)),
            ⟨416⟩, ⟨192⟩, frobDartWord I, frobDinkWord I,
            frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I,
            frobIWord I, ⟨524⟩, vatSelWord I]
          (frobIlkArtUpdatedMem σ_evm I
            (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
            (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
            (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I)))
          (UInt256.ofNat 18) ByteArray.empty (cA, σ_evm) k' C' := by
    intro hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos hRateMax hDtabMul
    obtain ⟨_, _, hIlk⟩ :=
      hthreeAddsEvm hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
    obtain ⟨_, _, hDtab⟩ :=
      RD.vatFrobDtabMulSuccess (h := by simpa using hIlk) hRateMax hDtabMul
    exact ⟨_, _, by simpa using hDtab⟩
  have hUrnInkEq :
      solcSlotWord σ_evm I (frobUrnInkSlot I) =
        solcSlotWord σ_solm I (frobUrnInkSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobUrnInkSlot I) ⟨0⟩
  have hUrnArtEq :
      solcSlotWord σ_evm I (frobUrnArtSlot I) =
        solcSlotWord σ_solm I (frobUrnArtSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobUrnArtSlot I) ⟨0⟩
  have hIlkArtEq :
      solcSlotWord σ_evm I (frobIlkArtSlot I) =
        solcSlotWord σ_solm I (frobIlkArtSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkArtSlot I) ⟨0⟩
  have hIlkRateEq :
      solcSlotWord σ_evm I (frobIlkRateSlot I) =
        solcSlotWord σ_solm I (frobIlkRateSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkRateSlot I) ⟨0⟩
  let dtab : Int := Int.ofNat ilkRate.toNat * frobDartInt I
  classical
  rcases hAdd with ⟨hInkNeg, hInkPos, hArtNeg, hArtPos, hIlkNeg, hIlkPos⟩
  have hInkNegSource :
      UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDinkWord I + urnInk) urnInk = ⟨0⟩ := by
    simpa [urnInk, vatSlotWord, hUrnInkEq] using hInkNeg
  have hInkPosSource :
      UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobDinkWord I + urnInk) urnInk = ⟨0⟩ := by
    simpa [urnInk, vatSlotWord, hUrnInkEq] using hInkPos
  have hArtNegSource :
      UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDartWord I + urnArt) urnArt = ⟨0⟩ := by
    simpa [urnArt, vatSlotWord, hUrnArtEq] using hArtNeg
  have hArtPosSource :
      UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobDartWord I + urnArt) urnArt = ⟨0⟩ := by
    simpa [urnArt, vatSlotWord, hUrnArtEq] using hArtPos
  have hIlkNegSource :
      UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDartWord I + ilkArt) ilkArt = ⟨0⟩ := by
    simpa [ilkArt, vatSlotWord, hIlkArtEq] using hIlkNeg
  have hIlkPosSource :
      UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobDartWord I + ilkArt) ilkArt = ⟨0⟩ := by
    simpa [ilkArt, vatSlotWord, hIlkArtEq] using hIlkPos
  by_cases hRateMax :
      UInt256.slt (solcSlotWord σ_evm I (frobIlkRateSlot I)) ⟨0⟩ = ⟨0⟩
  · by_cases hDtabMul :
        frobDartWord I = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.sdiv
              (UInt256.mul (frobDartWord I)
                (solcSlotWord σ_evm I (frobIlkRateSlot I)))
              (frobDartWord I))
            (solcSlotWord σ_evm I (frobIlkRateSlot I)) ≠ ⟨0⟩
    · by_cases hTabMul :
          (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)) = ⟨0⟩ ∨
            UInt256.eq
              (UInt256.div
                (UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                  (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
                (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
              (solcSlotWord σ_evm I (frobIlkRateSlot I)) ≠ ⟨0⟩
      · have hMul : frobLiveMulArithmeticGuards σ_evm I := by
          unfold frobLiveMulArithmeticGuards
          exact ⟨hRateMax, hDtabMul, hTabMul⟩
        exact False.elim (hMulFail hMul)
      · have hRateMaxSource : UInt256.slt ilkRate ⟨0⟩ = ⟨0⟩ := by
          simpa [ilkRate, vatSlotWord, hIlkRateEq] using hRateMax
        have hDtabMulSource :
            frobDartWord I = ⟨0⟩ ∨
              UInt256.eq
                (UInt256.sdiv (UInt256.mul (frobDartWord I) ilkRate)
                  (frobDartWord I)) ilkRate ≠ ⟨0⟩ := by
          simpa [ilkRate, vatSlotWord, hIlkRateEq] using hDtabMul
        have hTabMulSourceFail :
            ¬ ((frobDartWord I + urnArt) = ⟨0⟩ ∨
              UInt256.eq
                (UInt256.div (UInt256.mul ilkRate (frobDartWord I + urnArt))
                  (frobDartWord I + urnArt)) ilkRate ≠ ⟨0⟩) := by
          intro hsrc
          exact hTabMul (by
            simpa [urnArt, ilkRate, vatSlotWord, hUrnArtEq, hIlkRateEq] using hsrc)
        have htabOverflow := uintCheckedMulFail_to_overflow hTabMulSourceFail
        have hsrcPrefixRevert :=
          execFrobLoadedPrefixTabMulRevertOverflow
            (evm := evm0) (I := I)
            urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust dtab
            hsourcePrefix
            (frobDinkAddGuardNegCond hInkNegSource)
            (frobDinkAddGuardPosCond hInkPosSource)
            (frobDartAddGuardNegCond hArtNegSource)
            (frobDartAddGuardPosCond hArtPosSource)
            (frobDartAddGuardNegCond hIlkNegSource)
            (frobDartAddGuardPosCond hIlkPosSource)
            (by rfl) hRateMaxSource hDtabMulSource htabOverflow
        have hsrcFullRevert := hsourceRevertFromTabMul hsrcPrefixRevert
        obtain ⟨_, _, hDtabDone⟩ :=
          hthroughDtabEvm hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
            hRateMax hDtabMul
        have hrev := RD.vatFrobTabMulRevert
          (h := by simpa using hDtabDone)
          hTabMul
        exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel) hdecode
          hsrcFullRevert
    · have hbadRange : dtab < -((2 : Int) ^ 255) ∨ dtab ≥ (2 : Int) ^ 255 := by
        have hraw :=
          frobDtabBadRangeOfMulGuardFail
            (σ := σ_evm) (I := I) (ilkRate := ilkRate)
            (by simpa [ilkRate, vatSlotWord] using hIlkRateEq)
            hDtabMul
        change Int.ofNat ilkRate.toNat * frobDartInt I < -((2 : Int) ^ 255) ∨
          Int.ofNat ilkRate.toNat * frobDartInt I ≥ (2 : Int) ^ 255
        change Int.ofNat ilkRate.toNat * frobDartInt I < -((2 : Int) ^ 255) ∨
          Int.ofNat ilkRate.toNat * frobDartInt I ≥ (2 : Int) ^ 255 at hraw
        exact hraw
      have hsrcPrefixRevert :=
        execFrobLoadedPrefixDtabMulRevertRange
          (evm := evm0) (I := I)
          urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust dtab hsourcePrefix
          (frobDinkAddGuardNegCond hInkNegSource)
          (frobDinkAddGuardPosCond hInkPosSource)
          (frobDartAddGuardNegCond hArtNegSource)
          (frobDartAddGuardPosCond hArtPosSource)
          (frobDartAddGuardNegCond hIlkNegSource)
          (frobDartAddGuardPosCond hIlkPosSource)
          (by rfl) hbadRange
      have hsrcFullRevert := hsourceRevertFromDtabMul hsrcPrefixRevert
      obtain ⟨_, _, hIlkDone⟩ :=
        hthreeAddsEvm hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
      have hrev := RD.vatFrobDtabMulRevert
        (h := by simpa using hIlkDone)
        (Or.inr ⟨hRateMax, hDtabMul⟩)
      exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel) hdecode
        hsrcFullRevert
  · have hRateMaxSourceFail : UInt256.slt ilkRate ⟨0⟩ ≠ ⟨0⟩ := by
      intro hslt
      exact hRateMax (by
        simpa [ilkRate, vatSlotWord, hIlkRateEq] using hslt)
    have hsrcPrefixRevert :=
      execFrobLoadedPrefixDtabMulRevertMaxSlt
        (evm := evm0) (I := I)
        urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust dtab hsourcePrefix
        (frobDinkAddGuardNegCond hInkNegSource)
        (frobDinkAddGuardPosCond hInkPosSource)
        (frobDartAddGuardNegCond hArtNegSource)
        (frobDartAddGuardPosCond hArtPosSource)
        (frobDartAddGuardNegCond hIlkNegSource)
        (frobDartAddGuardPosCond hIlkPosSource)
        (by rfl) hRateMaxSourceFail
    have hsrcFullRevert := hsourceRevertFromDtabMul hsrcPrefixRevert
    obtain ⟨_, _, hIlkDone⟩ :=
      hthreeAddsEvm hInkNeg hInkPos hArtNeg hArtPos hIlkNeg hIlkPos
    have hrev := RD.vatFrobDtabMulRevert
      (h := by simpa using hIlkDone)
      (Or.inl hRateMax)
    exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel) hdecode
      hsrcFullRevert

set_option maxHeartbeats 0 in
theorem vatFrobBodyCoreLiveFinalArithmeticOverflowReverts
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (vatSelBytes 11))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz196 : 196 ≤ I.calldata.size)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (frobTransition.params.map Param.name)
        (transitionSignature frobTransition).paramTypes I.calldata = some (frobStore I))
    (hdecoded :
      ∃ k C,
        RD vatBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2975⟩
          [frobDartWord I, frobDinkWord I, frobWMaskedWord I, frobVMaskedWord I,
            frobUMaskedWord I, frobIWord I, ⟨524⟩, vatSelWord I]
          solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hlive : vatSlotWord ⟨10⟩ σ_evm I = ⟨1⟩)
    (hrateZeroEvm : ¬ solcSlotWord σ_evm I (frobIlkRateSlot I) = ⟨0⟩)
    (hArithmetic : frobLiveArithmeticPrefixGuards σ_evm I)
    (hDebtSafety : frobLiveDebtCeilingSafetyGuards σ_evm I)
    (hWishAuthDust : frobLiveWishAuthDustGuards σ_evm I)
    (hFinalArithmeticFail : ¬ frobLiveFinalArithmeticGuards σ_evm I) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  classical
  obtain ⟨_, _, hafterLive⟩ := vatFrobLiveOk
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (sel := vatSelWord I) hlive hdecoded
  let urnInk := vatSlotWord (frobUrnInkSlot I) σ_solm I
  let urnArt := vatSlotWord (frobUrnArtSlot I) σ_solm I
  let ilkArt := vatSlotWord (frobIlkArtSlot I) σ_solm I
  let ilkRate := vatSlotWord (frobIlkRateSlot I) σ_solm I
  let ilkSpot := vatSlotWord (frobIlkSpotSlot I) σ_solm I
  let ilkLine := vatSlotWord (frobIlkLineSlot I) σ_solm I
  let ilkDust := vatSlotWord (frobIlkDustSlot I) σ_solm I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveWord : vatSlotWord ⟨10⟩ σ_evm I = vatSlotWord ⟨10⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨10⟩ ⟨0⟩
  have hliveSolm : vatSlotWord ⟨10⟩ σ_solm I = ⟨1⟩ := by
    rw [← hliveWord]
    exact hlive
  have hrateWordNe :
      vatSlotWord (frobIlkRateSlot I) σ_solm I ≠ ⟨0⟩ := by
    intro hzeroSolm
    apply hrateZeroEvm
    have heq :
        vatSlotWord (frobIlkRateSlot I) σ_evm I =
          vatSlotWord (frobIlkRateSlot I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (frobIlkRateSlot I) ⟨0⟩
    simpa [vatSlotWord, hzeroSolm] using heq.trans hzeroSolm
  have hratePos : 0 < ilkRate.toNat := by
    have hnat : ilkRate.toNat ≠ 0 := by
      intro hzeroNat
      apply hrateWordNe
      apply u256_inj
      simp [ilkRate, hzeroNat]
    exact Nat.pos_of_ne_zero hnat
  have hsourcePrefixRaw :
      let locals := frobStore I
      let evm0' := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      ExecBlock config { contract := contract, locals := locals } evm0'
        (nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ])
        (.ok
          { contract := contract,
            locals :=
              frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust }
          evm0') := by
    exact vatFrobSourceRateNonzeroPrefix
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := g)
        (urnInk := urnInk) (urnArt := urnArt) (ilkArt := ilkArt)
        (ilkRate := ilkRate) (ilkSpot := ilkSpot) (ilkLine := ilkLine)
        (ilkDust := ilkDust)
        hwv hsz196 hliveSolm
        (by simpa [urnInk] using
          (frobSourceLoad_urnInk (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [urnArt] using
          (frobSourceLoad_urnArt (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkArt] using
          (frobSourceLoad_ilkArt (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkRate] using
          (frobSourceLoad_ilkRate (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkSpot] using
          (frobSourceLoad_ilkSpot (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkLine] using
          (frobSourceLoad_ilkLine (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkDust] using
          (frobSourceLoad_ilkDust (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        hratePos
  have hsourcePrefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm0
        (nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ])
        (.ok
          { contract := contract,
            locals :=
              frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust }
          evm0) := by
    simpa [evm0] using hsourcePrefixRaw
  obtain ⟨_, _, hafterUrn⟩ := RD.vatFrobUrnLoads hafterLive
  obtain ⟨_, _, hafterRateNonzero⟩ :=
    RD.vatFrobIlkLoadsRateNonzero hafterUrn hrateZeroEvm
  rcases hArithmetic with
    ⟨hInkNeg, hInkPos, hArtNeg, hArtPos, hIlkNeg, hIlkPos, hRateMax,
      hDtabMul, hTabMul⟩
  rcases hDebtSafety with
    ⟨hDebtNeg, hDebtPos, hCeilingMul, hCeilingOk, hDebtLoadStore, hInkMul,
      hSafetyOk⟩
  rcases hWishAuthDust with ⟨hU, hV, hW, hDust⟩
  obtain ⟨_, _, hInkDone⟩ :=
    RD.vatFrobUrnInkAddSuccess (h := hafterRateNonzero) hInkNeg hInkPos
  obtain ⟨_, _, hArtDone⟩ :=
    RD.vatFrobUrnArtAddSuccess (h := by simpa using hInkDone) hArtNeg hArtPos
  obtain ⟨_, _, hIlkDone⟩ :=
    RD.vatFrobIlkArtAddSuccess (h := by simpa using hArtDone) hIlkNeg hIlkPos
  obtain ⟨_, _, hDtabDone⟩ :=
    RD.vatFrobDtabMulSuccess (h := by simpa using hIlkDone) hRateMax hDtabMul
  obtain ⟨_, _, hTabDone⟩ :=
    RD.vatFrobTabMulSuccess
      (h := by simpa using hDtabDone)
      (urnArtNew := frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
      (ilkArtNew := frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
      (dtabWord :=
        UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)))
      (by simpa using hTabMul)
  obtain ⟨_, _, hDebtDone⟩ :=
    RD.vatFrobDebtAddStoreSuccess
      (h := by simpa using hTabDone)
      (hperm := hperm)
      (by simpa using hDebtNeg)
      (by simpa using hDebtPos)
  obtain ⟨_, _, hCeilingDone⟩ :=
    RD.vatFrobCeilingCheckSuccess
      (h := by simpa using hDebtDone)
      (by simpa using hCeilingMul)
      (by simpa using hCeilingOk)
      (by simpa [foldDebtSlot] using hDebtLoadStore)
  obtain ⟨_, _, hSafetyDone⟩ :=
    RD.vatFrobSafetyCheckSuccess
      (h := by simpa using hCeilingDone)
      (by simpa using hInkMul)
      (by simpa using hSafetyOk)
  have hUrnInkEq :
      solcSlotWord σ_evm I (frobUrnInkSlot I) =
        solcSlotWord σ_solm I (frobUrnInkSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobUrnInkSlot I) ⟨0⟩
  have hUrnArtEq :
      solcSlotWord σ_evm I (frobUrnArtSlot I) =
        solcSlotWord σ_solm I (frobUrnArtSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobUrnArtSlot I) ⟨0⟩
  have hIlkArtEq :
      solcSlotWord σ_evm I (frobIlkArtSlot I) =
        solcSlotWord σ_solm I (frobIlkArtSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkArtSlot I) ⟨0⟩
  have hIlkRateEq :
      solcSlotWord σ_evm I (frobIlkRateSlot I) =
        solcSlotWord σ_solm I (frobIlkRateSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkRateSlot I) ⟨0⟩
  have hDebtEq :
      solcSlotWord σ_evm I foldDebtSlot = solcSlotWord σ_solm I foldDebtSlot :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner foldDebtSlot ⟨0⟩
  have hIlkSpotEq :
      solcSlotWord σ_evm I (frobIlkSpotSlot I) =
        solcSlotWord σ_solm I (frobIlkSpotSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkSpotSlot I) ⟨0⟩
  have hIlkLineEq :
      solcSlotWord σ_evm I (frobIlkLineSlot I) =
        solcSlotWord σ_solm I (frobIlkLineSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkLineSlot I) ⟨0⟩
  have hIlkDustEq :
      solcSlotWord σ_evm I (frobIlkDustSlot I) =
        solcSlotWord σ_solm I (frobIlkDustSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkDustSlot I) ⟨0⟩
  have hLineEq : solcSlotWord σ_evm I ⟨9⟩ = solcSlotWord σ_solm I ⟨9⟩ :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨9⟩ ⟨0⟩
  let dtab : Int := Int.ofNat ilkRate.toNat * frobDartInt I
  let debtOld := vatSlotWord foldDebtSlot σ_solm I
  let dtabWord := UInt256.mul (frobDartWord I) ilkRate
  let debtNew := dtabWord + debtOld
  let Line := vatSlotWord ⟨9⟩ σ_solm I
  let urnInkNew := frobDinkWord I + urnInk
  let urnArtNew := frobDartWord I + urnArt
  let ilkArtNew := frobDartWord I + ilkArt
  let tab := UInt256.mul ilkRate urnArtNew
  let ceilingDebt := UInt256.mul ilkArtNew ilkRate
  let inkSpot := UInt256.mul urnInkNew ilkSpot
  let localsLoaded :=
    frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
  let localsIlk :=
    (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
        "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat)))
  let localsDtab := localsIlk.insert "dtab" (.int dtab)
  let localsTab := localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))
  let localsDebt := localsTab.insert "debtNew" (.int (Int.ofNat debtNew.toNat))
  let evmDebt := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner foldDebtSlot debtNew
  let localsSafe :=
    (localsDebt.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))).insert
      "inkSpot" (.int (Int.ofNat inkSpot.toNat))
  let uWish := vatSlotWord (frobUWishSlot I)
    (sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew) I
  let vWish := vatSlotWord (frobVWishSlot I)
    (sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew) I
  let wWish := vatSlotWord (frobWWishSlot I)
    (sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew) I
  have hInkNegSource :
      UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDinkWord I + urnInk) urnInk = ⟨0⟩ := by
    simpa [urnInk, vatSlotWord, hUrnInkEq] using hInkNeg
  have hInkPosSource :
      UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobDinkWord I + urnInk) urnInk = ⟨0⟩ := by
    simpa [urnInk, vatSlotWord, hUrnInkEq] using hInkPos
  have hArtNegSource :
      UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDartWord I + urnArt) urnArt = ⟨0⟩ := by
    simpa [urnArt, vatSlotWord, hUrnArtEq] using hArtNeg
  have hArtPosSource :
      UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobDartWord I + urnArt) urnArt = ⟨0⟩ := by
    simpa [urnArt, vatSlotWord, hUrnArtEq] using hArtPos
  have hIlkNegSource :
      UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDartWord I + ilkArt) ilkArt = ⟨0⟩ := by
    simpa [ilkArt, vatSlotWord, hIlkArtEq] using hIlkNeg
  have hIlkPosSource :
      UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobDartWord I + ilkArt) ilkArt = ⟨0⟩ := by
    simpa [ilkArt, vatSlotWord, hIlkArtEq] using hIlkPos
  have hRateMaxSource : UInt256.slt ilkRate ⟨0⟩ = ⟨0⟩ := by
    simpa [ilkRate, vatSlotWord, hIlkRateEq] using hRateMax
  have hDtabMulSource :
      frobDartWord I = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.sdiv (UInt256.mul (frobDartWord I) ilkRate)
            (frobDartWord I)) ilkRate ≠ ⟨0⟩ := by
    simpa [ilkRate, vatSlotWord, hIlkRateEq] using hDtabMul
  have hTabMulSource :
      urnArtNew = ⟨0⟩ ∨
        UInt256.eq (UInt256.div (UInt256.mul ilkRate urnArtNew) urnArtNew)
          ilkRate ≠ ⟨0⟩ := by
    simpa [urnArtNew, urnArt, ilkRate, vatSlotWord, hUrnArtEq, hIlkRateEq]
      using hTabMul
  have hDebtNegSource :
      UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt debtNew debtOld = ⟨0⟩ := by
    simpa [dtabWord, debtNew, debtOld, ilkRate, vatSlotWord, hIlkRateEq,
      hDebtEq] using hDebtNeg
  have hDebtPosSource :
      UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt debtNew debtOld = ⟨0⟩ := by
    simpa [dtabWord, debtNew, debtOld, ilkRate, vatSlotWord, hIlkRateEq,
      hDebtEq] using hDebtPos
  have hCeilingMulSource :
      ilkRate = ⟨0⟩ ∨
        UInt256.eq (UInt256.div (UInt256.mul ilkArtNew ilkRate) ilkRate)
          ilkArtNew ≠ ⟨0⟩ := by
    simpa [ilkArtNew, ilkArt, ilkRate, vatSlotWord, hIlkArtEq, hIlkRateEq]
      using hCeilingMul
  have hInkMulSource :
      ilkSpot = ⟨0⟩ ∨
        UInt256.eq (UInt256.div (UInt256.mul urnInkNew ilkSpot) ilkSpot)
          urnInkNew ≠ ⟨0⟩ := by
    simpa [urnInkNew, urnInk, ilkSpot, vatSlotWord, hUrnInkEq, hIlkSpotEq]
      using hInkMul
  have hCeilingOkSource :
      UInt256.lor
        (UInt256.land
          (UInt256.isZero (UInt256.gt debtNew Line))
          (UInt256.isZero (UInt256.gt ceilingDebt ilkLine)))
        (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) ≠ ⟨0⟩ := by
    simpa [ceilingDebt, debtNew, dtabWord, debtOld, Line, ilkArtNew, ilkArt,
      ilkRate, ilkLine, vatSlotWord, hIlkArtEq, hIlkRateEq, hIlkLineEq, hDebtEq,
      hLineEq] using hCeilingOk
  have hSafetyOkSource :
      UInt256.lor
        (UInt256.isZero (UInt256.gt tab inkSpot))
        (UInt256.land
          (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
          (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) ≠ ⟨0⟩ := by
    simpa [tab, inkSpot, urnInkNew, urnInk, urnArtNew, urnArt, ilkRate,
      ilkSpot, vatSlotWord, hUrnInkEq, hUrnArtEq, hIlkRateEq, hIlkSpotEq]
      using hSafetyOk
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner foldDebtSlot =
        debtOld := by
    simpa [evm0, debtOld, vatSlotWord, solcSlotWord, codeOwnerStorageWord] using
      (codeOwnerStorageWord_initState
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) foldDebtSlot)
  have hdtabMod :
      dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat := by
    change
      (Int.ofNat ilkRate.toNat * frobDartInt I) %
          (Int.ofNat EVM.wordModulus) =
        Int.ofNat (UInt256.mul (frobDartWord I) ilkRate).toNat
    exact frobDtab_mod_word I ilkRate
  have hlineLoad :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner foldDebtSlot debtNew)
          evm0.executionEnv.codeOwner ⟨9⟩ =
        Line := by
    have hne : (⟨9⟩ : UInt256) ≠ foldDebtSlot := by
      simp [foldDebtSlot]
    have hload0 :
        Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨9⟩ =
          Line := by
      simpa [evm0, Line, initState, vatSlotWord, solcSlotWord,
        codeOwnerStorageWord] using
        (codeOwnerStorageWord_initState
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
          (A := A) (I := I) (g := Sat256.ofUInt256 g) ⟨9⟩)
    have hstore :
        Solm.EVM.storageLoad
            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner foldDebtSlot debtNew)
            evm0.executionEnv.codeOwner ⟨9⟩ =
          Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨9⟩ :=
      storageLoad_storageStore_ne evm0 evm0.executionEnv.codeOwner hne
    exact hstore.trans hload0
  have hsourceSafety :
      ExecBlock config { contract := contract, locals := frobStore I } evm0
        ((nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
          checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
          checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
          checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
          checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
          checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
          checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
          [ .assign .storage debtRef (.var "debtNew") ] ++
          checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
          [ .require
              (eitherExpr
                (.binary .le (.var "dart") (.intLit 0))
                (bothExpr
                  (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                  (.binary .le (.var "debtNew") (.storage LineRef)))),
            .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (.binary .le (.var "tab") (.var "inkSpot"))) ])
        (.ok { contract := contract, locals := localsSafe } evmDebt) := by
    have hraw :=
      execFrobLoadedPrefixThroughSafetyOk
        (evm := evm0) (I := I)
        urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
        dtab debtOld debtNew dtabWord Line hsourcePrefix
        (frobDinkAddGuardNegCond hInkNegSource)
        (frobDinkAddGuardPosCond hInkPosSource)
        (frobDartAddGuardNegCond hArtNegSource)
        (frobDartAddGuardPosCond hArtPosSource)
        (frobDartAddGuardNegCond hIlkNegSource)
        (frobDartAddGuardPosCond hIlkPosSource)
        (by rfl) hRateMaxSource hDtabMulSource hTabMulSource
        hdebtLoad hdtabMod (by rfl) hDebtNegSource hDebtPosSource hlineLoad
        hCeilingMulSource (frobCeilingSourceCond_of_evm (I := I) hCeilingOkSource)
        hInkMulSource (frobSafetySourceCond_of_evm (I := I) hSafetyOkSource)
    simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk, localsDtab,
      tab, localsTab, localsDebt, evmDebt, ceilingDebt, inkSpot, localsSafe,
      List.append_assoc] using hraw
  have hUWishEq :
      vatSlotWord (frobUWishSlot I)
        (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
          (UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
            solcSlotWord σ_evm I foldDebtSlot)) I = uWish := by
    simpa [uWish, debtNew, dtabWord, debtOld, ilkRate, vatSlotWord, hIlkRateEq,
      hDebtEq] using
      (vatSlotWord_debtStore_accountMapEquiv
        (σ_evm := σ_evm) (σ_solm := σ_solm) (I := I) hAccounts
        (frobUWishSlot I) debtNew)
  have hVWishEq :
      vatSlotWord (frobVWishSlot I)
        (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
          (UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
            solcSlotWord σ_evm I foldDebtSlot)) I = vWish := by
    simpa [vWish, debtNew, dtabWord, debtOld, ilkRate, vatSlotWord, hIlkRateEq,
      hDebtEq] using
      (vatSlotWord_debtStore_accountMapEquiv
        (σ_evm := σ_evm) (σ_solm := σ_solm) (I := I) hAccounts
        (frobVWishSlot I) debtNew)
  have hWWishEq :
      vatSlotWord (frobWWishSlot I)
        (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
          (UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
            solcSlotWord σ_evm I foldDebtSlot)) I = wWish := by
    simpa [wWish, debtNew, dtabWord, debtOld, ilkRate, vatSlotWord, hIlkRateEq,
      hDebtEq] using
      (vatSlotWord_debtStore_accountMapEquiv
        (σ_evm := σ_evm) (σ_solm := σ_solm) (I := I) hAccounts
        (frobWWishSlot I) debtNew)
  have hloadU :
      Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
        (frobUWishSlot I) = uWish := by
    have hmap :
        evmDebt.accountMap =
          sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew := by
      simpa [evmDebt, evm0, initState] using
        storageStore_accountMap evm0 evm0.executionEnv.codeOwner foldDebtSlot debtNew
    change Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
        (frobUWishSlot I) =
      solcSlotWord (sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew) I
        (frobUWishSlot I)
    simp only [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
    rw [hmap]
    simp [solcSlotWord, evmDebt, evm0, initState, storageStore_executionEnv]
  have hloadV :
      Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
        (frobVWishSlot I) = vWish := by
    have hmap :
        evmDebt.accountMap =
          sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew := by
      simpa [evmDebt, evm0, initState] using
        storageStore_accountMap evm0 evm0.executionEnv.codeOwner foldDebtSlot debtNew
    change Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
        (frobVWishSlot I) =
      solcSlotWord (sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew) I
        (frobVWishSlot I)
    simp only [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
    rw [hmap]
    simp [solcSlotWord, evmDebt, evm0, initState, storageStore_executionEnv]
  have hloadW :
      Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
        (frobWWishSlot I) = wWish := by
    have hmap :
        evmDebt.accountMap =
          sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew := by
      simpa [evmDebt, evm0, initState] using
        storageStore_accountMap evm0 evm0.executionEnv.codeOwner foldDebtSlot debtNew
    change Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
        (frobWWishSlot I) =
      solcSlotWord (sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew) I
        (frobWWishSlot I)
    simp only [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
    rw [hmap]
    simp [solcSlotWord, evmDebt, evm0, initState, storageStore_executionEnv]
  have hsrcDebt : evmDebt.executionEnv.source = I.source := by
    simp [evmDebt, evm0, initState, storageStore_executionEnv]
  have hparam :=
    frobConstructedLocalsParamFacts (I := I) urnInk urnArt ilkArt ilkRate
      ilkSpot ilkLine ilkDust dtab debtOld dtabWord
  have hcomputed :=
    frobConstructedLocalsComputedFacts (I := I) urnInk urnArt ilkArt ilkRate
      ilkSpot ilkLine ilkDust dtab debtOld dtabWord
  have hilks :=
    frobConstructedLocalsIlkFacts (I := I) urnInk urnArt ilkArt ilkRate
      ilkSpot ilkLine ilkDust dtab debtOld dtabWord
  have hbase :=
    frobConstructedLocalsBaseFacts (I := I) urnInk urnArt ilkArt ilkRate
      ilkSpot ilkLine ilkDust dtab debtOld dtabWord
  have hextras :=
    frobConstructedLocalsAuthDustExtras (I := I) urnInk urnArt ilkArt ilkRate
      ilkSpot ilkLine ilkDust dtab debtOld dtabWord
  rcases hparam with ⟨hsafeI, hsafeU, hsafeV, hsafeW, hsafeDink⟩
  rcases hcomputed with
    ⟨hsafeDtab, _hsafeUrnInkNew, hsafeUrnArtNew, _hsafeIlkArtNew⟩
  rcases hilks with ⟨_hsafeIlkRate, _hsafeIlkSpot, _hsafeIlkLine, hsafeIlkDust⟩
  rcases hbase with ⟨hsafeBaseGem, hsafeBaseDai, _hsafeBaseUrns, _hsafeBaseIlks⟩
  rcases hextras with ⟨hsafeDart, hsafeTab, hsafeBaseCan⟩
  have hUOk :=
    frobAuthUSourceCond_of_evm (I := I) (uWish := uWish) (by
      simpa [uWish, hUWishEq] using hU)
  have hVOk :=
    frobAuthVSourceCond_of_evm (I := I) (vWish := vWish) (by
      simpa [vWish, hVWishEq] using hV)
  have hWOk :=
    frobAuthWSourceCond_of_evm (I := I) (wWish := wWish) (by
      simpa [wWish, hWWishEq] using hW)
  have hDustSource :
      UInt256.lor
        (UInt256.isZero (UInt256.lt tab ilkDust))
        (UInt256.eq ⟨0⟩ urnArtNew) ≠ ⟨0⟩ := by
    simpa [tab, urnArtNew, urnArt, ilkRate, ilkDust, vatSlotWord,
      hUrnArtEq, hIlkRateEq, hIlkDustEq] using hDust
  have hDustOk := frobDustSourceCond_of_evm hDustSource
  have hauthDust :
      ExecBlock config { contract := contract, locals := localsSafe } evmDebt
        [ .require
            (eitherExpr
              (bothExpr
                (.binary .le (.var "dart") (.intLit 0))
                (.binary .ge (.var "dink") (.intLit 0)))
              (wishExpr (.var "u") sender)),
          .require
            (eitherExpr (.binary .le (.var "dink") (.intLit 0))
              (wishExpr (.var "v") sender)),
          .require
            (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
              (wishExpr (.var "w") sender)),
          .require
            (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
              (.binary .ge (.var "tab") (.var "ilkDust"))) ]
        (.ok { contract := contract, locals := localsSafe } evmDebt) := by
    exact execFrobAuthorizationDustOk_from_sourceConds
      (evm := evmDebt) (I := I) (locals := localsSafe)
      uWish vWish wWish urnArtNew tab ilkDust
      hsafeDart hsafeDink hsafeU hsafeV hsafeW hsafeBaseCan hsrcDebt
      hloadU hloadV hloadW hsafeUrnArtNew hsafeTab hsafeIlkDust
      hUOk hVOk hWOk hDustOk
  have hsourceDust :
      ExecBlock config { contract := contract, locals := frobStore I } evm0
        ((nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
          checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
          checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
          checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
          checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
          checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
          checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
          [ .assign .storage debtRef (.var "debtNew") ] ++
          checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
          [ .require
              (eitherExpr
                (.binary .le (.var "dart") (.intLit 0))
                (bothExpr
                  (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                  (.binary .le (.var "debtNew") (.storage LineRef)))),
            .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (.binary .le (.var "tab") (.var "inkSpot"))) ] ++
          [ .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (wishExpr (.var "u") sender)),
            .require
              (eitherExpr (.binary .le (.var "dink") (.intLit 0))
                (wishExpr (.var "v") sender)),
            .require
              (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
                (wishExpr (.var "w") sender)),
            .require
              (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
                (.binary .ge (.var "tab") (.var "ilkDust"))) ])
        (.ok { contract := contract, locals := localsSafe } evmDebt) := by
    have hprefix := Reasoning.Refinement.execBlock_append hsourceSafety hauthDust
    simpa [List.append_assoc] using hprefix
  obtain ⟨_, _, hDustDone⟩ :=
    RD.vatFrobAuthorizationDustChecksSuccess
      (h := by simpa using hSafetyDone)
      (by simpa [foldDebtSlot] using hU)
      (by simpa [foldDebtSlot] using hV)
      (by simpa [foldDebtSlot] using hW)
      (by simpa [foldDebtSlot] using hDust)
  let gemOld := solcSlotWord (frobAfterDebt σ_solm I) I (frobGemVSlot I)
  let gemNew := frobGemNew σ_solm I
  have hdtabRange :=
    frobDtabRangeOfMulGuard (I := I) (ilkRate := ilkRate) hRateMaxSource
      hDtabMulSource
  have hDebtAccounts :
      accountMapEquiv (frobAfterDebt σ_evm I) (frobAfterDebt σ_solm I) :=
    accountMapEquiv_frobAfterDebt (I := I) hAccounts
  have hGemOldEq :
      solcSlotWord (frobAfterDebt σ_evm I) I (frobGemVSlot I) = gemOld :=
    accountMapEquiv_storage_findD hDebtAccounts I.codeOwner (frobGemVSlot I) ⟨0⟩
  have hGemNewEq : frobGemNew σ_evm I = gemNew := by
    simp [gemNew, frobGemNew, gemOld, hGemOldEq]
  have hloadGem :
      Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
        (frobGemVSourceSlot I) = gemOld := by
    simp [evmDebt, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, storageStore_accountMap, storageStore_executionEnv,
      frobAfterDebt, frobDebtNew, gemOld, debtNew, dtabWord, debtOld,
      frobDtabWord, ilkRate, vatSlotWord, frobGemVSourceSlot_eq I hsz196]
  have hmemDustSize :
      (twoWordHashMem (hopeSourceWord I)
        (solcMappingSlot ⟨1⟩ (frobWMaskedWord I))
        (twoWordHashMem (frobWMaskedWord I) ⟨1⟩
          (twoWordHashMem (hopeSourceWord I)
            (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
            (twoWordHashMem (frobVMaskedWord I) ⟨1⟩
              (twoWordHashMem (hopeSourceWord I)
                (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
                (twoWordHashMem (frobUMaskedWord I) ⟨1⟩
                  (frobIlkArtUpdatedMem σ_evm I
                    (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
                    (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
                    (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))))))))).size =
        576 := by
    exact twoWordHashMem_size_576 (hopeSourceWord I)
      (solcMappingSlot ⟨1⟩ (frobWMaskedWord I))
      (twoWordHashMem_size_576 (frobWMaskedWord I) ⟨1⟩
        (twoWordHashMem_size_576 (hopeSourceWord I)
          (solcMappingSlot ⟨1⟩ (frobVMaskedWord I))
          (twoWordHashMem_size_576 (frobVMaskedWord I) ⟨1⟩
            (twoWordHashMem_size_576 (hopeSourceWord I)
              (solcMappingSlot ⟨1⟩ (frobUMaskedWord I))
              (twoWordHashMem_size_576 (frobUMaskedWord I) ⟨1⟩
                (frobIlkArtUpdatedMem_size σ_evm I
                  (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
                  (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
                  (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))))))))
  by_cases hGemPos :
      UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobGemNew σ_evm I)
          (solcSlotWord (frobAfterDebt σ_evm I) I (frobGemVSlot I)) = ⟨0⟩
  · by_cases hGemNeg :
      UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobGemNew σ_evm I)
          (solcSlotWord (frobAfterDebt σ_evm I) I (frobGemVSlot I)) = ⟨0⟩
    · let evmGem :=
        Solm.EVM.storageStore evmDebt evmDebt.executionEnv.codeOwner
          (frobGemVSourceSlot I) gemNew
      let localsGem := localsSafe.insert "gemNew" (.int (Int.ofNat gemNew.toNat))
      let daiOld := solcSlotWord (frobAfterGem σ_solm I) I (frobDaiWSlot I)
      let daiNew := frobDaiNew σ_solm I
      have hGemPosS :
          UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
            UInt256.gt gemNew gemOld = ⟨0⟩ := by
        simpa [gemNew, gemOld, hGemNewEq, hGemOldEq] using hGemPos
      have hGemNegS :
          UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
            UInt256.lt gemNew gemOld = ⟨0⟩ := by
        simpa [gemNew, gemOld, hGemNewEq, hGemOldEq] using hGemNeg
      have hgemDone :
          ExecBlock config { contract := contract, locals := localsSafe } evmDebt
            (checkedSubSignedInto "gemNew"
                (.storage (gemRef (.var "i") (.var "v"))) (.var "dink") ++
              [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ])
            (.ok { contract := contract, locals := localsGem } evmGem) := by
        simpa [localsGem, evmGem] using
          execFrobGemUpdateOk (evm := evmDebt) (I := I) localsSafe
            gemOld gemNew hsz196 hsafeI hsafeV hsafeDink hsafeBaseGem hloadGem
            (by simp [gemNew, gemOld, frobGemNew])
            (frobDinkSubGuardNegCond hGemPosS)
            (frobDinkSubGuardPosCond hGemNegS)
      obtain ⟨_, _, hGemDoneEvm⟩ :=
        RD.vatFrobGemSubSuccess
          (h := by
            simpa [frobTabWord, frobDtabWord, frobUrnInkNew, frobUrnArtNew,
              frobIlkArtNew, frobAfterDebt, frobDebtNew, foldDebtSlot] using
              hDustDone)
          (by rw [hmemDustSize]; omega)
          (by simpa [frobGemNew, frobAfterDebt, frobDebtNew, foldDebtSlot]
            using hGemPos)
          (by simpa [frobGemNew, frobAfterDebt, frobDebtNew, foldDebtSlot]
            using hGemNeg)
      have hAfterGemAccounts :
          accountMapEquiv (frobAfterGem σ_evm I) (frobAfterGem σ_solm I) :=
        accountMapEquiv_frobAfterGem (I := I) hAccounts
      have hDaiOldEq :
          solcSlotWord (frobAfterGem σ_evm I) I (frobDaiWSlot I) = daiOld :=
        accountMapEquiv_storage_findD hAfterGemAccounts I.codeOwner
          (frobDaiWSlot I) ⟨0⟩
      have hDtabEq : frobDtabWord σ_evm I = dtabWord := by
        simp [frobDtabWord, dtabWord, ilkRate, vatSlotWord, hIlkRateEq]
      have hDaiNewEq : frobDaiNew σ_evm I = daiNew := by
        calc
          frobDaiNew σ_evm I =
              frobDtabWord σ_evm I +
                solcSlotWord (frobAfterGem σ_evm I) I (frobDaiWSlot I) := by
            rfl
          _ = dtabWord + daiOld := by
            rw [hDtabEq, hDaiOldEq]
          _ = daiNew := by
            simp [daiNew, frobDaiNew, daiOld, dtabWord, frobDtabWord, ilkRate,
              vatSlotWord, frobAfterGem]
      have hloadDai :
          Solm.EVM.storageLoad evmGem evmGem.executionEnv.codeOwner
            (frobDaiWSourceSlot I) = daiOld := by
        simp [evmGem, evmDebt, evm0, initState, Solm.EVM.storageLoad,
          State.lookupAccount, Account.lookupStorage, storageStore_accountMap,
          storageStore_executionEnv, frobAfterGem, frobAfterDebt, frobDebtNew,
          frobGemNew, gemNew, daiOld, debtNew, dtabWord, debtOld,
          frobDtabWord, ilkRate, vatSlotWord, frobGemVSourceSlot_eq I hsz196,
          frobDaiWSourceSlot_eq I]
      by_cases hDaiNeg :
          UInt256.slt (frobDtabWord σ_evm I) ⟨0⟩ = ⟨0⟩ ∨
            UInt256.gt (frobDaiNew σ_evm I)
              (solcSlotWord (frobAfterGem σ_evm I) I (frobDaiWSlot I)) = ⟨0⟩
      · by_cases hDaiPos :
          UInt256.sgt (frobDtabWord σ_evm I) ⟨0⟩ = ⟨0⟩ ∨
            UInt256.lt (frobDaiNew σ_evm I)
              (solcSlotWord (frobAfterGem σ_evm I) I (frobDaiWSlot I)) = ⟨0⟩
        · have hFinal : frobLiveFinalArithmeticGuards σ_evm I := by
            unfold frobLiveFinalArithmeticGuards
            exact ⟨hGemPos, hGemNeg, hDaiNeg, hDaiPos⟩
          exact False.elim (hFinalArithmeticFail hFinal)
        · have hDaiNegS :
            UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
              UInt256.gt daiNew daiOld = ⟨0⟩ := by
            simpa [dtabWord, daiNew, daiOld, hDtabEq, hDaiNewEq, hDaiOldEq]
              using hDaiNeg
          have hDaiPosSFail :
              ¬ (UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
                UInt256.lt daiNew daiOld = ⟨0⟩) := by
            intro h
            exact hDaiPos (by
              simpa [dtabWord, daiNew, daiOld, hDtabEq, hDaiNewEq, hDaiOldEq]
                using h)
          have hrev := RD.vatFrobGemStoreDaiAddRevert
            (h := by
              simpa [frobGemNew, frobAfterDebt, frobDebtNew, foldDebtSlot] using
                hGemDoneEvm)
            (by
              exact twoWordHashMem_twoWordHashMem_ge64
                (frobVMaskedWord I) (solcMappingSlot ⟨4⟩ (frobIWord I))
                (frobIWord I) ⟨4⟩ (by rw [hmemDustSize]; omega))
            hperm
            (Or.inr ⟨by
              simpa [daiNew, dtabWord, gemNew, frobAfterGem] using hDaiNeg, by
              intro h
              exact hDaiPos (by
                simpa [daiNew, dtabWord, gemNew, frobAfterGem] using h)⟩)
          have hdaiRevert :
              ExecBlock config { contract := contract, locals := localsGem } evmGem
                (checkedAddSignedInto "daiNew"
                  (.storage (daiRef (.var "w"))) (.var "dtab"))
                .reverted := by
            exact execFrobDaiAddCheckedRevertGuardPos
              (evm := evmGem) (I := I) localsGem daiOld daiNew dtabWord dtab
              (by
                change (localsSafe.insert "gemNew"
                  (.int (Int.ofNat gemNew.toNat))).get? "w" =
                  some (frobWValue I)
                rw [store_get_ne _ _ (by decide)]
                exact hsafeW)
              (by
                change (localsSafe.insert "gemNew"
                  (.int (Int.ofNat gemNew.toNat))).get? "dtab" =
                  some (.int dtab)
                rw [store_get_ne _ _ (by decide)]
                exact hsafeDtab)
              (by
                change (localsSafe.insert "gemNew"
                  (.int (Int.ofNat gemNew.toNat))).get? "dai" = none
                rw [store_get_ne _ _ (by decide)]
                exact hsafeBaseDai)
              (by simpa [evmGem] using hloadDai)
              hdtabMod
              (by rfl)
              hDaiNegS hDaiPosSFail hdtabRange.1 hdtabRange.2
          have htail := execFrobFinalStoreTailDaiRevertFromBlock hgemDone hdaiRevert
          exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel) hdecode
            (hsourceRevertFromFinalStoreTail hsourceDust htail)
      · have hDaiNegSFail :
            ¬ (UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
              UInt256.gt daiNew daiOld = ⟨0⟩) := by
          intro h
          exact hDaiNeg (by
            simpa [dtabWord, daiNew, daiOld, hDtabEq, hDaiNewEq, hDaiOldEq] using h)
        have hrev := RD.vatFrobGemStoreDaiAddRevert
          (h := by
            simpa [frobGemNew, frobAfterDebt, frobDebtNew, foldDebtSlot] using
              hGemDoneEvm)
          (by
            exact twoWordHashMem_twoWordHashMem_ge64
              (frobVMaskedWord I) (solcMappingSlot ⟨4⟩ (frobIWord I))
              (frobIWord I) ⟨4⟩ (by rw [hmemDustSize]; omega))
          hperm
          (Or.inl (by
            intro h
            exact hDaiNeg (by
              simpa [daiNew, dtabWord, gemNew, frobAfterGem] using h)))
        have hdaiRevert :
            ExecBlock config { contract := contract, locals := localsGem } evmGem
              (checkedAddSignedInto "daiNew"
                (.storage (daiRef (.var "w"))) (.var "dtab"))
              .reverted := by
          exact execFrobDaiAddCheckedRevertGuardNeg
            (evm := evmGem) (I := I) localsGem daiOld daiNew dtabWord dtab
            (by
              change (localsSafe.insert "gemNew"
                (.int (Int.ofNat gemNew.toNat))).get? "w" =
                some (frobWValue I)
              rw [store_get_ne _ _ (by decide)]
              exact hsafeW)
            (by
              change (localsSafe.insert "gemNew"
                (.int (Int.ofNat gemNew.toNat))).get? "dtab" =
                some (.int dtab)
              rw [store_get_ne _ _ (by decide)]
              exact hsafeDtab)
            (by
              change (localsSafe.insert "gemNew"
                (.int (Int.ofNat gemNew.toNat))).get? "dai" = none
              rw [store_get_ne _ _ (by decide)]
              exact hsafeBaseDai)
            (by simpa [evmGem] using hloadDai)
            hdtabMod
            (by rfl)
            hDaiNegSFail hdtabRange.1 hdtabRange.2
        have htail := execFrobFinalStoreTailDaiRevertFromBlock hgemDone hdaiRevert
        exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel) hdecode
          (hsourceRevertFromFinalStoreTail hsourceDust htail)
    · have hGemPosS :
        UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt gemNew gemOld = ⟨0⟩ := by
        simpa [gemNew, gemOld, hGemNewEq, hGemOldEq] using hGemPos
      have hGemNegSFail :
          ¬ (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
            UInt256.lt gemNew gemOld = ⟨0⟩) := by
        intro h
        exact hGemNeg (by simpa [gemNew, gemOld, hGemNewEq, hGemOldEq] using h)
      have hrev := RD.vatFrobGemSubRevert
        (h := by
          simpa [frobTabWord, frobDtabWord, frobUrnInkNew, frobUrnArtNew,
            frobIlkArtNew, frobAfterDebt, frobDebtNew, foldDebtSlot] using
            hDustDone)
        (by rw [hmemDustSize]; omega)
        (Or.inr ⟨by
          simpa [frobGemNew, frobAfterDebt, frobDebtNew, foldDebtSlot] using hGemPos,
          by
            simpa [frobGemNew, frobAfterDebt, frobDebtNew, foldDebtSlot] using
              hGemNeg⟩)
      have hgemRevert :
          ExecBlock config { contract := contract, locals := localsSafe } evmDebt
            (checkedSubSignedInto "gemNew"
              (.storage (gemRef (.var "i") (.var "v"))) (.var "dink"))
            .reverted := by
        exact execFrobGemSubCheckedRevertGuardPos
          (evm := evmDebt) (I := I) localsSafe gemOld gemNew hsz196
          hsafeI hsafeV hsafeDink hsafeBaseGem hloadGem
          (by simp [gemNew, gemOld, frobGemNew])
          hGemPosS hGemNegSFail
      have htail := execFrobFinalStoreTailGemRevertFromBlock hgemRevert
      exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel) hdecode
        (hsourceRevertFromFinalStoreTail hsourceDust htail)
  · have hGemPosSFail :
        ¬ (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt gemNew gemOld = ⟨0⟩) := by
      intro h
      exact hGemPos (by simpa [gemNew, gemOld, hGemNewEq, hGemOldEq] using h)
    have hrev := RD.vatFrobGemSubRevert
      (h := by
        simpa [frobTabWord, frobDtabWord, frobUrnInkNew, frobUrnArtNew,
          frobIlkArtNew, frobAfterDebt, frobDebtNew, foldDebtSlot] using
          hDustDone)
      (by rw [hmemDustSize]; omega)
      (Or.inl (by
        simpa [frobGemNew, frobAfterDebt, frobDebtNew, foldDebtSlot] using hGemPos))
    have hgemRevert :
        ExecBlock config { contract := contract, locals := localsSafe } evmDebt
          (checkedSubSignedInto "gemNew"
            (.storage (gemRef (.var "i") (.var "v"))) (.var "dink"))
          .reverted := by
      exact execFrobGemSubCheckedRevertGuardNeg
        (evm := evmDebt) (I := I) localsSafe gemOld gemNew hsz196
        hsafeI hsafeV hsafeDink hsafeBaseGem hloadGem
        (by simp [gemNew, gemOld, frobGemNew])
        hGemPosSFail
    have htail := execFrobFinalStoreTailGemRevertFromBlock hgemRevert
    exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel) hdecode
      (hsourceRevertFromFinalStoreTail hsourceDust htail)

set_option maxHeartbeats 0 in
theorem vatFrobBodyCoreLiveArithmeticOverflowReverts
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (vatSelBytes 11))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz196 : 196 ≤ I.calldata.size)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (frobTransition.params.map Param.name)
        (transitionSignature frobTransition).paramTypes I.calldata = some (frobStore I))
    (hdecoded :
      ∃ k C,
        RD vatBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2975⟩
          [frobDartWord I, frobDinkWord I, frobWMaskedWord I, frobVMaskedWord I,
            frobUMaskedWord I, frobIWord I, ⟨524⟩, vatSelWord I]
          solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hlive : vatSlotWord ⟨10⟩ σ_evm I = ⟨1⟩)
    (hrateZeroEvm : ¬ solcSlotWord σ_evm I (frobIlkRateSlot I) = ⟨0⟩)
    (hArithmeticFail : ¬ frobLiveArithmeticPrefixGuards σ_evm I) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  classical
  by_cases hAdd : frobLiveAddArithmeticGuards σ_evm I
  · by_cases hMul : frobLiveMulArithmeticGuards σ_evm I
    · have hArithmetic : frobLiveArithmeticPrefixGuards σ_evm I :=
        frobLiveArithmeticPrefixGuards_of_add_mul hAdd hMul
      exact False.elim (hArithmeticFail hArithmetic)
    · exact vatFrobBodyCoreLiveMulOverflowReverts
        (hcode := hcode) (hwv := hwv)
        (hsel := hsel) (hAccounts := hAccounts) (hsz196 := hsz196)
        (hdecode := hdecode) (hdecoded := hdecoded) (hlive := hlive)
        (hrateZeroEvm := hrateZeroEvm) (hAdd := hAdd) (hMulFail := hMul)
  · exact vatFrobBodyCoreLiveAddOverflowReverts
      (hcode := hcode) (hwv := hwv) (hsel := hsel)
      (hAccounts := hAccounts) (hsz196 := hsz196)
      (hdecode := hdecode) (hdecoded := hdecoded) (hlive := hlive)
      (hrateZeroEvm := hrateZeroEvm) (hAddFail := hAdd)

set_option maxHeartbeats 0 in
theorem vatFrobBodyCoreLiveDebtCeilingSafetyReverts
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (vatSelBytes 11))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz196 : 196 ≤ I.calldata.size)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (frobTransition.params.map Param.name)
        (transitionSignature frobTransition).paramTypes I.calldata = some (frobStore I))
    (hdecoded :
      ∃ k C,
        RD vatBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2975⟩
          [frobDartWord I, frobDinkWord I, frobWMaskedWord I, frobVMaskedWord I,
            frobUMaskedWord I, frobIWord I, ⟨524⟩, vatSelWord I]
          solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hlive : vatSlotWord ⟨10⟩ σ_evm I = ⟨1⟩)
    (hrateZeroEvm : ¬ solcSlotWord σ_evm I (frobIlkRateSlot I) = ⟨0⟩)
    (hArithmetic : frobLiveArithmeticPrefixGuards σ_evm I)
    (hDebtSafetyFail : ¬ frobLiveDebtCeilingSafetyGuards σ_evm I) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  classical
  obtain ⟨_, _, hafterLive⟩ := vatFrobLiveOk
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (sel := vatSelWord I) hlive hdecoded
  let urnInk := vatSlotWord (frobUrnInkSlot I) σ_solm I
  let urnArt := vatSlotWord (frobUrnArtSlot I) σ_solm I
  let ilkArt := vatSlotWord (frobIlkArtSlot I) σ_solm I
  let ilkRate := vatSlotWord (frobIlkRateSlot I) σ_solm I
  let ilkSpot := vatSlotWord (frobIlkSpotSlot I) σ_solm I
  let ilkLine := vatSlotWord (frobIlkLineSlot I) σ_solm I
  let ilkDust := vatSlotWord (frobIlkDustSlot I) σ_solm I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveWord : vatSlotWord ⟨10⟩ σ_evm I = vatSlotWord ⟨10⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨10⟩ ⟨0⟩
  have hliveSolm : vatSlotWord ⟨10⟩ σ_solm I = ⟨1⟩ := by
    rw [← hliveWord]
    exact hlive
  have hrateWordNe :
      vatSlotWord (frobIlkRateSlot I) σ_solm I ≠ ⟨0⟩ := by
    intro hzeroSolm
    apply hrateZeroEvm
    have heq :
        vatSlotWord (frobIlkRateSlot I) σ_evm I =
          vatSlotWord (frobIlkRateSlot I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (frobIlkRateSlot I) ⟨0⟩
    simpa [vatSlotWord, hzeroSolm] using heq.trans hzeroSolm
  have hratePos : 0 < ilkRate.toNat := by
    have hnat : ilkRate.toNat ≠ 0 := by
      intro hzeroNat
      apply hrateWordNe
      apply u256_inj
      simp [ilkRate, hzeroNat]
    exact Nat.pos_of_ne_zero hnat
  have hsourcePrefixRaw :
      let locals := frobStore I
      let evm0' := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      ExecBlock config { contract := contract, locals := locals } evm0'
        (nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ])
        (.ok
          { contract := contract,
            locals :=
              frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust }
          evm0') := by
    exact vatFrobSourceRateNonzeroPrefix
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := g)
        (urnInk := urnInk) (urnArt := urnArt) (ilkArt := ilkArt)
        (ilkRate := ilkRate) (ilkSpot := ilkSpot) (ilkLine := ilkLine)
        (ilkDust := ilkDust)
        hwv hsz196 hliveSolm
        (by simpa [urnInk] using
          (frobSourceLoad_urnInk (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [urnArt] using
          (frobSourceLoad_urnArt (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkArt] using
          (frobSourceLoad_ilkArt (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkRate] using
          (frobSourceLoad_ilkRate (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkSpot] using
          (frobSourceLoad_ilkSpot (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkLine] using
          (frobSourceLoad_ilkLine (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkDust] using
          (frobSourceLoad_ilkDust (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        hratePos
  have hsourcePrefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm0
        (nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ])
        (.ok
          { contract := contract,
            locals :=
              frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust }
          evm0) := by
    simpa [evm0] using hsourcePrefixRaw
  obtain ⟨_, _, hafterUrn⟩ := RD.vatFrobUrnLoads hafterLive
  obtain ⟨_, _, hafterRateNonzero⟩ :=
    RD.vatFrobIlkLoadsRateNonzero hafterUrn hrateZeroEvm
  rcases hArithmetic with
    ⟨hInkNeg, hInkPos, hArtNeg, hArtPos, hIlkNeg, hIlkPos, hRateMax,
      hDtabMul, hTabMul⟩
  obtain ⟨_, _, hInkDone⟩ :=
    RD.vatFrobUrnInkAddSuccess (h := hafterRateNonzero) hInkNeg hInkPos
  obtain ⟨_, _, hArtDone⟩ :=
    RD.vatFrobUrnArtAddSuccess (h := by simpa using hInkDone) hArtNeg hArtPos
  obtain ⟨_, _, hIlkDone⟩ :=
    RD.vatFrobIlkArtAddSuccess (h := by simpa using hArtDone) hIlkNeg hIlkPos
  obtain ⟨_, _, hDtabDone⟩ :=
    RD.vatFrobDtabMulSuccess (h := by simpa using hIlkDone) hRateMax hDtabMul
  obtain ⟨_, _, hTabDone⟩ :=
    RD.vatFrobTabMulSuccess
      (h := by simpa using hDtabDone)
      (urnArtNew := frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
      (ilkArtNew := frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
      (dtabWord :=
        UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)))
      (by simpa using hTabMul)
  have hUrnInkEq :
      solcSlotWord σ_evm I (frobUrnInkSlot I) =
        solcSlotWord σ_solm I (frobUrnInkSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobUrnInkSlot I) ⟨0⟩
  have hUrnArtEq :
      solcSlotWord σ_evm I (frobUrnArtSlot I) =
        solcSlotWord σ_solm I (frobUrnArtSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobUrnArtSlot I) ⟨0⟩
  have hIlkArtEq :
      solcSlotWord σ_evm I (frobIlkArtSlot I) =
        solcSlotWord σ_solm I (frobIlkArtSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkArtSlot I) ⟨0⟩
  have hIlkRateEq :
      solcSlotWord σ_evm I (frobIlkRateSlot I) =
        solcSlotWord σ_solm I (frobIlkRateSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkRateSlot I) ⟨0⟩
  have hDebtEq :
      solcSlotWord σ_evm I foldDebtSlot = solcSlotWord σ_solm I foldDebtSlot :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner foldDebtSlot ⟨0⟩
  have hIlkSpotEq :
      solcSlotWord σ_evm I (frobIlkSpotSlot I) =
        solcSlotWord σ_solm I (frobIlkSpotSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkSpotSlot I) ⟨0⟩
  have hIlkLineEq :
      solcSlotWord σ_evm I (frobIlkLineSlot I) =
        solcSlotWord σ_solm I (frobIlkLineSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkLineSlot I) ⟨0⟩
  have hLineEq : solcSlotWord σ_evm I ⟨9⟩ = solcSlotWord σ_solm I ⟨9⟩ :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨9⟩ ⟨0⟩
  let dtab : Int := Int.ofNat ilkRate.toNat * frobDartInt I
  let debtOld := vatSlotWord foldDebtSlot σ_solm I
  let dtabWord := UInt256.mul (frobDartWord I) ilkRate
  let debtNew := dtabWord + debtOld
  let Line := vatSlotWord ⟨9⟩ σ_solm I
  let urnInkNew := frobDinkWord I + urnInk
  let urnArtNew := frobDartWord I + urnArt
  let ilkArtNew := frobDartWord I + ilkArt
  let tab := UInt256.mul ilkRate urnArtNew
  let ceilingDebt := UInt256.mul ilkArtNew ilkRate
  let inkSpot := UInt256.mul urnInkNew ilkSpot
  have hInkNegSource :
      UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDinkWord I + urnInk) urnInk = ⟨0⟩ := by
    simpa [urnInk, vatSlotWord, hUrnInkEq] using hInkNeg
  have hInkPosSource :
      UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobDinkWord I + urnInk) urnInk = ⟨0⟩ := by
    simpa [urnInk, vatSlotWord, hUrnInkEq] using hInkPos
  have hArtNegSource :
      UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDartWord I + urnArt) urnArt = ⟨0⟩ := by
    simpa [urnArt, vatSlotWord, hUrnArtEq] using hArtNeg
  have hArtPosSource :
      UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobDartWord I + urnArt) urnArt = ⟨0⟩ := by
    simpa [urnArt, vatSlotWord, hUrnArtEq] using hArtPos
  have hIlkNegSource :
      UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDartWord I + ilkArt) ilkArt = ⟨0⟩ := by
    simpa [ilkArt, vatSlotWord, hIlkArtEq] using hIlkNeg
  have hIlkPosSource :
      UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobDartWord I + ilkArt) ilkArt = ⟨0⟩ := by
    simpa [ilkArt, vatSlotWord, hIlkArtEq] using hIlkPos
  have hRateMaxSource : UInt256.slt ilkRate ⟨0⟩ = ⟨0⟩ := by
    simpa [ilkRate, vatSlotWord, hIlkRateEq] using hRateMax
  have hDtabMulSource :
      frobDartWord I = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.sdiv (UInt256.mul (frobDartWord I) ilkRate)
            (frobDartWord I)) ilkRate ≠ ⟨0⟩ := by
    simpa [ilkRate, vatSlotWord, hIlkRateEq] using hDtabMul
  have hTabMulSource :
      urnArtNew = ⟨0⟩ ∨
        UInt256.eq (UInt256.div (UInt256.mul ilkRate urnArtNew) urnArtNew)
          ilkRate ≠ ⟨0⟩ := by
    simpa [urnArtNew, urnArt, ilkRate, vatSlotWord, hUrnArtEq, hIlkRateEq]
      using hTabMul
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner foldDebtSlot =
        debtOld := by
    simpa [evm0, debtOld, vatSlotWord, solcSlotWord, codeOwnerStorageWord] using
      (codeOwnerStorageWord_initState
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) foldDebtSlot)
  have hdtabMod :
      dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat := by
    change
      (Int.ofNat ilkRate.toNat * frobDartInt I) %
          (Int.ofNat EVM.wordModulus) =
        Int.ofNat (UInt256.mul (frobDartWord I) ilkRate).toNat
    exact frobDtab_mod_word I ilkRate
  have hlineLoad :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner foldDebtSlot debtNew)
          evm0.executionEnv.codeOwner ⟨9⟩ =
        Line := by
    have hne : (⟨9⟩ : UInt256) ≠ foldDebtSlot := by
      simp [foldDebtSlot]
    have hload0 :
        Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨9⟩ =
          Line := by
      simpa [evm0, Line, initState, vatSlotWord, solcSlotWord,
        codeOwnerStorageWord] using
        (codeOwnerStorageWord_initState
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
          (A := A) (I := I) (g := Sat256.ofUInt256 g) ⟨9⟩)
    have hstore :
        Solm.EVM.storageLoad
            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner foldDebtSlot debtNew)
            evm0.executionEnv.codeOwner ⟨9⟩ =
          Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨9⟩ :=
      storageLoad_storageStore_ne evm0 evm0.executionEnv.codeOwner hne
    exact hstore.trans hload0
  have hDebtLoadStore :
      (((sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
        (UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
          solcSlotWord σ_evm I foldDebtSlot)).find? I.codeOwner).option
          (default : UInt256)
          (fun acc => acc.storage.findD (⟨7⟩ : UInt256) (default : UInt256))) =
        (UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
          solcSlotWord σ_evm I foldDebtSlot) := by
    have hpresent : σ_evm.find? I.codeOwner ≠ none := by
      intro hmissing
      apply hrateZeroEvm
      simp [solcSlotWord, hmissing, Option.option]
    obtain ⟨acc, hacc⟩ := Option.ne_none_iff_exists'.mp hpresent
    simpa [foldDebtSlot] using
      sstoreAccountMap_storage_findD_self_present σ_evm I.codeOwner hacc
        foldDebtSlot
        (UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
          solcSlotWord σ_evm I foldDebtSlot)
  by_cases hDebtNeg :
      UInt256.slt
          (UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)))
          ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
            solcSlotWord σ_evm I foldDebtSlot)
          (solcSlotWord σ_evm I foldDebtSlot) = ⟨0⟩
  · have hDebtNegSource :
        UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt debtNew debtOld = ⟨0⟩ := by
      simpa [dtabWord, debtNew, debtOld, ilkRate, vatSlotWord, hIlkRateEq,
        hDebtEq] using hDebtNeg
    by_cases hDebtPos :
        UInt256.sgt
            (UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)))
            ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
              solcSlotWord σ_evm I foldDebtSlot)
            (solcSlotWord σ_evm I foldDebtSlot) = ⟨0⟩
    · have hDebtPosSource :
          UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
            UInt256.lt debtNew debtOld = ⟨0⟩ := by
        simpa [dtabWord, debtNew, debtOld, ilkRate, vatSlotWord, hIlkRateEq,
          hDebtEq] using hDebtPos
      obtain ⟨_, _, hDebtDone⟩ :=
        RD.vatFrobDebtAddStoreSuccess
          (h := by simpa using hTabDone)
          (hperm := hperm)
          (by simpa using hDebtNeg)
          (by simpa using hDebtPos)
      by_cases hCeilingMul :
          solcSlotWord σ_evm I (frobIlkRateSlot I) = ⟨0⟩ ∨
            UInt256.eq
              (UInt256.div
                (UInt256.mul
                  (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
                  (solcSlotWord σ_evm I (frobIlkRateSlot I)))
                (solcSlotWord σ_evm I (frobIlkRateSlot I)))
              (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I)) ≠
                ⟨0⟩
      · have hCeilingMulSource :
            ilkRate = ⟨0⟩ ∨
              UInt256.eq (UInt256.div (UInt256.mul ilkArtNew ilkRate) ilkRate)
                ilkArtNew ≠ ⟨0⟩ := by
          simpa [ilkArtNew, ilkArt, ilkRate, vatSlotWord, hIlkArtEq, hIlkRateEq]
            using hCeilingMul
        by_cases hCeilingOk :
            UInt256.lor
              (UInt256.land
                (UInt256.isZero
                  (UInt256.gt
                    (UInt256.mul (frobDartWord I)
                      (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                    solcSlotWord σ_evm I foldDebtSlot)
                    (solcSlotWord σ_evm I ⟨9⟩)))
                (UInt256.isZero
                  (UInt256.gt
                    (UInt256.mul
                      (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
                      (solcSlotWord σ_evm I (frobIlkRateSlot I)))
                    (solcSlotWord σ_evm I (frobIlkLineSlot I)))))
              (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) ≠ ⟨0⟩
        · have hCeilingOkSource :
              UInt256.lor
                (UInt256.land
                  (UInt256.isZero (UInt256.gt debtNew Line))
                  (UInt256.isZero (UInt256.gt ceilingDebt ilkLine)))
                (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) ≠
                  ⟨0⟩ := by
            simpa [ceilingDebt, debtNew, dtabWord, debtOld, Line, ilkArtNew,
              ilkArt, ilkRate, ilkLine, vatSlotWord, hIlkArtEq, hIlkRateEq,
              hIlkLineEq, hDebtEq, hLineEq] using hCeilingOk
          obtain ⟨_, _, hCeilingDone⟩ :=
            RD.vatFrobCeilingCheckSuccess
              (h := by simpa using hDebtDone)
              (by simpa using hCeilingMul)
              (by simpa using hCeilingOk)
              (by simpa [foldDebtSlot] using hDebtLoadStore)
          by_cases hInkMul :
              solcSlotWord σ_evm I (frobIlkSpotSlot I) = ⟨0⟩ ∨
                UInt256.eq
                  (UInt256.div
                    (UInt256.mul
                      (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
                      (solcSlotWord σ_evm I (frobIlkSpotSlot I)))
                    (solcSlotWord σ_evm I (frobIlkSpotSlot I)))
                  (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I)) ≠
                    ⟨0⟩
          · have hInkMulSource :
                ilkSpot = ⟨0⟩ ∨
                  UInt256.eq (UInt256.div (UInt256.mul urnInkNew ilkSpot) ilkSpot)
                    urnInkNew ≠ ⟨0⟩ := by
              simpa [urnInkNew, urnInk, ilkSpot, vatSlotWord, hUrnInkEq,
                hIlkSpotEq] using hInkMul
            by_cases hSafetyOk :
                UInt256.lor
                  (UInt256.isZero
                    (UInt256.gt
                      (UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                        (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
                      (UInt256.mul
                        (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
                        (solcSlotWord σ_evm I (frobIlkSpotSlot I)))))
                  (UInt256.land
                    (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
                    (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) ≠ ⟨0⟩
            · have hDebtSafety : frobLiveDebtCeilingSafetyGuards σ_evm I := by
                unfold frobLiveDebtCeilingSafetyGuards
                exact ⟨hDebtNeg, hDebtPos, hCeilingMul, hCeilingOk,
                  hDebtLoadStore, hInkMul, hSafetyOk⟩
              exact False.elim (hDebtSafetyFail hDebtSafety)
            · have hSafetyOkZero :
                  UInt256.lor
                    (UInt256.isZero
                      (UInt256.gt
                        (UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                          (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
                        (UInt256.mul
                          (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
                          (solcSlotWord σ_evm I (frobIlkSpotSlot I)))))
                    (UInt256.land
                      (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
                      (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) =
                    ⟨0⟩ := by
                by_contra hne
                exact hSafetyOk hne
              have hSafetyOkSourceZero :
                  UInt256.lor
                    (UInt256.isZero (UInt256.gt tab inkSpot))
                    (UInt256.land
                      (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
                      (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) =
                    ⟨0⟩ := by
                simpa [tab, inkSpot, urnInkNew, urnInk, urnArtNew, urnArt, ilkRate,
                  ilkSpot, vatSlotWord, hUrnInkEq, hUrnArtEq, hIlkRateEq,
                  hIlkSpotEq] using hSafetyOkZero
              have hSafetyBad :=
                frobSafetySourceFalseCond_of_evm (I := I) hSafetyOkSourceZero
              have hCeilingReq :=
                frobCeilingSourceCond_of_evm (I := I) hCeilingOkSource
              have hsrcPrefixRevert :=
                execFrobLoadedPrefixSafetyRequireRevert
                  (evm := evm0) (I := I)
                  urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
                  dtab debtOld debtNew dtabWord Line hsourcePrefix
                  (frobDinkAddGuardNegCond hInkNegSource)
                  (frobDinkAddGuardPosCond hInkPosSource)
                  (frobDartAddGuardNegCond hArtNegSource)
                  (frobDartAddGuardPosCond hArtPosSource)
                  (frobDartAddGuardNegCond hIlkNegSource)
                  (frobDartAddGuardPosCond hIlkPosSource)
                  (by rfl) hRateMaxSource hDtabMulSource hTabMulSource
                  hdebtLoad hdtabMod (by rfl) hDebtNegSource hDebtPosSource
                  hlineLoad hCeilingMulSource hCeilingReq hInkMulSource
                  hSafetyBad
              have hsrcFullRevert := hsourceRevertFromSafetyRequire hsrcPrefixRevert
              have hrev := RD.vatFrobSafetyCheckRevert
                (h := by simpa using hCeilingDone)
                (by simpa using hInkMul)
                (by simpa [tab, inkSpot, urnInkNew, urnInk, urnArtNew, urnArt,
                  ilkRate, ilkSpot, vatSlotWord, hUrnInkEq, hUrnArtEq,
                  hIlkRateEq, hIlkSpotEq] using hSafetyOkZero)
              exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel)
                hdecode hsrcFullRevert
          · have hInkMulSourceFail :
                ¬ (ilkSpot = ⟨0⟩ ∨
                  UInt256.eq (UInt256.div (UInt256.mul urnInkNew ilkSpot) ilkSpot)
                    urnInkNew ≠ ⟨0⟩) := by
              intro hsrc
              exact hInkMul (by
                simpa [urnInkNew, urnInk, ilkSpot, vatSlotWord, hUrnInkEq,
                  hIlkSpotEq] using hsrc)
            have hInkOverflow := uintCheckedMulFail_to_overflow hInkMulSourceFail
            have hsrcPrefixRevert :=
              execFrobLoadedPrefixInkSpotMulRevertOverflow
                (evm := evm0) (I := I)
                urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
                dtab debtOld debtNew dtabWord hsourcePrefix
                (frobDinkAddGuardNegCond hInkNegSource)
                (frobDinkAddGuardPosCond hInkPosSource)
                (frobDartAddGuardNegCond hArtNegSource)
                (frobDartAddGuardPosCond hArtPosSource)
                (frobDartAddGuardNegCond hIlkNegSource)
                (frobDartAddGuardPosCond hIlkPosSource)
                (by rfl) hRateMaxSource hDtabMulSource hTabMulSource
                hdebtLoad hdtabMod (by rfl) hDebtNegSource hDebtPosSource
                hCeilingMulSource hInkOverflow
            have hsrcFullRevert := hsourceRevertFromInkSpotMul hsrcPrefixRevert
            have hrev := RD.vatFrobInkSpotMulRevert
              (h := by simpa using hCeilingDone)
              (by
                intro hsrc
                exact hInkMul (by
                  simpa [urnInkNew, urnInk, ilkSpot, vatSlotWord, hUrnInkEq,
                    hIlkSpotEq] using hsrc))
            exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel)
              hdecode hsrcFullRevert
        · have hCeilingOkZero :
              UInt256.lor
                (UInt256.land
                  (UInt256.isZero
                    (UInt256.gt
                      (UInt256.mul (frobDartWord I)
                        (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                      solcSlotWord σ_evm I foldDebtSlot)
                      (solcSlotWord σ_evm I ⟨9⟩)))
                  (UInt256.isZero
                    (UInt256.gt
                      (UInt256.mul
                        (frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
                        (solcSlotWord σ_evm I (frobIlkRateSlot I)))
                      (solcSlotWord σ_evm I (frobIlkLineSlot I)))))
                (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) =
                ⟨0⟩ := by
            by_contra hne
            exact hCeilingOk hne
          have hrev := RD.vatFrobCeilingCheckRevert
            (h := by simpa using hDebtDone)
            (by simpa using hCeilingMul)
            (by simpa [debtNew, dtabWord, debtOld, ilkArtNew, ilkArt, ilkRate,
              vatSlotWord, hIlkArtEq, hIlkRateEq, hDebtEq] using hCeilingOkZero)
            (by simpa [foldDebtSlot] using hDebtLoadStore)
          by_cases hInkMul :
              solcSlotWord σ_evm I (frobIlkSpotSlot I) = ⟨0⟩ ∨
                UInt256.eq
                  (UInt256.div
                    (UInt256.mul
                      (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I))
                      (solcSlotWord σ_evm I (frobIlkSpotSlot I)))
                    (solcSlotWord σ_evm I (frobIlkSpotSlot I)))
                  (frobDinkWord I + solcSlotWord σ_evm I (frobUrnInkSlot I)) ≠
                    ⟨0⟩
          · have hInkMulSource :
                ilkSpot = ⟨0⟩ ∨
                  UInt256.eq (UInt256.div (UInt256.mul urnInkNew ilkSpot) ilkSpot)
                    urnInkNew ≠ ⟨0⟩ := by
              simpa [urnInkNew, urnInk, ilkSpot, vatSlotWord, hUrnInkEq,
                hIlkSpotEq] using hInkMul
            have hCeilingOkSourceZero :
                UInt256.lor
                  (UInt256.land
                    (UInt256.isZero (UInt256.gt debtNew Line))
                    (UInt256.isZero (UInt256.gt ceilingDebt ilkLine)))
                  (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) =
                  ⟨0⟩ := by
              simpa [ceilingDebt, debtNew, dtabWord, debtOld, Line, ilkArtNew,
                ilkArt, ilkRate, ilkLine, vatSlotWord, hIlkArtEq, hIlkRateEq,
                hIlkLineEq, hDebtEq, hLineEq] using hCeilingOkZero
            have hCeilingBad :=
              frobCeilingSourceFalseCond_of_evm (I := I) hCeilingOkSourceZero
            have hsrcPrefixRevert :=
              execFrobLoadedPrefixCeilingRequireRevert
                (evm := evm0) (I := I)
                urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
                dtab debtOld debtNew dtabWord Line hsourcePrefix
                (frobDinkAddGuardNegCond hInkNegSource)
                (frobDinkAddGuardPosCond hInkPosSource)
                (frobDartAddGuardNegCond hArtNegSource)
                (frobDartAddGuardPosCond hArtPosSource)
                (frobDartAddGuardNegCond hIlkNegSource)
                (frobDartAddGuardPosCond hIlkPosSource)
                (by rfl) hRateMaxSource hDtabMulSource hTabMulSource
                hdebtLoad hdtabMod (by rfl) hDebtNegSource hDebtPosSource
                hlineLoad hCeilingMulSource hInkMulSource hCeilingBad
            have hsrcFullRevert := hsourceRevertFromCeilingRequire hsrcPrefixRevert
            exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel)
              hdecode hsrcFullRevert
          · have hInkMulSourceFail :
                ¬ (ilkSpot = ⟨0⟩ ∨
                  UInt256.eq (UInt256.div (UInt256.mul urnInkNew ilkSpot) ilkSpot)
                    urnInkNew ≠ ⟨0⟩) := by
              intro hsrc
              exact hInkMul (by
                simpa [urnInkNew, urnInk, ilkSpot, vatSlotWord, hUrnInkEq,
                  hIlkSpotEq] using hsrc)
            have hInkOverflow := uintCheckedMulFail_to_overflow hInkMulSourceFail
            have hsrcPrefixRevert :=
              execFrobLoadedPrefixInkSpotMulRevertOverflow
                (evm := evm0) (I := I)
                urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
                dtab debtOld debtNew dtabWord hsourcePrefix
                (frobDinkAddGuardNegCond hInkNegSource)
                (frobDinkAddGuardPosCond hInkPosSource)
                (frobDartAddGuardNegCond hArtNegSource)
                (frobDartAddGuardPosCond hArtPosSource)
                (frobDartAddGuardNegCond hIlkNegSource)
                (frobDartAddGuardPosCond hIlkPosSource)
                (by rfl) hRateMaxSource hDtabMulSource hTabMulSource
                hdebtLoad hdtabMod (by rfl) hDebtNegSource hDebtPosSource
                hCeilingMulSource hInkOverflow
            have hsrcFullRevert := hsourceRevertFromInkSpotMul hsrcPrefixRevert
            exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel)
              hdecode hsrcFullRevert
      · have hCeilingMulSourceFail :
            ¬ (ilkRate = ⟨0⟩ ∨
              UInt256.eq (UInt256.div (UInt256.mul ilkArtNew ilkRate) ilkRate)
                ilkArtNew ≠ ⟨0⟩) := by
          intro hsrc
          exact hCeilingMul (by
            simpa [ilkArtNew, ilkArt, ilkRate, vatSlotWord, hIlkArtEq, hIlkRateEq]
              using hsrc)
        have hCeilingOverflow := uintCheckedMulFail_to_overflow hCeilingMulSourceFail
        have hsrcPrefixRevert :=
          execFrobLoadedPrefixCeilingMulRevertOverflow
            (evm := evm0) (I := I)
            urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
            dtab debtOld debtNew dtabWord hsourcePrefix
            (frobDinkAddGuardNegCond hInkNegSource)
            (frobDinkAddGuardPosCond hInkPosSource)
            (frobDartAddGuardNegCond hArtNegSource)
            (frobDartAddGuardPosCond hArtPosSource)
            (frobDartAddGuardNegCond hIlkNegSource)
            (frobDartAddGuardPosCond hIlkPosSource)
            (by rfl) hRateMaxSource hDtabMulSource hTabMulSource
            hdebtLoad hdtabMod (by rfl) hDebtNegSource hDebtPosSource
            hCeilingOverflow
        have hsrcFullRevert := hsourceRevertFromCeilingMul hsrcPrefixRevert
        have hrev := RD.vatFrobCeilingMulRevert
          (h := by simpa using hDebtDone)
          hCeilingMul
        exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel)
          hdecode hsrcFullRevert
    · have hDebtPosSourceFail :
          ¬ (UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
            UInt256.lt debtNew debtOld = ⟨0⟩) := by
        intro hsrc
        exact hDebtPos (by
          simpa [dtabWord, debtNew, debtOld, ilkRate, vatSlotWord, hIlkRateEq,
            hDebtEq] using hsrc)
      have hsrcPrefixRevert :=
        execFrobLoadedPrefixDebtAddRevertGuardPos
          (evm := evm0) (I := I)
          urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
          dtab debtOld debtNew dtabWord hsourcePrefix
          (frobDinkAddGuardNegCond hInkNegSource)
          (frobDinkAddGuardPosCond hInkPosSource)
          (frobDartAddGuardNegCond hArtNegSource)
          (frobDartAddGuardPosCond hArtPosSource)
          (frobDartAddGuardNegCond hIlkNegSource)
          (frobDartAddGuardPosCond hIlkPosSource)
          (by rfl) hRateMaxSource hDtabMulSource hTabMulSource
          hdebtLoad hdtabMod (by rfl) hDebtNegSource hDebtPosSourceFail
      have hsrcFullRevert := hsourceRevertFromDebtAdd hsrcPrefixRevert
      have hrev := RD.vatFrobDebtAddStoreRevert
        (h := by simpa using hTabDone)
        (Or.inr ⟨hDebtNeg, hDebtPos⟩)
      exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel)
        hdecode hsrcFullRevert
  · have hDebtNegSourceFail :
        ¬ (UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
          UInt256.gt debtNew debtOld = ⟨0⟩) := by
      intro hsrc
      exact hDebtNeg (by
        simpa [dtabWord, debtNew, debtOld, ilkRate, vatSlotWord, hIlkRateEq,
          hDebtEq] using hsrc)
    have hsrcPrefixRevert :=
      execFrobLoadedPrefixDebtAddRevertGuardNeg
        (evm := evm0) (I := I)
        urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
        dtab debtOld debtNew dtabWord hsourcePrefix
        (frobDinkAddGuardNegCond hInkNegSource)
        (frobDinkAddGuardPosCond hInkPosSource)
        (frobDartAddGuardNegCond hArtNegSource)
        (frobDartAddGuardPosCond hArtPosSource)
        (frobDartAddGuardNegCond hIlkNegSource)
        (frobDartAddGuardPosCond hIlkPosSource)
        (by rfl) hRateMaxSource hDtabMulSource hTabMulSource
        hdebtLoad hdtabMod (by rfl) hDebtNegSourceFail
    have hsrcFullRevert := hsourceRevertFromDebtAdd hsrcPrefixRevert
    have hrev := RD.vatFrobDebtAddStoreRevert
      (h := by simpa using hTabDone)
      (Or.inl hDebtNeg)
    exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel)
      hdecode hsrcFullRevert

set_option maxHeartbeats 0 in
theorem vatFrobBodyCoreLiveWishAuthDustReverts
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (vatSelBytes 11))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz196 : 196 ≤ I.calldata.size)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (frobTransition.params.map Param.name)
        (transitionSignature frobTransition).paramTypes I.calldata = some (frobStore I))
    (hdecoded :
      ∃ k C,
        RD vatBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2975⟩
          [frobDartWord I, frobDinkWord I, frobWMaskedWord I, frobVMaskedWord I,
            frobUMaskedWord I, frobIWord I, ⟨524⟩, vatSelWord I]
          solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hlive : vatSlotWord ⟨10⟩ σ_evm I = ⟨1⟩)
    (hrateZeroEvm : ¬ solcSlotWord σ_evm I (frobIlkRateSlot I) = ⟨0⟩)
    (hArithmetic : frobLiveArithmeticPrefixGuards σ_evm I)
    (hDebtSafety : frobLiveDebtCeilingSafetyGuards σ_evm I)
    (hWishAuthDustFail : ¬ frobLiveWishAuthDustGuards σ_evm I) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  classical
  obtain ⟨_, _, hafterLive⟩ := vatFrobLiveOk
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (sel := vatSelWord I) hlive hdecoded
  let urnInk := vatSlotWord (frobUrnInkSlot I) σ_solm I
  let urnArt := vatSlotWord (frobUrnArtSlot I) σ_solm I
  let ilkArt := vatSlotWord (frobIlkArtSlot I) σ_solm I
  let ilkRate := vatSlotWord (frobIlkRateSlot I) σ_solm I
  let ilkSpot := vatSlotWord (frobIlkSpotSlot I) σ_solm I
  let ilkLine := vatSlotWord (frobIlkLineSlot I) σ_solm I
  let ilkDust := vatSlotWord (frobIlkDustSlot I) σ_solm I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveWord : vatSlotWord ⟨10⟩ σ_evm I = vatSlotWord ⟨10⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨10⟩ ⟨0⟩
  have hliveSolm : vatSlotWord ⟨10⟩ σ_solm I = ⟨1⟩ := by
    rw [← hliveWord]
    exact hlive
  have hrateWordNe :
      vatSlotWord (frobIlkRateSlot I) σ_solm I ≠ ⟨0⟩ := by
    intro hzeroSolm
    apply hrateZeroEvm
    have heq :
        vatSlotWord (frobIlkRateSlot I) σ_evm I =
          vatSlotWord (frobIlkRateSlot I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (frobIlkRateSlot I) ⟨0⟩
    simpa [vatSlotWord, hzeroSolm] using heq.trans hzeroSolm
  have hratePos : 0 < ilkRate.toNat := by
    have hnat : ilkRate.toNat ≠ 0 := by
      intro hzeroNat
      apply hrateWordNe
      apply u256_inj
      simp [ilkRate, hzeroNat]
    exact Nat.pos_of_ne_zero hnat
  have hsourcePrefixRaw :
      let locals := frobStore I
      let evm0' := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      ExecBlock config { contract := contract, locals := locals } evm0'
        (nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ])
        (.ok
          { contract := contract,
            locals :=
              frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust }
          evm0') := by
    exact vatFrobSourceRateNonzeroPrefix
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := g)
        (urnInk := urnInk) (urnArt := urnArt) (ilkArt := ilkArt)
        (ilkRate := ilkRate) (ilkSpot := ilkSpot) (ilkLine := ilkLine)
        (ilkDust := ilkDust)
        hwv hsz196 hliveSolm
        (by simpa [urnInk] using
          (frobSourceLoad_urnInk (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [urnArt] using
          (frobSourceLoad_urnArt (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkArt] using
          (frobSourceLoad_ilkArt (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkRate] using
          (frobSourceLoad_ilkRate (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkSpot] using
          (frobSourceLoad_ilkSpot (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkLine] using
          (frobSourceLoad_ilkLine (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        (by simpa [ilkDust] using
          (frobSourceLoad_ilkDust (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
        hratePos
  have hsourcePrefix :
      ExecBlock config { contract := contract, locals := frobStore I } evm0
        (nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ])
        (.ok
          { contract := contract,
            locals :=
              frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust }
          evm0) := by
    simpa [evm0] using hsourcePrefixRaw
  obtain ⟨_, _, hafterUrn⟩ := RD.vatFrobUrnLoads hafterLive
  obtain ⟨_, _, hafterRateNonzero⟩ :=
    RD.vatFrobIlkLoadsRateNonzero hafterUrn hrateZeroEvm
  rcases hArithmetic with
    ⟨hInkNeg, hInkPos, hArtNeg, hArtPos, hIlkNeg, hIlkPos, hRateMax,
      hDtabMul, hTabMul⟩
  rcases hDebtSafety with
    ⟨hDebtNeg, hDebtPos, hCeilingMul, hCeilingOk, hDebtLoadStore, hInkMul,
      hSafetyOk⟩
  obtain ⟨_, _, hInkDone⟩ :=
    RD.vatFrobUrnInkAddSuccess (h := hafterRateNonzero) hInkNeg hInkPos
  obtain ⟨_, _, hArtDone⟩ :=
    RD.vatFrobUrnArtAddSuccess (h := by simpa using hInkDone) hArtNeg hArtPos
  obtain ⟨_, _, hIlkDone⟩ :=
    RD.vatFrobIlkArtAddSuccess (h := by simpa using hArtDone) hIlkNeg hIlkPos
  obtain ⟨_, _, hDtabDone⟩ :=
    RD.vatFrobDtabMulSuccess (h := by simpa using hIlkDone) hRateMax hDtabMul
  obtain ⟨_, _, hTabDone⟩ :=
    RD.vatFrobTabMulSuccess
      (h := by simpa using hDtabDone)
      (urnArtNew := frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))
      (ilkArtNew := frobDartWord I + solcSlotWord σ_evm I (frobIlkArtSlot I))
      (dtabWord :=
        UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)))
      (by simpa using hTabMul)
  obtain ⟨_, _, hDebtDone⟩ :=
    RD.vatFrobDebtAddStoreSuccess
      (h := by simpa using hTabDone)
      (hperm := hperm)
      (by simpa using hDebtNeg)
      (by simpa using hDebtPos)
  obtain ⟨_, _, hCeilingDone⟩ :=
    RD.vatFrobCeilingCheckSuccess
      (h := by simpa using hDebtDone)
      (by simpa using hCeilingMul)
      (by simpa using hCeilingOk)
      (by simpa [foldDebtSlot] using hDebtLoadStore)
  obtain ⟨_, _, hSafetyDone⟩ :=
    RD.vatFrobSafetyCheckSuccess
      (h := by simpa using hCeilingDone)
      (by simpa using hInkMul)
      (by simpa using hSafetyOk)
  have hUrnInkEq :
      solcSlotWord σ_evm I (frobUrnInkSlot I) =
        solcSlotWord σ_solm I (frobUrnInkSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobUrnInkSlot I) ⟨0⟩
  have hUrnArtEq :
      solcSlotWord σ_evm I (frobUrnArtSlot I) =
        solcSlotWord σ_solm I (frobUrnArtSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobUrnArtSlot I) ⟨0⟩
  have hIlkArtEq :
      solcSlotWord σ_evm I (frobIlkArtSlot I) =
        solcSlotWord σ_solm I (frobIlkArtSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkArtSlot I) ⟨0⟩
  have hIlkRateEq :
      solcSlotWord σ_evm I (frobIlkRateSlot I) =
        solcSlotWord σ_solm I (frobIlkRateSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkRateSlot I) ⟨0⟩
  have hDebtEq :
      solcSlotWord σ_evm I foldDebtSlot = solcSlotWord σ_solm I foldDebtSlot :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner foldDebtSlot ⟨0⟩
  have hIlkSpotEq :
      solcSlotWord σ_evm I (frobIlkSpotSlot I) =
        solcSlotWord σ_solm I (frobIlkSpotSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkSpotSlot I) ⟨0⟩
  have hIlkLineEq :
      solcSlotWord σ_evm I (frobIlkLineSlot I) =
        solcSlotWord σ_solm I (frobIlkLineSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkLineSlot I) ⟨0⟩
  have hIlkDustEq :
      solcSlotWord σ_evm I (frobIlkDustSlot I) =
        solcSlotWord σ_solm I (frobIlkDustSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (frobIlkDustSlot I) ⟨0⟩
  have hLineEq : solcSlotWord σ_evm I ⟨9⟩ = solcSlotWord σ_solm I ⟨9⟩ :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨9⟩ ⟨0⟩
  let dtab : Int := Int.ofNat ilkRate.toNat * frobDartInt I
  let debtOld := vatSlotWord foldDebtSlot σ_solm I
  let dtabWord := UInt256.mul (frobDartWord I) ilkRate
  let debtNew := dtabWord + debtOld
  let Line := vatSlotWord ⟨9⟩ σ_solm I
  let urnInkNew := frobDinkWord I + urnInk
  let urnArtNew := frobDartWord I + urnArt
  let ilkArtNew := frobDartWord I + ilkArt
  let tab := UInt256.mul ilkRate urnArtNew
  let ceilingDebt := UInt256.mul ilkArtNew ilkRate
  let inkSpot := UInt256.mul urnInkNew ilkSpot
  let localsLoaded :=
    frobStoreIlkDust I urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
  let localsIlk :=
    (((localsLoaded.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).insert
        "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat)))
  let localsDtab := localsIlk.insert "dtab" (.int dtab)
  let localsTab := localsDtab.insert "tab" (.int (Int.ofNat tab.toNat))
  let localsDebt := localsTab.insert "debtNew" (.int (Int.ofNat debtNew.toNat))
  let evmDebt := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner foldDebtSlot debtNew
  let localsSafe :=
    (localsDebt.insert "ceilingDebt" (.int (Int.ofNat ceilingDebt.toNat))).insert
      "inkSpot" (.int (Int.ofNat inkSpot.toNat))
  let uWish := vatSlotWord (frobUWishSlot I)
    (sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew) I
  let vWish := vatSlotWord (frobVWishSlot I)
    (sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew) I
  let wWish := vatSlotWord (frobWWishSlot I)
    (sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew) I
  have hInkNegSource :
      UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDinkWord I + urnInk) urnInk = ⟨0⟩ := by
    simpa [urnInk, vatSlotWord, hUrnInkEq] using hInkNeg
  have hInkPosSource :
      UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobDinkWord I + urnInk) urnInk = ⟨0⟩ := by
    simpa [urnInk, vatSlotWord, hUrnInkEq] using hInkPos
  have hArtNegSource :
      UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDartWord I + urnArt) urnArt = ⟨0⟩ := by
    simpa [urnArt, vatSlotWord, hUrnArtEq] using hArtNeg
  have hArtPosSource :
      UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobDartWord I + urnArt) urnArt = ⟨0⟩ := by
    simpa [urnArt, vatSlotWord, hUrnArtEq] using hArtPos
  have hIlkNegSource :
      UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (frobDartWord I + ilkArt) ilkArt = ⟨0⟩ := by
    simpa [ilkArt, vatSlotWord, hIlkArtEq] using hIlkNeg
  have hIlkPosSource :
      UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (frobDartWord I + ilkArt) ilkArt = ⟨0⟩ := by
    simpa [ilkArt, vatSlotWord, hIlkArtEq] using hIlkPos
  have hRateMaxSource : UInt256.slt ilkRate ⟨0⟩ = ⟨0⟩ := by
    simpa [ilkRate, vatSlotWord, hIlkRateEq] using hRateMax
  have hDtabMulSource :
      frobDartWord I = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.sdiv (UInt256.mul (frobDartWord I) ilkRate)
            (frobDartWord I)) ilkRate ≠ ⟨0⟩ := by
    simpa [ilkRate, vatSlotWord, hIlkRateEq] using hDtabMul
  have hTabMulSource :
      urnArtNew = ⟨0⟩ ∨
        UInt256.eq (UInt256.div (UInt256.mul ilkRate urnArtNew) urnArtNew)
          ilkRate ≠ ⟨0⟩ := by
    simpa [urnArtNew, urnArt, ilkRate, vatSlotWord, hUrnArtEq, hIlkRateEq]
      using hTabMul
  have hDebtNegSource :
      UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt debtNew debtOld = ⟨0⟩ := by
    simpa [dtabWord, debtNew, debtOld, ilkRate, vatSlotWord, hIlkRateEq,
      hDebtEq] using hDebtNeg
  have hDebtPosSource :
      UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt debtNew debtOld = ⟨0⟩ := by
    simpa [dtabWord, debtNew, debtOld, ilkRate, vatSlotWord, hIlkRateEq,
      hDebtEq] using hDebtPos
  have hCeilingMulSource :
      ilkRate = ⟨0⟩ ∨
        UInt256.eq (UInt256.div (UInt256.mul ilkArtNew ilkRate) ilkRate)
          ilkArtNew ≠ ⟨0⟩ := by
    simpa [ilkArtNew, ilkArt, ilkRate, vatSlotWord, hIlkArtEq, hIlkRateEq]
      using hCeilingMul
  have hInkMulSource :
      ilkSpot = ⟨0⟩ ∨
        UInt256.eq (UInt256.div (UInt256.mul urnInkNew ilkSpot) ilkSpot)
          urnInkNew ≠ ⟨0⟩ := by
    simpa [urnInkNew, urnInk, ilkSpot, vatSlotWord, hUrnInkEq, hIlkSpotEq]
      using hInkMul
  have hCeilingOkSource :
      UInt256.lor
        (UInt256.land
          (UInt256.isZero (UInt256.gt debtNew Line))
          (UInt256.isZero (UInt256.gt ceilingDebt ilkLine)))
        (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) ≠ ⟨0⟩ := by
    simpa [ceilingDebt, debtNew, dtabWord, debtOld, Line, ilkArtNew, ilkArt,
      ilkRate, ilkLine, vatSlotWord, hIlkArtEq, hIlkRateEq, hIlkLineEq, hDebtEq,
      hLineEq] using hCeilingOk
  have hSafetyOkSource :
      UInt256.lor
        (UInt256.isZero (UInt256.gt tab inkSpot))
        (UInt256.land
          (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
          (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) ≠ ⟨0⟩ := by
    simpa [tab, inkSpot, urnInkNew, urnInk, urnArtNew, urnArt, ilkRate,
      ilkSpot, vatSlotWord, hUrnInkEq, hUrnArtEq, hIlkRateEq, hIlkSpotEq]
      using hSafetyOk
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner foldDebtSlot =
        debtOld := by
    simpa [evm0, debtOld, vatSlotWord, solcSlotWord, codeOwnerStorageWord] using
      (codeOwnerStorageWord_initState
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) foldDebtSlot)
  have hdtabMod :
      dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat := by
    change
      (Int.ofNat ilkRate.toNat * frobDartInt I) %
          (Int.ofNat EVM.wordModulus) =
        Int.ofNat (UInt256.mul (frobDartWord I) ilkRate).toNat
    exact frobDtab_mod_word I ilkRate
  have hlineLoad :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner foldDebtSlot debtNew)
          evm0.executionEnv.codeOwner ⟨9⟩ =
        Line := by
    have hne : (⟨9⟩ : UInt256) ≠ foldDebtSlot := by
      simp [foldDebtSlot]
    have hload0 :
        Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨9⟩ =
          Line := by
      simpa [evm0, Line, initState, vatSlotWord, solcSlotWord,
        codeOwnerStorageWord] using
        (codeOwnerStorageWord_initState
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
          (A := A) (I := I) (g := Sat256.ofUInt256 g) ⟨9⟩)
    have hstore :
        Solm.EVM.storageLoad
            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner foldDebtSlot debtNew)
            evm0.executionEnv.codeOwner ⟨9⟩ =
          Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨9⟩ :=
      storageLoad_storageStore_ne evm0 evm0.executionEnv.codeOwner hne
    exact hstore.trans hload0
  have hsourceSafety :
      ExecBlock config { contract := contract, locals := frobStore I } evm0
        ((nonpayable ++ requireLive ++
          [ .letDecl "urnInk" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "ink")),
            .letDecl "urnArt" (some uint256)
              (.storage (urnsF (.var "i") (.var "u") "art")),
            .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
            .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
            .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
            .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
            .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
            .require (.binary .ne (.var "ilkRate") (.intLit 0)) ]) ++
          checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
          checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
          checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
          checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
          checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
          checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
          [ .assign .storage debtRef (.var "debtNew") ] ++
          checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
          checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
          [ .require
              (eitherExpr
                (.binary .le (.var "dart") (.intLit 0))
                (bothExpr
                  (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
                  (.binary .le (.var "debtNew") (.storage LineRef)))),
            .require
              (eitherExpr
                (bothExpr
                  (.binary .le (.var "dart") (.intLit 0))
                  (.binary .ge (.var "dink") (.intLit 0)))
                (.binary .le (.var "tab") (.var "inkSpot"))) ])
        (.ok { contract := contract, locals := localsSafe } evmDebt) := by
    have hraw :=
      execFrobLoadedPrefixThroughSafetyOk
        (evm := evm0) (I := I)
        urnInk urnArt ilkArt ilkRate ilkSpot ilkLine ilkDust
        dtab debtOld debtNew dtabWord Line hsourcePrefix
        (frobDinkAddGuardNegCond hInkNegSource)
        (frobDinkAddGuardPosCond hInkPosSource)
        (frobDartAddGuardNegCond hArtNegSource)
        (frobDartAddGuardPosCond hArtPosSource)
        (frobDartAddGuardNegCond hIlkNegSource)
        (frobDartAddGuardPosCond hIlkPosSource)
        (by rfl) hRateMaxSource hDtabMulSource hTabMulSource
        hdebtLoad hdtabMod (by rfl) hDebtNegSource hDebtPosSource hlineLoad
        hCeilingMulSource (frobCeilingSourceCond_of_evm (I := I) hCeilingOkSource)
        hInkMulSource (frobSafetySourceCond_of_evm (I := I) hSafetyOkSource)
    simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk, localsDtab,
      tab, localsTab, localsDebt, evmDebt, ceilingDebt, inkSpot, localsSafe,
      List.append_assoc] using hraw
  have hUWishEq :
      vatSlotWord (frobUWishSlot I)
        (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
          (UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
            solcSlotWord σ_evm I foldDebtSlot)) I = uWish := by
    simpa [uWish, debtNew, dtabWord, debtOld, ilkRate, vatSlotWord, hIlkRateEq,
      hDebtEq] using
      (vatSlotWord_debtStore_accountMapEquiv
        (σ_evm := σ_evm) (σ_solm := σ_solm) (I := I) hAccounts
        (frobUWishSlot I) debtNew)
  have hVWishEq :
      vatSlotWord (frobVWishSlot I)
        (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
          (UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
            solcSlotWord σ_evm I foldDebtSlot)) I = vWish := by
    simpa [vWish, debtNew, dtabWord, debtOld, ilkRate, vatSlotWord, hIlkRateEq,
      hDebtEq] using
      (vatSlotWord_debtStore_accountMapEquiv
        (σ_evm := σ_evm) (σ_solm := σ_solm) (I := I) hAccounts
        (frobVWishSlot I) debtNew)
  have hWWishEq :
      vatSlotWord (frobWWishSlot I)
        (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
          (UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
            solcSlotWord σ_evm I foldDebtSlot)) I = wWish := by
    simpa [wWish, debtNew, dtabWord, debtOld, ilkRate, vatSlotWord, hIlkRateEq,
      hDebtEq] using
      (vatSlotWord_debtStore_accountMapEquiv
        (σ_evm := σ_evm) (σ_solm := σ_solm) (I := I) hAccounts
        (frobWWishSlot I) debtNew)
  have hloadU :
      Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
        (frobUWishSlot I) = uWish := by
    have hmap :
        evmDebt.accountMap =
          sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew := by
      simpa [evmDebt, evm0, initState] using
        storageStore_accountMap evm0 evm0.executionEnv.codeOwner foldDebtSlot debtNew
    change Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
        (frobUWishSlot I) =
      solcSlotWord (sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew) I
        (frobUWishSlot I)
    simp only [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
    rw [hmap]
    simp [solcSlotWord, evmDebt, evm0, initState, storageStore_executionEnv]
  have hloadV :
      Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
        (frobVWishSlot I) = vWish := by
    have hmap :
        evmDebt.accountMap =
          sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew := by
      simpa [evmDebt, evm0, initState] using
        storageStore_accountMap evm0 evm0.executionEnv.codeOwner foldDebtSlot debtNew
    change Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
        (frobVWishSlot I) =
      solcSlotWord (sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew) I
        (frobVWishSlot I)
    simp only [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
    rw [hmap]
    simp [solcSlotWord, evmDebt, evm0, initState, storageStore_executionEnv]
  have hloadW :
      Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
        (frobWWishSlot I) = wWish := by
    have hmap :
        evmDebt.accountMap =
          sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew := by
      simpa [evmDebt, evm0, initState] using
        storageStore_accountMap evm0 evm0.executionEnv.codeOwner foldDebtSlot debtNew
    change Solm.EVM.storageLoad evmDebt evmDebt.executionEnv.codeOwner
        (frobWWishSlot I) =
      solcSlotWord (sstoreAccountMap I.codeOwner σ_solm foldDebtSlot debtNew) I
        (frobWWishSlot I)
    simp only [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
    rw [hmap]
    simp [solcSlotWord, evmDebt, evm0, initState, storageStore_executionEnv]
  have hsrcDebt : evmDebt.executionEnv.source = I.source := by
    simp [evmDebt, evm0, initState, storageStore_executionEnv]
  have hsafeDart : localsSafe.get? "dart" = some (frobDartValue I) := by
    change
      ((((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
        (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
        (.int (Int.ofNat inkSpot.toNat))).get? "dart" =
        some (frobDartValue I)
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_dart I urnInk urnArt ilkArt ilkRate ilkSpot
        ilkLine ilkDust
  have hsafeDink : localsSafe.get? "dink" = some (frobDinkValue I) := by
    change
      ((((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
        (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
        (.int (Int.ofNat inkSpot.toNat))).get? "dink" =
        some (frobDinkValue I)
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_dink I urnInk urnArt ilkArt ilkRate ilkSpot
        ilkLine ilkDust
  have hsafeU : localsSafe.get? "u" = some (frobUValue I) := by
    change
      ((((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
        (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
        (.int (Int.ofNat inkSpot.toNat))).get? "u" =
        some (frobUValue I)
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_u I urnInk urnArt ilkArt ilkRate ilkSpot
        ilkLine ilkDust
  have hsafeV : localsSafe.get? "v" = some (frobVValue I) := by
    change
      ((((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
        (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
        (.int (Int.ofNat inkSpot.toNat))).get? "v" =
        some (frobVValue I)
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_v I urnInk urnArt ilkArt ilkRate ilkSpot
        ilkLine ilkDust
  have hsafeW : localsSafe.get? "w" = some (frobWValue I) := by
    change
      ((((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
        (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
        (.int (Int.ofNat inkSpot.toNat))).get? "w" =
        some (frobWValue I)
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simpa [localsLoaded] using
      frobStoreIlkDust_get_w I urnInk urnArt ilkArt ilkRate ilkSpot
        ilkLine ilkDust
  have hsafeBaseCan : localsSafe.get? "can" = none := by
    change
      ((((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
        (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
        (.int (Int.ofNat inkSpot.toNat))).get? "can" = none
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simp [localsLoaded, frobStoreIlkDust, frobStore]
  have hsafeUrnArtNew :
      localsSafe.get? "urnArtNew" = some (.int (Int.ofNat urnArtNew.toNat)) := by
    change
      ((((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
        (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
        (.int (Int.ofNat inkSpot.toNat))).get? "urnArtNew" =
        some (.int (Int.ofNat urnArtNew.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_self]
  have hsafeTab :
      localsSafe.get? "tab" = some (.int (Int.ofNat tab.toNat)) := by
    change
      ((((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
        (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
        (.int (Int.ofNat inkSpot.toNat))).get? "tab" =
        some (.int (Int.ofNat tab.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_self]
  have hsafeIlkDust :
      localsSafe.get? "ilkDust" = some (.int (Int.ofNat ilkDust.toNat)) := by
    change
      ((((((((localsLoaded.insert "urnInkNew"
        (.int (Int.ofNat urnInkNew.toNat))).insert "urnArtNew"
        (.int (Int.ofNat urnArtNew.toNat))).insert "ilkArtNew"
        (.int (Int.ofNat ilkArtNew.toNat))).insert "dtab" (.int dtab)).insert
        "tab" (.int (Int.ofNat tab.toNat))).insert "debtNew"
        (.int (Int.ofNat debtNew.toNat))).insert "ceilingDebt"
        (.int (Int.ofNat ceilingDebt.toNat))).insert "inkSpot"
        (.int (Int.ofNat inkSpot.toNat))).get? "ilkDust" =
        some (.int (Int.ofNat ilkDust.toNat))
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    rw [store_get_ne _ _ (by decide)]
    simp [localsLoaded, frobStoreIlkDust]
  have mkAuthRevert :
      ExecBlock config { contract := contract, locals := localsSafe } evmDebt
        [ .require
            (eitherExpr
              (bothExpr
                (.binary .le (.var "dart") (.intLit 0))
                (.binary .ge (.var "dink") (.intLit 0)))
              (wishExpr (.var "u") sender)),
          .require
            (eitherExpr (.binary .le (.var "dink") (.intLit 0))
              (wishExpr (.var "v") sender)),
          .require
            (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
              (wishExpr (.var "w") sender)),
          .require
            (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
              (.binary .ge (.var "tab") (.var "ilkDust"))) ]
        .reverted →
      ExecTransitionBody config contract evm0 (frobStore I) frobTransition.body
        .reverted := by
    intro hauthRevert
    exact hsourceRevertFromAuthorizationDust (by
      have hprefix := Reasoning.Refinement.execBlock_append hsourceSafety hauthRevert
      simpa [localsLoaded, urnInkNew, urnArtNew, ilkArtNew, localsIlk, localsDtab,
        tab, localsTab, debtOld, dtabWord, debtNew, localsDebt, evmDebt,
        ceilingDebt, inkSpot, localsSafe, List.append_assoc] using hprefix)
  by_cases hU :
      UInt256.lor
        (UInt256.lor
          (UInt256.eq (vatSlotWord (frobUWishSlot I)
            (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
              (UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                solcSlotWord σ_evm I foldDebtSlot)) I) ⟨1⟩)
          (UInt256.eq (frobUMaskedWord I) (hopeSourceWord I)))
        (UInt256.land
          (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
          (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) ≠ ⟨0⟩
  · have hUOk :=
      frobAuthUSourceCond_of_evm (I := I) (uWish := uWish) (by
        simpa [uWish, hUWishEq] using hU)
    obtain ⟨_, _, hUDone⟩ :=
      RD.vatFrobUWishCheckSuccess
        (h := by simpa using hSafetyDone)
        (by simpa [foldDebtSlot] using hU)
    by_cases hV :
        UInt256.lor
          (UInt256.lor
            (UInt256.eq (vatSlotWord (frobVWishSlot I)
              (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
                (UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                  solcSlotWord σ_evm I foldDebtSlot)) I) ⟨1⟩)
            (UInt256.eq (frobVMaskedWord I) (hopeSourceWord I)))
          (UInt256.isZero (UInt256.sgt (frobDinkWord I) ⟨0⟩)) ≠ ⟨0⟩
    · have hVOk :=
        frobAuthVSourceCond_of_evm (I := I) (vWish := vWish) (by
          simpa [vWish, hVWishEq] using hV)
      obtain ⟨_, _, hVDone⟩ :=
        RD.vatFrobVWishCheckSuccess
          (h := by simpa using hUDone)
          (by simpa [foldDebtSlot] using hV)
      by_cases hW :
          UInt256.lor
            (UInt256.lor
              (UInt256.eq (vatSlotWord (frobWWishSlot I)
                (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
                  (UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                    solcSlotWord σ_evm I foldDebtSlot)) I) ⟨1⟩)
              (UInt256.eq (frobWMaskedWord I) (hopeSourceWord I)))
            (UInt256.isZero (UInt256.slt (frobDartWord I) ⟨0⟩)) ≠ ⟨0⟩
      · have hWOk :=
          frobAuthWSourceCond_of_evm (I := I) (wWish := wWish) (by
            simpa [wWish, hWWishEq] using hW)
        obtain ⟨_, _, hWDone⟩ :=
          RD.vatFrobWWishCheckSuccess
            (h := by simpa using hVDone)
            (by simpa [foldDebtSlot] using hW)
        by_cases hDust :
            UInt256.lor
              (UInt256.isZero
                (UInt256.lt
                  (UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                    (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
                  (solcSlotWord σ_evm I (frobIlkDustSlot I))))
              (UInt256.eq ⟨0⟩
                (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))) ≠ ⟨0⟩
        · have hWishAuthDust : frobLiveWishAuthDustGuards σ_evm I := by
            unfold frobLiveWishAuthDustGuards
            exact ⟨hU, hV, hW, hDust⟩
          exact False.elim (hWishAuthDustFail hWishAuthDust)
        · have hDustZero :
              UInt256.lor
                (UInt256.isZero
                  (UInt256.lt
                    (UInt256.mul (solcSlotWord σ_evm I (frobIlkRateSlot I))
                      (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I)))
                    (solcSlotWord σ_evm I (frobIlkDustSlot I))))
                (UInt256.eq ⟨0⟩
                  (frobDartWord I + solcSlotWord σ_evm I (frobUrnArtSlot I))) =
                ⟨0⟩ := by
            by_contra hne
            exact hDust hne
          have hDustSourceZero :
              UInt256.lor
                (UInt256.isZero (UInt256.lt tab ilkDust))
                (UInt256.eq ⟨0⟩ urnArtNew) = ⟨0⟩ := by
            simpa [tab, urnArtNew, urnArt, ilkRate, ilkDust, vatSlotWord,
              hUrnArtEq, hIlkRateEq, hIlkDustEq] using hDustZero
          have hbadDust := frobDustSourceFalseCond_of_evm hDustSourceZero
          have huEval := evalExpr_frob_auth_u_req_true
            (evm := evmDebt) (I := I) (locals := localsSafe)
            uWish hsafeDart hsafeDink hsafeU hsafeBaseCan hsrcDebt hloadU hUOk
          have hvEval := evalExpr_frob_auth_v_req_true
            (evm := evmDebt) (I := I) (locals := localsSafe)
            vWish hsafeDink hsafeV hsafeBaseCan hsrcDebt hloadV hVOk
          have hwEval := evalExpr_frob_auth_w_req_true
            (evm := evmDebt) (I := I) (locals := localsSafe)
            wWish hsafeDart hsafeW hsafeBaseCan hsrcDebt hloadW hWOk
          have hdustEval :=
            evalExpr_frob_dust_req_false (evm := evmDebt) (locals := localsSafe)
              urnArtNew tab ilkDust
              hsafeUrnArtNew hsafeTab hsafeIlkDust hbadDust
          have hsrcFullRevert :=
            mkAuthRevert (execFrobAuthorizationDustRevertDust huEval hvEval hwEval
              hdustEval)
          have hrev := RD.vatFrobDustCheckRevert
            (h := by simpa using hWDone)
            (by simpa [foldDebtSlot] using hDustZero)
          exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel)
            hdecode hsrcFullRevert
      · have hWZero :
            UInt256.lor
              (UInt256.lor
                (UInt256.eq (vatSlotWord (frobWWishSlot I)
                  (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
                    (UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                      solcSlotWord σ_evm I foldDebtSlot)) I) ⟨1⟩)
                (UInt256.eq (frobWMaskedWord I) (hopeSourceWord I)))
              (UInt256.isZero (UInt256.slt (frobDartWord I) ⟨0⟩)) = ⟨0⟩ := by
          by_contra hne
          exact hW hne
        have hWSourceZero :
            UInt256.lor
              (UInt256.lor (UInt256.eq wWish ⟨1⟩)
                (UInt256.eq (frobWMaskedWord I) (hopeSourceWord I)))
              (UInt256.isZero (UInt256.slt (frobDartWord I) ⟨0⟩)) =
            ⟨0⟩ := by
          simpa [wWish, hWWishEq] using hWZero
        have hbadW := frobAuthWSourceFalseCond_of_evm (I := I) hWSourceZero
        have huEval := evalExpr_frob_auth_u_req_true
          (evm := evmDebt) (I := I) (locals := localsSafe)
          uWish hsafeDart hsafeDink hsafeU hsafeBaseCan hsrcDebt hloadU hUOk
        have hvEval := evalExpr_frob_auth_v_req_true
          (evm := evmDebt) (I := I) (locals := localsSafe)
          vWish hsafeDink hsafeV hsafeBaseCan hsrcDebt hloadV hVOk
        have hwEval := evalExpr_frob_auth_w_req_false
          (evm := evmDebt) (I := I) (locals := localsSafe)
          wWish hsafeDart hsafeW hsafeBaseCan hsrcDebt hloadW hbadW
        have hsrcFullRevert :=
          mkAuthRevert (execFrobAuthorizationDustRevertW huEval hvEval hwEval)
        have hrev := RD.vatFrobWWishCheckRevert
          (h := by simpa using hVDone)
          (by simpa [foldDebtSlot] using hWZero)
        exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel)
          hdecode hsrcFullRevert
    · have hVZero :
          UInt256.lor
            (UInt256.lor
              (UInt256.eq (vatSlotWord (frobVWishSlot I)
                (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
                  (UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                    solcSlotWord σ_evm I foldDebtSlot)) I) ⟨1⟩)
              (UInt256.eq (frobVMaskedWord I) (hopeSourceWord I)))
            (UInt256.isZero (UInt256.sgt (frobDinkWord I) ⟨0⟩)) = ⟨0⟩ := by
        by_contra hne
        exact hV hne
      have hVSourceZero :
          UInt256.lor
            (UInt256.lor (UInt256.eq vWish ⟨1⟩)
              (UInt256.eq (frobVMaskedWord I) (hopeSourceWord I)))
            (UInt256.isZero (UInt256.sgt (frobDinkWord I) ⟨0⟩)) =
          ⟨0⟩ := by
        simpa [vWish, hVWishEq] using hVZero
      have hbadV := frobAuthVSourceFalseCond_of_evm (I := I) hVSourceZero
      have huEval := evalExpr_frob_auth_u_req_true
        (evm := evmDebt) (I := I) (locals := localsSafe)
        uWish hsafeDart hsafeDink hsafeU hsafeBaseCan hsrcDebt hloadU hUOk
      have hvEval := evalExpr_frob_auth_v_req_false
        (evm := evmDebt) (I := I) (locals := localsSafe)
        vWish hsafeDink hsafeV hsafeBaseCan hsrcDebt hloadV hbadV
      have hsrcFullRevert :=
        mkAuthRevert (execFrobAuthorizationDustRevertV huEval hvEval)
      have hrev := RD.vatFrobVWishCheckRevert
        (h := by simpa using hUDone)
        (by simpa [foldDebtSlot] using hVZero)
      exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel)
        hdecode hsrcFullRevert
  · have hUZero :
        UInt256.lor
          (UInt256.lor
            (UInt256.eq (vatSlotWord (frobUWishSlot I)
              (sstoreAccountMap I.codeOwner σ_evm foldDebtSlot
                (UInt256.mul (frobDartWord I) (solcSlotWord σ_evm I (frobIlkRateSlot I)) +
                  solcSlotWord σ_evm I foldDebtSlot)) I) ⟨1⟩)
            (UInt256.eq (frobUMaskedWord I) (hopeSourceWord I)))
          (UInt256.land
            (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
            (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) = ⟨0⟩ := by
      by_contra hne
      exact hU hne
    have hUSourceZero :
        UInt256.lor
          (UInt256.lor (UInt256.eq uWish ⟨1⟩)
            (UInt256.eq (frobUMaskedWord I) (hopeSourceWord I)))
          (UInt256.land
            (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
            (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) =
        ⟨0⟩ := by
      simpa [uWish, hUWishEq] using hUZero
    have hbadU := frobAuthUSourceFalseCond_of_evm (I := I) hUSourceZero
    have huEval := evalExpr_frob_auth_u_req_false
      (evm := evmDebt) (I := I) (locals := localsSafe)
      uWish hsafeDart hsafeDink hsafeU hsafeBaseCan hsrcDebt hloadU hbadU
    have hsrcFullRevert :=
      mkAuthRevert (execFrobAuthorizationDustRevertU huEval)
    have hrev := RD.vatFrobUWishCheckRevert
      (h := by simpa using hSafetyDone)
      (by simpa [foldDebtSlot] using hUZero)
    exact hrev.reEquivExecutionRevert hcode (vatDispatchFrob hsel)
      hdecode hsrcFullRevert

set_option maxHeartbeats 0 in
theorem vatFrobBodyCoreLive
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (vatSelBytes 11))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz196 : 196 ≤ I.calldata.size)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (frobTransition.params.map Param.name)
        (transitionSignature frobTransition).paramTypes I.calldata = some (frobStore I))
    (hdecoded :
      ∃ k C,
        RD vatBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2975⟩
          [frobDartWord I, frobDinkWord I, frobWMaskedWord I, frobVMaskedWord I,
            frobUMaskedWord I, frobIWord I, ⟨524⟩, vatSelWord I]
          solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hlive : vatSlotWord ⟨10⟩ σ_evm I = ⟨1⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  classical
  by_cases hrateZeroEvm : solcSlotWord σ_evm I (frobIlkRateSlot I) = ⟨0⟩
  · exact vatFrobBodyCoreLiveRateZeroRevert
      (hcode := hcode) (hwv := hwv) (hsel := hsel)
      (hAccounts := hAccounts) (hsz196 := hsz196)
      (hdecode := hdecode) (hdecoded := hdecoded) (hlive := hlive)
      (hrateZeroEvm := hrateZeroEvm)
  · by_cases hArithmetic : frobLiveArithmeticPrefixGuards σ_evm I
    · by_cases hDebtSafety : frobLiveDebtCeilingSafetyGuards σ_evm I
      · by_cases hWishAuthDust : frobLiveWishAuthDustGuards σ_evm I
        · by_cases hFinalArithmetic : frobLiveFinalArithmeticGuards σ_evm I
          · have hSuccess : frobLiveSuccessGuards σ_evm I :=
              frobLiveSuccessGuards_of_groups hArithmetic hDebtSafety hWishAuthDust
                hFinalArithmetic
            exact vatFrobBodyCoreLiveSuccessGuards
              (hcode := hcode) (hsize := hsize) (hperm := hperm) (hwv := hwv)
              (hsel := hsel) (hAccounts := hAccounts) (hsz196 := hsz196)
              (hdecode := hdecode) (hdecoded := hdecoded)
              (hSuccess := hSuccess) (hlive := hlive)
          · exact vatFrobBodyCoreLiveFinalArithmeticOverflowReverts
              (hcode := hcode) (hperm := hperm) (hwv := hwv)
              (hsel := hsel) (hAccounts := hAccounts) (hsz196 := hsz196)
              (hdecode := hdecode) (hdecoded := hdecoded) (hlive := hlive)
              (hrateZeroEvm := hrateZeroEvm)
              (hArithmetic := hArithmetic) (hDebtSafety := hDebtSafety)
              (hWishAuthDust := hWishAuthDust)
              (hFinalArithmeticFail := hFinalArithmetic)
        · exact vatFrobBodyCoreLiveWishAuthDustReverts
            (hcode := hcode) (hperm := hperm) (hwv := hwv)
            (hsel := hsel) (hAccounts := hAccounts) (hsz196 := hsz196)
            (hdecode := hdecode) (hdecoded := hdecoded) (hlive := hlive)
            (hrateZeroEvm := hrateZeroEvm) (hArithmetic := hArithmetic)
            (hDebtSafety := hDebtSafety) (hWishAuthDustFail := hWishAuthDust)
      · exact vatFrobBodyCoreLiveDebtCeilingSafetyReverts
          (hcode := hcode) (hperm := hperm) (hwv := hwv)
          (hsel := hsel) (hAccounts := hAccounts) (hsz196 := hsz196)
          (hdecode := hdecode) (hdecoded := hdecoded) (hlive := hlive)
          (hrateZeroEvm := hrateZeroEvm) (hArithmetic := hArithmetic)
          (hDebtSafetyFail := hDebtSafety)
    · exact vatFrobBodyCoreLiveArithmeticOverflowReverts
        (hcode := hcode) (hwv := hwv)
        (hsel := hsel) (hAccounts := hAccounts) (hsz196 := hsz196)
        (hdecode := hdecode) (hdecoded := hdecoded) (hlive := hlive)
        (hrateZeroEvm := hrateZeroEvm)
        (hArithmeticFail := by
          exact hArithmetic)

end Benchmarks.Dss.Vat
