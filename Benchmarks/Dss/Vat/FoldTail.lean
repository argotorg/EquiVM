import Benchmarks.Dss.Vat.FoldCommon

namespace Benchmarks.Dss.Vat

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

theorem vatFoldDaiAddRevertGuardNeg (evm : EVM.State) (I : ExecutionEnv)
    {rateNew daiOld daiNew radWord : UInt256} {rad : Int}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (foldDaiSlot I) = daiOld)
    (hradWord : rad % (Int.ofNat EVM.wordModulus) = Int.ofNat radWord.toNat)
    (hdaiNew : daiNew = radWord + daiOld)
    (hguardNeg :
      evalExpr? config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew } evm
        (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
          (.binary .le (.var "daiNew") (.storage (daiRef (.var "u"))))) =
        .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := foldStoreRad I rateNew rad } evm
      (checkedAddSignedInto "daiNew" (.storage (daiRef (.var "u"))) (.var "rad"))
      .reverted := by
  have hdai :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
          (.storage (daiRef (.var "u"))) =
        .ok (.int (Int.ofNat daiOld.toNat)) := by
    rw [evalExpr_fold_dai_u evm I (foldStoreRad I rateNew rad)
      (foldStoreRad_get_u I rateNew rad) (foldStoreRad_dai I rateNew rad)]
    rw [hload]
  have hrad :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (.var "rad") = .ok (.int rad) :=
    vatEvalExpr_varInt (foldStoreRad_get_rad I rateNew rad)
  have hlet :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (wordWrap256 (.binary .add (.storage (daiRef (.var "u"))) (.var "rad"))) =
        .ok (.int (Int.ofNat daiNew.toNat)) :=
    evalExpr_fold_wordWrapAdd_ok hdai hrad hradWord hdaiNew
  change ExecBlock config { contract := contract, locals := foldStoreRad I rateNew rad } evm
    [ .letDecl "daiNew" (some uint256)
        (wordWrap256 (.binary .add (.storage (daiRef (.var "u"))) (.var "rad"))),
      .require
        (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
          (.binary .le (.var "daiNew") (.storage (daiRef (.var "u"))))),
      .require
        (eitherExpr (.binary .le (.var "rad") (.intLit 0))
          (.binary .ge (.var "daiNew") (.storage (daiRef (.var "u"))))) ]
    .reverted
  exact ExecBlock.consNormal (ExecStmt.letDecl hlet)
    (ExecBlock.consRevert (ExecStmt.requireFalse hguardNeg))

theorem vatFoldDaiAddRevertGuardPos (evm : EVM.State) (I : ExecutionEnv)
    {rateNew daiOld daiNew radWord : UInt256} {rad : Int}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (foldDaiSlot I) = daiOld)
    (hradWord : rad % (Int.ofNat EVM.wordModulus) = Int.ofNat radWord.toNat)
    (hdaiNew : daiNew = radWord + daiOld)
    (hguardNeg :
      evalExpr? config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew } evm
        (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
          (.binary .le (.var "daiNew") (.storage (daiRef (.var "u"))))) =
        .ok (.bool true))
    (hguardPos :
      evalExpr? config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew } evm
        (eitherExpr (.binary .le (.var "rad") (.intLit 0))
          (.binary .ge (.var "daiNew") (.storage (daiRef (.var "u"))))) =
        .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := foldStoreRad I rateNew rad } evm
      (checkedAddSignedInto "daiNew" (.storage (daiRef (.var "u"))) (.var "rad"))
      .reverted := by
  have hdai :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
          (.storage (daiRef (.var "u"))) =
        .ok (.int (Int.ofNat daiOld.toNat)) := by
    rw [evalExpr_fold_dai_u evm I (foldStoreRad I rateNew rad)
      (foldStoreRad_get_u I rateNew rad) (foldStoreRad_dai I rateNew rad)]
    rw [hload]
  have hrad :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (.var "rad") = .ok (.int rad) :=
    vatEvalExpr_varInt (foldStoreRad_get_rad I rateNew rad)
  have hlet :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (wordWrap256 (.binary .add (.storage (daiRef (.var "u"))) (.var "rad"))) =
        .ok (.int (Int.ofNat daiNew.toNat)) :=
    evalExpr_fold_wordWrapAdd_ok hdai hrad hradWord hdaiNew
  change ExecBlock config { contract := contract, locals := foldStoreRad I rateNew rad } evm
    [ .letDecl "daiNew" (some uint256)
        (wordWrap256 (.binary .add (.storage (daiRef (.var "u"))) (.var "rad"))),
      .require
        (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
          (.binary .le (.var "daiNew") (.storage (daiRef (.var "u"))))),
      .require
        (eitherExpr (.binary .le (.var "rad") (.intLit 0))
          (.binary .ge (.var "daiNew") (.storage (daiRef (.var "u"))))) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguardNeg)
    (ExecBlock.consRevert (ExecStmt.requireFalse hguardPos))

theorem vatFoldDebtAddRevertGuardNeg (evm : EVM.State) (I : ExecutionEnv)
    {rateNew daiNew debtOld debtNew radWord : UInt256} {rad : Int}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner foldDebtSlot = debtOld)
    (hradWord : rad % (Int.ofNat EVM.wordModulus) = Int.ofNat radWord.toNat)
    (hdebtNew : debtNew = radWord + debtOld)
    (hguardNeg :
      evalExpr? config
        { contract := contract, locals := foldStoreDebtNew I rateNew rad daiNew debtNew } evm
        (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
          (.binary .le (.var "debtNew") (.storage debtRef))) =
        .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew } evm
      (checkedAddSignedInto "debtNew" (.storage debtRef) (.var "rad"))
      .reverted := by
  have hdebt :
      evalExpr? config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew }
          evm (.storage debtRef) =
        .ok (.int (Int.ofNat debtOld.toNat)) := by
    rw [evalExpr_fold_debt evm (foldStoreDaiNew I rateNew rad daiNew)
      (foldStoreDaiNew_debt I rateNew rad daiNew)]
    rw [hload]
  have hrad :
      evalExpr? config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew }
        evm (.var "rad") = .ok (.int rad) :=
    vatEvalExpr_varInt (foldStoreDaiNew_get_rad I rateNew rad daiNew)
  have hlet :
      evalExpr? config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew }
        evm (wordWrap256 (.binary .add (.storage debtRef) (.var "rad"))) =
        .ok (.int (Int.ofNat debtNew.toNat)) :=
    evalExpr_fold_wordWrapAdd_ok hdebt hrad hradWord hdebtNew
  change ExecBlock config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew }
    evm
    [ .letDecl "debtNew" (some uint256)
        (wordWrap256 (.binary .add (.storage debtRef) (.var "rad"))),
      .require
        (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
          (.binary .le (.var "debtNew") (.storage debtRef))),
      .require
        (eitherExpr (.binary .le (.var "rad") (.intLit 0))
          (.binary .ge (.var "debtNew") (.storage debtRef))) ]
    .reverted
  exact ExecBlock.consNormal (ExecStmt.letDecl hlet)
    (ExecBlock.consRevert (ExecStmt.requireFalse hguardNeg))

theorem vatFoldDebtAddRevertGuardPos (evm : EVM.State) (I : ExecutionEnv)
    {rateNew daiNew debtOld debtNew radWord : UInt256} {rad : Int}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner foldDebtSlot = debtOld)
    (hradWord : rad % (Int.ofNat EVM.wordModulus) = Int.ofNat radWord.toNat)
    (hdebtNew : debtNew = radWord + debtOld)
    (hguardNeg :
      evalExpr? config
        { contract := contract, locals := foldStoreDebtNew I rateNew rad daiNew debtNew } evm
        (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
          (.binary .le (.var "debtNew") (.storage debtRef))) =
        .ok (.bool true))
    (hguardPos :
      evalExpr? config
        { contract := contract, locals := foldStoreDebtNew I rateNew rad daiNew debtNew } evm
        (eitherExpr (.binary .le (.var "rad") (.intLit 0))
          (.binary .ge (.var "debtNew") (.storage debtRef))) =
        .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew } evm
      (checkedAddSignedInto "debtNew" (.storage debtRef) (.var "rad"))
      .reverted := by
  have hdebt :
      evalExpr? config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew }
          evm (.storage debtRef) =
        .ok (.int (Int.ofNat debtOld.toNat)) := by
    rw [evalExpr_fold_debt evm (foldStoreDaiNew I rateNew rad daiNew)
      (foldStoreDaiNew_debt I rateNew rad daiNew)]
    rw [hload]
  have hrad :
      evalExpr? config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew }
        evm (.var "rad") = .ok (.int rad) :=
    vatEvalExpr_varInt (foldStoreDaiNew_get_rad I rateNew rad daiNew)
  have hlet :
      evalExpr? config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew }
        evm (wordWrap256 (.binary .add (.storage debtRef) (.var "rad"))) =
        .ok (.int (Int.ofNat debtNew.toNat)) :=
    evalExpr_fold_wordWrapAdd_ok hdebt hrad hradWord hdebtNew
  change ExecBlock config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew }
    evm
    [ .letDecl "debtNew" (some uint256)
        (wordWrap256 (.binary .add (.storage debtRef) (.var "rad"))),
      .require
        (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
          (.binary .le (.var "debtNew") (.storage debtRef))),
      .require
        (eitherExpr (.binary .le (.var "rad") (.intLit 0))
          (.binary .ge (.var "debtNew") (.storage debtRef))) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguardNeg)
    (ExecBlock.consRevert (ExecStmt.requireFalse hguardPos))

theorem vatFoldRateAddAssignOk (evm : EVM.State) (I : ExecutionEnv)
    {rateOld rateNew : UInt256} (hsz100 : 100 ≤ I.calldata.size)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (foldRateSlot I) = rateOld)
    (hrateNew : rateNew = foldRateWord I + rateOld)
    (hguardNeg :
      evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNew } evm
        (eitherExpr (.binary .ge (.var "rate") (.intLit 0))
          (.binary .le (.var "rateNew") (.storage (ilksF (.var "i") "rate")))) =
        .ok (.bool true))
    (hguardPos :
      evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNew } evm
        (eitherExpr (.binary .le (.var "rate") (.intLit 0))
          (.binary .ge (.var "rateNew") (.storage (ilksF (.var "i") "rate")))) =
        .ok (.bool true)) :
    ExecBlock config { contract := contract, locals := foldStore I } evm
      (checkedAddSignedInto "rateNew" (.storage (ilksF (.var "i") "rate")) (.var "rate") ++
        [ .assign .storage (ilksF (.var "i") "rate") (.var "rateNew") ])
      (.ok { contract := contract, locals := foldStoreRateNew I rateNew }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (foldRateSlot I) rateNew)) := by
  have hrateOld :
      evalExpr? config { contract := contract, locals := foldStore I } evm
          (.storage (ilksF (.var "i") "rate")) =
        .ok (.int (Int.ofNat rateOld.toNat)) := by
    rw [evalExpr_fold_ilks_rate evm I (foldStore I) hsz100
      (foldStore_get_i I) (foldStore_ilks I)]
    rw [hload]
  have hrate :
      evalExpr? config { contract := contract, locals := foldStore I } evm (.var "rate") =
        .ok (.int (foldRateInt I)) :=
    vatEvalExpr_varInt (foldStore_get_rate I)
  have hlet :
      evalExpr? config { contract := contract, locals := foldStore I } evm
        (wordWrap256 (.binary .add (.storage (ilksF (.var "i") "rate")) (.var "rate"))) =
        .ok (.int (Int.ofNat rateNew.toNat)) :=
    evalExpr_fold_wordWrapAdd_ok hrateOld hrate (foldRateInt_mod_word I) hrateNew
  have hrateNewVar :
      evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNew } evm
        (.var "rateNew") = .ok (.int (Int.ofNat rateNew.toNat)) :=
    vatEvalExpr_varUInt256 (foldStoreRateNew_get_rateNew I rateNew)
  have hassign :
      assignStorageRef? config { contract := contract, locals := foldStoreRateNew I rateNew }
        evm .storage (ilksF (.var "i") "rate") (.int (Int.ofNat rateNew.toNat)) =
      .ok ({ contract := contract, locals := foldStoreRateNew I rateNew },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (foldRateSlot I) rateNew) :=
    assign_fold_rate evm I (foldStoreRateNew I rateNew) rateNew hsz100
      (foldStoreRateNew_get_i I rateNew) (foldStoreRateNew_ilks I rateNew)
  change ExecBlock config { contract := contract, locals := foldStore I } evm
    [ .letDecl "rateNew" (some uint256)
        (wordWrap256 (.binary .add (.storage (ilksF (.var "i") "rate")) (.var "rate"))),
      .require
        (eitherExpr (.binary .ge (.var "rate") (.intLit 0))
          (.binary .le (.var "rateNew") (.storage (ilksF (.var "i") "rate")))),
      .require
        (eitherExpr (.binary .le (.var "rate") (.intLit 0))
          (.binary .ge (.var "rateNew") (.storage (ilksF (.var "i") "rate")))),
      .assign .storage (ilksF (.var "i") "rate") (.var "rateNew") ]
    (.ok { contract := contract, locals := foldStoreRateNew I rateNew }
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (foldRateSlot I) rateNew))
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNeg) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardPos) ?_
  exact ExecBlock.consNormal (ExecStmt.assign hrateNewVar hassign) ExecBlock.nil

theorem vatFoldSourceRevertAfterRateBlock (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      evalExpr? config { contract := contract, locals := foldStore I } evm
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true))
    (hlive :
      evalExpr? config { contract := contract, locals := foldStore I } evm
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true))
    (hrateRevert :
      ExecBlock config { contract := contract, locals := foldStore I } evm
        (checkedAddSignedInto "rateNew" (.storage (ilksF (.var "i") "rate")) (.var "rate"))
        .reverted) :
    ExecTransitionBody config contract evm (foldStore I) foldTransition.body .reverted := by
  have hprefix :
      ExecBlock config { contract := contract, locals := foldStore I } evm
        (nonpayable ++ auth ++ requireLive)
        (.ok { contract := contract, locals := foldStore I } evm) := by
    change ExecBlock config { contract := contract, locals := foldStore I } evm
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
        .require (.binary .eq (.storage liveRef) (.intLit 1)) ]
      (.ok { contract := contract, locals := foldStore I } evm)
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true hwv
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauth) ?_
    exact ExecBlock.consNormal (ExecStmt.requireTrue hlive) ExecBlock.nil
  have h01 := execBlock_append hprefix hrateRevert
  have hblock := execBlock_append_term
    (s2 :=
      [ .assign .storage (ilksF (.var "i") "rate") (.var "rateNew") ] ++
      checkedMulSignedInto "rad" (.storage (ilksF (.var "i") "Art")) (.var "rate") ++
      checkedAddSignedInto "daiNew" (.storage (daiRef (.var "u"))) (.var "rad") ++
      [ .assign .storage (daiRef (.var "u")) (.var "daiNew") ] ++
      checkedAddSignedInto "debtNew" (.storage debtRef) (.var "rad") ++
      [ .assign .storage debtRef (.var "debtNew") ])
    h01 (by intro f e h; cases h)
  simpa [ExecTransitionBody, foldTransition, nonpayable, auth, requireLive,
    List.append_assoc] using ExecFuncBody.execBlockRevert hblock

theorem vatFoldSourceRevertAfterRadBlock (evm evmRate : EVM.State) (I : ExecutionEnv)
    {rateNew : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      evalExpr? config { contract := contract, locals := foldStore I } evm
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true))
    (hlive :
      evalExpr? config { contract := contract, locals := foldStore I } evm
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true))
    (hrateOk :
      ExecBlock config { contract := contract, locals := foldStore I } evm
        (checkedAddSignedInto "rateNew" (.storage (ilksF (.var "i") "rate")) (.var "rate") ++
          [ .assign .storage (ilksF (.var "i") "rate") (.var "rateNew") ])
        (.ok { contract := contract, locals := foldStoreRateNew I rateNew } evmRate))
    (hradRevert :
      ExecBlock config { contract := contract, locals := foldStoreRateNew I rateNew } evmRate
        (checkedMulSignedInto "rad" (.storage (ilksF (.var "i") "Art")) (.var "rate"))
        .reverted) :
    ExecTransitionBody config contract evm (foldStore I) foldTransition.body .reverted := by
  have hprefix :
      ExecBlock config { contract := contract, locals := foldStore I } evm
        (nonpayable ++ auth ++ requireLive)
        (.ok { contract := contract, locals := foldStore I } evm) := by
    change ExecBlock config { contract := contract, locals := foldStore I } evm
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
        .require (.binary .eq (.storage liveRef) (.intLit 1)) ]
      (.ok { contract := contract, locals := foldStore I } evm)
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true hwv
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauth) ?_
    exact ExecBlock.consNormal (ExecStmt.requireTrue hlive) ExecBlock.nil
  have h01 := execBlock_append hprefix hrateOk
  have h02 := execBlock_append h01 hradRevert
  have hblock := execBlock_append_term
    (s2 :=
      checkedAddSignedInto "daiNew" (.storage (daiRef (.var "u"))) (.var "rad") ++
      [ .assign .storage (daiRef (.var "u")) (.var "daiNew") ] ++
      checkedAddSignedInto "debtNew" (.storage debtRef) (.var "rad") ++
      [ .assign .storage debtRef (.var "debtNew") ])
    h02 (by intro f e h; cases h)
  simpa [ExecTransitionBody, foldTransition, nonpayable, auth, requireLive,
    List.append_assoc] using ExecFuncBody.execBlockRevert hblock

theorem vatFoldRadMulOk (evm : EVM.State) (I : ExecutionEnv)
    {rateNew artOld : UInt256} {rad : Int} (hsz100 : 100 ≤ I.calldata.size)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (foldArtSlot I) = artOld)
    (hrad : rad = Int.ofNat artOld.toNat * foldRateInt I)
    (hradLo : -((2 : Int) ^ 255) ≤ rad)
    (hradHi : rad < (2 : Int) ^ 255)
    (hguardMax :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (.binary .le (.storage (ilksF (.var "i") "Art")) (.intLit maxInt256)) =
        .ok (.bool true))
    (hguardMul :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (eitherExpr (.binary .eq (.var "rate") (.intLit 0))
          (.binary .eq (.binary .div (.var "rad") (.var "rate"))
            (.storage (ilksF (.var "i") "Art")))) =
        .ok (.bool true)) :
    ExecBlock config { contract := contract, locals := foldStoreRateNew I rateNew } evm
      (checkedMulSignedInto "rad" (.storage (ilksF (.var "i") "Art")) (.var "rate"))
      (.ok { contract := contract, locals := foldStoreRad I rateNew rad } evm) := by
  have hart :
      evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNew } evm
          (.storage (ilksF (.var "i") "Art")) =
        .ok (.int (Int.ofNat artOld.toNat)) := by
    rw [evalExpr_fold_ilks_art evm I (foldStoreRateNew I rateNew) hsz100
      (foldStoreRateNew_get_i I rateNew) (foldStoreRateNew_ilks I rateNew)]
    rw [hload]
  have hrate :
      evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNew } evm
        (.var "rate") = .ok (.int (foldRateInt I)) :=
    vatEvalExpr_varInt (foldStoreRateNew_get_rate I rateNew)
  have hmul :
      evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNew } evm
        (.binary .mul (.storage (ilksF (.var "i") "Art")) (.var "rate")) =
        .ok (.int rad) :=
    evalExpr_fold_mul_int_ok hart hrate hrad
  have hlet :
      evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNew } evm
        (s256 (.binary .mul (.storage (ilksF (.var "i") "Art")) (.var "rate"))) =
        .ok (.int rad) :=
    evalExpr_fold_s256_ok hmul hradLo hradHi
  change ExecBlock config { contract := contract, locals := foldStoreRateNew I rateNew } evm
    [ .letDecl "rad" (some int256)
        (s256 (.binary .mul (.storage (ilksF (.var "i") "Art")) (.var "rate"))),
      .require (.binary .le (.storage (ilksF (.var "i") "Art")) (.intLit maxInt256)),
      .require
        (eitherExpr (.binary .eq (.var "rate") (.intLit 0))
          (.binary .eq (.binary .div (.var "rad") (.var "rate"))
            (.storage (ilksF (.var "i") "Art")))) ]
    (.ok { contract := contract, locals := foldStoreRad I rateNew rad } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardMax) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguardMul) ExecBlock.nil

theorem vatFoldRadMulOk_zero_art (evm : EVM.State) (I : ExecutionEnv)
    {rateNew artOld : UInt256} (hsz100 : 100 ≤ I.calldata.size)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (foldArtSlot I) = artOld)
    (hartZero : artOld = ⟨0⟩)
    (hrateWordNe : foldRateWord I ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := foldStoreRateNew I rateNew } evm
      (checkedMulSignedInto "rad" (.storage (ilksF (.var "i") "Art")) (.var "rate"))
      (.ok { contract := contract, locals := foldStoreRad I rateNew 0 } evm) := by
  have hrateNe : foldRateInt I ≠ 0 :=
    foldRateInt_ne_zero_of_word_ne_zero I hrateWordNe
  have hrad : (0 : Int) = Int.ofNat artOld.toNat * foldRateInt I := by
    simp [hartZero]
  have hart :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew 0 } evm
          (.storage (ilksF (.var "i") "Art")) =
        .ok (.int (Int.ofNat artOld.toNat)) := by
    rw [evalExpr_fold_ilks_art evm I (foldStoreRad I rateNew 0) hsz100
      (foldStoreRad_get_i I rateNew 0) (foldStoreRad_ilks I rateNew 0)]
    rw [hload]
  have hguardMax :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew 0 } evm
        (.binary .le (.storage (ilksF (.var "i") "Art")) (.intLit maxInt256)) =
      .ok (.bool true) := by
    have hmaxLit :
        evalExpr? config { contract := contract, locals := foldStoreRad I rateNew 0 } evm
          (.intLit maxInt256) = .ok (.int maxInt256) := by
      simp [evalExpr?, pure]
    have hle : Int.ofNat artOld.toNat ≤ maxInt256 := by
      simp [hartZero, maxInt256]
    exact vatEvalExpr_le_int_true hart hmaxLit hle
  have hguardMul :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew 0 } evm
        (eitherExpr (.binary .eq (.var "rate") (.intLit 0))
          (.binary .eq (.binary .div (.var "rad") (.var "rate"))
            (.storage (ilksF (.var "i") "Art")))) =
      .ok (.bool true) := by
    exact evalExpr_fold_mul_guard_rad_zero_art_zero_true evm I rateNew hrateNe
      (by simpa [hartZero] using hart)
  exact vatFoldRadMulOk evm I hsz100 hload hrad (by norm_num) (by norm_num)
    hguardMax hguardMul

theorem vatFoldRadMulRevertMax (evm : EVM.State) (I : ExecutionEnv)
    {rateNew artOld : UInt256} (hsz100 : 100 ≤ I.calldata.size)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (foldArtSlot I) = artOld)
    (hgt : maxInt256 < Int.ofNat artOld.toNat) :
    ExecBlock config { contract := contract, locals := foldStoreRateNew I rateNew } evm
      (checkedMulSignedInto "rad" (.storage (ilksF (.var "i") "Art")) (.var "rate"))
      .reverted := by
  let prod := Int.ofNat artOld.toNat * foldRateInt I
  have hart :
      evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNew } evm
          (.storage (ilksF (.var "i") "Art")) =
        .ok (.int (Int.ofNat artOld.toNat)) := by
    rw [evalExpr_fold_ilks_art evm I (foldStoreRateNew I rateNew) hsz100
      (foldStoreRateNew_get_i I rateNew) (foldStoreRateNew_ilks I rateNew)]
    rw [hload]
  have hrate :
      evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNew } evm
        (.var "rate") = .ok (.int (foldRateInt I)) :=
    vatEvalExpr_varInt (foldStoreRateNew_get_rate I rateNew)
  have hmul :
      evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNew } evm
        (.binary .mul (.storage (ilksF (.var "i") "Art")) (.var "rate")) =
        .ok (.int prod) :=
    evalExpr_fold_mul_int_ok hart hrate rfl
  change ExecBlock config { contract := contract, locals := foldStoreRateNew I rateNew } evm
    [ .letDecl "rad" (some int256)
        (s256 (.binary .mul (.storage (ilksF (.var "i") "Art")) (.var "rate"))),
      .require (.binary .le (.storage (ilksF (.var "i") "Art")) (.intLit maxInt256)),
      .require
        (eitherExpr (.binary .eq (.var "rate") (.intLit 0))
          (.binary .eq (.binary .div (.var "rad") (.var "rate"))
            (.storage (ilksF (.var "i") "Art")))) ]
    .reverted
  by_cases hbad : prod < -((2 : Int) ^ 255) ∨ prod ≥ (2 : Int) ^ 255
  · exact ExecBlock.consRevert (ExecStmt.letDeclRevert (evalExpr_s256_revert hmul hbad))
  · have hlet := evalExpr_fold_s256_ok hmul
      (not_lt.mp (fun h => hbad (Or.inl h)))
      (not_le.mp (fun h => hbad (Or.inr h)))
    refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
    have hartRad :
        evalExpr? config { contract := contract, locals := foldStoreRad I rateNew prod } evm
            (.storage (ilksF (.var "i") "Art")) =
          .ok (.int (Int.ofNat artOld.toNat)) := by
      rw [evalExpr_fold_ilks_art evm I (foldStoreRad I rateNew prod) hsz100
        (foldStoreRad_get_i I rateNew prod) (foldStoreRad_ilks I rateNew prod)]
      rw [hload]
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse
        (vatEvalExpr_le_int_false hartRad (by simp [evalExpr?, pure]) hgt))

theorem vatFoldDaiAddOk (evm : EVM.State) (I : ExecutionEnv)
    {rateNew daiOld daiNew radWord : UInt256} {rad : Int}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (foldDaiSlot I) = daiOld)
    (hradWord : rad % (Int.ofNat EVM.wordModulus) = Int.ofNat radWord.toNat)
    (hdaiNew : daiNew = radWord + daiOld)
    (hguardNeg :
      evalExpr? config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew } evm
        (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
          (.binary .le (.var "daiNew") (.storage (daiRef (.var "u"))))) =
        .ok (.bool true))
    (hguardPos :
      evalExpr? config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew } evm
        (eitherExpr (.binary .le (.var "rad") (.intLit 0))
          (.binary .ge (.var "daiNew") (.storage (daiRef (.var "u"))))) =
        .ok (.bool true)) :
    ExecBlock config { contract := contract, locals := foldStoreRad I rateNew rad } evm
      (checkedAddSignedInto "daiNew" (.storage (daiRef (.var "u"))) (.var "rad"))
      (.ok { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew } evm) := by
  have hdai :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
          (.storage (daiRef (.var "u"))) =
        .ok (.int (Int.ofNat daiOld.toNat)) := by
    rw [evalExpr_fold_dai_u evm I (foldStoreRad I rateNew rad)
      (foldStoreRad_get_u I rateNew rad) (foldStoreRad_dai I rateNew rad)]
    rw [hload]
  have hrad :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (.var "rad") = .ok (.int rad) :=
    vatEvalExpr_varInt (foldStoreRad_get_rad I rateNew rad)
  have hlet :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (wordWrap256 (.binary .add (.storage (daiRef (.var "u"))) (.var "rad"))) =
        .ok (.int (Int.ofNat daiNew.toNat)) :=
    evalExpr_fold_wordWrapAdd_ok hdai hrad hradWord hdaiNew
  change ExecBlock config { contract := contract, locals := foldStoreRad I rateNew rad } evm
    [ .letDecl "daiNew" (some uint256)
        (wordWrap256 (.binary .add (.storage (daiRef (.var "u"))) (.var "rad"))),
      .require
        (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
          (.binary .le (.var "daiNew") (.storage (daiRef (.var "u"))))),
      .require
        (eitherExpr (.binary .le (.var "rad") (.intLit 0))
          (.binary .ge (.var "daiNew") (.storage (daiRef (.var "u"))))) ]
    (.ok { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNeg) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguardPos) ExecBlock.nil

theorem vatFoldDebtAddOk (evm : EVM.State) (I : ExecutionEnv)
    {rateNew daiNew debtOld debtNew radWord : UInt256} {rad : Int}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner foldDebtSlot = debtOld)
    (hradWord : rad % (Int.ofNat EVM.wordModulus) = Int.ofNat radWord.toNat)
    (hdebtNew : debtNew = radWord + debtOld)
    (hguardNeg :
      evalExpr? config
        { contract := contract, locals := foldStoreDebtNew I rateNew rad daiNew debtNew } evm
        (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
          (.binary .le (.var "debtNew") (.storage debtRef))) =
        .ok (.bool true))
    (hguardPos :
      evalExpr? config
        { contract := contract, locals := foldStoreDebtNew I rateNew rad daiNew debtNew } evm
        (eitherExpr (.binary .le (.var "rad") (.intLit 0))
          (.binary .ge (.var "debtNew") (.storage debtRef))) =
        .ok (.bool true)) :
    ExecBlock config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew } evm
      (checkedAddSignedInto "debtNew" (.storage debtRef) (.var "rad"))
      (.ok { contract := contract, locals := foldStoreDebtNew I rateNew rad daiNew debtNew } evm) := by
  have hdebt :
      evalExpr? config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew }
          evm (.storage debtRef) =
        .ok (.int (Int.ofNat debtOld.toNat)) := by
    rw [evalExpr_fold_debt evm (foldStoreDaiNew I rateNew rad daiNew)
      (foldStoreDaiNew_debt I rateNew rad daiNew)]
    rw [hload]
  have hrad :
      evalExpr? config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew }
        evm (.var "rad") = .ok (.int rad) :=
    vatEvalExpr_varInt (foldStoreDaiNew_get_rad I rateNew rad daiNew)
  have hlet :
      evalExpr? config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew }
        evm (wordWrap256 (.binary .add (.storage debtRef) (.var "rad"))) =
        .ok (.int (Int.ofNat debtNew.toNat)) :=
    evalExpr_fold_wordWrapAdd_ok hdebt hrad hradWord hdebtNew
  change ExecBlock config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew }
    evm
    [ .letDecl "debtNew" (some uint256)
        (wordWrap256 (.binary .add (.storage debtRef) (.var "rad"))),
      .require
        (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
          (.binary .le (.var "debtNew") (.storage debtRef))),
      .require
        (eitherExpr (.binary .le (.var "rad") (.intLit 0))
          (.binary .ge (.var "debtNew") (.storage debtRef))) ]
    (.ok { contract := contract, locals := foldStoreDebtNew I rateNew rad daiNew debtNew } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNeg) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguardPos) ExecBlock.nil

theorem vatFoldAssignDaiOk (evm : EVM.State) (I : ExecutionEnv)
    {rateNew daiNew : UInt256} {rad : Int} :
    ExecBlock config
      { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew } evm
      [ .assign .storage (daiRef (.var "u")) (.var "daiNew") ]
      (.ok { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (foldDaiSlot I) daiNew)) := by
  have hdaiNewVar :
      evalExpr? config
        { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew }
        evm (.var "daiNew") = .ok (.int (Int.ofNat daiNew.toNat)) :=
    vatEvalExpr_varUInt256 (foldStoreDaiNew_get_daiNew I rateNew rad daiNew)
  have hdaiAssign :
      assignStorageRef? config
        { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew }
        evm .storage (daiRef (.var "u")) (.int (Int.ofNat daiNew.toNat)) =
      .ok ({ contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (foldDaiSlot I) daiNew) :=
    assign_fold_dai_u evm I (foldStoreDaiNew I rateNew rad daiNew) daiNew
      (foldStoreDaiNew_get_u I rateNew rad daiNew)
      (foldStoreDaiNew_dai I rateNew rad daiNew)
  exact ExecBlock.consNormal (ExecStmt.assign hdaiNewVar hdaiAssign) ExecBlock.nil

theorem vatFoldAssignDebtOk (evm : EVM.State) (I : ExecutionEnv)
    {rateNew daiNew debtNew : UInt256} {rad : Int} :
    ExecBlock config
      { contract := contract, locals := foldStoreDebtNew I rateNew rad daiNew debtNew } evm
      [ .assign .storage debtRef (.var "debtNew") ]
      (.ok { contract := contract, locals := foldStoreDebtNew I rateNew rad daiNew debtNew }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner foldDebtSlot debtNew)) := by
  have hdebtNewVar :
      evalExpr? config
        { contract := contract, locals := foldStoreDebtNew I rateNew rad daiNew debtNew }
        evm (.var "debtNew") = .ok (.int (Int.ofNat debtNew.toNat)) :=
    vatEvalExpr_varUInt256 (foldStoreDebtNew_get_debtNew I rateNew rad daiNew debtNew)
  have hdebtAssign :
      assignStorageRef? config
        { contract := contract, locals := foldStoreDebtNew I rateNew rad daiNew debtNew }
        evm .storage debtRef (.int (Int.ofNat debtNew.toNat)) =
      .ok ({ contract := contract, locals := foldStoreDebtNew I rateNew rad daiNew debtNew },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner foldDebtSlot debtNew) :=
    assign_fold_debt evm (foldStoreDebtNew I rateNew rad daiNew debtNew) debtNew
      (foldStoreDebtNew_debt I rateNew rad daiNew debtNew)
  exact ExecBlock.consNormal (ExecStmt.assign hdebtNewVar hdebtAssign) ExecBlock.nil

set_option maxHeartbeats 0 in
theorem vatFoldSourceSuccess (evm : EVM.State) (I : ExecutionEnv)
    {rateOld rateNew artOld radWord daiOld daiNew debtOld debtNew : UInt256}
    {rad : Int}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth :
      evalExpr? config { contract := contract, locals := foldStore I } evm
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true))
    (hlive :
      evalExpr? config { contract := contract, locals := foldStore I } evm
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true))
    (hloadRate :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (foldRateSlot I) = rateOld)
    (hrateNew : rateNew = foldRateWord I + rateOld)
    (hRateGuardNeg :
      evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNew } evm
        (eitherExpr (.binary .ge (.var "rate") (.intLit 0))
          (.binary .le (.var "rateNew") (.storage (ilksF (.var "i") "rate")))) =
        .ok (.bool true))
    (hRateGuardPos :
      evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNew } evm
        (eitherExpr (.binary .le (.var "rate") (.intLit 0))
          (.binary .ge (.var "rateNew") (.storage (ilksF (.var "i") "rate")))) =
        .ok (.bool true))
    (hloadArt :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (foldRateSlot I) rateNew)
          evm.executionEnv.codeOwner (foldArtSlot I) = artOld)
    (hrad : rad = Int.ofNat artOld.toNat * foldRateInt I)
    (hradLo : -((2 : Int) ^ 255) ≤ rad)
    (hradHi : rad < (2 : Int) ^ 255)
    (hMulGuardMax :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (foldRateSlot I) rateNew)
        (.binary .le (.storage (ilksF (.var "i") "Art")) (.intLit maxInt256)) =
        .ok (.bool true))
    (hMulGuard :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (foldRateSlot I) rateNew)
        (eitherExpr (.binary .eq (.var "rate") (.intLit 0))
          (.binary .eq (.binary .div (.var "rad") (.var "rate"))
            (.storage (ilksF (.var "i") "Art")))) =
        .ok (.bool true))
    (hloadDai :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (foldRateSlot I) rateNew)
          evm.executionEnv.codeOwner (foldDaiSlot I) = daiOld)
    (hradWord : rad % (Int.ofNat EVM.wordModulus) = Int.ofNat radWord.toNat)
    (hdaiNew : daiNew = radWord + daiOld)
    (hDaiGuardNeg :
      evalExpr? config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (foldRateSlot I) rateNew)
        (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
          (.binary .le (.var "daiNew") (.storage (daiRef (.var "u"))))) =
        .ok (.bool true))
    (hDaiGuardPos :
      evalExpr? config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (foldRateSlot I) rateNew)
        (eitherExpr (.binary .le (.var "rad") (.intLit 0))
          (.binary .ge (.var "daiNew") (.storage (daiRef (.var "u"))))) =
        .ok (.bool true))
    (hloadDebt :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (foldRateSlot I) rateNew)
            evm.executionEnv.codeOwner (foldDaiSlot I) daiNew)
          evm.executionEnv.codeOwner foldDebtSlot = debtOld)
    (hdebtNew : debtNew = radWord + debtOld)
    (hDebtGuardNeg :
      evalExpr? config
        { contract := contract, locals := foldStoreDebtNew I rateNew rad daiNew debtNew }
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (foldRateSlot I) rateNew)
          evm.executionEnv.codeOwner (foldDaiSlot I) daiNew)
        (eitherExpr (.binary .ge (.var "rad") (.intLit 0))
          (.binary .le (.var "debtNew") (.storage debtRef))) =
        .ok (.bool true))
    (hDebtGuardPos :
      evalExpr? config
        { contract := contract, locals := foldStoreDebtNew I rateNew rad daiNew debtNew }
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (foldRateSlot I) rateNew)
          evm.executionEnv.codeOwner (foldDaiSlot I) daiNew)
        (eitherExpr (.binary .le (.var "rad") (.intLit 0))
          (.binary .ge (.var "debtNew") (.storage debtRef))) =
        .ok (.bool true)) :
    ExecTransitionBody config contract evm (foldStore I) foldTransition.body
      (.returned { contract := contract, locals := foldStoreDebtNew I rateNew rad daiNew debtNew }
        (foldPostState evm I rateNew daiNew debtNew) none) := by
  let evmRate := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (foldRateSlot I) rateNew
  let evmDai := Solm.EVM.storageStore evmRate evmRate.executionEnv.codeOwner (foldDaiSlot I) daiNew
  have hprefix :
      ExecBlock config { contract := contract, locals := foldStore I } evm
        (nonpayable ++ auth ++ requireLive)
        (.ok { contract := contract, locals := foldStore I } evm) := by
    change ExecBlock config { contract := contract, locals := foldStore I } evm
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
        .require (.binary .eq (.storage liveRef) (.intLit 1)) ]
      (.ok { contract := contract, locals := foldStore I } evm)
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true hwv
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauth) ?_
    exact ExecBlock.consNormal (ExecStmt.requireTrue hlive) ExecBlock.nil
  have hrateBlock := vatFoldRateAddAssignOk evm I hsz100 hloadRate hrateNew
    hRateGuardNeg hRateGuardPos
  have hradBlock := vatFoldRadMulOk evmRate I hsz100
    (by simpa [evmRate, storageStore_executionEnv] using hloadArt)
    hrad hradLo hradHi (by simpa [evmRate] using hMulGuardMax)
    (by simpa [evmRate] using hMulGuard)
  have hdaiBlock := vatFoldDaiAddOk evmRate I
    (by simpa [evmRate, storageStore_executionEnv] using hloadDai)
    hradWord hdaiNew (by simpa [evmRate] using hDaiGuardNeg)
    (by simpa [evmRate] using hDaiGuardPos)
  have hdaiAssign := vatFoldAssignDaiOk evmRate I (rateNew := rateNew) (rad := rad)
    (daiNew := daiNew)
  have hdebtBlock := vatFoldDebtAddOk evmDai I
    (by simpa [evmDai, evmRate, storageStore_executionEnv] using hloadDebt)
    hradWord hdebtNew
    (by simpa [evmDai, evmRate, storageStore_executionEnv] using hDebtGuardNeg)
    (by simpa [evmDai, evmRate, storageStore_executionEnv] using hDebtGuardPos)
  have hdebtAssign := vatFoldAssignDebtOk evmDai I (rateNew := rateNew) (rad := rad)
    (daiNew := daiNew) (debtNew := debtNew)
  have h01 := execBlock_append hprefix hrateBlock
  have h02 := execBlock_append h01 hradBlock
  have h03 := execBlock_append h02 hdaiBlock
  have h04 := execBlock_append h03 hdaiAssign
  have h05 := execBlock_append h04 hdebtBlock
  have hblock := execBlock_append h05 hdebtAssign
  simpa [ExecTransitionBody, foldTransition, nonpayable, auth, requireLive,
    List.append_assoc, evmRate, evmDai, foldPostState, storageStore_executionEnv] using
    ExecFuncBody.execBlockOK hblock

set_option maxHeartbeats 0 in
theorem vatDecode_fold_ok {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (foldTransition.params.map Param.name)
      (transitionSignature foldTransition).paramTypes I.calldata = some (foldStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["i", "u", "rate"]
    [bytes32, addr, int256] I.calldata = _
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["i", "u", "rate"]
    [bytes32, addr, int256] I.calldata =
      some ((((∅ : Store).insert "i" (foldIlkValue I)).insert "u" (foldUsrValue I)).insert
        "rate" (foldRateValue I))
  simpa [foldIlkValue, foldUsrValue, foldRateValue, foldRateInt, foldUsrWord, foldRateWord,
    calldataWord] using
      decodeCalldata_legacyBytes32_address_int256_ok
        (cd := I.calldata) (x := "i") (y := "u") (z := "rate") hsz100

theorem vatDecode_fold_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode (foldTransition.params.map Param.name)
      (transitionSignature foldTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["i", "u", "rate"]
    [bytes32, addr, int256] I.calldata = none
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["i", "u", "rate"]
    [bytes32, addr, int256] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [bytes32, addr, int256, isDynamicABIType])]
  simp only
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, addr, int256] = some 96 by native_decide]
  simp only [bind, Option.bind]
  rw [if_pos (by rw [List.length_drop, htlen]; omega :
    (I.calldata.toList.drop 4).length < 96)]

theorem vatDispatchFold {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 9)) :
    dispatchMsg contract I.calldata = some foldTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 9 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some foldTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, LineSelectorBytes, cageSelectorBytes,
    canSelectorBytes, daiSelectorBytes, debtSelectorBytes, denySelectorBytes,
    fileIlkSelectorBytes, fileLineSelectorBytes, fluxSelectorBytes, foldSelectorBytes]
  native_decide

theorem vatReachFoldBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 9)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1245⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0xb65337df⟩ :=
    vatSelWord_eq_of_beq I hsz 0xb6 0x53 0x37 0xdf ⟨0xb65337df⟩
      (by native_decide) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh :
      UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhighlow :
      UInt256.gt (armSelNat vatBytecode vatHighLowSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms163FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms163FirstPc 2))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vatReachArms163Body 2 (by omega) ⟨1245⟩ hcode hwv hsz hsize
    hroot hhigh hhighlow heq0 htake (by jump_dest) (by native_decide)

theorem vatFoldX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 96
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨1245⟩) (ret := ⟨524⟩)
    (decoded := ⟨1267⟩) (need := ⟨96⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem vatFoldBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hsel : selIs I (vatSelBytes 9))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1245⟩ [vatSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (vatFoldX_shortarg (g := Sat256.ofUInt256 g) hsz4 hshort hsize hreach)
    |>.reEquivDecodingFailed hcode (vatDispatchFold hsel)
      (vatDecode_fold_none_short hsz4 hshort)

theorem vatFoldX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5581⟩
        [foldRateWord I, foldUsrMaskedWord I, foldIlkWord I, ⟨524⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨1245⟩) (ret := ⟨524⟩)
    (decoded := ⟨1267⟩) (need := ⟨96⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.solcSlipExternalLoadAndJump
    (code := vatBytecode) (decoded := ⟨1267⟩) (ret := ⟨524⟩) (routine := ⟨5581⟩)
    (R := [sel]) hdecoded
    (by
      unfold solcSlipExternalLoadAndJumpWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [foldRateWord, foldUsrMaskedWord, foldUsrWord, foldIlkWord, calldataWord]
      using hroutine⟩

end Benchmarks.Dss.Vat
