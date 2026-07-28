import Benchmarks.Dss.Flopper.Dent.Part2

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false

namespace Benchmarks.Dss.Flopper
theorem flopperDentBodyReverts_insufficientDecrease (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : dentLiveWord evm = ⟨1⟩)
    (hguy : dentGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (dentTimestampWord evm).toNat < (dentTicWord evm I).toNat ∨
        dentTicWord evm I = ⟨0⟩)
    (hendGt : (dentTimestampWord evm).toNat < (dentEndWord evm I).toNat)
    (hbid : dentBidWord I = dentBidStoredWord evm I)
    (hlotLt : (dentLotWord I).toNat < (dentLotStoredWord evm I).toNat)
    (hbegFit : (dentBegWord evm).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit : (dentLotStoredWord evm I).toNat * dentOneWord.toNat < UInt256.size)
    (hinsuff : (dentLotOneWord evm I).toNat < (dentBegLotWord evm I).toNat) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body .reverted := by
  have hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_dent_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_dent_tic_guard_true_zero evm I hzero
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dentTransition, nonpayable, checkedMulUintInto, List.cons_append, List.nil_append]
    using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hticGuard) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_end_gt_timestamp_true evm I hendGt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_bid_eq_true evm I hbid)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_lot_lt_true evm I hlotLt)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_dent_begLot_ok evm I hbegFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_begLot_mul_guard_true evm I hbegFit)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_dent_lotOne_ok evm I hlotOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_lotOne_mul_guard_true evm I hlotOneFit)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_dent_decrease_false evm I hinsuff)))

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyReverts_moveNoCode (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : dentLiveWord evm = ⟨1⟩)
    (hguy : dentGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (dentTimestampWord evm).toNat < (dentTicWord evm I).toNat ∨
        dentTicWord evm I = ⟨0⟩)
    (hendGt : (dentTimestampWord evm).toNat < (dentEndWord evm I).toNat)
    (hbid : dentBidWord I = dentBidStoredWord evm I)
    (hlotLt : (dentLotWord I).toNat < (dentLotStoredWord evm I).toNat)
    (hbegFit : (dentBegWord evm).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit : (dentLotStoredWord evm I).toNat * dentOneWord.toNat < UInt256.size)
    (hsuff : (dentBegLotWord evm I).toNat ≤ (dentLotOneWord evm I).toNat)
    (hcaller : UInt256.ofNat evm.executionEnv.source.val ≠ dentGuyWord evm I)
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (dentVatWord evm) = ⟨0⟩) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body .reverted := by
  have hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_dent_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_dent_tic_guard_true_zero evm I hzero
  have hcallerCond :=
    evalExpr_dent_sender_ne_guy_true_lotOneLocals evm I hcaller
  have hvat :
      evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
          (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (dentVatWord evm).toNat)) :=
    evalExpr_dent_vat_storage_of_locals evm I (dentLotOneLocals evm I)
      (by simp [dentLotOneLocals, dentBegLotLocals, dentLocals])
  have hnoCodeLookup :
      (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (dentVatWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat = 0 := by
    simpa [State.lookupAccount] using
      flopperExtCodeSizeWord_zero_lookup_code_zero
        (σ := evm.accountMap)
        (target := dentVatWord evm)
        (addr := AccountAddress.ofNat (dentVatWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hnoCode
  have hguard :
      evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_yank_extCodeGuard_false hvat hnoCodeLookup
  have hchecked :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet")
        .reverted := by
    exact checkedExternalCallNoCode hguard
  have hthen :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
            [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
          [ .ite
              (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
              (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                  (.intLit 0) [] "Ash" ++
                [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                  (.intLit 0) [.var "kissAmt"] "_kissRet")
              [],
            .assign .storage (bidsF (.var "id") "guy") sender ])
        .reverted :=
   .execBlock_append_term hchecked (by intro f e h; cases h)
  have hite :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        [.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
            [ .ite
                (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
                (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                    (.intLit 0) [] "Ash" ++
                  [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                  checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                    (.intLit 0) [.var "kissAmt"] "_kissRet")
                [],
              .assign .storage (bidsF (.var "id") "guy") sender ])
          []]
        .reverted :=
    ExecBlock.consRevert (ExecStmt.iteTrue hcallerCond hthen)
  have htail :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        ([.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
            [ .ite
                (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
                (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                    (.intLit 0) [] "Ash" ++
                  [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                  checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                    (.intLit 0) [.var "kissAmt"] "_kissRet")
                [],
              .assign .storage (bidsF (.var "id") "guy") sender ])
          []] ++
          (
          [.assign .storage (bidsF (.var "id") "lot") (.var "lot")] ++
          checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")]))
        .reverted :=
   .execBlock_append_term hite (by intro f e h; cases h)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dentTransition, nonpayable, checkedMulUintInto, List.cons_append, List.nil_append]
    using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hticGuard) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_end_gt_timestamp_true evm I hendGt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_bid_eq_true evm I hbid)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_lot_lt_true evm I hlotLt)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_dent_begLot_ok evm I hbegFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_begLot_mul_guard_true evm I hbegFit)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_dent_lotOne_ok evm I hlotOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_lotOne_mul_guard_true evm I hlotOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_decrease_true evm I hsuff)) <|
      htail)

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyReverts_moveCallFailure
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : dentLiveWord evm = ⟨1⟩)
    (hguy : dentGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (dentTimestampWord evm).toNat < (dentTicWord evm I).toNat ∨
        dentTicWord evm I = ⟨0⟩)
    (hendGt : (dentTimestampWord evm).toNat < (dentEndWord evm I).toNat)
    (hbid : dentBidWord I = dentBidStoredWord evm I)
    (hlotLt : (dentLotWord I).toNat < (dentLotStoredWord evm I).toNat)
    (hbegFit : (dentBegWord evm).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit : (dentLotStoredWord evm I).toNat * dentOneWord.toNat < UInt256.size)
    (hsuff : (dentBegLotWord evm I).toNat ≤ (dentLotOneWord evm I).toNat)
    (hcaller : UInt256.ofNat evm.executionEnv.source.val ≠ dentGuyWord evm I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (dentVatWord evm) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (dentVatWord evm).toNat)) "move" 0
        [.address evm.executionEnv.source,
          .address (AccountAddress.ofNat (dentGuyWord evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (false, evm', out) true) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body .reverted := by
  have hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_dent_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_dent_tic_guard_true_zero evm I hzero
  have hcallerCond :=
    evalExpr_dent_sender_ne_guy_true_lotOneLocals evm I hcaller
  have hvat :
      evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
          (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (dentVatWord evm).toNat)) :=
    evalExpr_dent_vat_storage_of_locals evm I (dentLotOneLocals evm I)
      (by simp [dentLotOneLocals, dentBegLotLocals, dentLocals])
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (dentVatWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flopperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := dentVatWord evm)
        (addr := AccountAddress.ofNat (dentVatWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_yank_extCodeGuard_true hvat hcodeLookup
  have hargs := evalExprs_dent_move_args_lotOneLocals evm I
  have hchecked :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet")
        .reverted := by
    exact checkedExternalCallFailure hguard hvat hargs hcall
  have hthen :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
            [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
          [ .ite
              (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
              (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                  (.intLit 0) [] "Ash" ++
                [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                  (.intLit 0) [.var "kissAmt"] "_kissRet")
              [],
            .assign .storage (bidsF (.var "id") "guy") sender ])
        .reverted :=
   .execBlock_append_term hchecked (by intro f e h; cases h)
  have hite :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        [.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
            [ .ite
                (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
                (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                    (.intLit 0) [] "Ash" ++
                  [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                  checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                    (.intLit 0) [.var "kissAmt"] "_kissRet")
                [],
              .assign .storage (bidsF (.var "id") "guy") sender ])
          []]
        .reverted :=
    ExecBlock.consRevert (ExecStmt.iteTrue hcallerCond hthen)
  have htail :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        ([.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
            [ .ite
                (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
                (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                    (.intLit 0) [] "Ash" ++
                  [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                  checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                    (.intLit 0) [.var "kissAmt"] "_kissRet")
                [],
              .assign .storage (bidsF (.var "id") "guy") sender ])
          []] ++
          (
          [.assign .storage (bidsF (.var "id") "lot") (.var "lot")] ++
          checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")]))
        .reverted :=
   .execBlock_append_term hite (by intro f e h; cases h)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dentTransition, nonpayable, checkedMulUintInto, List.cons_append, List.nil_append]
    using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hticGuard) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_end_gt_timestamp_true evm I hendGt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_bid_eq_true evm I hbid)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_lot_lt_true evm I hlotLt)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_dent_begLot_ok evm I hbegFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_begLot_mul_guard_true evm I hbegFit)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_dent_lotOne_ok evm I hlotOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_lotOne_mul_guard_true evm I hlotOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_decrease_true evm I hsuff)) <|
      htail)

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyReverts_ashNoCode_moveCallerNe_ticZero
    (evm evmMove : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : dentLiveWord evm = ⟨1⟩)
    (hguy : dentGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (dentTimestampWord evm).toNat < (dentTicWord evm I).toNat ∨
        dentTicWord evm I = ⟨0⟩)
    (hendGt : (dentTimestampWord evm).toNat < (dentEndWord evm I).toNat)
    (hbid : dentBidWord I = dentBidStoredWord evm I)
    (hlotLt : (dentLotWord I).toNat < (dentLotStoredWord evm I).toNat)
    (hbegFit : (dentBegWord evm).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit : (dentLotStoredWord evm I).toNat * dentOneWord.toNat < UInt256.size)
    (hsuff : (dentBegLotWord evm I).toNat ≤ (dentLotOneWord evm I).toNat)
    (hcaller : UInt256.ofNat evm.executionEnv.source.val ≠ dentGuyWord evm I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (dentVatWord evm) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (dentVatWord evm).toNat)) "move" 0
        [.address evm.executionEnv.source,
          .address (AccountAddress.ofNat (dentGuyWord evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmMove, out) true)
    (hticMove : dentTicWord evmMove I = ⟨0⟩)
    (hashNoCode :
      Reasoning.Theory.extCodeSizeWord evmMove.accountMap (dentGuyWord evmMove I) =
        ⟨0⟩) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body .reverted := by
  have hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_dent_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_dent_tic_guard_true_zero evm I hzero
  have hcallerCond :=
    evalExpr_dent_sender_ne_guy_true_lotOneLocals evm I hcaller
  have hvat :
      evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
          (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (dentVatWord evm).toNat)) :=
    evalExpr_dent_vat_storage_of_locals evm I (dentLotOneLocals evm I)
      (by simp [dentLotOneLocals, dentBegLotLocals, dentLocals])
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (dentVatWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flopperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := dentVatWord evm)
        (addr := AccountAddress.ofNat (dentVatWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_yank_extCodeGuard_true hvat hcodeLookup
  have hargs := evalExprs_dent_move_args_lotOneLocals evm I
  have hchecked :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet")
        (.ok { contract := contract, locals := dentMoveLocals evm I } evmMove) := by
    simpa [checkedExternalCallStmts, dentMoveLocals] using
      checkedExternalCallSuccess hguard hvat hargs hcall (dentMoveDecode_ok out)
  have hticCond :
      evalExpr? config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_dent_tic_eq_zero_true_of_locals evmMove I
      (dentMoveLocals_get_id evm I)
      (by simp [dentMoveLocals, dentLotOneLocals, dentBegLotLocals, dentLocals])
      hticMove
  have hashTarget :
      evalExpr? config { contract := contract, locals := dentMoveLocals evm I } evmMove
          (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat (dentGuyWord evmMove I).toNat)) :=
    evalExpr_dent_guy_storage_of_locals evmMove I
      (dentMoveLocals_get_id evm I)
      (by simp [dentMoveLocals, dentLotOneLocals, dentBegLotLocals, dentLocals])
  have hashNoCodeLookup :
      (UInt256.ofNat
        ((evmMove.lookupAccount (AccountAddress.ofNat (dentGuyWord evmMove I).toNat)).option
          0 (fun acc => acc.code.size))).toNat = 0 := by
    simpa [State.lookupAccount] using
      flopperExtCodeSizeWord_zero_lookup_code_zero
        (σ := evmMove.accountMap)
        (target := dentGuyWord evmMove I)
        (addr := AccountAddress.ofNat (dentGuyWord evmMove I).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hashNoCode
  have hashGuard :
      evalExpr? config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (.binary .gt (.extCodeSize (.storage (bidsF (.var "id") "guy"))) (.intLit 0)) =
          .ok (.bool false) :=
    evalExpr_yank_extCodeGuard_false hashTarget hashNoCodeLookup
  have hashChecked :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
          (.intLit 0) [] "Ash")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      (checkedExternalCallNoCode (cfg := config) (C := contract) (evm := evmMove)
        (locals := dentMoveLocals evm I) (receiver := .storage (bidsF (.var "id") "guy"))
        (retVar := "Ash") (name := "Ash") (sendVal := 0) (args := [])
        (perm := true) hashGuard)
  have hashMin :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
            (.intLit 0) [] "Ash" ++
          [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ])
        .reverted :=
   .execBlock_append_term hashChecked (by intro f e h; cases h)
  have hashBranch :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
            (.intLit 0) [] "Ash" ++
          [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
          checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
            (.intLit 0) [.var "kissAmt"] "_kissRet")
        .reverted :=
   .execBlock_append_term hashMin (by intro f e h; cases h)
  have hafterMove :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmMove
        [.ite (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
            (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                (.intLit 0) [] "Ash" ++
              [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
              checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                (.intLit 0) [.var "kissAmt"] "_kissRet")
            [],
          .assign .storage (bidsF (.var "id") "guy") sender]
        .reverted :=
    ExecBlock.consRevert (ExecStmt.iteTrue hticCond hashBranch)
  have hthen :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
            [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
          [ .ite
              (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
              (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                  (.intLit 0) [] "Ash" ++
                [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                  (.intLit 0) [.var "kissAmt"] "_kissRet")
              [],
            .assign .storage (bidsF (.var "id") "guy") sender ])
        .reverted :=
   .execBlock_append hchecked hafterMove
  have hite :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        [.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
            [ .ite
                (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
                (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                    (.intLit 0) [] "Ash" ++
                  [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                  checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                    (.intLit 0) [.var "kissAmt"] "_kissRet")
                [],
              .assign .storage (bidsF (.var "id") "guy") sender ])
          []]
        .reverted :=
    ExecBlock.consRevert (ExecStmt.iteTrue hcallerCond hthen)
  have htail :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        ([.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
            [ .ite
                (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
                (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                    (.intLit 0) [] "Ash" ++
                  [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                  checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                    (.intLit 0) [.var "kissAmt"] "_kissRet")
                [],
              .assign .storage (bidsF (.var "id") "guy") sender ])
          []] ++
          (
          [.assign .storage (bidsF (.var "id") "lot") (.var "lot")] ++
          checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")]))
        .reverted :=
   .execBlock_append_term hite (by intro f e h; cases h)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dentTransition, nonpayable, checkedMulUintInto, List.cons_append, List.nil_append]
    using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hticGuard) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_end_gt_timestamp_true evm I hendGt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_bid_eq_true evm I hbid)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_lot_lt_true evm I hlotLt)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_dent_begLot_ok evm I hbegFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_begLot_mul_guard_true evm I hbegFit)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_dent_lotOne_ok evm I hlotOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_lotOne_mul_guard_true evm I hlotOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_decrease_true evm I hsuff)) <|
      htail)

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyReverts_ashCallFailure_moveCallerNe_ticZero
    (evm evmMove evmAsh : EVM.State) (I : ExecutionEnv)
    (outMove outAsh : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : dentLiveWord evm = ⟨1⟩)
    (hguy : dentGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (dentTimestampWord evm).toNat < (dentTicWord evm I).toNat ∨
        dentTicWord evm I = ⟨0⟩)
    (hendGt : (dentTimestampWord evm).toNat < (dentEndWord evm I).toNat)
    (hbid : dentBidWord I = dentBidStoredWord evm I)
    (hlotLt : (dentLotWord I).toNat < (dentLotStoredWord evm I).toNat)
    (hbegFit : (dentBegWord evm).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit : (dentLotStoredWord evm I).toNat * dentOneWord.toNat < UInt256.size)
    (hsuff : (dentBegLotWord evm I).toNat ≤ (dentLotOneWord evm I).toNat)
    (hcaller : UInt256.ofNat evm.executionEnv.source.val ≠ dentGuyWord evm I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (dentVatWord evm) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (dentVatWord evm).toNat)) "move" 0
        [.address evm.executionEnv.source,
          .address (AccountAddress.ofNat (dentGuyWord evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmMove, outMove) true)
    (hticMove : dentTicWord evmMove I = ⟨0⟩)
    (hashCodeSize :
      Reasoning.Theory.extCodeSizeWord evmMove.accountMap (dentGuyWord evmMove I) ≠
        ⟨0⟩)
    (hashCall :
      typedCallViaEVM config evmMove
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmMove I).toNat)) "Ash" 0 []
        (false, evmAsh, outAsh) true) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body .reverted := by
  have hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_dent_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_dent_tic_guard_true_zero evm I hzero
  have hcallerCond :=
    evalExpr_dent_sender_ne_guy_true_lotOneLocals evm I hcaller
  have hvat :
      evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
          (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (dentVatWord evm).toNat)) :=
    evalExpr_dent_vat_storage_of_locals evm I (dentLotOneLocals evm I)
      (by simp [dentLotOneLocals, dentBegLotLocals, dentLocals])
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (dentVatWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flopperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := dentVatWord evm)
        (addr := AccountAddress.ofNat (dentVatWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_yank_extCodeGuard_true hvat hcodeLookup
  have hargs := evalExprs_dent_move_args_lotOneLocals evm I
  have hchecked :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet")
        (.ok { contract := contract, locals := dentMoveLocals evm I } evmMove) := by
    simpa [checkedExternalCallStmts, dentMoveLocals] using
      checkedExternalCallSuccess hguard hvat hargs hcall (dentMoveDecode_ok outMove)
  have hticCond :
      evalExpr? config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_dent_tic_eq_zero_true_of_locals evmMove I
      (dentMoveLocals_get_id evm I)
      (by simp [dentMoveLocals, dentLotOneLocals, dentBegLotLocals, dentLocals])
      hticMove
  have hashTarget :
      evalExpr? config { contract := contract, locals := dentMoveLocals evm I } evmMove
          (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat (dentGuyWord evmMove I).toNat)) :=
    evalExpr_dent_guy_storage_of_locals evmMove I
      (dentMoveLocals_get_id evm I)
      (by simp [dentMoveLocals, dentLotOneLocals, dentBegLotLocals, dentLocals])
  have hashCodeLookup :
      0 < (UInt256.ofNat
        ((evmMove.lookupAccount (AccountAddress.ofNat (dentGuyWord evmMove I).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flopperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evmMove.accountMap)
        (target := dentGuyWord evmMove I)
        (addr := AccountAddress.ofNat (dentGuyWord evmMove I).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hashCodeSize
  have hashGuard :
      evalExpr? config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (.binary .gt (.extCodeSize (.storage (bidsF (.var "id") "guy"))) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_yank_extCodeGuard_true hashTarget hashCodeLookup
  have hashArgs :
      evalExprs? config { contract := contract, locals := dentMoveLocals evm I } evmMove [] =
        .ok [] := by
    simp [evalExprs?, pure]
  have hashChecked :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
          (.intLit 0) [] "Ash")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallFailure hashGuard hashTarget hashArgs hashCall
  have hashMin :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
            (.intLit 0) [] "Ash" ++
          [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ])
        .reverted :=
   .execBlock_append_term hashChecked (by intro f e h; cases h)
  have hashBranch :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
            (.intLit 0) [] "Ash" ++
          [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
          checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
            (.intLit 0) [.var "kissAmt"] "_kissRet")
        .reverted :=
   .execBlock_append_term hashMin (by intro f e h; cases h)
  have hafterMove :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmMove
        [.ite (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
            (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                (.intLit 0) [] "Ash" ++
              [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
              checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                (.intLit 0) [.var "kissAmt"] "_kissRet")
            [],
          .assign .storage (bidsF (.var "id") "guy") sender]
        .reverted :=
    ExecBlock.consRevert (ExecStmt.iteTrue hticCond hashBranch)
  have hthen :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
            [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
          [ .ite
              (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
              (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                  (.intLit 0) [] "Ash" ++
                [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                  (.intLit 0) [.var "kissAmt"] "_kissRet")
              [],
            .assign .storage (bidsF (.var "id") "guy") sender ])
        .reverted :=
   .execBlock_append hchecked hafterMove
  have hite :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        [.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
            [ .ite
                (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
                (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                    (.intLit 0) [] "Ash" ++
                  [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                  checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                    (.intLit 0) [.var "kissAmt"] "_kissRet")
                [],
              .assign .storage (bidsF (.var "id") "guy") sender ])
          []]
        .reverted :=
    ExecBlock.consRevert (ExecStmt.iteTrue hcallerCond hthen)
  have htail :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        ([.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
            [ .ite
                (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
                (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                    (.intLit 0) [] "Ash" ++
                  [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                  checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                    (.intLit 0) [.var "kissAmt"] "_kissRet")
                [],
              .assign .storage (bidsF (.var "id") "guy") sender ])
          []] ++
          (
          [.assign .storage (bidsF (.var "id") "lot") (.var "lot")] ++
          checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")]))
        .reverted :=
   .execBlock_append_term hite (by intro f e h; cases h)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dentTransition, nonpayable, checkedMulUintInto, List.cons_append, List.nil_append]
    using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hticGuard) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_end_gt_timestamp_true evm I hendGt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_bid_eq_true evm I hbid)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_lot_lt_true evm I hlotLt)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_dent_begLot_ok evm I hbegFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_begLot_mul_guard_true evm I hbegFit)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_dent_lotOne_ok evm I hlotOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_lotOne_mul_guard_true evm I hlotOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_decrease_true evm I hsuff)) <|
      htail)

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyReverts_ashDecodeShort_moveCallerNe_ticZero
    (evm evmMove evmAsh : EVM.State) (I : ExecutionEnv)
    (outMove outAsh : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : dentLiveWord evm = ⟨1⟩)
    (hguy : dentGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (dentTimestampWord evm).toNat < (dentTicWord evm I).toNat ∨
        dentTicWord evm I = ⟨0⟩)
    (hendGt : (dentTimestampWord evm).toNat < (dentEndWord evm I).toNat)
    (hbid : dentBidWord I = dentBidStoredWord evm I)
    (hlotLt : (dentLotWord I).toNat < (dentLotStoredWord evm I).toNat)
    (hbegFit : (dentBegWord evm).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit : (dentLotStoredWord evm I).toNat * dentOneWord.toNat < UInt256.size)
    (hsuff : (dentBegLotWord evm I).toNat ≤ (dentLotOneWord evm I).toNat)
    (hcaller : UInt256.ofNat evm.executionEnv.source.val ≠ dentGuyWord evm I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (dentVatWord evm) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (dentVatWord evm).toNat)) "move" 0
        [.address evm.executionEnv.source,
          .address (AccountAddress.ofNat (dentGuyWord evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmMove, outMove) true)
    (hticMove : dentTicWord evmMove I = ⟨0⟩)
    (hashCodeSize :
      Reasoning.Theory.extCodeSizeWord evmMove.accountMap (dentGuyWord evmMove I) ≠
        ⟨0⟩)
    (hashCall :
      typedCallViaEVM config evmMove
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmMove I).toNat)) "Ash" 0 []
        (true, evmAsh, outAsh) true)
    (hashShort : outAsh.size < 32) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body .reverted := by
  have hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_dent_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_dent_tic_guard_true_zero evm I hzero
  have hcallerCond :=
    evalExpr_dent_sender_ne_guy_true_lotOneLocals evm I hcaller
  have hvat :
      evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
          (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (dentVatWord evm).toNat)) :=
    evalExpr_dent_vat_storage_of_locals evm I (dentLotOneLocals evm I)
      (by simp [dentLotOneLocals, dentBegLotLocals, dentLocals])
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (dentVatWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flopperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := dentVatWord evm)
        (addr := AccountAddress.ofNat (dentVatWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_yank_extCodeGuard_true hvat hcodeLookup
  have hargs := evalExprs_dent_move_args_lotOneLocals evm I
  have hchecked :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet")
        (.ok { contract := contract, locals := dentMoveLocals evm I } evmMove) := by
    simpa [checkedExternalCallStmts, dentMoveLocals] using
      checkedExternalCallSuccess hguard hvat hargs hcall (dentMoveDecode_ok outMove)
  have hticCond :
      evalExpr? config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_dent_tic_eq_zero_true_of_locals evmMove I
      (dentMoveLocals_get_id evm I)
      (by simp [dentMoveLocals, dentLotOneLocals, dentBegLotLocals, dentLocals])
      hticMove
  have hashTarget :
      evalExpr? config { contract := contract, locals := dentMoveLocals evm I } evmMove
          (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat (dentGuyWord evmMove I).toNat)) :=
    evalExpr_dent_guy_storage_of_locals evmMove I
      (dentMoveLocals_get_id evm I)
      (by simp [dentMoveLocals, dentLotOneLocals, dentBegLotLocals, dentLocals])
  have hashCodeLookup :
      0 < (UInt256.ofNat
        ((evmMove.lookupAccount (AccountAddress.ofNat (dentGuyWord evmMove I).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flopperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evmMove.accountMap)
        (target := dentGuyWord evmMove I)
        (addr := AccountAddress.ofNat (dentGuyWord evmMove I).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hashCodeSize
  have hashGuard :
      evalExpr? config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (.binary .gt (.extCodeSize (.storage (bidsF (.var "id") "guy"))) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_yank_extCodeGuard_true hashTarget hashCodeLookup
  have hashArgs :
      evalExprs? config { contract := contract, locals := dentMoveLocals evm I } evmMove [] =
        .ok [] := by
    simp [evalExprs?, pure]
  have hashChecked :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
          (.intLit 0) [] "Ash")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallDecodeRevert hashGuard hashTarget hashArgs hashCall
        (dentAshDecode_none_short hashShort)
  have hashMin :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
            (.intLit 0) [] "Ash" ++
          [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ])
        .reverted :=
   .execBlock_append_term hashChecked (by intro f e h; cases h)
  have hashBranch :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
            (.intLit 0) [] "Ash" ++
          [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
          checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
            (.intLit 0) [.var "kissAmt"] "_kissRet")
        .reverted :=
   .execBlock_append_term hashMin (by intro f e h; cases h)
  have hafterMove :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmMove
        [.ite (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
            (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                (.intLit 0) [] "Ash" ++
              [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
              checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                (.intLit 0) [.var "kissAmt"] "_kissRet")
            [],
          .assign .storage (bidsF (.var "id") "guy") sender]
        .reverted :=
    ExecBlock.consRevert (ExecStmt.iteTrue hticCond hashBranch)
  have hthen :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
            [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
          [ .ite
              (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
              (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                  (.intLit 0) [] "Ash" ++
                [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                  (.intLit 0) [.var "kissAmt"] "_kissRet")
              [],
            .assign .storage (bidsF (.var "id") "guy") sender ])
        .reverted :=
   .execBlock_append hchecked hafterMove
  have hite :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        [.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
            [ .ite
                (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
                (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                    (.intLit 0) [] "Ash" ++
                  [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                  checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                    (.intLit 0) [.var "kissAmt"] "_kissRet")
                [],
              .assign .storage (bidsF (.var "id") "guy") sender ])
          []]
        .reverted :=
    ExecBlock.consRevert (ExecStmt.iteTrue hcallerCond hthen)
  have htail :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        ([.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
            [ .ite
                (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
                (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                    (.intLit 0) [] "Ash" ++
                  [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                  checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                    (.intLit 0) [.var "kissAmt"] "_kissRet")
                [],
              .assign .storage (bidsF (.var "id") "guy") sender ])
          []] ++
          (
          [.assign .storage (bidsF (.var "id") "lot") (.var "lot")] ++
          checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")]))
        .reverted :=
   .execBlock_append_term hite (by intro f e h; cases h)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dentTransition, nonpayable, checkedMulUintInto, List.cons_append, List.nil_append]
    using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hticGuard) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_end_gt_timestamp_true evm I hendGt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_bid_eq_true evm I hbid)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_lot_lt_true evm I hlotLt)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_dent_begLot_ok evm I hbegFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_begLot_mul_guard_true evm I hbegFit)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_dent_lotOne_ok evm I hlotOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_lotOne_mul_guard_true evm I hlotOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_decrease_true evm I hsuff)) <|
      htail)

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyReverts_afterAshRevert_moveCallerNe_ticZero
    (evm evmMove evmAsh : EVM.State) (I : ExecutionEnv)
    (outMove outAsh : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : dentLiveWord evm = ⟨1⟩)
    (hguy : dentGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (dentTimestampWord evm).toNat < (dentTicWord evm I).toNat ∨
        dentTicWord evm I = ⟨0⟩)
    (hendGt : (dentTimestampWord evm).toNat < (dentEndWord evm I).toNat)
    (hbid : dentBidWord I = dentBidStoredWord evm I)
    (hlotLt : (dentLotWord I).toNat < (dentLotStoredWord evm I).toNat)
    (hbegFit : (dentBegWord evm).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit : (dentLotStoredWord evm I).toNat * dentOneWord.toNat < UInt256.size)
    (hsuff : (dentBegLotWord evm I).toNat ≤ (dentLotOneWord evm I).toNat)
    (hcaller : UInt256.ofNat evm.executionEnv.source.val ≠ dentGuyWord evm I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (dentVatWord evm) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (dentVatWord evm).toNat)) "move" 0
        [.address evm.executionEnv.source,
          .address (AccountAddress.ofNat (dentGuyWord evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmMove, outMove) true)
    (hticMove : dentTicWord evmMove I = ⟨0⟩)
    (hashCodeSize :
      Reasoning.Theory.extCodeSizeWord evmMove.accountMap (dentGuyWord evmMove I) ≠
        ⟨0⟩)
    (hashCall :
      typedCallViaEVM config evmMove
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmMove I).toNat)) "Ash" 0 []
        (true, evmAsh, outAsh) true)
    (houtAsh32 : 32 ≤ outAsh.size)
    (hafterAsh :
      ExecBlock config { contract := contract, locals := dentAshLocals evm I outAsh } evmAsh
        ([ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
          checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
            (.intLit 0) [.var "kissAmt"] "_kissRet")
        .reverted) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body .reverted := by
  have hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_dent_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_dent_tic_guard_true_zero evm I hzero
  have hcallerCond :=
    evalExpr_dent_sender_ne_guy_true_lotOneLocals evm I hcaller
  have hvat :
      evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
          (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (dentVatWord evm).toNat)) :=
    evalExpr_dent_vat_storage_of_locals evm I (dentLotOneLocals evm I)
      (by simp [dentLotOneLocals, dentBegLotLocals, dentLocals])
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (dentVatWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flopperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := dentVatWord evm)
        (addr := AccountAddress.ofNat (dentVatWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_yank_extCodeGuard_true hvat hcodeLookup
  have hargs := evalExprs_dent_move_args_lotOneLocals evm I
  have hchecked :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet")
        (.ok { contract := contract, locals := dentMoveLocals evm I } evmMove) := by
    simpa [checkedExternalCallStmts, dentMoveLocals] using
      checkedExternalCallSuccess hguard hvat hargs hcall (dentMoveDecode_ok outMove)
  have hticCond :
      evalExpr? config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_dent_tic_eq_zero_true_of_locals evmMove I
      (dentMoveLocals_get_id evm I)
      (by simp [dentMoveLocals, dentLotOneLocals, dentBegLotLocals, dentLocals])
      hticMove
  have hashTarget :
      evalExpr? config { contract := contract, locals := dentMoveLocals evm I } evmMove
          (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat (dentGuyWord evmMove I).toNat)) :=
    evalExpr_dent_guy_storage_of_locals evmMove I
      (dentMoveLocals_get_id evm I)
      (by simp [dentMoveLocals, dentLotOneLocals, dentBegLotLocals, dentLocals])
  have hashCodeLookup :
      0 < (UInt256.ofNat
        ((evmMove.lookupAccount (AccountAddress.ofNat (dentGuyWord evmMove I).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flopperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evmMove.accountMap)
        (target := dentGuyWord evmMove I)
        (addr := AccountAddress.ofNat (dentGuyWord evmMove I).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hashCodeSize
  have hashGuard :
      evalExpr? config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (.binary .gt (.extCodeSize (.storage (bidsF (.var "id") "guy"))) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_yank_extCodeGuard_true hashTarget hashCodeLookup
  have hashArgs :
      evalExprs? config { contract := contract, locals := dentMoveLocals evm I } evmMove [] =
        .ok [] := by
    simp [evalExprs?, pure]
  have hashChecked :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
          (.intLit 0) [] "Ash")
        (.ok { contract := contract, locals := dentAshLocals evm I outAsh } evmAsh) := by
    simpa [checkedExternalCallStmts, dentAshLocals] using
      checkedExternalCallSuccess hashGuard hashTarget hashArgs hashCall
        (dentAshDecode_ok houtAsh32)
  have hashBranch :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
            (.intLit 0) [] "Ash" ++
          [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
          checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
            (.intLit 0) [.var "kissAmt"] "_kissRet")
        .reverted := by
    simpa [List.append_assoc] using
     .execBlock_append hashChecked hafterAsh
  have hafterMove :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmMove
        [.ite (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
            (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                (.intLit 0) [] "Ash" ++
              [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
              checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                (.intLit 0) [.var "kissAmt"] "_kissRet")
            [],
          .assign .storage (bidsF (.var "id") "guy") sender]
        .reverted :=
    ExecBlock.consRevert (ExecStmt.iteTrue hticCond hashBranch)
  have hthen :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
            [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
          [ .ite
              (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
              (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                  (.intLit 0) [] "Ash" ++
                [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                  (.intLit 0) [.var "kissAmt"] "_kissRet")
              [],
            .assign .storage (bidsF (.var "id") "guy") sender ])
        .reverted :=
   .execBlock_append hchecked hafterMove
  have hite :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        [.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
            [ .ite
                (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
                (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                    (.intLit 0) [] "Ash" ++
                  [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                  checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                    (.intLit 0) [.var "kissAmt"] "_kissRet")
                [],
              .assign .storage (bidsF (.var "id") "guy") sender ])
          []]
        .reverted :=
    ExecBlock.consRevert (ExecStmt.iteTrue hcallerCond hthen)
  have htail :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        ([.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
            [ .ite
                (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
                (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                    (.intLit 0) [] "Ash" ++
                  [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                  checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                    (.intLit 0) [.var "kissAmt"] "_kissRet")
                [],
              .assign .storage (bidsF (.var "id") "guy") sender ])
          []] ++
          (
          [.assign .storage (bidsF (.var "id") "lot") (.var "lot")] ++
          checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")]))
        .reverted :=
   .execBlock_append_term hite (by intro f e h; cases h)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dentTransition, nonpayable, checkedMulUintInto, List.cons_append, List.nil_append]
    using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hticGuard) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_end_gt_timestamp_true evm I hendGt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_bid_eq_true evm I hbid)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_lot_lt_true evm I hlotLt)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_dent_begLot_ok evm I hbegFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_begLot_mul_guard_true evm I hbegFit)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_dent_lotOne_ok evm I hlotOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_lotOne_mul_guard_true evm I hlotOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_dent_decrease_true evm I hsuff)) <|
      htail)

theorem flopperDentBodyReverts_kissNoCode_moveCallerNe_ticZero
    (evm evmMove evmAsh : EVM.State) (I : ExecutionEnv)
    (outMove outAsh : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : dentLiveWord evm = ⟨1⟩)
    (hguy : dentGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (dentTimestampWord evm).toNat < (dentTicWord evm I).toNat ∨
        dentTicWord evm I = ⟨0⟩)
    (hendGt : (dentTimestampWord evm).toNat < (dentEndWord evm I).toNat)
    (hbid : dentBidWord I = dentBidStoredWord evm I)
    (hlotLt : (dentLotWord I).toNat < (dentLotStoredWord evm I).toNat)
    (hbegFit : (dentBegWord evm).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit : (dentLotStoredWord evm I).toNat * dentOneWord.toNat < UInt256.size)
    (hsuff : (dentBegLotWord evm I).toNat ≤ (dentLotOneWord evm I).toNat)
    (hcaller : UInt256.ofNat evm.executionEnv.source.val ≠ dentGuyWord evm I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (dentVatWord evm) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (dentVatWord evm).toNat)) "move" 0
        [.address evm.executionEnv.source,
          .address (AccountAddress.ofNat (dentGuyWord evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmMove, outMove) true)
    (hticMove : dentTicWord evmMove I = ⟨0⟩)
    (hashCodeSize :
      Reasoning.Theory.extCodeSizeWord evmMove.accountMap (dentGuyWord evmMove I) ≠
        ⟨0⟩)
    (hashCall :
      typedCallViaEVM config evmMove
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmMove I).toNat)) "Ash" 0 []
        (true, evmAsh, outAsh) true)
    (houtAsh32 : 32 ≤ outAsh.size)
    (hkissNoCode :
      Reasoning.Theory.extCodeSizeWord evmAsh.accountMap (dentGuyWord evmAsh I) =
        ⟨0⟩) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body .reverted :=
  flopperDentBodyReverts_afterAshRevert_moveCallerNe_ticZero
    evm evmMove evmAsh I outMove outAsh hwv hlive hguy hticOk hendGt hbid hlotLt
    hbegFit hlotOneFit hsuff hcaller hcodeSize hcall hticMove hashCodeSize hashCall
    houtAsh32
    (flopperDentBodyAfterAshSuccessKissNoCode evm evmAsh I outAsh hkissNoCode)

theorem flopperDentBodyReverts_kissCallFailure_moveCallerNe_ticZero
    (evm evmMove evmAsh evmKiss : EVM.State) (I : ExecutionEnv)
    (outMove outAsh outKiss : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : dentLiveWord evm = ⟨1⟩)
    (hguy : dentGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (dentTimestampWord evm).toNat < (dentTicWord evm I).toNat ∨
        dentTicWord evm I = ⟨0⟩)
    (hendGt : (dentTimestampWord evm).toNat < (dentEndWord evm I).toNat)
    (hbid : dentBidWord I = dentBidStoredWord evm I)
    (hlotLt : (dentLotWord I).toNat < (dentLotStoredWord evm I).toNat)
    (hbegFit : (dentBegWord evm).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit : (dentLotStoredWord evm I).toNat * dentOneWord.toNat < UInt256.size)
    (hsuff : (dentBegLotWord evm I).toNat ≤ (dentLotOneWord evm I).toNat)
    (hcaller : UInt256.ofNat evm.executionEnv.source.val ≠ dentGuyWord evm I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (dentVatWord evm) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (dentVatWord evm).toNat)) "move" 0
        [.address evm.executionEnv.source,
          .address (AccountAddress.ofNat (dentGuyWord evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmMove, outMove) true)
    (hticMove : dentTicWord evmMove I = ⟨0⟩)
    (hashCodeSize :
      Reasoning.Theory.extCodeSizeWord evmMove.accountMap (dentGuyWord evmMove I) ≠
        ⟨0⟩)
    (hashCall :
      typedCallViaEVM config evmMove
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmMove I).toNat)) "Ash" 0 []
        (true, evmAsh, outAsh) true)
    (houtAsh32 : 32 ≤ outAsh.size)
    (hkissCodeSize :
      Reasoning.Theory.extCodeSizeWord evmAsh.accountMap (dentGuyWord evmAsh I) ≠
        ⟨0⟩)
    (hkissCall :
      typedCallViaEVM config evmAsh
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmAsh I).toNat)) "kiss" 0
        [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)]
        (false, evmKiss, outKiss) true) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body .reverted :=
  flopperDentBodyReverts_afterAshRevert_moveCallerNe_ticZero
    evm evmMove evmAsh I outMove outAsh hwv hlive hguy hticOk hendGt hbid hlotLt
    hbegFit hlotOneFit hsuff hcaller hcodeSize hcall hticMove hashCodeSize hashCall
    houtAsh32
    (flopperDentBodyAfterAshSuccessKissCallFailure
      evm evmAsh evmKiss I outAsh outKiss hkissCodeSize hkissCall)

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyMoveSuccessTicNonzeroToLot
    (evm evmMove : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hcaller : UInt256.ofNat evm.executionEnv.source.val ≠ dentGuyWord evm I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (dentVatWord evm) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (dentVatWord evm).toNat)) "move" 0
        [.address evm.executionEnv.source,
          .address (AccountAddress.ofNat (dentGuyWord evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmMove, out) true)
    (hticMove : dentTicWord evmMove I ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
      ([.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
            [ .ite
                (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
                (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                    (.intLit 0) [] "Ash" ++
                  [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                  checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                    (.intLit 0) [.var "kissAmt"] "_kissRet")
                [],
              .assign .storage (bidsF (.var "id") "guy") sender ])
          []] ++
        [.assign .storage (bidsF (.var "id") "lot") (.var "lot")])
      (.ok { contract := contract, locals := dentMoveLocals evm I }
        (dentAfterLotStore (dentAfterGuyStore evmMove I) I)) := by
  let evmGuy := dentAfterGuyStore evmMove I
  let evmLot := dentAfterLotStore evmGuy I
  have hcallerCond :=
    evalExpr_dent_sender_ne_guy_true_lotOneLocals evm I hcaller
  have hvat :
      evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
          (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (dentVatWord evm).toNat)) :=
    evalExpr_dent_vat_storage_of_locals evm I (dentLotOneLocals evm I)
      (by simp [dentLotOneLocals, dentBegLotLocals, dentLocals])
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (dentVatWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flopperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := dentVatWord evm)
        (addr := AccountAddress.ofNat (dentVatWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_yank_extCodeGuard_true hvat hcodeLookup
  have hargs := evalExprs_dent_move_args_lotOneLocals evm I
  have hdec := dentMoveDecode_ok out
  have hchecked :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet")
        (.ok { contract := contract, locals := dentMoveLocals evm I } evmMove) := by
    simpa [checkedExternalCallStmts, dentMoveLocals] using
      checkedExternalCallSuccess hguard hvat hargs hcall hdec
  have hticCond :
      evalExpr? config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
          .ok (.bool false) :=
    evalExpr_dent_tic_eq_zero_false_of_locals evmMove I
      (dentMoveLocals_get_id evm I)
      (by simp [dentMoveLocals, dentLotOneLocals, dentBegLotLocals, dentLocals])
      hticMove
  have hguyAssign :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmMove
        [.ite (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
            (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                (.intLit 0) [] "Ash" ++
              [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
              checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                (.intLit 0) [.var "kissAmt"] "_kissRet")
            [],
          .assign .storage (bidsF (.var "id") "guy") sender]
        (.ok { contract := contract, locals := dentMoveLocals evm I } evmGuy) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hticCond ExecBlock.nil) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_dent_sender evmMove (dentMoveLocals evm I))
          (by
            simpa [evmGuy] using
              assign_dentGuyStorage_of_locals evmMove I
                (dentMoveLocals_get_id evm I) (dentMoveLocals_get_bids evm I)))
        ExecBlock.nil
  have hthen :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
            [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
          [ .ite
              (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
              (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                  (.intLit 0) [] "Ash" ++
                [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                  (.intLit 0) [.var "kissAmt"] "_kissRet")
              [],
            .assign .storage (bidsF (.var "id") "guy") sender ])
        (.ok { contract := contract, locals := dentMoveLocals evm I } evmGuy) :=
   .execBlock_append hchecked hguyAssign
  have hite :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        [.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
            [ .ite
                (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
                (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                    (.intLit 0) [] "Ash" ++
                  [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                  checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                    (.intLit 0) [.var "kissAmt"] "_kissRet")
                [],
              .assign .storage (bidsF (.var "id") "guy") sender ])
          []]
        (.ok { contract := contract, locals := dentMoveLocals evm I } evmGuy) :=
    ExecBlock.consNormal (ExecStmt.iteTrue hcallerCond hthen) ExecBlock.nil
  have hlotAssign :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmGuy
        [.assign .storage (bidsF (.var "id") "lot") (.var "lot")]
        (.ok { contract := contract, locals := dentMoveLocals evm I } evmLot) := by
    exact ExecBlock.consNormal
      (ExecStmt.assign (evalExpr_dent_lot_var_moveLocals evm evmGuy I)
        (by
          simpa [evmLot] using
            assign_dentLotStorage_of_locals evmGuy I
              (dentMoveLocals_get_id evm I) (dentMoveLocals_get_bids evm I)))
      ExecBlock.nil
  have htail :=
   .execBlock_append hite hlotAssign
  simpa [evmGuy, evmLot] using htail

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyMoveAshKissSuccessTicZeroToLot
    (evm evmMove evmAsh evmKiss : EVM.State) (I : ExecutionEnv)
    (outMove outAsh outKiss : ByteArray)
    (hcaller : UInt256.ofNat evm.executionEnv.source.val ≠ dentGuyWord evm I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (dentVatWord evm) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (dentVatWord evm).toNat)) "move" 0
        [.address evm.executionEnv.source,
          .address (AccountAddress.ofNat (dentGuyWord evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmMove, outMove) true)
    (hticMove : dentTicWord evmMove I = ⟨0⟩)
    (hashCodeSize :
      Reasoning.Theory.extCodeSizeWord evmMove.accountMap (dentGuyWord evmMove I) ≠
        ⟨0⟩)
    (hashCall :
      typedCallViaEVM config evmMove
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmMove I).toNat)) "Ash" 0 []
        (true, evmAsh, outAsh) true)
    (houtAsh32 : 32 ≤ outAsh.size)
    (hkissCodeSize :
      Reasoning.Theory.extCodeSizeWord evmAsh.accountMap (dentGuyWord evmAsh I) ≠
        ⟨0⟩)
    (hkissCall :
      typedCallViaEVM config evmAsh
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmAsh I).toNat)) "kiss" 0
        [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)]
        (true, evmKiss, outKiss) true) :
    ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
      ([.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
            [ .ite
                (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
                (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                    (.intLit 0) [] "Ash" ++
                  [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                  checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                    (.intLit 0) [.var "kissAmt"] "_kissRet")
                [],
              .assign .storage (bidsF (.var "id") "guy") sender ])
          []] ++
        [.assign .storage (bidsF (.var "id") "lot") (.var "lot")])
      (.ok { contract := contract, locals := dentKissRetLocals evm I outAsh }
        (dentAfterLotStore (dentAfterGuyStore evmKiss I) I)) := by
  let evmGuy := dentAfterGuyStore evmKiss I
  let evmLot := dentAfterLotStore evmGuy I
  have hcallerCond :=
    evalExpr_dent_sender_ne_guy_true_lotOneLocals evm I hcaller
  have hvat :
      evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
          (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (dentVatWord evm).toNat)) :=
    evalExpr_dent_vat_storage_of_locals evm I (dentLotOneLocals evm I)
      (by simp [dentLotOneLocals, dentBegLotLocals, dentLocals])
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (dentVatWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flopperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := dentVatWord evm)
        (addr := AccountAddress.ofNat (dentVatWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := dentLotOneLocals evm I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_yank_extCodeGuard_true hvat hcodeLookup
  have hargs := evalExprs_dent_move_args_lotOneLocals evm I
  have hchecked :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet")
        (.ok { contract := contract, locals := dentMoveLocals evm I } evmMove) := by
    simpa [checkedExternalCallStmts, dentMoveLocals] using
      checkedExternalCallSuccess hguard hvat hargs hcall (dentMoveDecode_ok outMove)
  have hticCond :
      evalExpr? config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_dent_tic_eq_zero_true_of_locals evmMove I
      (dentMoveLocals_get_id evm I)
      (by simp [dentMoveLocals, dentLotOneLocals, dentBegLotLocals, dentLocals])
      hticMove
  have hashTarget :
      evalExpr? config { contract := contract, locals := dentMoveLocals evm I } evmMove
          (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat (dentGuyWord evmMove I).toNat)) :=
    evalExpr_dent_guy_storage_of_locals evmMove I
      (dentMoveLocals_get_id evm I)
      (by simp [dentMoveLocals, dentLotOneLocals, dentBegLotLocals, dentLocals])
  have hashCodeLookup :
      0 < (UInt256.ofNat
        ((evmMove.lookupAccount (AccountAddress.ofNat (dentGuyWord evmMove I).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flopperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evmMove.accountMap)
        (target := dentGuyWord evmMove I)
        (addr := AccountAddress.ofNat (dentGuyWord evmMove I).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hashCodeSize
  have hashGuard :
      evalExpr? config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (.binary .gt (.extCodeSize (.storage (bidsF (.var "id") "guy"))) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_yank_extCodeGuard_true hashTarget hashCodeLookup
  have hashArgs :
      evalExprs? config { contract := contract, locals := dentMoveLocals evm I } evmMove [] =
        .ok [] := by
    simp [evalExprs?, pure]
  have hashChecked :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
          (.intLit 0) [] "Ash")
        (.ok { contract := contract, locals := dentAshLocals evm I outAsh } evmAsh) := by
    simpa [checkedExternalCallStmts, dentAshLocals] using
      checkedExternalCallSuccess hashGuard hashTarget hashArgs hashCall
        (dentAshDecode_ok houtAsh32)
  have hafterAsh :=
    flopperDentBodyAfterAshSuccessKissCallSuccess
      evm evmAsh evmKiss I outAsh outKiss hkissCodeSize hkissCall
  have hashBranch :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmMove
        (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
            (.intLit 0) [] "Ash" ++
          [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
          checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
            (.intLit 0) [.var "kissAmt"] "_kissRet")
        (.ok { contract := contract, locals := dentKissRetLocals evm I outAsh } evmKiss) := by
    simpa [List.append_assoc] using
     .execBlock_append hashChecked hafterAsh
  have hinnerGuy :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmMove
        [.ite (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
            (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                (.intLit 0) [] "Ash" ++
              [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
              checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                (.intLit 0) [.var "kissAmt"] "_kissRet")
            [],
          .assign .storage (bidsF (.var "id") "guy") sender]
        (.ok { contract := contract, locals := dentKissRetLocals evm I outAsh } evmGuy) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hticCond hashBranch) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_dent_sender evmKiss (dentKissRetLocals evm I outAsh))
          (by
            simpa [evmGuy] using
              assign_dentGuyStorage_of_locals evmKiss I
                (dentKissRetLocals_get_id evm I outAsh)
                (dentKissRetLocals_get_bids evm I outAsh)))
        ExecBlock.nil
  have hthen :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
            [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
          [ .ite
              (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
              (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                  (.intLit 0) [] "Ash" ++
                [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                  (.intLit 0) [.var "kissAmt"] "_kissRet")
              [],
            .assign .storage (bidsF (.var "id") "guy") sender ])
        (.ok { contract := contract, locals := dentKissRetLocals evm I outAsh } evmGuy) :=
   .execBlock_append hchecked hinnerGuy
  have hite :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evm
        [.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
            [ .ite
                (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
                (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash"
                    (.intLit 0) [] "Ash" ++
                  [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                  checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
                    (.intLit 0) [.var "kissAmt"] "_kissRet")
                [],
              .assign .storage (bidsF (.var "id") "guy") sender ])
          []]
        (.ok { contract := contract, locals := dentKissRetLocals evm I outAsh } evmGuy) :=
    ExecBlock.consNormal (ExecStmt.iteTrue hcallerCond hthen) ExecBlock.nil
  have hlotAssign :
      ExecBlock config { contract := contract, locals := dentKissRetLocals evm I outAsh }
          evmGuy
        [.assign .storage (bidsF (.var "id") "lot") (.var "lot")]
        (.ok { contract := contract, locals := dentKissRetLocals evm I outAsh } evmLot) := by
    exact ExecBlock.consNormal
      (ExecStmt.assign (evalExpr_dent_lot_var_kissRetLocals evm evmGuy I outAsh)
        (by
          simpa [evmLot] using
            assign_dentLotStorage_of_locals evmGuy I
              (dentKissRetLocals_get_id evm I outAsh)
              (dentKissRetLocals_get_bids evm I outAsh)))
      ExecBlock.nil
  have htail :=
   .execBlock_append hite hlotAssign
  simpa [evmGuy, evmLot] using htail

end Benchmarks.Dss.Flopper
