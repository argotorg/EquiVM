import Benchmarks.Dss.Flopper.Dent.Part3

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false

namespace Benchmarks.Dss.Flopper
set_option maxHeartbeats 1000000 in
theorem flopperDentBodyReverts_addOverflow_moveCallerNe_ticZero_kissSuccess
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
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap (dentVatWord evm) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (dentVatWord evm).toNat)) "move" 0
        [.address evm.executionEnv.source,
          .address (AccountAddress.ofNat (dentGuyWord evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmMove, outMove) true)
    (hticMove : dentTicWord evmMove I = ⟨0⟩)
    (hashCodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evmMove.accountMap (dentGuyWord evmMove I) ≠
        ⟨0⟩)
    (hashCall :
      typedCallViaEVM config evmMove
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmMove I).toNat)) "Ash" 0 []
        (true, evmAsh, outAsh) true)
    (houtAsh32 : 32 ≤ outAsh.size)
    (hkissCodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evmAsh.accountMap (dentGuyWord evmAsh I) ≠
        ⟨0⟩)
    (hkissCall :
      typedCallViaEVM config evmAsh
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmAsh I).toNat)) "kiss" 0
        [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)]
        (true, evmKiss, outKiss) true)
    (haddOverflow :
      2 ^ 48 ≤
        (dentNow48Word (dentAfterGuyStore evmKiss I)).toNat +
          (dentTtlWord (dentAfterLotStore (dentAfterGuyStore evmKiss I) I)).toNat) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body .reverted := by
  let evmGuy := dentAfterGuyStore evmKiss I
  let evmLot := dentAfterLotStore evmGuy I
  have hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_dent_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_dent_tic_guard_true_zero evm I hzero
  have htailIteLot :=
    flopperDentBodyMoveAshKissSuccessTicZeroToLot
      evm evmMove evmAsh evmKiss I outMove outAsh outKiss hcaller hcodeSize hcall
      hticMove hashCodeSize hashCall houtAsh32 hkissCodeSize hkissCall
  have htickChecked :
      ExecBlock config { contract := contract, locals := dentKissRetLocals evm I outAsh }
          evmLot
        (checkedAdd48Into "tic_" now48 (.storage ttlRef)) .reverted := by
    simpa [checkedAdd48Into, evmGuy, evmLot] using
      (ExecBlock.consNormal
        (ExecStmt.letDecl
          (evalExpr_dent_ticAdd_wrapped_kissRetLocals evm evmGuy I outAsh)) <|
        ExecBlock.consRevert
          (ExecStmt.requireFalse
            (evalExpr_dent_tic_guard_false_wrapped_kissRetLocals evm evmGuy I outAsh
              haddOverflow)))
  have htickTail :
      ExecBlock config { contract := contract, locals := dentKissRetLocals evm I outAsh }
          evmLot
        (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")]) .reverted :=
    Reasoning.Refinement.execBlock_append_term htickChecked (by intro f e h; cases h)
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
          [],
         .assign .storage (bidsF (.var "id") "lot") (.var "lot")] ++
          (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
            [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")]))
        .reverted := by
    simpa [List.cons_append, List.nil_append, evmGuy, evmLot] using
      Reasoning.Refinement.execBlock_append htailIteLot htickTail
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
theorem flopperDentBodyReturns_success_moveCallerNe_ticZero_kissSuccess
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
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap (dentVatWord evm) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (dentVatWord evm).toNat)) "move" 0
        [.address evm.executionEnv.source,
          .address (AccountAddress.ofNat (dentGuyWord evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmMove, outMove) true)
    (hticMove : dentTicWord evmMove I = ⟨0⟩)
    (hashCodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evmMove.accountMap (dentGuyWord evmMove I) ≠
        ⟨0⟩)
    (hashCall :
      typedCallViaEVM config evmMove
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmMove I).toNat)) "Ash" 0 []
        (true, evmAsh, outAsh) true)
    (houtAsh32 : 32 ≤ outAsh.size)
    (hkissCodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord evmAsh.accountMap (dentGuyWord evmAsh I) ≠
        ⟨0⟩)
    (hkissCall :
      typedCallViaEVM config evmAsh
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmAsh I).toNat)) "kiss" 0
        [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)]
        (true, evmKiss, outKiss) true)
    (haddFit :
      (dentNow48Word (dentAfterGuyStore evmKiss I)).toNat +
          (dentTtlWord (dentAfterLotStore (dentAfterGuyStore evmKiss I) I)).toNat <
        2 ^ 48) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body
      (.returned
        { contract := contract
          locals := dentKissRetTicLocals evm (dentAfterGuyStore evmKiss I) I outAsh }
        (dentPostState (dentAfterGuyStore evmKiss I) I) none) := by
  let evmGuy := dentAfterGuyStore evmKiss I
  let evmLot := dentAfterLotStore evmGuy I
  have hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_dent_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_dent_tic_guard_true_zero evm I hzero
  have htailIteLot :=
    flopperDentBodyMoveAshKissSuccessTicZeroToLot
      evm evmMove evmAsh evmKiss I outMove outAsh outKiss hcaller hcodeSize hcall
      hticMove hashCodeSize hashCall houtAsh32 hkissCodeSize hkissCall
  have htickLet :
      ExecBlock config { contract := contract, locals := dentKissRetLocals evm I outAsh }
          evmLot
        (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")])
        (.ok { contract := contract, locals := dentKissRetTicLocals evm evmGuy I outAsh }
          (dentPostState evmGuy I)) := by
    simpa [checkedAdd48Into, evmGuy, evmLot] using
      (ExecBlock.consNormal
        (ExecStmt.letDecl
          (evalExpr_dent_ticAdd_ok_kissRetLocals evm evmGuy I outAsh haddFit)) <|
        ExecBlock.consNormal
          (ExecStmt.requireTrue
            (evalExpr_dent_tic_guard_true_kissRetLocals evm evmGuy I outAsh haddFit)) <|
        ExecBlock.consNormal
          (ExecStmt.assign
            (evalExpr_dent_tic_var_kissRetTicLocals evm evmGuy I outAsh)
            (assign_dentTicStorage_value_of_locals evmGuy I
              (dentKissRetTicLocals_get_id evm evmGuy I outAsh)
              (dentKissRetTicLocals_get_bids evm evmGuy I outAsh) haddFit))
          ExecBlock.nil)
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
          [],
         .assign .storage (bidsF (.var "id") "lot") (.var "lot")] ++
          (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
            [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")]))
        (.ok { contract := contract, locals := dentKissRetTicLocals evm evmGuy I outAsh }
          (dentPostState evmGuy I)) := by
    simpa [List.cons_append, List.nil_append, evmGuy, evmLot] using
      Reasoning.Refinement.execBlock_append htailIteLot htickLet
  refine ExecFuncBody.execBlockOK ?_
  simpa [dentTransition, nonpayable, checkedMulUintInto, List.cons_append, List.nil_append,
    evmGuy] using
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
theorem flopperDentBodyReverts_addOverflow_moveCallerNe_ticNonzero
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
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap (dentVatWord evm) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (dentVatWord evm).toNat)) "move" 0
        [.address evm.executionEnv.source,
          .address (AccountAddress.ofNat (dentGuyWord evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmMove, out) true)
    (hticMove : dentTicWord evmMove I ≠ ⟨0⟩)
    (haddOverflow :
      2 ^ 48 ≤
        (dentNow48Word (dentAfterGuyStore evmMove I)).toNat +
          (dentTtlWord (dentAfterLotStore (dentAfterGuyStore evmMove I) I)).toNat) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body .reverted := by
  let evmGuy := dentAfterGuyStore evmMove I
  let evmLot := dentAfterLotStore evmGuy I
  have hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_dent_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_dent_tic_guard_true_zero evm I hzero
  have htailIteLot :=
    flopperDentBodyMoveSuccessTicNonzeroToLot evm evmMove I out hcaller hcodeSize hcall
      hticMove
  have htickChecked :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmLot
        (checkedAdd48Into "tic_" now48 (.storage ttlRef)) .reverted := by
    simpa [checkedAdd48Into, evmGuy, evmLot] using
      (ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_dent_ticAdd_wrapped_moveLocals evm evmGuy I)) <|
        ExecBlock.consRevert
          (ExecStmt.requireFalse
            (evalExpr_dent_tic_guard_false_wrapped_moveLocals evm evmGuy I
              haddOverflow)))
  have htickTail :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmLot
        (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")]) .reverted :=
    Reasoning.Refinement.execBlock_append_term htickChecked (by intro f e h; cases h)
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
          [],
         .assign .storage (bidsF (.var "id") "lot") (.var "lot")] ++
          (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
            [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")]))
        .reverted := by
    simpa [List.cons_append, List.nil_append, evmGuy, evmLot] using
      Reasoning.Refinement.execBlock_append htailIteLot htickTail
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
theorem flopperDentBodyReturns_success_moveCallerNe_ticNonzero
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
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap (dentVatWord evm) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (dentVatWord evm).toNat)) "move" 0
        [.address evm.executionEnv.source,
          .address (AccountAddress.ofNat (dentGuyWord evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmMove, out) true)
    (hticMove : dentTicWord evmMove I ≠ ⟨0⟩)
    (haddFit :
      (dentNow48Word (dentAfterGuyStore evmMove I)).toNat +
          (dentTtlWord (dentAfterLotStore (dentAfterGuyStore evmMove I) I)).toNat <
        2 ^ 48) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body
      (.returned { contract := contract, locals := (dentMoveTicLocals evm (dentAfterGuyStore evmMove I) I) }
        (dentPostState (dentAfterGuyStore evmMove I) I) none) := by
  let evmGuy := dentAfterGuyStore evmMove I
  let evmLot := dentAfterLotStore evmGuy I
  have hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_dent_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_dent_tic_guard_true_zero evm I hzero
  have htailIteLot :=
    flopperDentBodyMoveSuccessTicNonzeroToLot evm evmMove I out hcaller hcodeSize hcall
      hticMove
  have htickLet :
      ExecBlock config { contract := contract, locals := dentMoveLocals evm I } evmLot
        (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")])
        (.ok { contract := contract, locals := dentMoveTicLocals evm evmGuy I }
          (dentPostState evmGuy I)) := by
    simpa [checkedAdd48Into, evmGuy, evmLot] using
      (ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_dent_ticAdd_ok_moveLocals evm evmGuy I haddFit)) <|
        ExecBlock.consNormal
          (ExecStmt.requireTrue
            (evalExpr_dent_tic_guard_true_moveLocals evm evmGuy I haddFit)) <|
        ExecBlock.consNormal
          (ExecStmt.assign (evalExpr_dent_tic_var_moveTicLocals evm evmGuy I)
            (assign_dentTicStorage_value_of_locals evmGuy I
              (dentMoveTicLocals_get_id evm evmGuy I)
              (dentMoveTicLocals_get_bids evm evmGuy I) haddFit))
          ExecBlock.nil)
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
          [],
         .assign .storage (bidsF (.var "id") "lot") (.var "lot")] ++
          (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
            [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")]))
        (.ok { contract := contract, locals := dentMoveTicLocals evm evmGuy I }
          (dentPostState evmGuy I)) := by
    simpa [List.cons_append, List.nil_append, evmGuy, evmLot] using
      Reasoning.Refinement.execBlock_append htailIteLot htickLet
  refine ExecFuncBody.execBlockOK ?_
  simpa [dentTransition, nonpayable, checkedMulUintInto, List.cons_append, List.nil_append,
    evmGuy] using
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
theorem flopperDentBodyReverts_addOverflow_callerEq (evm : EVM.State) (I : ExecutionEnv)
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
    (hcaller : UInt256.ofNat evm.executionEnv.source.val = dentGuyWord evm I)
    (haddOverflow :
      2 ^ 48 ≤
        (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body .reverted := by
  let evmLot := dentAfterLotStore evm I
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
    evalExpr_dent_sender_ne_guy_false_lotOneLocals evm I hcaller
  have htailIteLot :
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
          [],
         .assign .storage (bidsF (.var "id") "lot") (.var "lot")]
        (.ok { contract := contract, locals := dentLotOneLocals evm I } evmLot) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hcallerCond ExecBlock.nil) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_dent_lot_var_lotOneLocals evm I)
          (by simpa [evmLot] using assign_dentLotStorage evm I))
        ExecBlock.nil
  have htickChecked :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evmLot
        (checkedAdd48Into "tic_" now48 (.storage ttlRef)) .reverted := by
    simpa [checkedAdd48Into, evmLot] using
      (ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_dent_ticAdd_wrapped evm I)) <|
        ExecBlock.consRevert
          (ExecStmt.requireFalse
            (evalExpr_dent_tic_guard_false_wrapped evm I haddOverflow)))
  have htickTail :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evmLot
        (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")]) .reverted :=
    Reasoning.Refinement.execBlock_append_term htickChecked (by intro f e h; cases h)
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
          [],
         .assign .storage (bidsF (.var "id") "lot") (.var "lot")] ++
          (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
            [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")]))
        .reverted :=
    Reasoning.Refinement.execBlock_append htailIteLot htickTail
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
theorem flopperDentBodyReturns_success_callerEq (evm : EVM.State) (I : ExecutionEnv)
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
    (hcaller : UInt256.ofNat evm.executionEnv.source.val = dentGuyWord evm I)
    (haddFit :
      (dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat <
        2 ^ 48) :
    ExecTransitionBody config contract evm (dentLocals I) dentTransition.body
      (.returned { contract := contract, locals := dentTicLocals evm I }
        (dentPostState evm I) none) := by
  let evmLot := dentAfterLotStore evm I
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
    evalExpr_dent_sender_ne_guy_false_lotOneLocals evm I hcaller
  have htailIteLot :
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
          [],
         .assign .storage (bidsF (.var "id") "lot") (.var "lot")]
        (.ok { contract := contract, locals := dentLotOneLocals evm I } evmLot) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hcallerCond ExecBlock.nil) <|
      ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_dent_lot_var_lotOneLocals evm I)
          (by simpa [evmLot] using assign_dentLotStorage evm I))
        ExecBlock.nil
  have htickLet :
      ExecBlock config { contract := contract, locals := dentLotOneLocals evm I } evmLot
        (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")])
        (.ok { contract := contract, locals := dentTicLocals evm I } (dentPostState evm I)) := by
    simpa [checkedAdd48Into, evmLot] using
      (ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_dent_ticAdd_ok evm I haddFit)) <|
        ExecBlock.consNormal
          (ExecStmt.requireTrue (evalExpr_dent_tic_guard_true evm I haddFit)) <|
        ExecBlock.consNormal
          (ExecStmt.assign (evalExpr_dent_tic_var evm I)
            (assign_dentTicStorage_value evm I haddFit))
          ExecBlock.nil)
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
          [],
         .assign .storage (bidsF (.var "id") "lot") (.var "lot")] ++
          (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
            [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")]))
        (.ok { contract := contract, locals := dentTicLocals evm I } (dentPostState evm I)) :=
    Reasoning.Refinement.execBlock_append htailIteLot htickLet
  refine ExecFuncBody.execBlockOK ?_
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

theorem flopperUint48Offset0Word_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (slot : UInt256) :
    flopperUint48Offset0Word slot σ I = flopperUint48Offset0Word slot τ I := by
  simp [flopperUint48Offset0Word, flopperSlotWord_accountMapEquiv hAccounts slot]

theorem dentRuntimeAfterLotMap_source_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv (dentRuntimeAfterLotMap I.codeOwner σ_evm I)
      (dentAfterLotStore (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I).accountMap := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  simpa [evmSolm, dentRuntimeAfterLotMap, dentAfterLotStore, storageStore_accountMap,
    initState] using
    accountMapEquiv_sstoreAccountMap I.codeOwner (auctionLotSlot (dentIdWord I))
      (dentLotWord I) hAccounts

theorem dentRuntimeTtlWord_source_eq
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    dentRuntimeTtlWord I.codeOwner σ_evm I =
      dentTtlWord
        (dentAfterLotStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I) := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hAfter :=
    dentRuntimeAfterLotMap_source_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hAccounts
  have h := flopperUint48Offset0Word_accountMapEquiv (I := I) hAfter ⟨6⟩
  simpa [evmSolm, dentRuntimeTtlWord, dentTtlWord, dentAfterLotStore_executionEnv,
    initState] using h

theorem dentRuntimeTailSuccessAccountMap_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (dentRuntimeTtlWord I.codeOwner σ_evm I).toNat < 2 ^ 48) :
    accountMapEquiv (dentRuntimeTailSuccessAccountMap I.codeOwner σ_evm I)
      (dentPostState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I).accountMap := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let packedSlot := auctionPackedSlot (dentIdWord I)
  let runtimeOld := solcSlotWord (dentRuntimeAfterLotMap I.codeOwner σ_evm I) I packedSlot
  let runtimeAdd := dentRuntimeTicAddWord I.codeOwner σ_evm I
  have hAfter :=
    dentRuntimeAfterLotMap_source_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hAccounts
  have httl :=
    dentRuntimeTtlWord_source_eq
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hAccounts
  have haddFitSolm :
      (dentNow48Word evmSolm).toNat +
          (dentTtlWord (dentAfterLotStore evmSolm I)).toNat < 2 ^ 48 := by
    simpa [evmSolm, dentNow48Word, dentTimestampWord, initState, httl] using haddFit
  have hmaskedRuntime :
      UInt256.land runtimeAdd flopperUint48Mask = dentTicPostWord evmSolm I := by
    apply u256_inj
    change (UInt256.land (dentRuntimeTicAddWord I.codeOwner σ_evm I) flopperUint48Mask).toNat =
      (dentTicPostWord evmSolm I).toNat
    rw [dentRuntimeTicAddWord]
    rw [uint48Mask_add_no_wrap_toNat (UInt256.ofNat I.header.timestamp)
      (dentRuntimeTtlWord I.codeOwner σ_evm I) haddFit]
    rw [dentTicPostWord_toNat evmSolm I haddFitSolm]
    simpa [evmSolm, dentNow48Word, dentTimestampWord, initState, httl]
  have hsourceClean :
      UInt256.land (dentTicPostWord evmSolm I) flopperUint48Mask =
        dentTicPostWord evmSolm I := by
    apply flopperUint48Mask_clean_of_canonical
    have hticNat := dentTicPostWord_toNat evmSolm I haddFitSolm
    rw [hticNat]
    simpa [EVM.twoPow] using haddFitSolm
  have hold :
      runtimeOld =
        Solm.EVM.storageLoad (dentAfterLotStore evmSolm I)
          (dentAfterLotStore evmSolm I).executionEnv.codeOwner packedSlot := by
    have hslot := flopperSlotWord_accountMapEquiv (I := I) hAfter packedSlot
    simpa [runtimeOld, packedSlot, flopperSlotWord, solcSlotWord, evmSolm,
      initState, dentAfterLotStore_executionEnv] using hslot
  have hstored :
      dentRuntimeTicStoredWord I.codeOwner σ_evm I = dentTicStoredWord evmSolm I := by
    unfold dentRuntimeTicStoredWord dentTicStoredWord
    apply u256_inj
    rw [setUint48Offset20Word_toNat, setUint48Offset20Word_toNat]
    change
      runtimeOld.toNat % 2 ^ 160 +
            (UInt256.land runtimeAdd flopperUint48Mask).toNat * 2 ^ 160 +
          runtimeOld.toNat / 2 ^ 208 * 2 ^ 208 =
        (Solm.EVM.storageLoad (dentAfterLotStore evmSolm I)
              (dentAfterLotStore evmSolm I).executionEnv.codeOwner packedSlot).toNat %
            2 ^ 160 +
          (UInt256.land (dentTicPostWord evmSolm I) flopperUint48Mask).toNat *
            2 ^ 160 +
        (Solm.EVM.storageLoad (dentAfterLotStore evmSolm I)
              (dentAfterLotStore evmSolm I).executionEnv.codeOwner packedSlot).toNat /
            2 ^ 208 *
          2 ^ 208
    rw [hold, hmaskedRuntime, hsourceClean]
  simpa [evmSolm, initState, storageStore_accountMap, dentAfterLotStore_executionEnv,
    packedSlot, runtimeOld, runtimeAdd, dentRuntimeTailSuccessAccountMap, dentAfterTicStore,
    dentPostState, hstored] using
    accountMapEquiv_sstoreAccountMap I.codeOwner packedSlot (dentTicStoredWord evmSolm I)
      hAfter

theorem dentRuntimeAfterGuyMap_accountMapEquiv
    {σ_evm : AccountMap} {evmSolm : EVM.State} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm evmSolm.accountMap)
    (hEnv : evmSolm.executionEnv = I) :
    accountMapEquiv (dentRuntimeAfterGuyMap I.codeOwner σ_evm I)
      (dentAfterGuyStore evmSolm I).accountMap := by
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hold :
      solcSlotWord σ_evm I packedSlot =
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner packedSlot := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts packedSlot
    simpa [flopperSlotWord, solcSlotWord, hEnv] using hword
  have hstored :
      setAddressOffset0Word (solcSlotWord σ_evm I packedSlot) (UInt256.ofNat I.source.val) =
        setAddressOffset0Word
          (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner packedSlot)
          (UInt256.ofNat evmSolm.executionEnv.source.val) := by
    simp [hold, hEnv]
  simpa [dentRuntimeAfterGuyMap, dentAfterGuyStore, storageStore_accountMap, hEnv,
    packedSlot, hstored] using
    accountMapEquiv_sstoreAccountMap I.codeOwner packedSlot
      (setAddressOffset0Word
        (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner packedSlot)
        (UInt256.ofNat evmSolm.executionEnv.source.val))
      hAccounts

theorem dentRuntimeTtlWord_afterGuy_eq
    {σ_evm : AccountMap} {evmSolm : EVM.State} {I : ExecutionEnv}
    (hAfterGuy :
      accountMapEquiv (dentRuntimeAfterGuyMap I.codeOwner σ_evm I)
        (dentAfterGuyStore evmSolm I).accountMap)
    (hEnv : evmSolm.executionEnv = I) :
    dentRuntimeTtlWord I.codeOwner (dentRuntimeAfterGuyMap I.codeOwner σ_evm I) I =
      dentTtlWord (dentAfterLotStore (dentAfterGuyStore evmSolm I) I) := by
  have hAfterLot :
      accountMapEquiv
        (dentRuntimeAfterLotMap I.codeOwner (dentRuntimeAfterGuyMap I.codeOwner σ_evm I) I)
        (dentAfterLotStore (dentAfterGuyStore evmSolm I) I).accountMap := by
    simpa [dentRuntimeAfterLotMap, dentAfterLotStore, storageStore_accountMap,
      dentAfterGuyStore, storageStore_executionEnv, hEnv] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (auctionLotSlot (dentIdWord I))
        (dentLotWord I) hAfterGuy
  have h := flopperUint48Offset0Word_accountMapEquiv (I := I) hAfterLot ⟨6⟩
  simpa [dentRuntimeTtlWord, dentTtlWord, dentAfterLotStore_executionEnv,
    dentAfterGuyStore, storageStore_executionEnv, hEnv] using h

theorem dentRuntimeTailSuccessAccountMap_afterGuy_accountMapEquiv
    {σ_evm : AccountMap} {evmSolm : EVM.State} {I : ExecutionEnv}
    (hAfterGuy :
      accountMapEquiv (dentRuntimeAfterGuyMap I.codeOwner σ_evm I)
        (dentAfterGuyStore evmSolm I).accountMap)
    (hEnv : evmSolm.executionEnv = I)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
          (dentRuntimeTtlWord I.codeOwner (dentRuntimeAfterGuyMap I.codeOwner σ_evm I) I).toNat <
        2 ^ 48) :
    accountMapEquiv
      (dentRuntimeTailSuccessAccountMap I.codeOwner
        (dentRuntimeAfterGuyMap I.codeOwner σ_evm I) I)
      (dentPostState (dentAfterGuyStore evmSolm I) I).accountMap := by
  let σGuy := dentRuntimeAfterGuyMap I.codeOwner σ_evm I
  let evmGuy := dentAfterGuyStore evmSolm I
  let packedSlot := auctionPackedSlot (dentIdWord I)
  let runtimeOld := solcSlotWord (dentRuntimeAfterLotMap I.codeOwner σGuy I) I packedSlot
  let runtimeAdd := dentRuntimeTicAddWord I.codeOwner σGuy I
  have hAfterLot :
      accountMapEquiv (dentRuntimeAfterLotMap I.codeOwner σGuy I)
        (dentAfterLotStore evmGuy I).accountMap := by
    simpa [σGuy, evmGuy, dentRuntimeAfterLotMap, dentAfterLotStore,
      storageStore_accountMap, dentAfterGuyStore, storageStore_executionEnv, hEnv] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (auctionLotSlot (dentIdWord I))
        (dentLotWord I) hAfterGuy
  have httl :
      dentRuntimeTtlWord I.codeOwner σGuy I =
        dentTtlWord (dentAfterLotStore evmGuy I) := by
    simpa [σGuy, evmGuy] using
      dentRuntimeTtlWord_afterGuy_eq (I := I) hAfterGuy hEnv
  have haddFitSolm :
      (dentNow48Word evmGuy).toNat +
          (dentTtlWord (dentAfterLotStore evmGuy I)).toNat < 2 ^ 48 := by
    simpa [σGuy, evmGuy, dentNow48Word, dentTimestampWord, dentAfterGuyStore,
      storageStore_executionEnv, hEnv, httl] using haddFit
  have hmaskedRuntime :
      UInt256.land runtimeAdd flopperUint48Mask = dentTicPostWord evmGuy I := by
    apply u256_inj
    change
      (UInt256.land (dentRuntimeTicAddWord I.codeOwner σGuy I) flopperUint48Mask).toNat =
        (dentTicPostWord evmGuy I).toNat
    rw [dentRuntimeTicAddWord]
    rw [uint48Mask_add_no_wrap_toNat (UInt256.ofNat I.header.timestamp)
      (dentRuntimeTtlWord I.codeOwner σGuy I) haddFit]
    rw [dentTicPostWord_toNat evmGuy I haddFitSolm]
    simpa [σGuy, evmGuy, dentNow48Word, dentTimestampWord, dentAfterGuyStore,
      storageStore_executionEnv, hEnv, httl]
  have hsourceClean :
      UInt256.land (dentTicPostWord evmGuy I) flopperUint48Mask =
        dentTicPostWord evmGuy I := by
    apply flopperUint48Mask_clean_of_canonical
    have hticNat := dentTicPostWord_toNat evmGuy I haddFitSolm
    rw [hticNat]
    simpa [EVM.twoPow] using haddFitSolm
  have hold :
      runtimeOld =
        Solm.EVM.storageLoad (dentAfterLotStore evmGuy I)
          (dentAfterLotStore evmGuy I).executionEnv.codeOwner packedSlot := by
    have hslot := flopperSlotWord_accountMapEquiv (I := I) hAfterLot packedSlot
    simpa [runtimeOld, packedSlot, flopperSlotWord, solcSlotWord,
      dentAfterLotStore_executionEnv, evmGuy, dentAfterGuyStore, storageStore_executionEnv,
      hEnv] using hslot
  have hstored :
      dentRuntimeTicStoredWord I.codeOwner σGuy I = dentTicStoredWord evmGuy I := by
    unfold dentRuntimeTicStoredWord dentTicStoredWord
    apply u256_inj
    rw [setUint48Offset20Word_toNat, setUint48Offset20Word_toNat]
    change
      runtimeOld.toNat % 2 ^ 160 +
            (UInt256.land runtimeAdd flopperUint48Mask).toNat * 2 ^ 160 +
          runtimeOld.toNat / 2 ^ 208 * 2 ^ 208 =
        (Solm.EVM.storageLoad (dentAfterLotStore evmGuy I)
              (dentAfterLotStore evmGuy I).executionEnv.codeOwner packedSlot).toNat %
            2 ^ 160 +
          (UInt256.land (dentTicPostWord evmGuy I) flopperUint48Mask).toNat *
            2 ^ 160 +
        (Solm.EVM.storageLoad (dentAfterLotStore evmGuy I)
              (dentAfterLotStore evmGuy I).executionEnv.codeOwner packedSlot).toNat /
            2 ^ 208 *
          2 ^ 208
    rw [hold, hmaskedRuntime, hsourceClean]
  simpa [σGuy, evmGuy, storageStore_accountMap, dentAfterLotStore_executionEnv,
    dentAfterGuyStore, storageStore_executionEnv, hEnv, packedSlot, runtimeOld, runtimeAdd,
    dentRuntimeTailSuccessAccountMap, dentAfterTicStore, dentPostState, hstored] using
    accountMapEquiv_sstoreAccountMap I.codeOwner packedSlot (dentTicStoredWord evmGuy I)
      hAfterLot

theorem flopperDentBodyCoreRevert
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flopperBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (dentLocals I)
        dentTransition.body .reverted)
    (hrev : RDrev flopperBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperDentBodyCoreSuccessCallerEqBridge
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flopperBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (dentLocals I)
        dentTransition.body
        (.returned
          { contract := contract
            locals :=
              dentTicLocals (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I }
          (dentPostState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
          none))
    (hret : RDret flopperBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (cA, dentRuntimeTailSuccessAccountMap I.codeOwner σ_evm I) ByteArray.empty)
    (hAccountsPost :
      accountMapEquiv (dentRuntimeTailSuccessAccountMap I.codeOwner σ_evm I)
        (dentPostState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).accountMap) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by
      simp only [dentPostState, dentAfterTicStore, dentAfterLotStore,
        storageStore_createdAccounts]
      rfl)
    (by simpa [evmSolm] using hAccountsPost)
    (by
      simpa [dentTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem flopperDecode_dent_ok {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
      (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I) := by
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["id", "lot", "bid"]
      [abiUInt256, abiUInt256, abiUInt256] I.calldata =
    some ((((∅ : Store).insert "id" (dentIdValue I)).insert "lot" (dentLotValue I)).insert
      "bid" (dentBidValue I))
  exact decodeCalldata_legacyUint256_uint256_uint256_ok (cd := I.calldata)
    (x := "id") (y := "lot") (z := "bid") hsz100

theorem flopperDecode_dent_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
      (transitionSignature dentTransition).paramTypes I.calldata = none := by
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["id", "lot", "bid"]
      [abiUInt256, abiUInt256, abiUInt256] I.calldata = none
  exact
    decodeCalldata_legacyUint256_uint256_uint256_none_short (cd := I.calldata)
      (x := "id") (y := "lot") (z := "bid") hsz4 hshort

theorem flopperReachDentBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flopperSelBytes 4)) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨533⟩ [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flopperSelWord I = ⟨0x5ff3a382⟩ := by
    simpa [flopperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0x5f 0xf3 0xa3 0x82 ⟨0x5ff3a382⟩
        (by native_decide) (by simpa [flopperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flopperBytecode flopperRootSplitPc)
      (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat flopperBytecode flopperLowSplitPc)
      (flopperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  obtain ⟨_, _, hfirst⟩ :=
    flopperReachLowHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  have heq0 : ∀ j, j < 0 →
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperLowHighFirstArmPc j))
        (flopperSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperLowHighFirstArmPc 0))
        (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo ⟨533⟩ 0 hfirst
    (fun j hj => flopperLowHighArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem flopperDentX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨533⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1634⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flopperBytecode) (sel := sel) (entry := ⟨533⟩) (ret := ⟨334⟩)
    (decoded := ⟨555⟩) (need := ⟨96⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize)
  have rd556 := hdecoded.jumpdest (by native_decide) (by evm_ov)
  have rd557 := rd556.pop (by native_decide) (by evm_ov)
  have rd558 := rd557.dup1 (by native_decide) (by evm_ov)
  have rd559 := rd558.calldataload (by native_decide) (by evm_ov)
  have rd560 := rd559.swap1 (by native_decide) (by evm_ov)
  have rd562 := rd560.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd563 := rd562.dup2 (by native_decide) (by evm_ov)
  have rd564 := rd563.add (by native_decide) (by evm_ov)
  have rd565 := rd564.calldataload (by native_decide) (by evm_ov)
  have rd566 := rd565.swap1 (by native_decide) (by evm_ov)
  have rd568 := rd566.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd569 := rd568.add (by native_decide) (by evm_ov)
  have rd570 := rd569.calldataload (by native_decide) (by evm_ov)
  have rd573 := rd570.push2 ⟨1634⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [dentIdWord, dentLotWord, dentBidWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨32⟩).toNat = 36 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨64⟩).toNat = 68 from by decide]
      using rd573.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem flopperDentX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨533⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 96
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flopperBytecode) (sel := sel) (entry := ⟨533⟩) (ret := ⟨334⟩)
    (decoded := ⟨555⟩) (need := ⟨96⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

set_option maxHeartbeats 1000000 in
theorem flopperDentX_notLive {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flopperSlotWord ⟨8⟩ σ I ≠ ⟨1⟩)
    (h : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1634⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1634⟩ := h
  have rd1637 := evm_run rd1634 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k1638, C1638, rd1638raw⟩ := rd1637.sload (by native_decide) (by evm_ov)
  have rd1638 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1638⟩
      (flopperSlotWord ⟨8⟩ σ I :: dentBidWord I :: dentLotWord I :: dentIdWord I ::
        ⟨334⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1638 C1638 := by
    simpa [flopperSlotWord] using rd1638raw
  have rd1644 := evm_run rd1638 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw push2 ⟨1708⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.eq (⟨1⟩ : UInt256) (flopperSlotWord ⟨8⟩ σ I) = ⟨0⟩ := by
    apply u256_eq_of_ne
    intro hbad
    exact hlive hbad.symm
  have rd1645 := rd1644.jumpiNT (by native_decide) hcond (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1645⟩)
    (len := ⟨16⟩)
    (rawWord := ⟨0x466c6f707065722f6e6f742d6c697665⟩)
    (shift := ⟨128⟩)
    (word := ⟨0x466c6f707065722f6e6f742d6c69766500000000000000000000000000000000⟩)
    (op := .PUSH16)
    (width := 16)
    rd1645
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by simp)

theorem flopperDentX_liveOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flopperSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (h : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1634⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1708⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1634⟩ := h
  have rd1637 := evm_run rd1634 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k1638, C1638, rd1638raw⟩ := rd1637.sload (by native_decide) (by evm_ov)
  have rd1638 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1638⟩
      (flopperSlotWord ⟨8⟩ σ I :: dentBidWord I :: dentLotWord I :: dentIdWord I ::
        ⟨334⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1638 C1638 := by
    simpa [flopperSlotWord] using rd1638raw
  have rd1644 := evm_run rd1638 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw push2 ⟨1708⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.eq (⟨1⟩ : UInt256) (flopperSlotWord ⟨8⟩ σ I) ≠ ⟨0⟩ := by
    rw [hlive, u256_eq_refl]
    exact one_ne_zero_uint
  exact ⟨_, _, rd1644.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flopperDentX_toGuyGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (rd1708 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1708⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dentIdWord I
    let memMap := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1736⟩
      [flopperAddressReturnWord (auctionPackedSlot id) σ I, dentBidWord I,
        dentLotWord I, id, ⟨334⟩, sel]
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memMap
  let memKey := wordAt0Mem id solcFreePtrMem
  let base := solcMappingSlot ⟨1⟩ id
  have rd1713pre := evm_run rd1708 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1714 := rd1713pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd1718pre := evm_run rd1714 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd1719 := rd1718pre.mstore 0 memMap (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memMap, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd1722pre := evm_run rd1719 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memMap.readWithPadding 0 64))) = base := by
    simpa [base, memMap, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ (dentIdWord I) solcFreePtrMem
  have rd1723 := rd1722pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd1726pre := evm_run rd1723 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd1726pre
  obtain ⟨k1727, C1727, rd1727raw⟩ := rd1726pre.sload (by native_decide) (by evm_ov)
  have rd1727 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1727⟩
      [flopperSlotWord (auctionPackedSlot id) σ I, dentBidWord I, dentLotWord I,
        id, ⟨334⟩, sel]
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1727 C1727 := by
    simpa [flopperSlotWord] using rd1727raw
  have rd1736raw := evm_run rd1727 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        (flopperSlotWord (auctionPackedSlot id) σ I) =
      flopperAddressReturnWord (auctionPackedSlot id) σ I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    rw [u256_land_comm]
  exact ⟨_, _, by simpa [hmask] using rd1736raw⟩

set_option maxHeartbeats 1000000 in
theorem flopperDentX_guyNotSet {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flopperSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (h : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1634⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let id := dentIdWord I
  let memMap := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  obtain ⟨_, _, rd1708⟩ := flopperDentX_liveOk (g := g) hlive h
  obtain ⟨_, _, rd1736⟩ := flopperDentX_toGuyGuard rd1708
  have rd1739 := rd1736.push2 ⟨1806⟩ (by native_decide) (by evm_ov)
  have rd1740 := rd1739.jumpiNT (by native_decide) (by simpa [id] using hguy) (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1740⟩)
    (len := ⟨19⟩)
    (rawWord := ⟨0x119b1bdc1c195c8bd9dd5e4b5b9bdd0b5cd95d⟩)
    (shift := ⟨106⟩)
    (word := ⟨0x466c6f707065722f6775792d6e6f742d73657400000000000000000000000000⟩)
    (op := .PUSH19)
    (width := 19)
    rd1740
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    (by
      simpa [memMap, id] using
        (twoWordHashMem_size_96 (dentIdWord I) ⟨1⟩ solcFreePtrMem_size))
    (by
      simpa [memMap, id] using
        twoWordHashMem_read64 (dentIdWord I) ⟨1⟩ solcFreePtrMem_size
          solcFreePtrMem_read64)
    (by simp)

set_option maxHeartbeats 1000000 in
theorem flopperDentX_guyOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flopperSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (h : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1634⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1806⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      (twoWordHashMem (dentIdWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1708⟩ := flopperDentX_liveOk (g := g) hlive h
  obtain ⟨_, _, rd1736⟩ := flopperDentX_toGuyGuard rd1708
  have rd1739 := rd1736.push2 ⟨1806⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1739.jumpiT (by native_decide) hguy (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flopperDentX_toTicGtGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (rd1806 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1806⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      (twoWordHashMem (dentIdWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dentIdWord I
    let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    let memTic := twoWordHashMem id ⟨1⟩ memGuy
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1843⟩
      [UInt256.gt (flopperUint48Offset20Word (auctionPackedSlot id) σ I)
        (UInt256.ofNat I.header.timestamp), dentBidWord I, dentLotWord I, id, ⟨334⟩, sel]
      memTic (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memGuy memTic
  let memKey := wordAt0Mem id memGuy
  let base := solcMappingSlot ⟨1⟩ id
  have rd1811pre := evm_run rd1806 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1812 := rd1811pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, memGuy, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd1816pre := evm_run rd1812 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd1817 := rd1816pre.mstore 0 memTic (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memTic, memGuy, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd1820pre := evm_run rd1817 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memTic.readWithPadding 0 64))) = base := by
    simpa [base, memTic, memGuy, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memGuy
  have rd1821 := rd1820pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd1824pre := evm_run rd1821 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd1824pre
  obtain ⟨k1825, C1825, rd1825raw⟩ := rd1824pre.sload (by native_decide) (by evm_ov)
  have rd1825 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1825⟩
      [flopperSlotWord (auctionPackedSlot id) σ I, dentBidWord I, dentLotWord I,
        id, ⟨334⟩, sel]
      memTic (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1825 C1825 := by
    simpa [flopperSlotWord] using rd1825raw
  have rd1834 := evm_run rd1825 with [
    raw timestamp (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  have rd1841 := rd1834.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd1842 := rd1841.and (by native_decide) (by evm_ov)
  have rd1843 := rd1842.gt (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [id, flopperUint48Offset20Word,
      show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩ = UInt256.ofNat (256 ^ 20)
        from by native_decide]
      using rd1843⟩

set_option maxHeartbeats 1000000 in
theorem flopperDentX_ticFinished {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flopperSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticNe : flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticLe :
      (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (h : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1634⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let id := dentIdWord I
  let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ memGuy
  let memTicZero := twoWordHashMem id ⟨1⟩ memTic
  obtain ⟨_, _, rd1806⟩ := flopperDentX_guyOk (g := g) hlive hguy h
  obtain ⟨_, _, rd1843⟩ := flopperDentX_toTicGtGuard rd1806
  have hgt :
      UInt256.gt (flopperUint48Offset20Word (auctionPackedSlot id) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨0⟩ := by
    apply ugt_zero
    simpa [id] using hticLe
  have rd1847 := evm_run rd1843 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨1883⟩ (by native_decide) (by evm_ov)]
  have rd1848 := rd1847.jumpiNT (by native_decide) hgt (by evm_ov)
  have rd1849 := rd1848.pop (by native_decide) (by evm_ov)
  let memKey := wordAt0Mem id memTic
  let base := solcMappingSlot ⟨1⟩ id
  have rd1853pre := evm_run rd1849 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1854 := rd1853pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, memTic, memGuy, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd1858pre := evm_run rd1854 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd1859 := rd1858pre.mstore 0 memTicZero (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memTicZero, memTic, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd1862pre := evm_run rd1859 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memTicZero.readWithPadding 0 64))) = base := by
    simpa [base, memTicZero, memTic, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memTic
  have rd1863 := rd1862pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd1866pre := evm_run rd1863 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd1866pre
  obtain ⟨k1867, C1867, rd1867raw⟩ := rd1866pre.sload (by native_decide) (by evm_ov)
  have rd1867 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1867⟩
      [flopperSlotWord (auctionPackedSlot id) σ I, dentBidWord I, dentLotWord I,
        id, ⟨334⟩, sel]
      memTicZero (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1867 C1867 := by
    simpa [flopperSlotWord] using rd1867raw
  have rd1882 := evm_run rd1867 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  have rd1881 := rd1882.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd1882' := rd1881.and (by native_decide) (by evm_ov)
  have rd1883pre := rd1882'.iszero (by native_decide) (by evm_ov)
  have hticZero :
      UInt256.isZero (flopperUint48Offset20Word (auctionPackedSlot id) σ I) = ⟨0⟩ :=
    isZero_eq_zero_of_ne (by simpa [id] using hticNe)
  have hpc1883 :
      (⟨1867⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat (Nat.succ 6) + ⟨1⟩ + ⟨1⟩ =
        ⟨1883⟩ := by
    native_decide
  rw [hpc1883] at rd1883pre
  have hticRaw :
      UInt256.land flopperUint48Mask
          (UInt256.div (flopperSlotWord (auctionPackedSlot id) σ I)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)) =
        flopperUint48Offset20Word (auctionPackedSlot id) σ I := by
    rw [show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩ = UInt256.ofNat (256 ^ 20)
      from by native_decide]
    rfl
  have rd1883 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1883⟩
      [UInt256.isZero (flopperUint48Offset20Word (auctionPackedSlot id) σ I),
        dentBidWord I, dentLotWord I, id, ⟨334⟩, sel]
      memTicZero (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      (k1867 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
      (C1867 + 3 + 3 + 3 + 3 + 5 + 3 + 3 + 3) := by
    simpa [id, hticRaw] using rd1883pre
  have rd1884 := rd1883.jumpdest (by native_decide) (by evm_ov)
  have rd1887 := rd1884.push2 ⟨1964⟩ (by native_decide) (by evm_ov)
  have rd1888 := rd1887.jumpiNT (by native_decide) hticZero (by evm_ov)
  exact solcErrorStringRevertTailFullWord
    (pc := ⟨1888⟩)
    (len := ⟨28⟩)
    (word :=
      ⟨0x466c6f707065722f616c72656164792d66696e69736865642d74696300000000⟩)
    rd1888
    (by
      unfold solcErrorStringRevertTailFullWordWf
      repeat' first | apply And.intro | native_decide)
    (by
      have hmemGuy : memGuy.size = 96 := by
        simpa [memGuy, id] using twoWordHashMem_size_96 (dentIdWord I) ⟨1⟩
          solcFreePtrMem_size
      have hmemTic : memTic.size = 96 := by
        simpa [memTic, memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemGuy
      simpa [memTicZero, memTic, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemTic)
    (by
      have hmemGuy : memGuy.size = 96 := by
        simpa [memGuy, id] using twoWordHashMem_size_96 (dentIdWord I) ⟨1⟩
          solcFreePtrMem_size
      have hreadGuy : memGuy.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
        simpa [memGuy, id] using twoWordHashMem_read64 (dentIdWord I) ⟨1⟩
          solcFreePtrMem_size solcFreePtrMem_read64
      have hmemTic : memTic.size = 96 := by
        simpa [memTic, memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemGuy
      have hreadTic : memTic.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
        simpa [memTic, memGuy, id] using twoWordHashMem_read64 id ⟨1⟩ hmemGuy hreadGuy
      simpa [memTicZero, memTic, id] using
        twoWordHashMem_read64 id ⟨1⟩ hmemTic hreadTic)
    (by simp)

set_option maxHeartbeats 1000000 in
theorem flopperDentX_ticGtOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flopperSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat)
    (h : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1634⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1964⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      (twoWordHashMem (dentIdWord I) ⟨1⟩
        (twoWordHashMem (dentIdWord I) ⟨1⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  let id := dentIdWord I
  obtain ⟨_, _, rd1806⟩ := flopperDentX_guyOk (g := g) hlive hguy h
  obtain ⟨_, _, rd1843⟩ := flopperDentX_toTicGtGuard rd1806
  have hgt :
      UInt256.gt (flopperUint48Offset20Word (auctionPackedSlot id) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨1⟩ := by
    apply ugt_one
    simpa [id] using hticGt
  have rd1847 := evm_run rd1843 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨1883⟩ (by native_decide) (by evm_ov)]
  have rd1883 := rd1847.jumpiT (by native_decide)
    (by rw [hgt]; exact one_ne_zero_uint) (by jump_dest) (by evm_ov)
  have rd1884 := rd1883.jumpdest (by native_decide) (by evm_ov)
  have rd1887 := rd1884.push2 ⟨1964⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [id, hgt] using
      rd1887.jumpiT (by native_decide)
        (by rw [hgt]; exact one_ne_zero_uint)
        (by jump_dest) (by evm_ov)⟩

end Benchmarks.Dss.Flopper
