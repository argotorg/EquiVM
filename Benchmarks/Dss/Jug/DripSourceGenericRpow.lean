import Benchmarks.Dss.Jug.DripSourceRho

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Jug

theorem jugDripSourceBodyVatIlksRpowReverts
    {cA gh bl σ σ₀ A I} {g age : UInt256} {evmVat : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hle :
      (jugSlotWord (fileDutyRhoSlotFor I) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (dripVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      typedCallViaEVM config evm0 (EVM.address (dripVatAddress σ I)) "ilks" 0
        [.fixedBytes bytes32Width (fileDutyIlkBytes I)] (true, evmVat, out) true)
    (hdec :
      config.externalABI.decode? "ilks" out =
        some [.int (Int.ofNat (dripVatIlksArtWord out).toNat),
          .int (Int.ofNat (dripVatIlksPrevWord out).toNat)])
    (haddNo :
      ¬ UInt256.size ≤
        (jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv).toNat +
          (jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv).toNat)
    (hage :
      UInt256.sub (UInt256.ofNat evmVat.executionEnv.header.timestamp)
        (jugSlotWord (fileDutyRhoSlotFor I) evmVat.accountMap evmVat.executionEnv) = age)
    (hrpowBody :
      ExecFuncBody config
        { contract := contract,
          locals :=
            uintTernaryLocals
              (jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv +
                jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv)
              age jugRay }
        evmVat rpowFunction.body .reverted) :
    let locals := dripLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dripTransition.body .reverted := by
  intro locals evm0
  let base := jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv
  let duty := jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv
  let fee := base + duty
  have htimeGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ge (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))) =
          .ok (.bool true) := by
    simpa [locals, evm0, initState, jugSlotWord] using
      (evalExpr_dripNowGeRho_true (evm := evm0) (I := I) hsz36 (by
        simpa [evm0, initState, jugSlotWord] using hle))
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (dripVatAddress evm0.accountMap evm0.executionEnv)) := by
    simpa [locals] using evalExpr_dripStorageVat evm0 I
  have hvatCode0 :
      0 <
        (UInt256.ofNat
          ((evm0.lookupAccount (dripVatAddress evm0.accountMap evm0.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat := by
    simpa [evm0, initState] using hvatCode
  have hvatGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_dripVatCodeGuard_true hvat hvatCode0
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (fileDutyIlkBytes I)] := by
    simpa [locals] using evalExprs_dripVatIlksArgs evm0 I
  have hprev :
      evalExpr? config { contract := contract, locals := dripVatIlksLocals I out } evmVat
        (.tupleGet (.var "vatIlk") 1) =
          .ok (.int (Int.ofNat (dripVatIlksPrevWord out).toNat)) :=
    evalExpr_dripVatIlksPrev evmVat I out
  have haddArgs :
      evalExprs? config { contract := contract, locals := dripVatIlksPrevLocals I out } evmVat
        [.storage baseRef, .storage (ilksF (.var "ilk") "duty")] =
          .ok [.int (Int.ofNat base.toNat), .int (Int.ofNat duty.toNat)] := by
    simpa [base, duty] using evalExprs_dripAddArgs evmVat I out hsz36
  have hlookupAdd : lookupCallable? contract "_add" = some addFunction.toCallable := by
    rfl
  have hbindAdd :
      bindParams? addFunction.params [.int (Int.ofNat base.toNat), .int (Int.ofNat duty.toNat)] =
        some (uintBinaryLocals base duty) := by
    simp [addFunction, uintBinaryLocals, bindParams?]
  have hfitAdd : base.toNat + duty.toNat < UInt256.size := by
    exact Nat.lt_of_not_ge haddNo
  have haddReturn :
      ExecStmt config { contract := contract, locals := dripVatIlksPrevLocals I out } evmVat
        (.internalCall "_add"
          [.storage baseRef, .storage (ilksF (.var "ilk") "duty")] "fee")
        (.ok { contract := contract, locals := dripFeeLocals I out fee } evmVat) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := dripVatIlksPrevLocals I out })
      (evm := evmVat) (name := "_add") (retVar := "fee")
      (args := [.storage baseRef, .storage (ilksF (.var "ilk") "duty")])
      (argVals := [.int (Int.ofNat base.toNat), .int (Int.ofNat duty.toNat)])
      (callee := addFunction) (locals := uintBinaryLocals base duty)
      haddArgs hlookupAdd hbindAdd
      (execAddFunctionReturn evmVat (x := base) (y := duty) (sum := fee) rfl hfitAdd)
    simpa [resumeAfterInternalCall, dripFeeLocals, fee] using h
  have hrpowArgs :
      evalExprs? config { contract := contract, locals := dripFeeLocals I out fee } evmVat
        [ .var "fee",
          sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
          .intLit one ] =
          .ok [.int (Int.ofNat fee.toNat), .int (Int.ofNat age.toNat),
            .int (Int.ofNat jugRay.toNat)] :=
    evalExprs_dripRpowArgs evmVat I out fee age hsz36 (by simpa using hage.symm)
  have hlookupRpow : lookupCallable? contract "_rpow" = some rpowFunction.toCallable := by
    rfl
  have hbindRpow :
      bindParams? rpowFunction.params
          [.int (Int.ofNat fee.toNat), .int (Int.ofNat age.toNat),
            .int (Int.ofNat jugRay.toNat)] =
        some (uintTernaryLocals fee age jugRay) := by
    simp [rpowFunction, uintTernaryLocals, bindParams?]
  have hrpowBodyLocal :
      ExecFuncBody config { contract := contract, locals := uintTernaryLocals fee age jugRay }
        evmVat rpowFunction.body .reverted := by
    simpa [fee, base, duty] using hrpowBody
  have hrpowRevert :
      ExecStmt config { contract := contract, locals := dripFeeLocals I out fee } evmVat
        (.internalCall "_rpow"
          [ .var "fee",
            sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
            .intLit one ] "pow")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := dripFeeLocals I out fee })
      (evm := evmVat) (name := "_rpow") (retVar := "pow")
      (args :=
        [ .var "fee",
          sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
          .intLit one ])
      (argVals :=
        [.int (Int.ofNat fee.toNat), .int (Int.ofNat age.toNat),
          .int (Int.ofNat jugRay.toNat)])
      (callee := rpowFunction) (locals := uintTernaryLocals fee age jugRay)
      hrpowArgs hlookupRpow hbindRpow hrpowBodyLocal
  have hprevStmt :
      ExecStmt config { contract := contract, locals := dripVatIlksLocals I out } evmVat
        (.letDecl "prev" (some uint256) (.tupleGet (.var "vatIlk") 1))
        (.ok { contract := contract, locals := dripVatIlksPrevLocals I out } evmVat) := by
    simpa [dripVatIlksPrevLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := dripVatIlksLocals I out })
        (evm := evmVat)
        (name := "prev")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatIlk") 1)
        (value := .int (Int.ofNat (dripVatIlksPrevWord out).toNat))
        hprev)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dripTransition.body
        .reverted := by
    simp only [dripTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue htimeGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess (sendVal := 0) hvat
        (by simp [evalExpr?, pure]) hargs (by simpa [evm0] using hcall) hdec) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, dripVatIlksLocals, collapseReturns] using hprevStmt) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, collapseReturns] using
        haddReturn) ?_
    exact ExecBlock.consRevert (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, dripFeeLocals,
        collapseReturns] using hrpowRevert)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem jugDripSourceBodyVatIlksRmulOverflowRevertsGeneric
    {cA gh bl σ σ₀ A I} {g age pow : UInt256} {evmVat : EVM.State}
    {out : ByteArray} {rpowLocals : Store}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hle :
      (jugSlotWord (fileDutyRhoSlotFor I) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (dripVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      typedCallViaEVM config evm0 (EVM.address (dripVatAddress σ I)) "ilks" 0
        [.fixedBytes bytes32Width (fileDutyIlkBytes I)] (true, evmVat, out) true)
    (hdec :
      config.externalABI.decode? "ilks" out =
        some [.int (Int.ofNat (dripVatIlksArtWord out).toNat),
          .int (Int.ofNat (dripVatIlksPrevWord out).toNat)])
    (haddNo :
      ¬ UInt256.size ≤
        (jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv).toNat +
          (jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv).toNat)
    (hage :
      UInt256.sub (UInt256.ofNat evmVat.executionEnv.header.timestamp)
        (jugSlotWord (fileDutyRhoSlotFor I) evmVat.accountMap evmVat.executionEnv) = age)
    (hrpowBody :
      ExecFuncBody config
        { contract := contract,
          locals :=
            uintTernaryLocals
              (jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv +
                jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv)
              age jugRay }
        evmVat rpowFunction.body
        (.returned { contract := contract, locals := rpowLocals } evmVat
          (some [.int (Int.ofNat pow.toNat)])))
    (hrmulOverflow :
      UInt256.size ≤ pow.toNat * (dripVatIlksPrevWord out).toNat) :
    let locals := dripLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dripTransition.body .reverted := by
  intro locals evm0
  let base := jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv
  let duty := jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv
  let fee := base + duty
  have htimeGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ge (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))) =
          .ok (.bool true) := by
    simpa [locals, evm0, initState, jugSlotWord] using
      (evalExpr_dripNowGeRho_true (evm := evm0) (I := I) hsz36 (by
        simpa [evm0, initState, jugSlotWord] using hle))
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (dripVatAddress evm0.accountMap evm0.executionEnv)) := by
    simpa [locals] using evalExpr_dripStorageVat evm0 I
  have hvatCode0 :
      0 <
        (UInt256.ofNat
          ((evm0.lookupAccount (dripVatAddress evm0.accountMap evm0.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat := by
    simpa [evm0, initState] using hvatCode
  have hvatGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_dripVatCodeGuard_true hvat hvatCode0
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (fileDutyIlkBytes I)] := by
    simpa [locals] using evalExprs_dripVatIlksArgs evm0 I
  have hprev :
      evalExpr? config { contract := contract, locals := dripVatIlksLocals I out } evmVat
        (.tupleGet (.var "vatIlk") 1) =
          .ok (.int (Int.ofNat (dripVatIlksPrevWord out).toNat)) :=
    evalExpr_dripVatIlksPrev evmVat I out
  have haddArgs :
      evalExprs? config { contract := contract, locals := dripVatIlksPrevLocals I out } evmVat
        [.storage baseRef, .storage (ilksF (.var "ilk") "duty")] =
          .ok [.int (Int.ofNat base.toNat), .int (Int.ofNat duty.toNat)] := by
    simpa [base, duty] using evalExprs_dripAddArgs evmVat I out hsz36
  have hlookupAdd : lookupCallable? contract "_add" = some addFunction.toCallable := by
    rfl
  have hbindAdd :
      bindParams? addFunction.params [.int (Int.ofNat base.toNat), .int (Int.ofNat duty.toNat)] =
        some (uintBinaryLocals base duty) := by
    simp [addFunction, uintBinaryLocals, bindParams?]
  have hfitAdd : base.toNat + duty.toNat < UInt256.size := by
    exact Nat.lt_of_not_ge haddNo
  have haddReturn :
      ExecStmt config { contract := contract, locals := dripVatIlksPrevLocals I out } evmVat
        (.internalCall "_add"
          [.storage baseRef, .storage (ilksF (.var "ilk") "duty")] "fee")
        (.ok { contract := contract, locals := dripFeeLocals I out fee } evmVat) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := dripVatIlksPrevLocals I out })
      (evm := evmVat) (name := "_add") (retVar := "fee")
      (args := [.storage baseRef, .storage (ilksF (.var "ilk") "duty")])
      (argVals := [.int (Int.ofNat base.toNat), .int (Int.ofNat duty.toNat)])
      (callee := addFunction) (locals := uintBinaryLocals base duty)
      haddArgs hlookupAdd hbindAdd
      (execAddFunctionReturn evmVat (x := base) (y := duty) (sum := fee) rfl hfitAdd)
    simpa [resumeAfterInternalCall, dripFeeLocals, fee] using h
  have hrpowArgs :
      evalExprs? config { contract := contract, locals := dripFeeLocals I out fee } evmVat
        [ .var "fee",
          sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
          .intLit one ] =
          .ok [.int (Int.ofNat fee.toNat), .int (Int.ofNat age.toNat),
            .int (Int.ofNat jugRay.toNat)] :=
    evalExprs_dripRpowArgs evmVat I out fee age hsz36 (by simpa using hage.symm)
  have hlookupRpow : lookupCallable? contract "_rpow" = some rpowFunction.toCallable := by
    rfl
  have hbindRpow :
      bindParams? rpowFunction.params
          [.int (Int.ofNat fee.toNat), .int (Int.ofNat age.toNat),
            .int (Int.ofNat jugRay.toNat)] =
        some (uintTernaryLocals fee age jugRay) := by
    simp [rpowFunction, uintTernaryLocals, bindParams?]
  have hrpowBodyLocal :
      ExecFuncBody config { contract := contract, locals := uintTernaryLocals fee age jugRay }
        evmVat rpowFunction.body
        (.returned { contract := contract, locals := rpowLocals } evmVat
          (some [.int (Int.ofNat pow.toNat)])) := by
    simpa [fee, base, duty] using hrpowBody
  have hrpowReturn :
      ExecStmt config { contract := contract, locals := dripFeeLocals I out fee } evmVat
        (.internalCall "_rpow"
          [ .var "fee",
            sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
            .intLit one ] "pow")
        (.ok { contract := contract, locals := dripPowLocals I out fee pow } evmVat) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := dripFeeLocals I out fee })
      (evm := evmVat) (name := "_rpow") (retVar := "pow")
      (args :=
        [ .var "fee",
          sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
          .intLit one ])
      (argVals :=
        [.int (Int.ofNat fee.toNat), .int (Int.ofNat age.toNat),
          .int (Int.ofNat jugRay.toNat)])
      (callee := rpowFunction) (locals := uintTernaryLocals fee age jugRay)
      (calleeSolm := { contract := contract, locals := rpowLocals })
      hrpowArgs hlookupRpow hbindRpow hrpowBodyLocal
    simpa [resumeAfterInternalCall, dripPowLocals] using h
  have hrmulArgs :
      evalExprs? config { contract := contract, locals := dripPowLocals I out fee pow }
        evmVat [.var "pow", .var "prev"] =
        .ok [.int (Int.ofNat pow.toNat),
          .int (Int.ofNat (dripVatIlksPrevWord out).toNat)] :=
    evalExprs_dripRmulArgs evmVat I out fee pow
  have hlookupRmul : lookupCallable? contract "_rmul" = some rmulFunction.toCallable := by
    rfl
  have hbindRmul :
      bindParams? rmulFunction.params
          [.int (Int.ofNat pow.toNat),
            .int (Int.ofNat (dripVatIlksPrevWord out).toNat)] =
        some (uintBinaryLocals pow (dripVatIlksPrevWord out)) := by
    simp [rmulFunction, uintBinaryLocals, bindParams?]
  have hrmulRevert :
      ExecStmt config { contract := contract, locals := dripPowLocals I out fee pow } evmVat
        (.internalCall "_rmul" [.var "pow", .var "prev"] "rate") .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := dripPowLocals I out fee pow })
      (evm := evmVat) (name := "_rmul") (retVar := "rate")
      (args := [.var "pow", .var "prev"])
      (argVals :=
        [.int (Int.ofNat pow.toNat),
          .int (Int.ofNat (dripVatIlksPrevWord out).toNat)])
      (callee := rmulFunction) (locals := uintBinaryLocals pow (dripVatIlksPrevWord out))
      hrmulArgs hlookupRmul hbindRmul
      (execRmulFunctionRevertMul evmVat (x := pow) (y := dripVatIlksPrevWord out)
        hrmulOverflow)
  have hprevStmt :
      ExecStmt config { contract := contract, locals := dripVatIlksLocals I out } evmVat
        (.letDecl "prev" (some uint256) (.tupleGet (.var "vatIlk") 1))
        (.ok { contract := contract, locals := dripVatIlksPrevLocals I out } evmVat) := by
    simpa [dripVatIlksPrevLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := dripVatIlksLocals I out })
        (evm := evmVat)
        (name := "prev")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatIlk") 1)
        (value := .int (Int.ofNat (dripVatIlksPrevWord out).toNat))
        hprev)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dripTransition.body
        .reverted := by
    simp only [dripTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue htimeGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess (sendVal := 0) hvat
        (by simp [evalExpr?, pure]) hargs (by simpa [evm0] using hcall) hdec) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, dripVatIlksLocals, collapseReturns] using hprevStmt) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, collapseReturns] using
        haddReturn) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, dripFeeLocals,
        collapseReturns] using hrpowReturn) ?_
    exact ExecBlock.consRevert (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, dripFeeLocals, dripPowLocals,
        collapseReturns] using hrmulRevert)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem jugDripSourceBodyVatIlksDiffXBoundRevertsGeneric
    {cA gh bl σ σ₀ A I} {g age pow : UInt256} {evmVat : EVM.State}
    {out : ByteArray} {rpowLocals : Store}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hle :
      (jugSlotWord (fileDutyRhoSlotFor I) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (dripVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      typedCallViaEVM config evm0 (EVM.address (dripVatAddress σ I)) "ilks" 0
        [.fixedBytes bytes32Width (fileDutyIlkBytes I)] (true, evmVat, out) true)
    (hdec :
      config.externalABI.decode? "ilks" out =
        some [.int (Int.ofNat (dripVatIlksArtWord out).toNat),
          .int (Int.ofNat (dripVatIlksPrevWord out).toNat)])
    (haddNo :
      ¬ UInt256.size ≤
        (jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv).toNat +
          (jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv).toNat)
    (hage :
      UInt256.sub (UInt256.ofNat evmVat.executionEnv.header.timestamp)
        (jugSlotWord (fileDutyRhoSlotFor I) evmVat.accountMap evmVat.executionEnv) = age)
    (hrpowBody :
      ExecFuncBody config
        { contract := contract,
          locals :=
            uintTernaryLocals
              (jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv +
                jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv)
              age jugRay }
        evmVat rpowFunction.body
        (.returned { contract := contract, locals := rpowLocals } evmVat
          (some [.int (Int.ofNat pow.toNat)])))
    (hfitRmul : pow.toNat * (dripVatIlksPrevWord out).toNat < UInt256.size)
    (hrateMaxNot :
      ¬ ((UInt256.div (dripVatIlksPrevWord out * pow) jugRay).toNat : Int) ≤ maxInt256) :
    let locals := dripLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dripTransition.body .reverted := by
  intro locals evm0
  let base := jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv
  let duty := jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv
  let fee := base + duty
  let prev := dripVatIlksPrevWord out
  let rate := UInt256.div (prev * pow) jugRay
  have hfitRmulLocal : pow.toNat * prev.toNat < UInt256.size := by
    simpa [prev] using hfitRmul
  have hrateMaxNotLocal : ¬ (rate.toNat : Int) ≤ maxInt256 := by
    simpa [rate, prev] using hrateMaxNot
  have hrateGt : maxInt256 < (rate.toNat : Int) := by
    exact lt_of_not_ge hrateMaxNotLocal
  have htimeGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ge (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))) =
          .ok (.bool true) := by
    simpa [locals, evm0, initState, jugSlotWord] using
      (evalExpr_dripNowGeRho_true (evm := evm0) (I := I) hsz36 (by
        simpa [evm0, initState, jugSlotWord] using hle))
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (dripVatAddress evm0.accountMap evm0.executionEnv)) := by
    simpa [locals] using evalExpr_dripStorageVat evm0 I
  have hvatCode0 :
      0 <
        (UInt256.ofNat
          ((evm0.lookupAccount (dripVatAddress evm0.accountMap evm0.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat := by
    simpa [evm0, initState] using hvatCode
  have hvatGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_dripVatCodeGuard_true hvat hvatCode0
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (fileDutyIlkBytes I)] := by
    simpa [locals] using evalExprs_dripVatIlksArgs evm0 I
  have hprev :
      evalExpr? config { contract := contract, locals := dripVatIlksLocals I out } evmVat
        (.tupleGet (.var "vatIlk") 1) = .ok (.int (Int.ofNat prev.toNat)) := by
    simpa [prev] using evalExpr_dripVatIlksPrev evmVat I out
  have haddArgs :
      evalExprs? config { contract := contract, locals := dripVatIlksPrevLocals I out } evmVat
        [.storage baseRef, .storage (ilksF (.var "ilk") "duty")] =
          .ok [.int (Int.ofNat base.toNat), .int (Int.ofNat duty.toNat)] := by
    simpa [base, duty] using evalExprs_dripAddArgs evmVat I out hsz36
  have hlookupAdd : lookupCallable? contract "_add" = some addFunction.toCallable := by
    rfl
  have hbindAdd :
      bindParams? addFunction.params [.int (Int.ofNat base.toNat), .int (Int.ofNat duty.toNat)] =
        some (uintBinaryLocals base duty) := by
    simp [addFunction, uintBinaryLocals, bindParams?]
  have hfitAdd : base.toNat + duty.toNat < UInt256.size := by
    exact Nat.lt_of_not_ge haddNo
  have haddReturn :
      ExecStmt config { contract := contract, locals := dripVatIlksPrevLocals I out } evmVat
        (.internalCall "_add"
          [.storage baseRef, .storage (ilksF (.var "ilk") "duty")] "fee")
        (.ok { contract := contract, locals := dripFeeLocals I out fee } evmVat) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := dripVatIlksPrevLocals I out })
      (evm := evmVat) (name := "_add") (retVar := "fee")
      (args := [.storage baseRef, .storage (ilksF (.var "ilk") "duty")])
      (argVals := [.int (Int.ofNat base.toNat), .int (Int.ofNat duty.toNat)])
      (callee := addFunction) (locals := uintBinaryLocals base duty)
      haddArgs hlookupAdd hbindAdd
      (execAddFunctionReturn evmVat (x := base) (y := duty) (sum := fee) rfl hfitAdd)
    simpa [resumeAfterInternalCall, dripFeeLocals, fee] using h
  have hrpowArgs :
      evalExprs? config { contract := contract, locals := dripFeeLocals I out fee } evmVat
        [ .var "fee",
          sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
          .intLit one ] =
          .ok [.int (Int.ofNat fee.toNat), .int (Int.ofNat age.toNat),
            .int (Int.ofNat jugRay.toNat)] :=
    evalExprs_dripRpowArgs evmVat I out fee age hsz36 (by simpa using hage.symm)
  have hlookupRpow : lookupCallable? contract "_rpow" = some rpowFunction.toCallable := by
    rfl
  have hbindRpow :
      bindParams? rpowFunction.params
          [.int (Int.ofNat fee.toNat), .int (Int.ofNat age.toNat),
            .int (Int.ofNat jugRay.toNat)] =
        some (uintTernaryLocals fee age jugRay) := by
    simp [rpowFunction, uintTernaryLocals, bindParams?]
  have hrpowBodyLocal :
      ExecFuncBody config { contract := contract, locals := uintTernaryLocals fee age jugRay }
        evmVat rpowFunction.body
        (.returned { contract := contract, locals := rpowLocals } evmVat
          (some [.int (Int.ofNat pow.toNat)])) := by
    simpa [fee, base, duty] using hrpowBody
  have hrpowReturn :
      ExecStmt config { contract := contract, locals := dripFeeLocals I out fee } evmVat
        (.internalCall "_rpow"
          [ .var "fee",
            sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
            .intLit one ] "pow")
        (.ok { contract := contract, locals := dripPowLocals I out fee pow } evmVat) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := dripFeeLocals I out fee })
      (evm := evmVat) (name := "_rpow") (retVar := "pow")
      (args :=
        [ .var "fee",
          sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
          .intLit one ])
      (argVals :=
        [.int (Int.ofNat fee.toNat), .int (Int.ofNat age.toNat),
          .int (Int.ofNat jugRay.toNat)])
      (callee := rpowFunction) (locals := uintTernaryLocals fee age jugRay)
      (calleeSolm := { contract := contract, locals := rpowLocals })
      hrpowArgs hlookupRpow hbindRpow hrpowBodyLocal
    simpa [resumeAfterInternalCall, dripPowLocals] using h
  have hrmulArgs :
      evalExprs? config { contract := contract, locals := dripPowLocals I out fee pow }
        evmVat [.var "pow", .var "prev"] =
        .ok [.int (Int.ofNat pow.toNat), .int (Int.ofNat prev.toNat)] := by
    simpa [prev] using evalExprs_dripRmulArgs evmVat I out fee pow
  have hlookupRmul : lookupCallable? contract "_rmul" = some rmulFunction.toCallable := by
    rfl
  have hbindRmul :
      bindParams? rmulFunction.params [.int (Int.ofNat pow.toNat), .int (Int.ofNat prev.toNat)] =
        some (uintBinaryLocals pow prev) := by
    simp [rmulFunction, uintBinaryLocals, bindParams?]
  have hprodComm : prev * pow = pow * prev := by
    simpa using u256_mul_comm prev pow
  have hq : rate = UInt256.div (pow * prev) jugRay := by
    dsimp [rate]
    rw [hprodComm]
  have hrmulReturn :
      ExecStmt config { contract := contract, locals := dripPowLocals I out fee pow } evmVat
        (.internalCall "_rmul" [.var "pow", .var "prev"] "rate")
        (.ok { contract := contract, locals := dripRateLocals I out fee pow rate } evmVat) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := dripPowLocals I out fee pow })
      (evm := evmVat) (name := "_rmul") (retVar := "rate")
      (args := [.var "pow", .var "prev"])
      (argVals := [.int (Int.ofNat pow.toNat), .int (Int.ofNat prev.toNat)])
      (callee := rmulFunction) (locals := uintBinaryLocals pow prev)
      hrmulArgs hlookupRmul hbindRmul
      (execRmulFunctionReturn evmVat (x := pow) (y := prev) (prod := pow * prev)
        (q := rate) rfl hfitRmulLocal hq)
    simpa [resumeAfterInternalCall, dripRateLocals] using h
  have hdiffArgs :
      evalExprs? config { contract := contract, locals := dripRateLocals I out fee pow rate }
        evmVat [.var "rate", .var "prev"] =
          .ok [.int (Int.ofNat rate.toNat), .int (Int.ofNat prev.toNat)] := by
    simpa [prev] using evalExprs_dripDiffArgs evmVat I out fee pow rate
  have hlookupDiff : lookupCallable? contract "_diff" = some diffFunction.toCallable := by
    rfl
  have hbindDiff :
      bindParams? diffFunction.params [.int (Int.ofNat rate.toNat), .int (Int.ofNat prev.toNat)] =
        some (uintBinaryLocals rate prev) := by
    simp [diffFunction, uintBinaryLocals, bindParams?]
  have hdiffRevert :
      ExecStmt config { contract := contract, locals := dripRateLocals I out fee pow rate }
        evmVat (.internalCall "_diff" [.var "rate", .var "prev"] "delta") .reverted := by
    by_cases hlo : -((2 : Int) ^ 255) ≤ (rate.toNat : Int) - (prev.toNat : Int)
    · by_cases hhi : (rate.toNat : Int) - (prev.toNat : Int) < (2 : Int) ^ 255
      · exact internalCallFunctionRevert
          (cfg := config)
          (caller := { contract := contract, locals := dripRateLocals I out fee pow rate })
          (evm := evmVat) (name := "_diff") (retVar := "delta")
          (args := [.var "rate", .var "prev"])
          (argVals := [.int (Int.ofNat rate.toNat), .int (Int.ofNat prev.toNat)])
          (callee := diffFunction) (locals := uintBinaryLocals rate prev)
          hdiffArgs hlookupDiff hbindDiff
          (execDiffFunctionRevertXBound evmVat (x := rate) (y := prev) hlo hhi hrateGt)
      · have hbad :
            (rate.toNat : Int) - (prev.toNat : Int) < -((2 : Int) ^ 255) ∨
              (rate.toNat : Int) - (prev.toNat : Int) ≥ (2 : Int) ^ 255 := by
          right
          omega
        exact internalCallFunctionRevert
          (cfg := config)
          (caller := { contract := contract, locals := dripRateLocals I out fee pow rate })
          (evm := evmVat) (name := "_diff") (retVar := "delta")
          (args := [.var "rate", .var "prev"])
          (argVals := [.int (Int.ofNat rate.toNat), .int (Int.ofNat prev.toNat)])
          (callee := diffFunction) (locals := uintBinaryLocals rate prev)
          hdiffArgs hlookupDiff hbindDiff
          (execDiffFunctionRevertCast evmVat (x := rate) (y := prev) hbad)
    · have hbad :
          (rate.toNat : Int) - (prev.toNat : Int) < -((2 : Int) ^ 255) ∨
            (rate.toNat : Int) - (prev.toNat : Int) ≥ (2 : Int) ^ 255 := by
        left
        omega
      exact internalCallFunctionRevert
        (cfg := config)
        (caller := { contract := contract, locals := dripRateLocals I out fee pow rate })
        (evm := evmVat) (name := "_diff") (retVar := "delta")
        (args := [.var "rate", .var "prev"])
        (argVals := [.int (Int.ofNat rate.toNat), .int (Int.ofNat prev.toNat)])
        (callee := diffFunction) (locals := uintBinaryLocals rate prev)
        hdiffArgs hlookupDiff hbindDiff
        (execDiffFunctionRevertCast evmVat (x := rate) (y := prev) hbad)
  have hprevStmt :
      ExecStmt config { contract := contract, locals := dripVatIlksLocals I out } evmVat
        (.letDecl "prev" (some uint256) (.tupleGet (.var "vatIlk") 1))
        (.ok { contract := contract, locals := dripVatIlksPrevLocals I out } evmVat) := by
    simpa [dripVatIlksPrevLocals, prev] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := dripVatIlksLocals I out })
        (evm := evmVat)
        (name := "prev")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatIlk") 1)
        (value := .int (Int.ofNat prev.toNat))
        hprev)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dripTransition.body
        .reverted := by
    simp only [dripTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue htimeGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess (sendVal := 0) hvat
        (by simp [evalExpr?, pure]) hargs (by simpa [evm0] using hcall) hdec) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, dripVatIlksLocals, collapseReturns] using hprevStmt) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, collapseReturns] using
        haddReturn) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, dripFeeLocals,
        collapseReturns] using hrpowReturn) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, dripFeeLocals, dripPowLocals,
        collapseReturns] using hrmulReturn) ?_
    exact ExecBlock.consRevert (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, dripFeeLocals, dripPowLocals,
        dripRateLocals, collapseReturns] using hdiffRevert)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem jugDripSourceBodyVatIlksDiffYBoundRevertsGeneric
    {cA gh bl σ σ₀ A I} {g age pow : UInt256} {evmVat : EVM.State}
    {out : ByteArray} {rpowLocals : Store}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hle :
      (jugSlotWord (fileDutyRhoSlotFor I) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (dripVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      typedCallViaEVM config evm0 (EVM.address (dripVatAddress σ I)) "ilks" 0
        [.fixedBytes bytes32Width (fileDutyIlkBytes I)] (true, evmVat, out) true)
    (hdec :
      config.externalABI.decode? "ilks" out =
        some [.int (Int.ofNat (dripVatIlksArtWord out).toNat),
          .int (Int.ofNat (dripVatIlksPrevWord out).toNat)])
    (haddNo :
      ¬ UInt256.size ≤
        (jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv).toNat +
          (jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv).toNat)
    (hage :
      UInt256.sub (UInt256.ofNat evmVat.executionEnv.header.timestamp)
        (jugSlotWord (fileDutyRhoSlotFor I) evmVat.accountMap evmVat.executionEnv) = age)
    (hrpowBody :
      ExecFuncBody config
        { contract := contract,
          locals :=
            uintTernaryLocals
              (jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv +
                jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv)
              age jugRay }
        evmVat rpowFunction.body
        (.returned { contract := contract, locals := rpowLocals } evmVat
          (some [.int (Int.ofNat pow.toNat)])))
    (hfitRmul : pow.toNat * (dripVatIlksPrevWord out).toNat < UInt256.size)
    (hrateMax :
      ((UInt256.div (dripVatIlksPrevWord out * pow) jugRay).toNat : Int) ≤ maxInt256)
    (hprevMaxNot : ¬ ((dripVatIlksPrevWord out).toNat : Int) ≤ maxInt256) :
    let locals := dripLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dripTransition.body .reverted := by
  intro locals evm0
  let base := jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv
  let duty := jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv
  let fee := base + duty
  let prev := dripVatIlksPrevWord out
  let rate := UInt256.div (prev * pow) jugRay
  have hfitRmulLocal : pow.toNat * prev.toNat < UInt256.size := by
    simpa [prev] using hfitRmul
  have hrateMaxLocal : (rate.toNat : Int) ≤ maxInt256 := by
    simpa [rate, prev] using hrateMax
  have hprevGt : maxInt256 < (prev.toNat : Int) := by
    exact lt_of_not_ge (by simpa [prev] using hprevMaxNot)
  have htimeGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ge (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))) =
          .ok (.bool true) := by
    simpa [locals, evm0, initState, jugSlotWord] using
      (evalExpr_dripNowGeRho_true (evm := evm0) (I := I) hsz36 (by
        simpa [evm0, initState, jugSlotWord] using hle))
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (dripVatAddress evm0.accountMap evm0.executionEnv)) := by
    simpa [locals] using evalExpr_dripStorageVat evm0 I
  have hvatCode0 :
      0 <
        (UInt256.ofNat
          ((evm0.lookupAccount (dripVatAddress evm0.accountMap evm0.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat := by
    simpa [evm0, initState] using hvatCode
  have hvatGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_dripVatCodeGuard_true hvat hvatCode0
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (fileDutyIlkBytes I)] := by
    simpa [locals] using evalExprs_dripVatIlksArgs evm0 I
  have hprev :
      evalExpr? config { contract := contract, locals := dripVatIlksLocals I out } evmVat
        (.tupleGet (.var "vatIlk") 1) = .ok (.int (Int.ofNat prev.toNat)) := by
    simpa [prev] using evalExpr_dripVatIlksPrev evmVat I out
  have haddArgs :
      evalExprs? config { contract := contract, locals := dripVatIlksPrevLocals I out } evmVat
        [.storage baseRef, .storage (ilksF (.var "ilk") "duty")] =
          .ok [.int (Int.ofNat base.toNat), .int (Int.ofNat duty.toNat)] := by
    simpa [base, duty] using evalExprs_dripAddArgs evmVat I out hsz36
  have hlookupAdd : lookupCallable? contract "_add" = some addFunction.toCallable := by
    rfl
  have hbindAdd :
      bindParams? addFunction.params [.int (Int.ofNat base.toNat), .int (Int.ofNat duty.toNat)] =
        some (uintBinaryLocals base duty) := by
    simp [addFunction, uintBinaryLocals, bindParams?]
  have hfitAdd : base.toNat + duty.toNat < UInt256.size := by
    exact Nat.lt_of_not_ge haddNo
  have haddReturn :
      ExecStmt config { contract := contract, locals := dripVatIlksPrevLocals I out } evmVat
        (.internalCall "_add"
          [.storage baseRef, .storage (ilksF (.var "ilk") "duty")] "fee")
        (.ok { contract := contract, locals := dripFeeLocals I out fee } evmVat) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := dripVatIlksPrevLocals I out })
      (evm := evmVat) (name := "_add") (retVar := "fee")
      (args := [.storage baseRef, .storage (ilksF (.var "ilk") "duty")])
      (argVals := [.int (Int.ofNat base.toNat), .int (Int.ofNat duty.toNat)])
      (callee := addFunction) (locals := uintBinaryLocals base duty)
      haddArgs hlookupAdd hbindAdd
      (execAddFunctionReturn evmVat (x := base) (y := duty) (sum := fee) rfl hfitAdd)
    simpa [resumeAfterInternalCall, dripFeeLocals, fee] using h
  have hrpowArgs :
      evalExprs? config { contract := contract, locals := dripFeeLocals I out fee } evmVat
        [ .var "fee",
          sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
          .intLit one ] =
          .ok [.int (Int.ofNat fee.toNat), .int (Int.ofNat age.toNat),
            .int (Int.ofNat jugRay.toNat)] :=
    evalExprs_dripRpowArgs evmVat I out fee age hsz36 (by simpa using hage.symm)
  have hlookupRpow : lookupCallable? contract "_rpow" = some rpowFunction.toCallable := by
    rfl
  have hbindRpow :
      bindParams? rpowFunction.params
          [.int (Int.ofNat fee.toNat), .int (Int.ofNat age.toNat),
            .int (Int.ofNat jugRay.toNat)] =
        some (uintTernaryLocals fee age jugRay) := by
    simp [rpowFunction, uintTernaryLocals, bindParams?]
  have hrpowBodyLocal :
      ExecFuncBody config { contract := contract, locals := uintTernaryLocals fee age jugRay }
        evmVat rpowFunction.body
        (.returned { contract := contract, locals := rpowLocals } evmVat
          (some [.int (Int.ofNat pow.toNat)])) := by
    simpa [fee, base, duty] using hrpowBody
  have hrpowReturn :
      ExecStmt config { contract := contract, locals := dripFeeLocals I out fee } evmVat
        (.internalCall "_rpow"
          [ .var "fee",
            sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
            .intLit one ] "pow")
        (.ok { contract := contract, locals := dripPowLocals I out fee pow } evmVat) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := dripFeeLocals I out fee })
      (evm := evmVat) (name := "_rpow") (retVar := "pow")
      (args :=
        [ .var "fee",
          sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
          .intLit one ])
      (argVals :=
        [.int (Int.ofNat fee.toNat), .int (Int.ofNat age.toNat),
          .int (Int.ofNat jugRay.toNat)])
      (callee := rpowFunction) (locals := uintTernaryLocals fee age jugRay)
      (calleeSolm := { contract := contract, locals := rpowLocals })
      hrpowArgs hlookupRpow hbindRpow hrpowBodyLocal
    simpa [resumeAfterInternalCall, dripPowLocals] using h
  have hrmulArgs :
      evalExprs? config { contract := contract, locals := dripPowLocals I out fee pow }
        evmVat [.var "pow", .var "prev"] =
        .ok [.int (Int.ofNat pow.toNat), .int (Int.ofNat prev.toNat)] := by
    simpa [prev] using evalExprs_dripRmulArgs evmVat I out fee pow
  have hlookupRmul : lookupCallable? contract "_rmul" = some rmulFunction.toCallable := by
    rfl
  have hbindRmul :
      bindParams? rmulFunction.params [.int (Int.ofNat pow.toNat), .int (Int.ofNat prev.toNat)] =
        some (uintBinaryLocals pow prev) := by
    simp [rmulFunction, uintBinaryLocals, bindParams?]
  have hprodComm : prev * pow = pow * prev := by
    simpa using u256_mul_comm prev pow
  have hq : rate = UInt256.div (pow * prev) jugRay := by
    dsimp [rate]
    rw [hprodComm]
  have hrmulReturn :
      ExecStmt config { contract := contract, locals := dripPowLocals I out fee pow } evmVat
        (.internalCall "_rmul" [.var "pow", .var "prev"] "rate")
        (.ok { contract := contract, locals := dripRateLocals I out fee pow rate } evmVat) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := dripPowLocals I out fee pow })
      (evm := evmVat) (name := "_rmul") (retVar := "rate")
      (args := [.var "pow", .var "prev"])
      (argVals := [.int (Int.ofNat pow.toNat), .int (Int.ofNat prev.toNat)])
      (callee := rmulFunction) (locals := uintBinaryLocals pow prev)
      hrmulArgs hlookupRmul hbindRmul
      (execRmulFunctionReturn evmVat (x := pow) (y := prev) (prod := pow * prev)
        (q := rate) rfl hfitRmulLocal hq)
    simpa [resumeAfterInternalCall, dripRateLocals] using h
  have hdiffArgs :
      evalExprs? config { contract := contract, locals := dripRateLocals I out fee pow rate }
        evmVat [.var "rate", .var "prev"] =
          .ok [.int (Int.ofNat rate.toNat), .int (Int.ofNat prev.toNat)] := by
    simpa [prev] using evalExprs_dripDiffArgs evmVat I out fee pow rate
  have hlookupDiff : lookupCallable? contract "_diff" = some diffFunction.toCallable := by
    rfl
  have hbindDiff :
      bindParams? diffFunction.params [.int (Int.ofNat rate.toNat), .int (Int.ofNat prev.toNat)] =
        some (uintBinaryLocals rate prev) := by
    simp [diffFunction, uintBinaryLocals, bindParams?]
  have hdiffRevert :
      ExecStmt config { contract := contract, locals := dripRateLocals I out fee pow rate }
        evmVat (.internalCall "_diff" [.var "rate", .var "prev"] "delta") .reverted := by
    by_cases hlo : -((2 : Int) ^ 255) ≤ (rate.toNat : Int) - (prev.toNat : Int)
    · have hhi : (rate.toNat : Int) - (prev.toNat : Int) < (2 : Int) ^ 255 := by
        have hrateHi : (rate.toNat : Int) < (2 : Int) ^ 255 := by
          have hle : (rate.toNat : Int) ≤ (2 : Int) ^ 255 - 1 := by
            simpa [maxInt256] using hrateMaxLocal
          omega
        have hprevNonneg : 0 ≤ (prev.toNat : Int) := Int.natCast_nonneg _
        omega
      exact internalCallFunctionRevert
        (cfg := config)
        (caller := { contract := contract, locals := dripRateLocals I out fee pow rate })
        (evm := evmVat) (name := "_diff") (retVar := "delta")
        (args := [.var "rate", .var "prev"])
        (argVals := [.int (Int.ofNat rate.toNat), .int (Int.ofNat prev.toNat)])
        (callee := diffFunction) (locals := uintBinaryLocals rate prev)
        hdiffArgs hlookupDiff hbindDiff
        (execDiffFunctionRevertYBound evmVat (x := rate) (y := prev)
          hlo hhi hrateMaxLocal hprevGt)
    · have hbad :
          (rate.toNat : Int) - (prev.toNat : Int) < -((2 : Int) ^ 255) ∨
            (rate.toNat : Int) - (prev.toNat : Int) ≥ (2 : Int) ^ 255 := by
        left
        omega
      exact internalCallFunctionRevert
        (cfg := config)
        (caller := { contract := contract, locals := dripRateLocals I out fee pow rate })
        (evm := evmVat) (name := "_diff") (retVar := "delta")
        (args := [.var "rate", .var "prev"])
        (argVals := [.int (Int.ofNat rate.toNat), .int (Int.ofNat prev.toNat)])
        (callee := diffFunction) (locals := uintBinaryLocals rate prev)
        hdiffArgs hlookupDiff hbindDiff
        (execDiffFunctionRevertCast evmVat (x := rate) (y := prev) hbad)
  have hprevStmt :
      ExecStmt config { contract := contract, locals := dripVatIlksLocals I out } evmVat
        (.letDecl "prev" (some uint256) (.tupleGet (.var "vatIlk") 1))
        (.ok { contract := contract, locals := dripVatIlksPrevLocals I out } evmVat) := by
    simpa [dripVatIlksPrevLocals, prev] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := dripVatIlksLocals I out })
        (evm := evmVat)
        (name := "prev")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatIlk") 1)
        (value := .int (Int.ofNat prev.toNat))
        hprev)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dripTransition.body
        .reverted := by
    simp only [dripTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue htimeGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess (sendVal := 0) hvat
        (by simp [evalExpr?, pure]) hargs (by simpa [evm0] using hcall) hdec) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, dripVatIlksLocals, collapseReturns] using hprevStmt) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, collapseReturns] using
        haddReturn) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, dripFeeLocals,
        collapseReturns] using hrpowReturn) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, dripFeeLocals, dripPowLocals,
        collapseReturns] using hrmulReturn) ?_
    exact ExecBlock.consRevert (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, dripFeeLocals, dripPowLocals,
        dripRateLocals, collapseReturns] using hdiffRevert)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

end Benchmarks.Dss.Jug
