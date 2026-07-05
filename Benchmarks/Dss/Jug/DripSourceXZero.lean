import Benchmarks.Dss.Jug.DripSourceNOne

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Jug

theorem jugDripSourceBodyVatIlksDiffBoundReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
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
        (jugSlotWord (fileDutyRhoSlotFor I) evmVat.accountMap evmVat.executionEnv) = ⟨0⟩)
    (hfitRmul : jugRay.toNat * (dripVatIlksPrevWord out).toNat < UInt256.size)
    (hprevMaxNot : ¬ ((dripVatIlksPrevWord out).toNat : Int) ≤ maxInt256) :
    let locals := dripLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dripTransition.body .reverted := by
  intro locals evm0
  let base := jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv
  let duty := jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv
  let fee := base + duty
  let rate := dripVatIlksPrevWord out
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
        (.tupleGet (.var "vatIlk") 1) = .ok (.int (Int.ofNat rate.toNat)) := by
    simpa [rate] using evalExpr_dripVatIlksPrev evmVat I out
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
          .ok [.int (Int.ofNat fee.toNat), .int 0, .int (Int.ofNat jugRay.toNat)] :=
    evalExprs_dripRpowNZeroArgs evmVat I out fee hsz36 hage
  have hlookupRpow : lookupCallable? contract "_rpow" = some rpowFunction.toCallable := by
    rfl
  have hbindRpow :
      bindParams? rpowFunction.params
          [.int (Int.ofNat fee.toNat), .int 0, .int (Int.ofNat jugRay.toNat)] =
        some (uintTernaryLocals fee ⟨0⟩ jugRay) := by
    simp [rpowFunction, uintTernaryLocals, bindParams?, jugUInt256Zero_toNat]
  have hrpowBody :
      ∃ doneLocals,
        ExecFuncBody config { contract := contract, locals := uintTernaryLocals fee ⟨0⟩ jugRay }
          evmVat rpowFunction.body
          (.returned { contract := contract, locals := doneLocals }
            evmVat (some [.int (Int.ofNat jugRay.toNat)])) := by
    by_cases hfee0 : fee = ⟨0⟩
    · exact ⟨uintTernaryLocals ⟨0⟩ ⟨0⟩ jugRay, by
        simpa [hfee0] using execRpowFunctionReturnXZeroNZero (evm := evmVat) (b := jugRay)⟩
    · have h := execRpowFunctionReturnXNonzeroNZero (evm := evmVat) (x := fee)
        (b := jugRay) hfee0
      exact ⟨rpowLocalsZHN fee ⟨0⟩ jugRay jugRay (UInt256.div jugRay ⟨2⟩) ⟨0⟩, h⟩
  obtain ⟨rpowDoneLocals, hrpowBody⟩ := hrpowBody
  have hrpowReturn :
      ExecStmt config { contract := contract, locals := dripFeeLocals I out fee } evmVat
        (.internalCall "_rpow"
          [ .var "fee",
            sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
            .intLit one ] "pow")
        (.ok { contract := contract, locals := dripPowLocals I out fee jugRay } evmVat) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := dripFeeLocals I out fee })
      (evm := evmVat) (name := "_rpow") (retVar := "pow")
      (args :=
        [ .var "fee",
          sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
          .intLit one ])
      (argVals := [.int (Int.ofNat fee.toNat), .int 0, .int (Int.ofNat jugRay.toNat)])
      (callee := rpowFunction) (locals := uintTernaryLocals fee ⟨0⟩ jugRay)
      (calleeSolm := { contract := contract, locals := rpowDoneLocals })
      hrpowArgs hlookupRpow hbindRpow hrpowBody
    simpa [resumeAfterInternalCall, dripPowLocals] using h
  have hrmulArgs :
      evalExprs? config { contract := contract, locals := dripPowLocals I out fee jugRay }
        evmVat [.var "pow", .var "prev"] =
        .ok [.int (Int.ofNat jugRay.toNat), .int (Int.ofNat rate.toNat)] := by
    simpa [rate] using evalExprs_dripRmulArgs evmVat I out fee jugRay
  have hlookupRmul : lookupCallable? contract "_rmul" = some rmulFunction.toCallable := by
    rfl
  have hbindRmul :
      bindParams? rmulFunction.params [.int (Int.ofNat jugRay.toNat), .int (Int.ofNat rate.toNat)] =
        some (uintBinaryLocals jugRay rate) := by
    simp [rmulFunction, uintBinaryLocals, bindParams?]
  have hmulComm : jugRay * rate = rate * jugRay := by
    simpa using u256_mul_comm jugRay rate
  have hq : rate = UInt256.div (jugRay * rate) jugRay := by
    rw [hmulComm]
    exact (jugRay_mul_div_cancel rate hfitRmul).symm
  have hrmulReturn :
      ExecStmt config { contract := contract, locals := dripPowLocals I out fee jugRay } evmVat
        (.internalCall "_rmul" [.var "pow", .var "prev"] "rate")
        (.ok { contract := contract, locals := dripRateLocals I out fee jugRay rate } evmVat) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := dripPowLocals I out fee jugRay })
      (evm := evmVat) (name := "_rmul") (retVar := "rate")
      (args := [.var "pow", .var "prev"])
      (argVals := [.int (Int.ofNat jugRay.toNat), .int (Int.ofNat rate.toNat)])
      (callee := rmulFunction) (locals := uintBinaryLocals jugRay rate)
      hrmulArgs hlookupRmul hbindRmul
      (execRmulFunctionReturn evmVat (x := jugRay) (y := rate) (prod := jugRay * rate)
        (q := rate) rfl hfitRmul hq)
    simpa [resumeAfterInternalCall, dripRateLocals] using h
  have hdiffArgs :
      evalExprs? config { contract := contract, locals := dripRateLocals I out fee jugRay rate }
        evmVat [.var "rate", .var "prev"] =
          .ok [.int (Int.ofNat rate.toNat), .int (Int.ofNat rate.toNat)] := by
    simpa [rate] using evalExprs_dripDiffArgs evmVat I out fee jugRay rate
  have hlookupDiff : lookupCallable? contract "_diff" = some diffFunction.toCallable := by
    rfl
  have hbindDiff :
      bindParams? diffFunction.params [.int (Int.ofNat rate.toNat), .int (Int.ofNat rate.toNat)] =
        some (uintBinaryLocals rate rate) := by
    simp [diffFunction, uintBinaryLocals, bindParams?]
  have hdiffZero : (rate.toNat : Int) - (rate.toNat : Int) = 0 := by omega
  have hdiffLo :
      -((2 : Int) ^ 255) ≤ (rate.toNat : Int) - (rate.toNat : Int) := by
    rw [hdiffZero]
    norm_num
  have hdiffHi :
      (rate.toNat : Int) - (rate.toNat : Int) < (2 : Int) ^ 255 := by
    rw [hdiffZero]
    norm_num
  have hprevGt : maxInt256 < (rate.toNat : Int) := by
    exact lt_of_not_ge hprevMaxNot
  have hdiffRevert :
      ExecStmt config { contract := contract, locals := dripRateLocals I out fee jugRay rate }
        evmVat (.internalCall "_diff" [.var "rate", .var "prev"] "delta") .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := dripRateLocals I out fee jugRay rate })
      (evm := evmVat) (name := "_diff") (retVar := "delta")
      (args := [.var "rate", .var "prev"])
      (argVals := [.int (Int.ofNat rate.toNat), .int (Int.ofNat rate.toNat)])
      (callee := diffFunction) (locals := uintBinaryLocals rate rate)
      hdiffArgs hlookupDiff hbindDiff
      (execDiffFunctionRevertXBound evmVat (x := rate) (y := rate) hdiffLo hdiffHi hprevGt)
  have hprevStmt :
      ExecStmt config { contract := contract, locals := dripVatIlksLocals I out } evmVat
        (.letDecl "prev" (some uint256) (.tupleGet (.var "vatIlk") 1))
        (.ok { contract := contract, locals := dripVatIlksPrevLocals I out } evmVat) := by
    simpa [dripVatIlksPrevLocals, rate] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := dripVatIlksLocals I out })
        (evm := evmVat)
        (name := "prev")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatIlk") 1)
        (value := .int (Int.ofNat rate.toNat))
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

theorem jugDripSourceBodyVatIlksDiffYBoundRevertsXZeroNNonzero
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
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
    (hfee0 :
      jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv +
          jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv =
        ⟨0⟩)
    (hageNZ :
      UInt256.sub (UInt256.ofNat evmVat.executionEnv.header.timestamp)
          (jugSlotWord (fileDutyRhoSlotFor I) evmVat.accountMap evmVat.executionEnv) ≠
        ⟨0⟩)
    (hprevMaxNot : ¬ ((dripVatIlksPrevWord out).toNat : Int) ≤ maxInt256) :
    let locals := dripLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dripTransition.body .reverted := by
  intro locals evm0
  let base := jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv
  let duty := jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv
  let fee := base + duty
  let age :=
    UInt256.sub (UInt256.ofNat evmVat.executionEnv.header.timestamp)
      (jugSlotWord (fileDutyRhoSlotFor I) evmVat.accountMap evmVat.executionEnv)
  let prev := dripVatIlksPrevWord out
  have hfee0Local : fee = ⟨0⟩ := by
    simpa [fee, base, duty] using hfee0
  have hageNZLocal : age ≠ ⟨0⟩ := by
    simpa [age] using hageNZ
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
            .int (Int.ofNat jugRay.toNat)] := by
    exact evalExprs_dripRpowArgs evmVat I out fee age hsz36 (by rfl)
  have hlookupRpow : lookupCallable? contract "_rpow" = some rpowFunction.toCallable := by
    rfl
  have hbindRpow :
      bindParams? rpowFunction.params
          [.int (Int.ofNat fee.toNat), .int (Int.ofNat age.toNat),
            .int (Int.ofNat jugRay.toNat)] =
        some (uintTernaryLocals fee age jugRay) := by
    simp [rpowFunction, uintTernaryLocals, bindParams?]
  have hrpowBody :
      ExecFuncBody config { contract := contract, locals := uintTernaryLocals fee age jugRay }
        evmVat rpowFunction.body
        (.returned { contract := contract, locals := uintTernaryLocals fee age jugRay }
          evmVat (some [.int 0])) := by
    simpa [hfee0Local] using
      (execRpowFunctionReturnXZeroNNonzero (evm := evmVat) (n := age)
        (b := jugRay) hageNZLocal)
  have hrpowReturn :
      ExecStmt config { contract := contract, locals := dripFeeLocals I out fee } evmVat
        (.internalCall "_rpow"
          [ .var "fee",
            sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
            .intLit one ] "pow")
        (.ok { contract := contract, locals := dripPowLocals I out fee ⟨0⟩ } evmVat) := by
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
      (calleeSolm := { contract := contract, locals := uintTernaryLocals fee age jugRay })
      hrpowArgs hlookupRpow hbindRpow hrpowBody
    simpa [resumeAfterInternalCall, dripPowLocals] using h
  have hrmulArgs :
      evalExprs? config { contract := contract, locals := dripPowLocals I out fee ⟨0⟩ }
        evmVat [.var "pow", .var "prev"] =
        .ok [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)] := by
    simpa [prev] using evalExprs_dripRmulArgs evmVat I out fee (⟨0⟩ : UInt256)
  have hlookupRmul : lookupCallable? contract "_rmul" = some rmulFunction.toCallable := by
    rfl
  have hbindRmul :
      bindParams? rmulFunction.params
          [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)] =
        some (uintBinaryLocals ⟨0⟩ prev) := by
    simp [rmulFunction, uintBinaryLocals, bindParams?]
  have hzeroProd : (⟨0⟩ : UInt256) = (⟨0⟩ : UInt256) * prev := by
    apply u256_inj
    rw [u256_mul_op_toNat]
    simp
  have hfitRmul : (⟨0⟩ : UInt256).toNat * prev.toNat < UInt256.size := by
    norm_num [UInt256.size]
  have hq : (⟨0⟩ : UInt256) = UInt256.div (⟨0⟩ : UInt256) jugRay := by
    apply u256_inj
    simp [udiv_toNat]
  have hrmulReturn :
      ExecStmt config { contract := contract, locals := dripPowLocals I out fee ⟨0⟩ } evmVat
        (.internalCall "_rmul" [.var "pow", .var "prev"] "rate")
        (.ok { contract := contract, locals := dripRateLocals I out fee ⟨0⟩ ⟨0⟩ }
          evmVat) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := dripPowLocals I out fee ⟨0⟩ })
      (evm := evmVat) (name := "_rmul") (retVar := "rate")
      (args := [.var "pow", .var "prev"])
      (argVals := [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)])
      (callee := rmulFunction) (locals := uintBinaryLocals ⟨0⟩ prev)
      hrmulArgs hlookupRmul hbindRmul
      (execRmulFunctionReturn evmVat (x := ⟨0⟩) (y := prev) (prod := ⟨0⟩)
        (q := ⟨0⟩) hzeroProd hfitRmul hq)
    simpa [resumeAfterInternalCall, dripRateLocals] using h
  have hdiffArgs :
      evalExprs? config { contract := contract, locals := dripRateLocals I out fee ⟨0⟩ ⟨0⟩ }
        evmVat [.var "rate", .var "prev"] =
          .ok [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)] := by
    simpa [prev] using evalExprs_dripDiffArgs evmVat I out fee (⟨0⟩ : UInt256)
      (⟨0⟩ : UInt256)
  have hlookupDiff : lookupCallable? contract "_diff" = some diffFunction.toCallable := by
    rfl
  have hbindDiff :
      bindParams? diffFunction.params
          [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)] =
        some (uintBinaryLocals ⟨0⟩ prev) := by
    simp [diffFunction, uintBinaryLocals, bindParams?]
  have hzeroMax : (((⟨0⟩ : UInt256).toNat : Int) ≤ maxInt256) := by
    norm_num [maxInt256]
  have hprevGt : maxInt256 < (prev.toNat : Int) := by
    exact lt_of_not_ge (by simpa [prev] using hprevMaxNot)
  have hdiffRevert :
      ExecStmt config { contract := contract, locals := dripRateLocals I out fee ⟨0⟩ ⟨0⟩ }
        evmVat (.internalCall "_diff" [.var "rate", .var "prev"] "delta") .reverted := by
    by_cases hlo :
        -((2 : Int) ^ 255) ≤ ((⟨0⟩ : UInt256).toNat : Int) - (prev.toNat : Int)
    · have hhi :
          ((⟨0⟩ : UInt256).toNat : Int) - (prev.toNat : Int) < (2 : Int) ^ 255 := by
        have hprevNonneg : 0 ≤ (prev.toNat : Int) := Int.natCast_nonneg _
        norm_num
        omega
      exact internalCallFunctionRevert
        (cfg := config)
        (caller := { contract := contract, locals := dripRateLocals I out fee ⟨0⟩ ⟨0⟩ })
        (evm := evmVat) (name := "_diff") (retVar := "delta")
        (args := [.var "rate", .var "prev"])
        (argVals :=
          [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)])
        (callee := diffFunction) (locals := uintBinaryLocals ⟨0⟩ prev)
        hdiffArgs hlookupDiff hbindDiff
        (execDiffFunctionRevertYBound evmVat (x := ⟨0⟩) (y := prev)
          hlo hhi hzeroMax hprevGt)
    · have hbad :
          ((⟨0⟩ : UInt256).toNat : Int) - (prev.toNat : Int) <
              -((2 : Int) ^ 255) ∨
            ((⟨0⟩ : UInt256).toNat : Int) - (prev.toNat : Int) ≥ (2 : Int) ^ 255 := by
        left
        omega
      exact internalCallFunctionRevert
        (cfg := config)
        (caller := { contract := contract, locals := dripRateLocals I out fee ⟨0⟩ ⟨0⟩ })
        (evm := evmVat) (name := "_diff") (retVar := "delta")
        (args := [.var "rate", .var "prev"])
        (argVals :=
          [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)])
        (callee := diffFunction) (locals := uintBinaryLocals ⟨0⟩ prev)
        hdiffArgs hlookupDiff hbindDiff
        (execDiffFunctionRevertCast evmVat (x := ⟨0⟩) (y := prev) hbad)
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

theorem jugDripSourceBodyVatFoldNoCodeRevertsXZeroNNonzero
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
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
    (hfee0 :
      jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv +
          jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv =
        ⟨0⟩)
    (hageNZ :
      UInt256.sub (UInt256.ofNat evmVat.executionEnv.header.timestamp)
          (jugSlotWord (fileDutyRhoSlotFor I) evmVat.accountMap evmVat.executionEnv) ≠
        ⟨0⟩)
    (hprevMax : ((dripVatIlksPrevWord out).toNat : Int) ≤ maxInt256)
    (hfoldNoCode :
      (UInt256.ofNat
        ((evmVat.lookupAccount (dripVatAddress evmVat.accountMap evmVat.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    let locals := dripLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dripTransition.body .reverted := by
  intro locals evm0
  let base := jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv
  let duty := jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv
  let fee := base + duty
  let age :=
    UInt256.sub (UInt256.ofNat evmVat.executionEnv.header.timestamp)
      (jugSlotWord (fileDutyRhoSlotFor I) evmVat.accountMap evmVat.executionEnv)
  let prev := dripVatIlksPrevWord out
  let delta : Int := ((⟨0⟩ : UInt256).toNat : Int) - (prev.toNat : Int)
  have hfee0Local : fee = ⟨0⟩ := by
    simpa [fee, base, duty] using hfee0
  have hageNZLocal : age ≠ ⟨0⟩ := by
    simpa [age] using hageNZ
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
            .int (Int.ofNat jugRay.toNat)] := by
    exact evalExprs_dripRpowArgs evmVat I out fee age hsz36 (by rfl)
  have hlookupRpow : lookupCallable? contract "_rpow" = some rpowFunction.toCallable := by
    rfl
  have hbindRpow :
      bindParams? rpowFunction.params
          [.int (Int.ofNat fee.toNat), .int (Int.ofNat age.toNat),
            .int (Int.ofNat jugRay.toNat)] =
        some (uintTernaryLocals fee age jugRay) := by
    simp [rpowFunction, uintTernaryLocals, bindParams?]
  have hrpowBody :
      ExecFuncBody config { contract := contract, locals := uintTernaryLocals fee age jugRay }
        evmVat rpowFunction.body
        (.returned { contract := contract, locals := uintTernaryLocals fee age jugRay }
          evmVat (some [.int 0])) := by
    simpa [hfee0Local] using
      (execRpowFunctionReturnXZeroNNonzero (evm := evmVat) (n := age)
        (b := jugRay) hageNZLocal)
  have hrpowReturn :
      ExecStmt config { contract := contract, locals := dripFeeLocals I out fee } evmVat
        (.internalCall "_rpow"
          [ .var "fee",
            sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
            .intLit one ] "pow")
        (.ok { contract := contract, locals := dripPowLocals I out fee ⟨0⟩ } evmVat) := by
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
      (calleeSolm := { contract := contract, locals := uintTernaryLocals fee age jugRay })
      hrpowArgs hlookupRpow hbindRpow hrpowBody
    simpa [resumeAfterInternalCall, dripPowLocals] using h
  have hrmulArgs :
      evalExprs? config { contract := contract, locals := dripPowLocals I out fee ⟨0⟩ }
        evmVat [.var "pow", .var "prev"] =
        .ok [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)] := by
    simpa [prev] using evalExprs_dripRmulArgs evmVat I out fee (⟨0⟩ : UInt256)
  have hlookupRmul : lookupCallable? contract "_rmul" = some rmulFunction.toCallable := by
    rfl
  have hbindRmul :
      bindParams? rmulFunction.params
          [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)] =
        some (uintBinaryLocals ⟨0⟩ prev) := by
    simp [rmulFunction, uintBinaryLocals, bindParams?]
  have hzeroProd : (⟨0⟩ : UInt256) = (⟨0⟩ : UInt256) * prev := by
    apply u256_inj
    rw [u256_mul_op_toNat]
    simp
  have hfitRmul : (⟨0⟩ : UInt256).toNat * prev.toNat < UInt256.size := by
    norm_num [UInt256.size]
  have hq : (⟨0⟩ : UInt256) = UInt256.div (⟨0⟩ : UInt256) jugRay := by
    apply u256_inj
    simp [udiv_toNat]
  have hrmulReturn :
      ExecStmt config { contract := contract, locals := dripPowLocals I out fee ⟨0⟩ } evmVat
        (.internalCall "_rmul" [.var "pow", .var "prev"] "rate")
        (.ok { contract := contract, locals := dripRateLocals I out fee ⟨0⟩ ⟨0⟩ }
          evmVat) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := dripPowLocals I out fee ⟨0⟩ })
      (evm := evmVat) (name := "_rmul") (retVar := "rate")
      (args := [.var "pow", .var "prev"])
      (argVals := [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)])
      (callee := rmulFunction) (locals := uintBinaryLocals ⟨0⟩ prev)
      hrmulArgs hlookupRmul hbindRmul
      (execRmulFunctionReturn evmVat (x := ⟨0⟩) (y := prev) (prod := ⟨0⟩)
        (q := ⟨0⟩) hzeroProd hfitRmul hq)
    simpa [resumeAfterInternalCall, dripRateLocals] using h
  have hdiffArgs :
      evalExprs? config { contract := contract, locals := dripRateLocals I out fee ⟨0⟩ ⟨0⟩ }
        evmVat [.var "rate", .var "prev"] =
          .ok [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)] := by
    simpa [prev] using evalExprs_dripDiffArgs evmVat I out fee (⟨0⟩ : UInt256)
      (⟨0⟩ : UInt256)
  have hlookupDiff : lookupCallable? contract "_diff" = some diffFunction.toCallable := by
    rfl
  have hbindDiff :
      bindParams? diffFunction.params
          [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)] =
        some (uintBinaryLocals ⟨0⟩ prev) := by
    simp [diffFunction, uintBinaryLocals, bindParams?]
  have hzeroMax : (((⟨0⟩ : UInt256).toNat : Int) ≤ maxInt256) := by
    norm_num [maxInt256]
  have hdiffReturn :
      ExecStmt config { contract := contract, locals := dripRateLocals I out fee ⟨0⟩ ⟨0⟩ }
        evmVat (.internalCall "_diff" [.var "rate", .var "prev"] "delta")
        (.ok { contract := contract, locals := dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta }
          evmVat) := by
    have h := internalCallFunctionReturn
      (cfg := config)
      (caller := { contract := contract, locals := dripRateLocals I out fee ⟨0⟩ ⟨0⟩ })
      (evm := evmVat) (name := "_diff") (retVar := "delta")
      (args := [.var "rate", .var "prev"])
      (argVals := [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)])
      (callee := diffFunction) (locals := uintBinaryLocals ⟨0⟩ prev)
      hdiffArgs hlookupDiff hbindDiff
      (execDiffFunctionReturn evmVat (x := ⟨0⟩) (y := prev) hzeroMax hprevMax)
    simpa [resumeAfterInternalCall, dripDeltaLocalsInt, delta] using h
  have hvatFold :
      evalExpr? config
          { contract := contract, locals := dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta }
          evmVat (.storage vatRef) =
        .ok (.address (dripVatAddress evmVat.accountMap evmVat.executionEnv)) := by
    exact evalExpr_dripStorageVatOfLocals
      (evm := evmVat) (locals := dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta)
      (dripDeltaLocalsInt_get_vat I out fee ⟨0⟩ ⟨0⟩ delta)
  have hfoldGuard :
      evalExpr? config
          { contract := contract, locals := dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta }
          evmVat (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool false) :=
    evalExpr_dripVatCodeGuard_false_ofLocals hvatFold hfoldNoCode
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
    refine ExecBlock.consNormal (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, dripFeeLocals, dripPowLocals,
        dripRateLocals, collapseReturns] using hdiffReturn) ?_
    exact ExecBlock.consRevert (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, dripFeeLocals, dripPowLocals,
        dripRateLocals, dripDeltaLocalsInt, collapseReturns] using
        (ExecStmt.requireFalse hfoldGuard))
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem jugDripSourceBodyVatFoldCallFailedRevertsXZeroNNonzero
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat evmFold : EVM.State} {out foldOut : ByteArray}
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
    (hfee0 :
      jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv +
          jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv =
        ⟨0⟩)
    (hageNZ :
      UInt256.sub (UInt256.ofNat evmVat.executionEnv.header.timestamp)
          (jugSlotWord (fileDutyRhoSlotFor I) evmVat.accountMap evmVat.executionEnv) ≠
        ⟨0⟩)
    (hprevMax : ((dripVatIlksPrevWord out).toNat : Int) ≤ maxInt256)
    (hfoldCode :
      0 <
        (UInt256.ofNat
          ((evmVat.lookupAccount (dripVatAddress evmVat.accountMap evmVat.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat)
    (hfoldCall :
      typedCallViaEVM config evmVat
        (EVM.address (dripVatAddress evmVat.accountMap evmVat.executionEnv)) "fold" 0
        [.fixedBytes bytes32Width (fileDutyIlkBytes I),
          .address (AccountAddress.ofUInt256
            (dripVowTargetWord evmVat.accountMap evmVat.executionEnv)),
          .int (((⟨0⟩ : UInt256).toNat : Int) - ((dripVatIlksPrevWord out).toNat : Int))]
        (false, evmFold, foldOut) true) :
    let locals := dripLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dripTransition.body .reverted := by
  intro locals evm0
  let base := jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv
  let duty := jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv
  let fee := base + duty
  let age :=
    UInt256.sub (UInt256.ofNat evmVat.executionEnv.header.timestamp)
      (jugSlotWord (fileDutyRhoSlotFor I) evmVat.accountMap evmVat.executionEnv)
  let prev := dripVatIlksPrevWord out
  let delta : Int := ((⟨0⟩ : UInt256).toNat : Int) - (prev.toNat : Int)
  have hfee0Local : fee = ⟨0⟩ := by
    simpa [fee, base, duty] using hfee0
  have hageNZLocal : age ≠ ⟨0⟩ := by
    simpa [age] using hageNZ
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
            .int (Int.ofNat jugRay.toNat)] := by
    exact evalExprs_dripRpowArgs evmVat I out fee age hsz36 (by rfl)
  have hlookupRpow : lookupCallable? contract "_rpow" = some rpowFunction.toCallable := by
    rfl
  have hbindRpow :
      bindParams? rpowFunction.params
          [.int (Int.ofNat fee.toNat), .int (Int.ofNat age.toNat),
            .int (Int.ofNat jugRay.toNat)] =
        some (uintTernaryLocals fee age jugRay) := by
    simp [rpowFunction, uintTernaryLocals, bindParams?]
  have hrpowBody :
      ExecFuncBody config { contract := contract, locals := uintTernaryLocals fee age jugRay }
        evmVat rpowFunction.body
        (.returned { contract := contract, locals := uintTernaryLocals fee age jugRay }
          evmVat (some [.int 0])) := by
    simpa [hfee0Local] using
      (execRpowFunctionReturnXZeroNNonzero (evm := evmVat) (n := age)
        (b := jugRay) hageNZLocal)
  have hrpowReturn :
      ExecStmt config { contract := contract, locals := dripFeeLocals I out fee } evmVat
        (.internalCall "_rpow"
          [ .var "fee",
            sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
            .intLit one ] "pow")
        (.ok { contract := contract, locals := dripPowLocals I out fee ⟨0⟩ } evmVat) := by
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
      (calleeSolm := { contract := contract, locals := uintTernaryLocals fee age jugRay })
      hrpowArgs hlookupRpow hbindRpow hrpowBody
    simpa [resumeAfterInternalCall, dripPowLocals] using h
  have hrmulArgs :
      evalExprs? config { contract := contract, locals := dripPowLocals I out fee ⟨0⟩ }
        evmVat [.var "pow", .var "prev"] =
        .ok [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)] := by
    simpa [prev] using evalExprs_dripRmulArgs evmVat I out fee (⟨0⟩ : UInt256)
  have hlookupRmul : lookupCallable? contract "_rmul" = some rmulFunction.toCallable := by
    rfl
  have hbindRmul :
      bindParams? rmulFunction.params
          [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)] =
        some (uintBinaryLocals ⟨0⟩ prev) := by
    simp [rmulFunction, uintBinaryLocals, bindParams?]
  have hzeroProd : (⟨0⟩ : UInt256) = (⟨0⟩ : UInt256) * prev := by
    apply u256_inj
    rw [u256_mul_op_toNat]
    simp
  have hfitRmul : (⟨0⟩ : UInt256).toNat * prev.toNat < UInt256.size := by
    norm_num [UInt256.size]
  have hq : (⟨0⟩ : UInt256) = UInt256.div (⟨0⟩ : UInt256) jugRay := by
    apply u256_inj
    simp [udiv_toNat]
  have hrmulReturn :
      ExecStmt config { contract := contract, locals := dripPowLocals I out fee ⟨0⟩ } evmVat
        (.internalCall "_rmul" [.var "pow", .var "prev"] "rate")
        (.ok { contract := contract, locals := dripRateLocals I out fee ⟨0⟩ ⟨0⟩ }
          evmVat) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := dripPowLocals I out fee ⟨0⟩ })
      (evm := evmVat) (name := "_rmul") (retVar := "rate")
      (args := [.var "pow", .var "prev"])
      (argVals := [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)])
      (callee := rmulFunction) (locals := uintBinaryLocals ⟨0⟩ prev)
      hrmulArgs hlookupRmul hbindRmul
      (execRmulFunctionReturn evmVat (x := ⟨0⟩) (y := prev) (prod := ⟨0⟩)
        (q := ⟨0⟩) hzeroProd hfitRmul hq)
    simpa [resumeAfterInternalCall, dripRateLocals] using h
  have hdiffArgs :
      evalExprs? config { contract := contract, locals := dripRateLocals I out fee ⟨0⟩ ⟨0⟩ }
        evmVat [.var "rate", .var "prev"] =
          .ok [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)] := by
    simpa [prev] using evalExprs_dripDiffArgs evmVat I out fee (⟨0⟩ : UInt256)
      (⟨0⟩ : UInt256)
  have hlookupDiff : lookupCallable? contract "_diff" = some diffFunction.toCallable := by
    rfl
  have hbindDiff :
      bindParams? diffFunction.params
          [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)] =
        some (uintBinaryLocals ⟨0⟩ prev) := by
    simp [diffFunction, uintBinaryLocals, bindParams?]
  have hzeroMax : (((⟨0⟩ : UInt256).toNat : Int) ≤ maxInt256) := by
    norm_num [maxInt256]
  have hdiffReturn :
      ExecStmt config { contract := contract, locals := dripRateLocals I out fee ⟨0⟩ ⟨0⟩ }
        evmVat (.internalCall "_diff" [.var "rate", .var "prev"] "delta")
        (.ok { contract := contract, locals := dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta }
          evmVat) := by
    have h := internalCallFunctionReturn
      (cfg := config)
      (caller := { contract := contract, locals := dripRateLocals I out fee ⟨0⟩ ⟨0⟩ })
      (evm := evmVat) (name := "_diff") (retVar := "delta")
      (args := [.var "rate", .var "prev"])
      (argVals := [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)])
      (callee := diffFunction) (locals := uintBinaryLocals ⟨0⟩ prev)
      hdiffArgs hlookupDiff hbindDiff
      (execDiffFunctionReturn evmVat (x := ⟨0⟩) (y := prev) hzeroMax hprevMax)
    simpa [resumeAfterInternalCall, dripDeltaLocalsInt, delta] using h
  have hvatFold :
      evalExpr? config
          { contract := contract, locals := dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta }
          evmVat (.storage vatRef) =
        .ok (.address (dripVatAddress evmVat.accountMap evmVat.executionEnv)) := by
    exact evalExpr_dripStorageVatOfLocals
      (evm := evmVat) (locals := dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta)
      (dripDeltaLocalsInt_get_vat I out fee ⟨0⟩ ⟨0⟩ delta)
  have hfoldGuard :
      evalExpr? config
          { contract := contract, locals := dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta }
          evmVat (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) :=
    evalExpr_dripVatCodeGuard_true_ofLocals hvatFold hfoldCode
  have hfoldArgs :
      evalExprs? config
          { contract := contract, locals := dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta }
          evmVat [.var "ilk", .storage vowRef, .var "delta"] =
        .ok [.fixedBytes bytes32Width (fileDutyIlkBytes I),
          .address (AccountAddress.ofUInt256
            (dripVowTargetWord evmVat.accountMap evmVat.executionEnv)),
          .int delta] :=
    evalExprs_dripVatFoldArgsInt evmVat I out fee ⟨0⟩ ⟨0⟩ delta
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
    refine ExecBlock.consNormal (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, dripFeeLocals, dripPowLocals,
        dripRateLocals, collapseReturns] using hdiffReturn) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hfoldGuard) ?_
    exact ExecBlock.consRevert
      (ExecStmt.externalCallFailure (sendVal := 0) hvatFold
        (by simp [evalExpr?, pure]) hfoldArgs (by simpa [delta] using hfoldCall))
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem jugDripSourceBodyVatFoldCallSucceededReturnsXZeroNNonzero
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat evmFold : EVM.State} {out foldOut : ByteArray}
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
    (hfee0 :
      jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv +
          jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv =
        ⟨0⟩)
    (hageNZ :
      UInt256.sub (UInt256.ofNat evmVat.executionEnv.header.timestamp)
          (jugSlotWord (fileDutyRhoSlotFor I) evmVat.accountMap evmVat.executionEnv) ≠
        ⟨0⟩)
    (hprevMax : ((dripVatIlksPrevWord out).toNat : Int) ≤ maxInt256)
    (hfoldCode :
      0 <
        (UInt256.ofNat
          ((evmVat.lookupAccount (dripVatAddress evmVat.accountMap evmVat.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat)
    (hfoldCall :
      typedCallViaEVM config evmVat
        (EVM.address (dripVatAddress evmVat.accountMap evmVat.executionEnv)) "fold" 0
        [.fixedBytes bytes32Width (fileDutyIlkBytes I),
          .address (AccountAddress.ofUInt256
            (dripVowTargetWord evmVat.accountMap evmVat.executionEnv)),
          .int (((⟨0⟩ : UInt256).toNat : Int) - ((dripVatIlksPrevWord out).toNat : Int))]
        (true, evmFold, foldOut) true) :
    let locals := dripLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let base := jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv
    let duty := jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap evmVat.executionEnv
    let fee := base + duty
    let rate : UInt256 := ⟨0⟩
    let delta : Int := ((⟨0⟩ : UInt256).toNat : Int) - ((dripVatIlksPrevWord out).toNat : Int)
    let foldLocals := (dripDeltaLocalsInt I out fee ⟨0⟩ rate delta).insert "_foldRet" .unit
    let timestamp := UInt256.ofNat evmFold.executionEnv.header.timestamp
    let evmRho := Solm.EVM.storageStore evmFold evmFold.executionEnv.codeOwner
      (fileDutyRhoSlotFor I) timestamp
    ExecTransitionBody config contract evm0 locals dripTransition.body
      (.returned { contract := contract, locals := foldLocals } evmRho
        (some [.int (Int.ofNat rate.toNat)])) := by
  intro locals evm0 base duty fee rate delta foldLocals timestamp evmRho
  let age :=
    UInt256.sub (UInt256.ofNat evmVat.executionEnv.header.timestamp)
      (jugSlotWord (fileDutyRhoSlotFor I) evmVat.accountMap evmVat.executionEnv)
  let prev := dripVatIlksPrevWord out
  have hfee0Local : fee = ⟨0⟩ := by
    simpa [fee, base, duty] using hfee0
  have hageNZLocal : age ≠ ⟨0⟩ := by
    simpa [age] using hageNZ
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
            .int (Int.ofNat jugRay.toNat)] := by
    exact evalExprs_dripRpowArgs evmVat I out fee age hsz36 (by rfl)
  have hlookupRpow : lookupCallable? contract "_rpow" = some rpowFunction.toCallable := by
    rfl
  have hbindRpow :
      bindParams? rpowFunction.params
          [.int (Int.ofNat fee.toNat), .int (Int.ofNat age.toNat),
            .int (Int.ofNat jugRay.toNat)] =
        some (uintTernaryLocals fee age jugRay) := by
    simp [rpowFunction, uintTernaryLocals, bindParams?]
  have hrpowBody :
      ExecFuncBody config { contract := contract, locals := uintTernaryLocals fee age jugRay }
        evmVat rpowFunction.body
        (.returned { contract := contract, locals := uintTernaryLocals fee age jugRay }
          evmVat (some [.int 0])) := by
    simpa [hfee0Local] using
      (execRpowFunctionReturnXZeroNNonzero (evm := evmVat) (n := age)
        (b := jugRay) hageNZLocal)
  have hrpowReturn :
      ExecStmt config { contract := contract, locals := dripFeeLocals I out fee } evmVat
        (.internalCall "_rpow"
          [ .var "fee",
            sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
            .intLit one ] "pow")
        (.ok { contract := contract, locals := dripPowLocals I out fee ⟨0⟩ } evmVat) := by
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
      (calleeSolm := { contract := contract, locals := uintTernaryLocals fee age jugRay })
      hrpowArgs hlookupRpow hbindRpow hrpowBody
    simpa [resumeAfterInternalCall, dripPowLocals] using h
  have hrmulArgs :
      evalExprs? config { contract := contract, locals := dripPowLocals I out fee ⟨0⟩ }
        evmVat [.var "pow", .var "prev"] =
        .ok [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)] := by
    simpa [prev] using evalExprs_dripRmulArgs evmVat I out fee (⟨0⟩ : UInt256)
  have hlookupRmul : lookupCallable? contract "_rmul" = some rmulFunction.toCallable := by
    rfl
  have hbindRmul :
      bindParams? rmulFunction.params
          [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)] =
        some (uintBinaryLocals ⟨0⟩ prev) := by
    simp [rmulFunction, uintBinaryLocals, bindParams?]
  have hzeroProd : (⟨0⟩ : UInt256) = (⟨0⟩ : UInt256) * prev := by
    apply u256_inj
    rw [u256_mul_op_toNat]
    simp
  have hfitRmul : (⟨0⟩ : UInt256).toNat * prev.toNat < UInt256.size := by
    norm_num [UInt256.size]
  have hq : (⟨0⟩ : UInt256) = UInt256.div (⟨0⟩ : UInt256) jugRay := by
    apply u256_inj
    simp [udiv_toNat]
  have hrmulReturn :
      ExecStmt config { contract := contract, locals := dripPowLocals I out fee ⟨0⟩ } evmVat
        (.internalCall "_rmul" [.var "pow", .var "prev"] "rate")
        (.ok { contract := contract, locals := dripRateLocals I out fee ⟨0⟩ ⟨0⟩ }
          evmVat) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := dripPowLocals I out fee ⟨0⟩ })
      (evm := evmVat) (name := "_rmul") (retVar := "rate")
      (args := [.var "pow", .var "prev"])
      (argVals := [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)])
      (callee := rmulFunction) (locals := uintBinaryLocals ⟨0⟩ prev)
      hrmulArgs hlookupRmul hbindRmul
      (execRmulFunctionReturn evmVat (x := ⟨0⟩) (y := prev) (prod := ⟨0⟩)
        (q := ⟨0⟩) hzeroProd hfitRmul hq)
    simpa [resumeAfterInternalCall, dripRateLocals] using h
  have hdiffArgs :
      evalExprs? config { contract := contract, locals := dripRateLocals I out fee ⟨0⟩ ⟨0⟩ }
        evmVat [.var "rate", .var "prev"] =
          .ok [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)] := by
    simpa [prev] using evalExprs_dripDiffArgs evmVat I out fee (⟨0⟩ : UInt256)
      (⟨0⟩ : UInt256)
  have hlookupDiff : lookupCallable? contract "_diff" = some diffFunction.toCallable := by
    rfl
  have hbindDiff :
      bindParams? diffFunction.params
          [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)] =
        some (uintBinaryLocals ⟨0⟩ prev) := by
    simp [diffFunction, uintBinaryLocals, bindParams?]
  have hzeroMax : (((⟨0⟩ : UInt256).toNat : Int) ≤ maxInt256) := by
    norm_num [maxInt256]
  have hdiffReturn :
      ExecStmt config { contract := contract, locals := dripRateLocals I out fee ⟨0⟩ ⟨0⟩ }
        evmVat (.internalCall "_diff" [.var "rate", .var "prev"] "delta")
        (.ok { contract := contract, locals := dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta }
          evmVat) := by
    have h := internalCallFunctionReturn
      (cfg := config)
      (caller := { contract := contract, locals := dripRateLocals I out fee ⟨0⟩ ⟨0⟩ })
      (evm := evmVat) (name := "_diff") (retVar := "delta")
      (args := [.var "rate", .var "prev"])
      (argVals := [.int (Int.ofNat (⟨0⟩ : UInt256).toNat), .int (Int.ofNat prev.toNat)])
      (callee := diffFunction) (locals := uintBinaryLocals ⟨0⟩ prev)
      hdiffArgs hlookupDiff hbindDiff
      (execDiffFunctionReturn evmVat (x := ⟨0⟩) (y := prev) hzeroMax hprevMax)
    simpa [resumeAfterInternalCall, dripDeltaLocalsInt, delta] using h
  have hvatFold :
      evalExpr? config
          { contract := contract, locals := dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta }
          evmVat (.storage vatRef) =
        .ok (.address (dripVatAddress evmVat.accountMap evmVat.executionEnv)) := by
    exact evalExpr_dripStorageVatOfLocals
      (evm := evmVat) (locals := dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta)
      (dripDeltaLocalsInt_get_vat I out fee ⟨0⟩ ⟨0⟩ delta)
  have hfoldGuard :
      evalExpr? config
          { contract := contract, locals := dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta }
          evmVat (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) :=
    evalExpr_dripVatCodeGuard_true_ofLocals hvatFold hfoldCode
  have hfoldArgs :
      evalExprs? config
          { contract := contract, locals := dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta }
          evmVat [.var "ilk", .storage vowRef, .var "delta"] =
        .ok [.fixedBytes bytes32Width (fileDutyIlkBytes I),
          .address (AccountAddress.ofUInt256
            (dripVowTargetWord evmVat.accountMap evmVat.executionEnv)),
          .int delta] :=
    evalExprs_dripVatFoldArgsInt evmVat I out fee ⟨0⟩ ⟨0⟩ delta
  have hfoldDecode : config.externalABI.decode? "fold" foldOut = some [] := by
    simp [config, jugExternalABI]
  have hfoldReturn :
      ExecStmt config
          { contract := contract, locals := dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta }
          evmVat
          (.externalCall (.storage vatRef) "fold" (.intLit 0)
            [.var "ilk", .storage vowRef, .var "delta"] "_foldRet" (perm := true))
          (.ok { contract := contract, locals := foldLocals } evmFold) := by
    have h := ExecStmt.externalCallSuccess (cfg := config)
      (solm :=
        { contract := contract, locals := dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta })
      (evm := evmVat) (receiver := .storage vatRef) (name := "fold") (eth := .intLit 0)
      (args := [.var "ilk", .storage vowRef, .var "delta"]) (retVar := "_foldRet")
      (perm := true) (target := dripVatAddress evmVat.accountMap evmVat.executionEnv)
      (sendVal := 0)
      (argVals :=
        [.fixedBytes bytes32Width (fileDutyIlkBytes I),
          .address (AccountAddress.ofUInt256
            (dripVowTargetWord evmVat.accountMap evmVat.executionEnv)),
          .int delta])
      (evm' := evmFold) (out := foldOut) (value := [])
      hvatFold (by simp [evalExpr?, pure]) hfoldArgs
      (by simpa [delta] using hfoldCall) hfoldDecode
    simpa [foldLocals, collapseReturns] using h
  have hfoldLocalsIlks : foldLocals.get? "ilks" = none := by
    dsimp [foldLocals]
    change ((dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta).insert "_foldRet" .unit).get?
        "ilks" = none
    rw [store_get_ne (dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta)
      (k := "_foldRet") (a := "ilks") .unit (by decide)]
    exact dripDeltaLocalsInt_get_ilks I out fee ⟨0⟩ ⟨0⟩ delta
  have hfoldLocalsIlk :
      foldLocals.get? "ilk" = some (.fixedBytes bytes32Width (fileDutyIlkBytes I)) := by
    dsimp [foldLocals]
    change ((dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta).insert "_foldRet" .unit).get?
        "ilk" = some (.fixedBytes bytes32Width (fileDutyIlkBytes I))
    rw [store_get_ne (dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta)
      (k := "_foldRet") (a := "ilk") .unit (by decide)]
    exact dripDeltaLocalsInt_get_ilk I out fee ⟨0⟩ ⟨0⟩ delta
  have hfoldLocalsRate :
      foldLocals.get? "rate" = some (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    dsimp [foldLocals]
    change ((dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta).insert "_foldRet" .unit).get?
        "rate" = some (.int (Int.ofNat (⟨0⟩ : UInt256).toNat))
    rw [store_get_ne (dripDeltaLocalsInt I out fee ⟨0⟩ ⟨0⟩ delta)
      (k := "_foldRet") (a := "rate") .unit (by decide)]
    exact dripDeltaLocalsInt_get_rate I out fee ⟨0⟩ ⟨0⟩ delta
  have htimestamp :
      evalExpr? config { contract := contract, locals := foldLocals } evmFold (.env .timestamp) =
        .ok (.int (Int.ofNat timestamp.toNat)) := by
    simp [evalExpr?, envValue, timestamp, pure]
  have hassignRho :
      ExecStmt config { contract := contract, locals := foldLocals } evmFold
        (.assign .storage (ilksF (.var "ilk") "rho") (.env .timestamp))
        (.ok { contract := contract, locals := foldLocals } evmRho) := by
    exact ExecStmt.assign htimestamp
      (by
        simpa [timestamp, evmRho] using
          (assign_dripRhoStorageOfLocals (evm := evmFold) (I := I)
            (locals := foldLocals) hsz36 hfoldLocalsIlks hfoldLocalsIlk))
  have hrate :
      evalExpr? config { contract := contract, locals := foldLocals } evmRho (.var "rate") =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    exact evalExpr_varUInt256 (evm := evmRho) (locals := foldLocals) (name := "rate")
      (value := (⟨0⟩ : UInt256)) hfoldLocalsRate
  have hreturn :
      evalExprs? config { contract := contract, locals := foldLocals } evmRho [.var "rate"] =
        .ok [.int (Int.ofNat (⟨0⟩ : UInt256).toNat)] := by
    simp [evalExprs?, hrate, EvalResult.bind, bind, pure]
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
        (.returned { contract := contract, locals := foldLocals } evmRho
          (some [.int (Int.ofNat (⟨0⟩ : UInt256).toNat)])) := by
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
    refine ExecBlock.consNormal (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, dripFeeLocals, dripPowLocals,
        dripRateLocals, collapseReturns] using hdiffReturn) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hfoldGuard) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, dripVatIlksLocals, dripVatIlksPrevLocals, dripFeeLocals, dripPowLocals,
        dripRateLocals, dripDeltaLocalsInt, foldLocals, collapseReturns] using hfoldReturn) ?_
    refine ExecBlock.consNormal hassignRho ?_
    exact ExecBlock.consReturn (ExecStmt.return hreturn)
  simpa [ExecTransitionBody, locals, evm0, base, duty, fee, rate, delta, foldLocals, timestamp,
    evmRho] using ExecFuncBody.execBlockRet hblock

end Benchmarks.Dss.Jug
