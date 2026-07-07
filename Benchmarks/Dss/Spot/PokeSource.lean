import Benchmarks.Dss.Spot.PokeCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Spot

theorem spotPokeSourceBodyPipNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hpipNoCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (pokePipAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0) :
    let locals := pokeLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals pokeTransition.body .reverted := by
  intro locals evm0
  have hpip :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.storage (ilksF (.var "ilk") "pip")) =
        .ok (.address (pokePipAddress evm0.accountMap I)) := by
    simpa [locals, evm0, initState] using
      (evalExpr_pokeStoragePip (evm := evm0) (I := I) hsz36 (by simp [evm0, initState]))
  have hpipNoCode0 :
      (UInt256.ofNat
        ((evm0.lookupAccount (pokePipAddress evm0.accountMap I)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    simpa [evm0, initState] using hpipNoCode
  have hpipGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage (ilksF (.var "ilk") "pip"))) (.intLit 0)) =
          .ok (.bool false) := by
    exact evalExpr_pokePipCodeGuard_false hsz36 hpip hpipNoCode0
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 pokeTransition.body
        .reverted := by
    simp only [pokeTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    exact ExecBlock.consRevert (ExecStmt.requireFalse hpipGuard)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem spotPokeSourceBodyPeekCallFailed {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmPip : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hpipCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (pokePipAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      typedCallViaEVM config evm0 (EVM.address (pokePipAddress σ I)) "peek" 0 []
        (false, evmPip, out) true) :
    let locals := pokeLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals pokeTransition.body .reverted := by
  intro locals evm0
  have hpip :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.storage (ilksF (.var "ilk") "pip")) =
        .ok (.address (pokePipAddress evm0.accountMap I)) := by
    simpa [locals, evm0, initState] using
      (evalExpr_pokeStoragePip (evm := evm0) (I := I) hsz36 (by simp [evm0, initState]))
  have hpipCode0 :
      0 <
        (UInt256.ofNat
          ((evm0.lookupAccount (pokePipAddress evm0.accountMap I)).option 0
            (fun acc => acc.code.size))).toNat := by
    simpa [evm0, initState] using hpipCode
  have hpipGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage (ilksF (.var "ilk") "pip"))) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_pokePipCodeGuard_true hsz36 hpip hpipCode0
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [] = .ok [] := by
    simpa [locals] using evalExprs_pokePeekArgs evm0 I
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 pokeTransition.body
        .reverted := by
    simp only [pokeTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hpipGuard) ?_
    exact ExecBlock.consRevert
      (ExecStmt.externalCallFailure (sendVal := 0) hpip (by simp [evalExpr?, pure]) hargs
        (by simpa [evm0] using hcall))
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem spotPokeSourceBodyPeekReturnDecodeReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmPip : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hpipCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (pokePipAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      typedCallViaEVM config evm0 (EVM.address (pokePipAddress σ I)) "peek" 0 []
        (true, evmPip, out) true)
    (hdec : config.externalABI.decode? "peek" out = none) :
    let locals := pokeLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals pokeTransition.body .reverted := by
  intro locals evm0
  have hpip :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.storage (ilksF (.var "ilk") "pip")) =
        .ok (.address (pokePipAddress evm0.accountMap I)) := by
    simpa [locals, evm0, initState] using
      (evalExpr_pokeStoragePip (evm := evm0) (I := I) hsz36 (by simp [evm0, initState]))
  have hpipCode0 :
      0 <
        (UInt256.ofNat
          ((evm0.lookupAccount (pokePipAddress evm0.accountMap I)).option 0
            (fun acc => acc.code.size))).toNat := by
    simpa [evm0, initState] using hpipCode
  have hpipGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage (ilksF (.var "ilk") "pip"))) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_pokePipCodeGuard_true hsz36 hpip hpipCode0
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [] = .ok [] := by
    simpa [locals] using evalExprs_pokePeekArgs evm0 I
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 pokeTransition.body
        .reverted := by
    simp only [pokeTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hpipGuard) ?_
    exact ExecBlock.consRevert
        (ExecStmt.externalCallReturnDecodeRevert (sendVal := 0) hpip
          (by simp [evalExpr?, pure]) hargs (by simpa [evm0] using hcall) hdec)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem spotPokeSourceBodyPeekHasFalseVatNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmPip : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hpipCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (pokePipAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      typedCallViaEVM config evm0 (EVM.address (pokePipAddress σ I)) "peek" 0 []
        (true, evmPip, out) true)
    (hdec : config.externalABI.decode? "peek" out = some (pokePeekReturnValues out))
    (hhas : pokePeekHasWord out = ⟨0⟩)
    (hvatNoCode :
      (UInt256.ofNat
        ((evmPip.lookupAccount (pokeVatAddress evmPip.accountMap evmPip.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    let locals := pokeLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals pokeTransition.body .reverted := by
  intro locals evm0
  have hpip :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.storage (ilksF (.var "ilk") "pip")) =
        .ok (.address (pokePipAddress evm0.accountMap I)) := by
    simpa [locals, evm0, initState] using
      (evalExpr_pokeStoragePip (evm := evm0) (I := I) hsz36 (by simp [evm0, initState]))
  have hpipCode0 :
      0 <
        (UInt256.ofNat
          ((evm0.lookupAccount (pokePipAddress evm0.accountMap I)).option 0
            (fun acc => acc.code.size))).toNat := by
    simpa [evm0, initState] using hpipCode
  have hpipGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage (ilksF (.var "ilk") "pip"))) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_pokePipCodeGuard_true hsz36 hpip hpipCode0
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [] = .ok [] := by
    simpa [locals] using evalExprs_pokePeekArgs evm0 I
  have hvalStmt :
      ExecStmt config { contract := contract, locals := pokePeekLocals I out } evmPip
        (.letDecl "val" (some bytes32) (.tupleGet (.var "peekRet") 0))
        (.ok { contract := contract, locals := pokeValLocals I out } evmPip) := by
    simpa [pokeValLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := pokePeekLocals I out })
        (evm := evmPip)
        (name := "val")
        (ty := some bytes32)
        (expr := .tupleGet (.var "peekRet") 0)
        (value := .fixedBytes bytes32Width (pokePeekValBytes out))
        (evalExpr_pokePeekVal evmPip I out))
  have hhasStmt :
      ExecStmt config { contract := contract, locals := pokeValLocals I out } evmPip
        (.letDecl "has" (some boolTy) (.tupleGet (.var "peekRet") 1))
        (.ok { contract := contract, locals := pokeHasLocals I out } evmPip) := by
    simpa [pokeHasLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := pokeValLocals I out })
        (evm := evmPip)
        (name := "has")
        (ty := some boolTy)
        (expr := .tupleGet (.var "peekRet") 1)
        (value := .bool (pokePeekHasBool out))
        (evalExpr_pokePeekHas evmPip I out))
  have hspotExpr :
      evalExpr? config { contract := contract, locals := pokeHasLocals I out } evmPip
        (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hspotStmt :
      ExecStmt config { contract := contract, locals := pokeHasLocals I out } evmPip
        (.letDecl "spot" (some uint256) (.intLit 0))
        (.ok { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evmPip) := by
    simpa [pokeSpotLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := pokeHasLocals I out })
        (evm := evmPip)
        (name := "spot")
        (ty := some uint256)
        (expr := .intLit 0)
        (value := .int (Int.ofNat (⟨0⟩ : UInt256).toNat))
        hspotExpr)
  have hhasGuard :
      evalExpr? config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evmPip
        (.var "has") = .ok (.bool false) :=
    evalExpr_pokeHas_false hhas
  have hvat :
      evalExpr? config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evmPip
        (.storage vatRef) =
        .ok (.address (pokeVatAddress evmPip.accountMap evmPip.executionEnv)) :=
    evalExpr_pokeStorageVatOfLocals (pokeSpotLocals_get_vat I out ⟨0⟩)
  have hvatGuard :
      evalExpr? config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evmPip
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool false) :=
    evalExpr_pokeVatCodeGuard_false_ofLocals hvat hvatNoCode
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 pokeTransition.body
        .reverted := by
    simp only [pokeTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hpipGuard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess (sendVal := 0) hpip
        (by simp [evalExpr?, pure]) hargs (by simpa [evm0] using hcall) hdec) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, pokePeekLocals, collapseReturns] using hvalStmt) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, pokePeekLocals, pokeValLocals, collapseReturns] using hhasStmt) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, pokePeekLocals, pokeValLocals, pokeHasLocals, collapseReturns]
        using hspotStmt) ?_
    refine ExecBlock.consNormal (ExecStmt.iteFalse hhasGuard ExecBlock.nil) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hvatGuard)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem spotPokeSourceBodyPeekHasFalseVatCallFailed {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmPip evmFile : EVM.State} {out fileOut : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hpipCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (pokePipAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      typedCallViaEVM config evm0 (EVM.address (pokePipAddress σ I)) "peek" 0 []
        (true, evmPip, out) true)
    (hdec : config.externalABI.decode? "peek" out = some (pokePeekReturnValues out))
    (hhas : pokePeekHasWord out = ⟨0⟩)
    (hvatCode :
      0 <
        (UInt256.ofNat
          ((evmPip.lookupAccount (pokeVatAddress evmPip.accountMap evmPip.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat)
    (hfileCall :
      typedCallViaEVM config evmPip
        (EVM.address (pokeVatAddress evmPip.accountMap evmPip.executionEnv)) "file" 0
        [.fixedBytes bytes32Width (pokeIlkBytes I),
          .fixedBytes bytes32Width pokeSpotParamBytes,
          .int (Int.ofNat (⟨0⟩ : UInt256).toNat)]
        (false, evmFile, fileOut) true) :
    let locals := pokeLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals pokeTransition.body .reverted := by
  intro locals evm0
  have hpip :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.storage (ilksF (.var "ilk") "pip")) =
        .ok (.address (pokePipAddress evm0.accountMap I)) := by
    simpa [locals, evm0, initState] using
      (evalExpr_pokeStoragePip (evm := evm0) (I := I) hsz36 (by simp [evm0, initState]))
  have hpipCode0 :
      0 <
        (UInt256.ofNat
          ((evm0.lookupAccount (pokePipAddress evm0.accountMap I)).option 0
            (fun acc => acc.code.size))).toNat := by
    simpa [evm0, initState] using hpipCode
  have hpipGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage (ilksF (.var "ilk") "pip"))) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_pokePipCodeGuard_true hsz36 hpip hpipCode0
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [] = .ok [] := by
    simpa [locals] using evalExprs_pokePeekArgs evm0 I
  have hvalStmt :
      ExecStmt config { contract := contract, locals := pokePeekLocals I out } evmPip
        (.letDecl "val" (some bytes32) (.tupleGet (.var "peekRet") 0))
        (.ok { contract := contract, locals := pokeValLocals I out } evmPip) := by
    simpa [pokeValLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := pokePeekLocals I out })
        (evm := evmPip)
        (name := "val")
        (ty := some bytes32)
        (expr := .tupleGet (.var "peekRet") 0)
        (value := .fixedBytes bytes32Width (pokePeekValBytes out))
        (evalExpr_pokePeekVal evmPip I out))
  have hhasStmt :
      ExecStmt config { contract := contract, locals := pokeValLocals I out } evmPip
        (.letDecl "has" (some boolTy) (.tupleGet (.var "peekRet") 1))
        (.ok { contract := contract, locals := pokeHasLocals I out } evmPip) := by
    simpa [pokeHasLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := pokeValLocals I out })
        (evm := evmPip)
        (name := "has")
        (ty := some boolTy)
        (expr := .tupleGet (.var "peekRet") 1)
        (value := .bool (pokePeekHasBool out))
        (evalExpr_pokePeekHas evmPip I out))
  have hspotExpr :
      evalExpr? config { contract := contract, locals := pokeHasLocals I out } evmPip
        (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hspotStmt :
      ExecStmt config { contract := contract, locals := pokeHasLocals I out } evmPip
        (.letDecl "spot" (some uint256) (.intLit 0))
        (.ok { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evmPip) := by
    simpa [pokeSpotLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := pokeHasLocals I out })
        (evm := evmPip)
        (name := "spot")
        (ty := some uint256)
        (expr := .intLit 0)
        (value := .int (Int.ofNat (⟨0⟩ : UInt256).toNat))
        hspotExpr)
  have hhasGuard :
      evalExpr? config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evmPip
        (.var "has") = .ok (.bool false) :=
    evalExpr_pokeHas_false hhas
  have hvat :
      evalExpr? config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evmPip
        (.storage vatRef) =
        .ok (.address (pokeVatAddress evmPip.accountMap evmPip.executionEnv)) :=
    evalExpr_pokeStorageVatOfLocals (pokeSpotLocals_get_vat I out ⟨0⟩)
  have hvatGuard :
      evalExpr? config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evmPip
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_pokeVatCodeGuard_true_ofLocals hvat hvatCode
  have hfileArgs :
      evalExprs? config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evmPip
        [.var "ilk", spotParamLit, .var "spot"] =
          .ok [.fixedBytes bytes32Width (pokeIlkBytes I),
            .fixedBytes bytes32Width pokeSpotParamBytes,
            .int (Int.ofNat (⟨0⟩ : UInt256).toNat)] :=
    evalExprs_pokeVatFileArgs evmPip I out ⟨0⟩
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 pokeTransition.body
        .reverted := by
    simp only [pokeTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hpipGuard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess (sendVal := 0) hpip
        (by simp [evalExpr?, pure]) hargs (by simpa [evm0] using hcall) hdec) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, pokePeekLocals, collapseReturns] using hvalStmt) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, pokePeekLocals, pokeValLocals, collapseReturns] using hhasStmt) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, pokePeekLocals, pokeValLocals, pokeHasLocals, collapseReturns]
        using hspotStmt) ?_
    refine ExecBlock.consNormal (ExecStmt.iteFalse hhasGuard ExecBlock.nil) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
    exact ExecBlock.consRevert
      (ExecStmt.externalCallFailure (sendVal := 0) hvat
        (by simp [evalExpr?, pure]) hfileArgs hfileCall)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem spotPokeSourceBodyPeekHasFalseVatCallSucceededReturns
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmPip evmFile : EVM.State} {out fileOut : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hpipCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (pokePipAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      typedCallViaEVM config evm0 (EVM.address (pokePipAddress σ I)) "peek" 0 []
        (true, evmPip, out) true)
    (hdec : config.externalABI.decode? "peek" out = some (pokePeekReturnValues out))
    (hhas : pokePeekHasWord out = ⟨0⟩)
    (hvatCode :
      0 <
        (UInt256.ofNat
          ((evmPip.lookupAccount (pokeVatAddress evmPip.accountMap evmPip.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat)
    (hfileCall :
      typedCallViaEVM config evmPip
        (EVM.address (pokeVatAddress evmPip.accountMap evmPip.executionEnv)) "file" 0
        [.fixedBytes bytes32Width (pokeIlkBytes I),
          .fixedBytes bytes32Width pokeSpotParamBytes,
          .int (Int.ofNat (⟨0⟩ : UInt256).toNat)]
        (true, evmFile, fileOut) true) :
    let locals := pokeLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let fileLocals := (pokeSpotLocals I out ⟨0⟩).insert "_fileRet" .unit
    ExecTransitionBody config contract evm0 locals pokeTransition.body
      (.returned { contract := contract, locals := fileLocals } evmFile none) := by
  intro locals evm0 fileLocals
  have hpip :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.storage (ilksF (.var "ilk") "pip")) =
        .ok (.address (pokePipAddress evm0.accountMap I)) := by
    simpa [locals, evm0, initState] using
      (evalExpr_pokeStoragePip (evm := evm0) (I := I) hsz36 (by simp [evm0, initState]))
  have hpipCode0 :
      0 <
        (UInt256.ofNat
          ((evm0.lookupAccount (pokePipAddress evm0.accountMap I)).option 0
            (fun acc => acc.code.size))).toNat := by
    simpa [evm0, initState] using hpipCode
  have hpipGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage (ilksF (.var "ilk") "pip"))) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_pokePipCodeGuard_true hsz36 hpip hpipCode0
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [] = .ok [] := by
    simpa [locals] using evalExprs_pokePeekArgs evm0 I
  have hvalStmt :
      ExecStmt config { contract := contract, locals := pokePeekLocals I out } evmPip
        (.letDecl "val" (some bytes32) (.tupleGet (.var "peekRet") 0))
        (.ok { contract := contract, locals := pokeValLocals I out } evmPip) := by
    simpa [pokeValLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := pokePeekLocals I out })
        (evm := evmPip)
        (name := "val")
        (ty := some bytes32)
        (expr := .tupleGet (.var "peekRet") 0)
        (value := .fixedBytes bytes32Width (pokePeekValBytes out))
        (evalExpr_pokePeekVal evmPip I out))
  have hhasStmt :
      ExecStmt config { contract := contract, locals := pokeValLocals I out } evmPip
        (.letDecl "has" (some boolTy) (.tupleGet (.var "peekRet") 1))
        (.ok { contract := contract, locals := pokeHasLocals I out } evmPip) := by
    simpa [pokeHasLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := pokeValLocals I out })
        (evm := evmPip)
        (name := "has")
        (ty := some boolTy)
        (expr := .tupleGet (.var "peekRet") 1)
        (value := .bool (pokePeekHasBool out))
        (evalExpr_pokePeekHas evmPip I out))
  have hspotExpr :
      evalExpr? config { contract := contract, locals := pokeHasLocals I out } evmPip
        (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hspotStmt :
      ExecStmt config { contract := contract, locals := pokeHasLocals I out } evmPip
        (.letDecl "spot" (some uint256) (.intLit 0))
        (.ok { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evmPip) := by
    simpa [pokeSpotLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := pokeHasLocals I out })
        (evm := evmPip)
        (name := "spot")
        (ty := some uint256)
        (expr := .intLit 0)
        (value := .int (Int.ofNat (⟨0⟩ : UInt256).toNat))
        hspotExpr)
  have hhasGuard :
      evalExpr? config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evmPip
        (.var "has") = .ok (.bool false) :=
    evalExpr_pokeHas_false hhas
  have hvat :
      evalExpr? config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evmPip
        (.storage vatRef) =
        .ok (.address (pokeVatAddress evmPip.accountMap evmPip.executionEnv)) :=
    evalExpr_pokeStorageVatOfLocals (pokeSpotLocals_get_vat I out ⟨0⟩)
  have hvatGuard :
      evalExpr? config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evmPip
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_pokeVatCodeGuard_true_ofLocals hvat hvatCode
  have hfileArgs :
      evalExprs? config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evmPip
        [.var "ilk", spotParamLit, .var "spot"] =
          .ok [.fixedBytes bytes32Width (pokeIlkBytes I),
            .fixedBytes bytes32Width pokeSpotParamBytes,
            .int (Int.ofNat (⟨0⟩ : UInt256).toNat)] :=
    evalExprs_pokeVatFileArgs evmPip I out ⟨0⟩
  have hfileDecode : config.externalABI.decode? "file" fileOut = some [] :=
    pokeVatFileDecode_ok fileOut
  have hfileReturn :
      ExecStmt config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evmPip
        (.externalCall (.storage vatRef) "file" (.intLit 0)
          [.var "ilk", spotParamLit, .var "spot"] "_fileRet" (perm := true))
        (.ok { contract := contract, locals := fileLocals } evmFile) := by
    have h := ExecStmt.externalCallSuccess (cfg := config)
      (solm := { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ })
      (evm := evmPip) (receiver := .storage vatRef) (name := "file") (eth := .intLit 0)
      (args := [.var "ilk", spotParamLit, .var "spot"]) (retVar := "_fileRet")
      (perm := true) (target := pokeVatAddress evmPip.accountMap evmPip.executionEnv)
      (sendVal := 0)
      (argVals :=
        [.fixedBytes bytes32Width (pokeIlkBytes I),
          .fixedBytes bytes32Width pokeSpotParamBytes,
          .int (Int.ofNat (⟨0⟩ : UInt256).toNat)])
      (evm' := evmFile) (out := fileOut) (value := [])
      hvat (by simp [evalExpr?, pure]) hfileArgs hfileCall hfileDecode
    simpa [fileLocals, collapseReturns] using h
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 pokeTransition.body
        (.ok { contract := contract, locals := fileLocals } evmFile) := by
    simp only [pokeTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hpipGuard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess (sendVal := 0) hpip
        (by simp [evalExpr?, pure]) hargs (by simpa [evm0] using hcall) hdec) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, pokePeekLocals, collapseReturns] using hvalStmt) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, pokePeekLocals, pokeValLocals, collapseReturns] using hhasStmt) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, pokePeekLocals, pokeValLocals, pokeHasLocals, collapseReturns]
        using hspotStmt) ?_
    refine ExecBlock.consNormal (ExecStmt.iteFalse hhasGuard ExecBlock.nil) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
    refine ExecBlock.consNormal hfileReturn ?_
    exact ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, fileLocals] using ExecFuncBody.execBlockOK hblock

theorem spotPokeSourceBodyPeekHasTrueTailReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmPip : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hpipCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (pokePipAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      typedCallViaEVM config evm0 (EVM.address (pokePipAddress σ I)) "peek" 0 []
        (true, evmPip, out) true)
    (hdec : config.externalABI.decode? "peek" out = some (pokePeekReturnValues out))
    (htail :
      ExecBlock config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evmPip
        pokeAfterSpotStmts .reverted) :
    let locals := pokeLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals pokeTransition.body .reverted := by
  intro locals evm0
  have hpip :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.storage (ilksF (.var "ilk") "pip")) =
        .ok (.address (pokePipAddress evm0.accountMap I)) := by
    simpa [locals, evm0, initState] using
      (evalExpr_pokeStoragePip (evm := evm0) (I := I) hsz36 (by simp [evm0, initState]))
  have hpipCode0 :
      0 <
        (UInt256.ofNat
          ((evm0.lookupAccount (pokePipAddress evm0.accountMap I)).option 0
            (fun acc => acc.code.size))).toNat := by
    simpa [evm0, initState] using hpipCode
  have hpipGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage (ilksF (.var "ilk") "pip"))) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_pokePipCodeGuard_true hsz36 hpip hpipCode0
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [] = .ok [] := by
    simpa [locals] using evalExprs_pokePeekArgs evm0 I
  have hvalStmt :
      ExecStmt config { contract := contract, locals := pokePeekLocals I out } evmPip
        (.letDecl "val" (some bytes32) (.tupleGet (.var "peekRet") 0))
        (.ok { contract := contract, locals := pokeValLocals I out } evmPip) := by
    simpa [pokeValLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := pokePeekLocals I out })
        (evm := evmPip)
        (name := "val")
        (ty := some bytes32)
        (expr := .tupleGet (.var "peekRet") 0)
        (value := .fixedBytes bytes32Width (pokePeekValBytes out))
        (evalExpr_pokePeekVal evmPip I out))
  have hhasStmt :
      ExecStmt config { contract := contract, locals := pokeValLocals I out } evmPip
        (.letDecl "has" (some boolTy) (.tupleGet (.var "peekRet") 1))
        (.ok { contract := contract, locals := pokeHasLocals I out } evmPip) := by
    simpa [pokeHasLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := pokeValLocals I out })
        (evm := evmPip)
        (name := "has")
        (ty := some boolTy)
        (expr := .tupleGet (.var "peekRet") 1)
        (value := .bool (pokePeekHasBool out))
        (evalExpr_pokePeekHas evmPip I out))
  have hspotExpr :
      evalExpr? config { contract := contract, locals := pokeHasLocals I out } evmPip
        (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hspotStmt :
      ExecStmt config { contract := contract, locals := pokeHasLocals I out } evmPip
        (.letDecl "spot" (some uint256) (.intLit 0))
        (.ok { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evmPip) := by
    simpa [pokeSpotLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := pokeHasLocals I out })
        (evm := evmPip)
        (name := "spot")
        (ty := some uint256)
        (expr := .intLit 0)
        (value := .int (Int.ofNat (⟨0⟩ : UInt256).toNat))
        hspotExpr)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 pokeTransition.body
        .reverted := by
    simp only [pokeTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hpipGuard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess (sendVal := 0) hpip
        (by simp [evalExpr?, pure]) hargs (by simpa [evm0] using hcall) hdec) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, pokePeekLocals, collapseReturns] using hvalStmt) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, pokePeekLocals, pokeValLocals, collapseReturns] using hhasStmt) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, pokePeekLocals, pokeValLocals, pokeHasLocals, collapseReturns]
        using hspotStmt) ?_
    simpa [pokeAfterSpotStmts, pokeTrueBranchStmts] using htail
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem spotPokeSourceBodyPeekHasTrueTailReturns {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmPip evmFile : EVM.State} {out : ByteArray} {fileLocals : Store}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hpipCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (pokePipAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      typedCallViaEVM config evm0 (EVM.address (pokePipAddress σ I)) "peek" 0 []
        (true, evmPip, out) true)
    (hdec : config.externalABI.decode? "peek" out = some (pokePeekReturnValues out))
    (htail :
      ExecBlock config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evmPip
        pokeAfterSpotStmts (.ok { contract := contract, locals := fileLocals } evmFile)) :
    let locals := pokeLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals pokeTransition.body
      (.returned { contract := contract, locals := fileLocals } evmFile none) := by
  intro locals evm0
  have hpip :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.storage (ilksF (.var "ilk") "pip")) =
        .ok (.address (pokePipAddress evm0.accountMap I)) := by
    simpa [locals, evm0, initState] using
      (evalExpr_pokeStoragePip (evm := evm0) (I := I) hsz36 (by simp [evm0, initState]))
  have hpipCode0 :
      0 <
        (UInt256.ofNat
          ((evm0.lookupAccount (pokePipAddress evm0.accountMap I)).option 0
            (fun acc => acc.code.size))).toNat := by
    simpa [evm0, initState] using hpipCode
  have hpipGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage (ilksF (.var "ilk") "pip"))) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_pokePipCodeGuard_true hsz36 hpip hpipCode0
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [] = .ok [] := by
    simpa [locals] using evalExprs_pokePeekArgs evm0 I
  have hvalStmt :
      ExecStmt config { contract := contract, locals := pokePeekLocals I out } evmPip
        (.letDecl "val" (some bytes32) (.tupleGet (.var "peekRet") 0))
        (.ok { contract := contract, locals := pokeValLocals I out } evmPip) := by
    simpa [pokeValLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := pokePeekLocals I out })
        (evm := evmPip)
        (name := "val")
        (ty := some bytes32)
        (expr := .tupleGet (.var "peekRet") 0)
        (value := .fixedBytes bytes32Width (pokePeekValBytes out))
        (evalExpr_pokePeekVal evmPip I out))
  have hhasStmt :
      ExecStmt config { contract := contract, locals := pokeValLocals I out } evmPip
        (.letDecl "has" (some boolTy) (.tupleGet (.var "peekRet") 1))
        (.ok { contract := contract, locals := pokeHasLocals I out } evmPip) := by
    simpa [pokeHasLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := pokeValLocals I out })
        (evm := evmPip)
        (name := "has")
        (ty := some boolTy)
        (expr := .tupleGet (.var "peekRet") 1)
        (value := .bool (pokePeekHasBool out))
        (evalExpr_pokePeekHas evmPip I out))
  have hspotExpr :
      evalExpr? config { contract := contract, locals := pokeHasLocals I out } evmPip
        (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hspotStmt :
      ExecStmt config { contract := contract, locals := pokeHasLocals I out } evmPip
        (.letDecl "spot" (some uint256) (.intLit 0))
        (.ok { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evmPip) := by
    simpa [pokeSpotLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := pokeHasLocals I out })
        (evm := evmPip)
        (name := "spot")
        (ty := some uint256)
        (expr := .intLit 0)
        (value := .int (Int.ofNat (⟨0⟩ : UInt256).toNat))
        hspotExpr)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 pokeTransition.body
        (.ok { contract := contract, locals := fileLocals } evmFile) := by
    simp only [pokeTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hpipGuard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess (sendVal := 0) hpip
        (by simp [evalExpr?, pure]) hargs (by simpa [evm0] using hcall) hdec) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, pokePeekLocals, collapseReturns] using hvalStmt) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, pokePeekLocals, pokeValLocals, collapseReturns] using hhasStmt) ?_
    refine ExecBlock.consNormal (by
      simpa [locals, pokePeekLocals, pokeValLocals, pokeHasLocals, collapseReturns]
        using hspotStmt) ?_
    simpa [pokeAfterSpotStmts, pokeTrueBranchStmts] using htail
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockOK hblock

theorem spotPokeTrueTailArithmeticReverts {evm : EVM.State} {I : ExecutionEnv}
    {out : ByteArray}
    (hhas : pokePeekHasWord out ≠ ⟨0⟩)
    (harith :
      ExecBlock config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
        pokeTrueBranchStmts .reverted) :
    ExecBlock config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
      pokeAfterSpotStmts .reverted := by
  have hhasGuard :
      evalExpr? config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
        (.var "has") = .ok (.bool true) :=
    evalExpr_pokeHas_true hhas
  simp only [pokeAfterSpotStmts, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue hhasGuard (by simpa [pokeTrueBranchStmts] using harith))

theorem spotPokeTrueTailVatNoCode {evm : EVM.State} {I : ExecutionEnv}
    {out : ByteArray} {valScaled spot1 spot2 : UInt256}
    (hhas : pokePeekHasWord out ≠ ⟨0⟩)
    (harith :
      ExecBlock config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
        pokeTrueBranchStmts
        (.ok { contract := contract, locals := pokeSpotAssignedLocals I out valScaled spot1 spot2 }
          evm))
    (hvatNoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (pokeVatAddress evm.accountMap evm.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    ExecBlock config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
      pokeAfterSpotStmts .reverted := by
  let localsA := pokeSpotAssignedLocals I out valScaled spot1 spot2
  have hhasGuard :
      evalExpr? config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
        (.var "has") = .ok (.bool true) :=
    evalExpr_pokeHas_true hhas
  have hvat :
      evalExpr? config { contract := contract, locals := localsA } evm (.storage vatRef) =
        .ok (.address (pokeVatAddress evm.accountMap evm.executionEnv)) := by
    simpa [localsA] using
      evalExpr_pokeStorageVatOfLocals
        (pokeSpotAssignedLocals_get_vat I out valScaled spot1 spot2)
  have hvatGuard :
      evalExpr? config { contract := contract, locals := localsA } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool false) :=
    evalExpr_pokeVatCodeGuard_false_ofLocals hvat hvatNoCode
  simp only [pokeAfterSpotStmts, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue hhasGuard (by simpa [pokeTrueBranchStmts] using harith)) ?_
  exact ExecBlock.consRevert (by simpa [localsA] using ExecStmt.requireFalse hvatGuard)

theorem spotPokeTrueTailVatCallFailed {evm evmFile : EVM.State} {I : ExecutionEnv}
    {out fileOut : ByteArray} {valScaled spot1 spot2 : UInt256}
    (hhas : pokePeekHasWord out ≠ ⟨0⟩)
    (harith :
      ExecBlock config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
        pokeTrueBranchStmts
        (.ok { contract := contract, locals := pokeSpotAssignedLocals I out valScaled spot1 spot2 }
          evm))
    (hvatCode :
      0 <
        (UInt256.ofNat
          ((evm.lookupAccount (pokeVatAddress evm.accountMap evm.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat)
    (hfileCall :
      typedCallViaEVM config evm
        (EVM.address (pokeVatAddress evm.accountMap evm.executionEnv)) "file" 0
        [.fixedBytes bytes32Width (pokeIlkBytes I),
          .fixedBytes bytes32Width pokeSpotParamBytes,
          .int (Int.ofNat spot2.toNat)]
        (false, evmFile, fileOut) true) :
    ExecBlock config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
      pokeAfterSpotStmts .reverted := by
  let localsA := pokeSpotAssignedLocals I out valScaled spot1 spot2
  have hhasGuard :
      evalExpr? config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
        (.var "has") = .ok (.bool true) :=
    evalExpr_pokeHas_true hhas
  have hvat :
      evalExpr? config { contract := contract, locals := localsA } evm (.storage vatRef) =
        .ok (.address (pokeVatAddress evm.accountMap evm.executionEnv)) := by
    simpa [localsA] using
      evalExpr_pokeStorageVatOfLocals
        (pokeSpotAssignedLocals_get_vat I out valScaled spot1 spot2)
  have hvatGuard :
      evalExpr? config { contract := contract, locals := localsA } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_pokeVatCodeGuard_true_ofLocals hvat hvatCode
  have hfileArgs :
      evalExprs? config { contract := contract, locals := localsA } evm
        [.var "ilk", spotParamLit, .var "spot"] =
          .ok [.fixedBytes bytes32Width (pokeIlkBytes I),
            .fixedBytes bytes32Width pokeSpotParamBytes,
            .int (Int.ofNat spot2.toNat)] :=
    evalExprs_pokeVatFileArgs_ofLocals evm I spot2
      (pokeSpotAssignedLocals_get_ilk I out valScaled spot1 spot2)
      (pokeSpotAssignedLocals_get_spot I out valScaled spot1 spot2)
  simp only [pokeAfterSpotStmts, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue hhasGuard (by simpa [pokeTrueBranchStmts] using harith)) ?_
  refine ExecBlock.consNormal (by simpa [localsA] using ExecStmt.requireTrue hvatGuard) ?_
  exact ExecBlock.consRevert
    (ExecStmt.externalCallFailure (sendVal := 0) hvat
      (by simp [evalExpr?, pure]) hfileArgs hfileCall)

theorem spotPokeTrueTailVatCallSucceededReturns {evm evmFile : EVM.State}
    {I : ExecutionEnv} {out fileOut : ByteArray} {valScaled spot1 spot2 : UInt256}
    (hhas : pokePeekHasWord out ≠ ⟨0⟩)
    (harith :
      ExecBlock config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
        pokeTrueBranchStmts
        (.ok { contract := contract, locals := pokeSpotAssignedLocals I out valScaled spot1 spot2 }
          evm))
    (hvatCode :
      0 <
        (UInt256.ofNat
          ((evm.lookupAccount (pokeVatAddress evm.accountMap evm.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat)
    (hfileCall :
      typedCallViaEVM config evm
        (EVM.address (pokeVatAddress evm.accountMap evm.executionEnv)) "file" 0
        [.fixedBytes bytes32Width (pokeIlkBytes I),
          .fixedBytes bytes32Width pokeSpotParamBytes,
          .int (Int.ofNat spot2.toNat)]
        (true, evmFile, fileOut) true) :
    let fileLocals := (pokeSpotAssignedLocals I out valScaled spot1 spot2).insert "_fileRet" .unit
    ExecBlock config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
      pokeAfterSpotStmts (.ok { contract := contract, locals := fileLocals } evmFile) := by
  intro fileLocals
  let localsA := pokeSpotAssignedLocals I out valScaled spot1 spot2
  have hhasGuard :
      evalExpr? config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
        (.var "has") = .ok (.bool true) :=
    evalExpr_pokeHas_true hhas
  have hvat :
      evalExpr? config { contract := contract, locals := localsA } evm (.storage vatRef) =
        .ok (.address (pokeVatAddress evm.accountMap evm.executionEnv)) := by
    simpa [localsA] using
      evalExpr_pokeStorageVatOfLocals
        (pokeSpotAssignedLocals_get_vat I out valScaled spot1 spot2)
  have hvatGuard :
      evalExpr? config { contract := contract, locals := localsA } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_pokeVatCodeGuard_true_ofLocals hvat hvatCode
  have hfileArgs :
      evalExprs? config { contract := contract, locals := localsA } evm
        [.var "ilk", spotParamLit, .var "spot"] =
          .ok [.fixedBytes bytes32Width (pokeIlkBytes I),
            .fixedBytes bytes32Width pokeSpotParamBytes,
            .int (Int.ofNat spot2.toNat)] :=
    evalExprs_pokeVatFileArgs_ofLocals evm I spot2
      (pokeSpotAssignedLocals_get_ilk I out valScaled spot1 spot2)
      (pokeSpotAssignedLocals_get_spot I out valScaled spot1 spot2)
  have hfileDecode : config.externalABI.decode? "file" fileOut = some [] :=
    pokeVatFileDecode_ok fileOut
  have hfileReturn :
      ExecStmt config { contract := contract, locals := localsA } evm
        (.externalCall (.storage vatRef) "file" (.intLit 0)
          [.var "ilk", spotParamLit, .var "spot"] "_fileRet" (perm := true))
        (.ok { contract := contract, locals := fileLocals } evmFile) := by
    have h := ExecStmt.externalCallSuccess (cfg := config)
      (solm := { contract := contract, locals := localsA })
      (evm := evm) (receiver := .storage vatRef) (name := "file") (eth := .intLit 0)
      (args := [.var "ilk", spotParamLit, .var "spot"]) (retVar := "_fileRet")
      (perm := true) (target := pokeVatAddress evm.accountMap evm.executionEnv)
      (sendVal := 0)
      (argVals :=
        [.fixedBytes bytes32Width (pokeIlkBytes I),
          .fixedBytes bytes32Width pokeSpotParamBytes,
          .int (Int.ofNat spot2.toNat)])
      (evm' := evmFile) (out := fileOut) (value := [])
      hvat (by simp [evalExpr?, pure]) hfileArgs hfileCall hfileDecode
    simpa [fileLocals, localsA, collapseReturns] using h
  simp only [pokeAfterSpotStmts, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue hhasGuard (by simpa [pokeTrueBranchStmts] using harith)) ?_
  refine ExecBlock.consNormal (by simpa [localsA] using ExecStmt.requireTrue hvatGuard) ?_
  refine ExecBlock.consNormal hfileReturn ?_
  exact ExecBlock.nil
end Benchmarks.Dss.Spot
