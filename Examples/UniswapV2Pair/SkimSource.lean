import Examples.UniswapV2Pair.SkimCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## Source body slices -/

theorem uniswapSkimLockEnterPrefix (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩) :
    ExecBlock config { contract := contract, locals := skimStore I } evm lockEnter
      (.ok { contract := contract, locals := skimStore I } (uniswapLockEnteredState evm)) := by
  exact uniswapLockEnterPrefix evm (skimStore I) hwv (by simp [skimStore]) hunlocked

theorem uniswapSkimLockExitSuffix (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock config { contract := contract, locals := skimStore I } evm lockExit
      (.ok { contract := contract, locals := skimStore I } (uniswapLockExitedState evm)) := by
  exact uniswapLockExitSuffix evm (skimStore I) (by simp [skimStore])

abbrev skimBalanceCallsBody : List Stmt :=
  pairBalanceOfThisStmts "balance0" "balance1"

abbrev skimToken0GuardTrue (evm : EVM.State) (I : ExecutionEnv) : Prop :=
  evalExpr? config { contract := contract, locals := skimStore I } (uniswapLockEnteredState evm)
    (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true)

abbrev skimToken1GuardTrue (evm0 : EVM.State) (I : ExecutionEnv) (balance0 : Value) : Prop :=
  evalExpr? config { contract := contract, locals := (skimStore I).insert "balance0" balance0 }
    evm0 (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true)

theorem uniswapSkimTokenPrefix (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩) :
    ExecBlock config { contract := contract, locals := skimStore I } evm
      (lockEnter ++
        [ .letDecl "_token0" (some addr) (.storage token0Ref),
          .letDecl "_token1" (some addr) (.storage token1Ref) ])
      (.ok { contract := contract, locals := skimTokenStore evm I }
        (uniswapLockEnteredState evm)) := by
  let evmL := uniswapLockEnteredState evm
  have hlock := uniswapSkimLockEnterPrefix evm I hwv hunlocked
  have htoken0 :
      evalExpr? config { contract := contract, locals := skimStore I } evmL
        (.storage token0Ref) = .ok (.address (uniswapAddressAtSlot evmL ⟨6⟩)) := by
    exact evalExpr_uniswap_storage_address evmL (skimStore I)
      (er := { base := "token0", steps := [] }) (slot := ⟨6⟩)
      (by simp [skimStore, token0Ref])
      (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl)
  have htoken1 :
      evalExpr? config
        { contract := contract,
          locals := (skimStore I).insert "_token0" (.address (uniswapAddressAtSlot evmL ⟨6⟩)) }
        evmL (.storage token1Ref) = .ok (.address (uniswapAddressAtSlot evmL ⟨7⟩)) := by
    exact evalExpr_uniswap_storage_address evmL
      ((skimStore I).insert "_token0" (.address (uniswapAddressAtSlot evmL ⟨6⟩)))
      (er := { base := "token1", steps := [] }) (slot := ⟨7⟩)
      (by simp [skimStore, token1Ref])
      (by simp [evalStorageRef, evalStorageRefSteps, token1Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl)
  have hlets :
      ExecBlock config { contract := contract, locals := skimStore I } evmL
        [ .letDecl "_token0" (some addr) (.storage token0Ref),
          .letDecl "_token1" (some addr) (.storage token1Ref) ]
        (.ok { contract := contract, locals := skimTokenStore evm I } evmL) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl htoken0) ?_
    exact ExecBlock.consNormal (ExecStmt.letDecl htoken1) (by
      simpa [skimTokenStore, evmL] using (ExecBlock.nil :
        ExecBlock config { contract := contract, locals := skimTokenStore evm I } evmL []
          (.ok { contract := contract, locals := skimTokenStore evm I } evmL)))
  simpa [List.append_assoc, evmL] using execBlock_append hlock hlets

-- LIBRARY CANDIDATE: Reasoning.SolmBody — variable-address receiver version of
-- `uniswapExternalBalanceOfThisFailure`, parameterized by receiver variable and target address.
theorem uniswapExternalBalanceOfThisVarFailure (evm evm' : EVM.State) (locals : Store)
    {receiver retVar : Ident} {target : AccountAddress} {out : ByteArray}
    (hreceiver : locals.get? receiver = some (.address target))
    (hcall : typedCallViaEVM config evm (EVM.address target)
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (false, evm', out) false) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .externalCall (.var receiver) "balanceOf" (.intLit 0) [this] retVar (perm := false) ] .reverted := by
  exact ExecBlock.consRevert
    (ExecStmt.externalCallFailure
      (by
        rw [evalExpr?, hreceiver]
        rfl)
      (by simp [evalExpr?, pure])
      (evalExprs_uniswap_this_single evm locals)
      hcall)

-- LIBRARY CANDIDATE: Reasoning.SolmBody — variable-address receiver version of
-- `uniswapExternalBalanceOfThisSuccess`, parameterized by receiver variable and target address.
theorem uniswapExternalBalanceOfThisVarSuccess (evm evm' : EVM.State) (locals : Store)
    {receiver retVar : Ident} {target : AccountAddress} {out : ByteArray} {value : Value}
    (hreceiver : locals.get? receiver = some (.address target))
    (hcall : typedCallViaEVM config evm (EVM.address target)
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm', out) false)
    (hdec : config.externalABI.decode? "balanceOf" out = some value) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .externalCall (.var receiver) "balanceOf" (.intLit 0) [this] retVar (perm := false) ]
      (.ok { contract := contract, locals := locals.insert retVar value } evm') := by
  exact ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      (by
        rw [evalExpr?, hreceiver]
        rfl)
      (by simp [evalExpr?, pure])
      (evalExprs_uniswap_this_single evm locals)
      hcall hdec)
    ExecBlock.nil

-- LIBRARY CANDIDATE: Reasoning.SolmBody — variable-address receiver version of
-- `uniswapExternalBalanceOfThisDecodeRevert`.
theorem uniswapExternalBalanceOfThisVarDecodeRevert
    (evm evm' : EVM.State) (locals : Store)
    {receiver retVar : Ident} {target : AccountAddress} {out : ByteArray}
    (hreceiver : locals.get? receiver = some (.address target))
    (hcall : typedCallViaEVM config evm (EVM.address target)
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm', out) false)
    (hdec : config.externalABI.decode? "balanceOf" out = none) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .externalCall (.var receiver) "balanceOf" (.intLit 0) [this] retVar (perm := false) ] .reverted := by
  exact ExecBlock.consRevert
    (ExecStmt.externalCallReturnDecodeRevert
      (by
        rw [evalExpr?, hreceiver]
        rfl)
      (by simp [evalExpr?, pure])
      (evalExprs_uniswap_this_single evm locals)
      hcall hdec)

-- LIBRARY CANDIDATE: Reasoning.SolmBody — source-side failed high-level external call after
-- an `EXTCODESIZE` guard, with the receiver read from a local variable.
theorem uniswapCheckedExternalBalanceOfThisVarFailure
    (evm evm' : EVM.State) (locals : Store)
    {receiver retVar : Ident} {target : AccountAddress} {out : ByteArray}
    (hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.var receiver)) (.intLit 0)) = .ok (.bool true))
    (hreceiver : locals.get? receiver = some (.address target))
    (hcall : typedCallViaEVM config evm (EVM.address target)
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (false, evm', out) false) :
    ExecBlock config { contract := contract, locals := locals } evm
      (balanceOfThisStmts (.var receiver) retVar) .reverted := by
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .require (.binary .gt (.extCodeSize (.var receiver)) (.intLit 0)),
      .externalCall (.var receiver) "balanceOf" (.intLit 0) [this] retVar (perm := false) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  exact uniswapExternalBalanceOfThisVarFailure evm evm' locals hreceiver hcall

-- LIBRARY CANDIDATE: Reasoning.SolmBody — source-side successful high-level external call after
-- an `EXTCODESIZE` guard, with the receiver read from a local variable.
theorem uniswapCheckedExternalBalanceOfThisVarSuccess
    (evm evm' : EVM.State) (locals : Store)
    {receiver retVar : Ident} {target : AccountAddress} {out : ByteArray} {value : Value}
    (hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.var receiver)) (.intLit 0)) = .ok (.bool true))
    (hreceiver : locals.get? receiver = some (.address target))
    (hcall : typedCallViaEVM config evm (EVM.address target)
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm', out) false)
    (hdec : config.externalABI.decode? "balanceOf" out = some value) :
    ExecBlock config { contract := contract, locals := locals } evm
      (balanceOfThisStmts (.var receiver) retVar)
      (.ok { contract := contract, locals := locals.insert retVar value } evm') := by
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .require (.binary .gt (.extCodeSize (.var receiver)) (.intLit 0)),
      .externalCall (.var receiver) "balanceOf" (.intLit 0) [this] retVar (perm := false) ]
    (.ok { contract := contract, locals := locals.insert retVar value } evm')
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  exact uniswapExternalBalanceOfThisVarSuccess evm evm' locals hreceiver hcall hdec

-- LIBRARY CANDIDATE: Reasoning.SolmBody — source-side ABI-decode revert after a successful
-- guarded high-level external call whose receiver is a local variable.
theorem uniswapCheckedExternalBalanceOfThisVarDecodeRevert
    (evm evm' : EVM.State) (locals : Store)
    {receiver retVar : Ident} {target : AccountAddress} {out : ByteArray}
    (hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.var receiver)) (.intLit 0)) = .ok (.bool true))
    (hreceiver : locals.get? receiver = some (.address target))
    (hcall : typedCallViaEVM config evm (EVM.address target)
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm', out) false)
    (hdec : config.externalABI.decode? "balanceOf" out = none) :
    ExecBlock config { contract := contract, locals := locals } evm
      (balanceOfThisStmts (.var receiver) retVar) .reverted := by
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .require (.binary .gt (.extCodeSize (.var receiver)) (.intLit 0)),
      .externalCall (.var receiver) "balanceOf" (.intLit 0) [this] retVar (perm := false) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  exact uniswapExternalBalanceOfThisVarDecodeRevert evm evm' locals hreceiver hcall hdec

-- LIBRARY CANDIDATE: Reasoning.SolmBody — source-side high-level external call reverts before
-- the call when Solidity's `EXTCODESIZE(receiver) > 0` guard is false and receiver is local.
theorem uniswapCheckedExternalBalanceOfThisVarNoCode
    (evm : EVM.State) (locals : Store)
    {receiver retVar : Ident}
    (hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.var receiver)) (.intLit 0)) = .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (balanceOfThisStmts (.var receiver) retVar) .reverted := by
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .require (.binary .gt (.extCodeSize (.var receiver)) (.intLit 0)),
      .externalCall (.var receiver) "balanceOf" (.intLit 0) [this] retVar (perm := false) ]
    .reverted
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)

theorem skimToken0Guard_cached_eq (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := skimTokenStore evm I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.var "_token0")) (.intLit 0)) =
      evalExpr? config { contract := contract, locals := skimStore I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) := by
  let evmL := uniswapLockEnteredState evm
  have hvar :
      evalExpr? config { contract := contract, locals := skimTokenStore evm I } evmL
        (.var "_token0") = .ok (.address (uniswapAddressAtSlot evmL ⟨6⟩)) := by
    simpa [evmL, evalExpr?, EvalResult.ofOption, Std.HashMap.get?_eq_getElem?]
      using skimTokenStore_token0 evm I
  have hstorage :
      evalExpr? config { contract := contract, locals := skimStore I } evmL
        (.storage token0Ref) = .ok (.address (uniswapAddressAtSlot evmL ⟨6⟩)) := by
    exact evalExpr_uniswap_storage_address evmL (skimStore I)
      (er := { base := "token0", steps := [] }) (slot := ⟨6⟩)
      (by simp [skimStore, token0Ref])
      (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl)
  simp [evmL, evalExpr?, EvalResult.bind, bind, pure, hvar, hstorage]

theorem skimToken0GuardTrue_cached (evm : EVM.State) (I : ExecutionEnv)
    (hguard0 : skimToken0GuardTrue evm I) :
    evalExpr? config { contract := contract, locals := skimTokenStore evm I }
      (uniswapLockEnteredState evm)
      (.binary .gt (.extCodeSize (.var "_token0")) (.intLit 0)) = .ok (.bool true) := by
  exact (skimToken0Guard_cached_eq evm I).trans hguard0

abbrev skimToken0GuardFalse (evm : EVM.State) (I : ExecutionEnv) : Prop :=
  evalExpr? config { contract := contract, locals := skimStore I } (uniswapLockEnteredState evm)
    (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool false)

theorem skimToken0GuardFalse_cached (evm : EVM.State) (I : ExecutionEnv)
    (hguard0 : skimToken0GuardFalse evm I) :
    evalExpr? config { contract := contract, locals := skimTokenStore evm I }
      (uniswapLockEnteredState evm)
      (.binary .gt (.extCodeSize (.var "_token0")) (.intLit 0)) = .ok (.bool false) := by
  exact (skimToken0Guard_cached_eq evm I).trans hguard0

theorem uniswapSkimCachedFirstCallFailure (evm evm0 : EVM.State) (I : ExecutionEnv)
    {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (false, evm0, out0) false) :
    ExecBlock config { contract := contract, locals := skimStore I } evm
      (lockEnter ++
        [ .letDecl "_token0" (some addr) (.storage token0Ref),
          .letDecl "_token1" (some addr) (.storage token1Ref) ] ++
        balanceOfThisStmts (.var "_token0") "balance0")
      .reverted := by
  let evmL := uniswapLockEnteredState evm
  have hprefix := uniswapSkimTokenPrefix evm I hwv hunlocked
  have hfail :
      ExecBlock config { contract := contract, locals := skimTokenStore evm I } evmL
        (balanceOfThisStmts (.var "_token0") "balance0") .reverted := by
    exact uniswapCheckedExternalBalanceOfThisVarFailure
      (evm := evmL) (evm' := evm0) (locals := skimTokenStore evm I)
      (receiver := "_token0") (retVar := "balance0")
      (target := uniswapAddressAtSlot evmL ⟨6⟩)
      (skimToken0GuardTrue_cached evm I hguard0)
      (by simpa [evmL] using skimTokenStore_token0 evm I)
      hcall0
  simpa [List.append_assoc, evmL] using execBlock_append hprefix hfail

theorem uniswapSkimCachedFirstCallDecodeRevert (evm evm0 : EVM.State) (I : ExecutionEnv)
    {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = none) :
    ExecBlock config { contract := contract, locals := skimStore I } evm
      (lockEnter ++
        [ .letDecl "_token0" (some addr) (.storage token0Ref),
          .letDecl "_token1" (some addr) (.storage token1Ref) ] ++
        balanceOfThisStmts (.var "_token0") "balance0")
      .reverted := by
  let evmL := uniswapLockEnteredState evm
  have hprefix := uniswapSkimTokenPrefix evm I hwv hunlocked
  have hfail :
      ExecBlock config { contract := contract, locals := skimTokenStore evm I } evmL
        (balanceOfThisStmts (.var "_token0") "balance0") .reverted := by
    exact uniswapCheckedExternalBalanceOfThisVarDecodeRevert
      (evm := evmL) (evm' := evm0) (locals := skimTokenStore evm I)
      (receiver := "_token0") (retVar := "balance0")
      (target := uniswapAddressAtSlot evmL ⟨6⟩)
      (skimToken0GuardTrue_cached evm I hguard0)
      (by simpa [evmL] using skimTokenStore_token0 evm I)
      hcall0 hdec0
  simpa [List.append_assoc, evmL] using execBlock_append hprefix hfail

theorem uniswapSkimCachedFirstCallSuccess (evm evm0 : EVM.State) (I : ExecutionEnv)
    {out0 : ByteArray} {balance0 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some (skimBalanceValue balance0)) :
    ExecBlock config { contract := contract, locals := skimStore I } evm
      (lockEnter ++
        [ .letDecl "_token0" (some addr) (.storage token0Ref),
          .letDecl "_token1" (some addr) (.storage token1Ref) ] ++
        balanceOfThisStmts (.var "_token0") "balance0")
      (.ok { contract := contract, locals := skimFirstBalanceStore evm I balance0 } evm0) := by
  let evmL := uniswapLockEnteredState evm
  have hprefix := uniswapSkimTokenPrefix evm I hwv hunlocked
  have hsuccess :
      ExecBlock config { contract := contract, locals := skimTokenStore evm I } evmL
        (balanceOfThisStmts (.var "_token0") "balance0")
        (.ok { contract := contract, locals := skimFirstBalanceStore evm I balance0 } evm0) := by
    exact uniswapCheckedExternalBalanceOfThisVarSuccess
      (evm := evmL) (evm' := evm0) (locals := skimTokenStore evm I)
      (receiver := "_token0") (retVar := "balance0")
      (target := uniswapAddressAtSlot evmL ⟨6⟩)
      (value := skimBalanceValue balance0)
      (skimToken0GuardTrue_cached evm I hguard0)
      (by simpa [evmL] using skimTokenStore_token0 evm I)
      hcall0 hdec0
  simpa [List.append_assoc, evmL, skimFirstBalanceStore] using execBlock_append hprefix hsuccess

theorem uniswapSkimBalanceOfCallsPrefix (evm evm0 evm1 : EVM.State) (I : ExecutionEnv)
    {out0 out1 : ByteArray} {balance0 balance1 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hguard1 : skimToken1GuardTrue evm0 I balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some balance1) :
    ExecBlock config { contract := contract, locals := skimStore I } evm
      (lockEnter ++ skimBalanceCallsBody)
      (.ok (uniswapBalanceOfFrame (skimStore I) balance0 balance1) evm1) := by
  have hlock := uniswapSkimLockEnterPrefix evm I hwv hunlocked
  have hcalls := uniswapCheckedTokenBalanceOfThisCallsPrefix
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (evm1 := evm1) (locals := skimStore I)
    (balance0 := balance0) (balance1 := balance1)
    hguard0 hguard1 (by simp [skimStore]) (by simp [skimStore]) hcall0 hdec0 hcall1 hdec1
  simpa [skimBalanceCallsBody] using execBlock_append hlock hcalls

theorem uniswapSkimBalanceOfFirstCallFailure (evm evm0 : EVM.State) (I : ExecutionEnv)
    {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (false, evm0, out0) false) :
    ExecBlock config { contract := contract, locals := skimStore I } evm
      (lockEnter ++ skimBalanceCallsBody)
      .reverted := by
  have hlock := uniswapSkimLockEnterPrefix evm I hwv hunlocked
  have hfail := uniswapCheckedTokenBalanceOfThisFirstCallFailure
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (locals := skimStore I)
    hguard0 (by simp [skimStore]) hcall0
  simpa [skimBalanceCallsBody] using execBlock_append hlock hfail

theorem uniswapSkimBalanceOfFirstCallDecodeRevert (evm evm0 : EVM.State) (I : ExecutionEnv)
    {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = none) :
    ExecBlock config { contract := contract, locals := skimStore I } evm
      (lockEnter ++ skimBalanceCallsBody)
      .reverted := by
  have hlock := uniswapSkimLockEnterPrefix evm I hwv hunlocked
  have hfail := uniswapCheckedTokenBalanceOfThisFirstCallDecodeRevert
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (locals := skimStore I)
    hguard0 (by simp [skimStore]) hcall0 hdec0
  simpa [skimBalanceCallsBody] using execBlock_append hlock hfail

theorem uniswapSkimBalanceOfSecondCallFailure (evm evm0 evm1 : EVM.State) (I : ExecutionEnv)
    {out0 out1 : ByteArray} {balance0 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hguard1 : skimToken1GuardTrue evm0 I balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (false, evm1, out1) false) :
    ExecBlock config { contract := contract, locals := skimStore I } evm
      (lockEnter ++ skimBalanceCallsBody)
      .reverted := by
  have hlock := uniswapSkimLockEnterPrefix evm I hwv hunlocked
  have hfail := uniswapCheckedTokenBalanceOfThisSecondCallFailure
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (evm1 := evm1)
    (locals := skimStore I) (balance0 := balance0)
    hguard0 hguard1 (by simp [skimStore]) (by simp [skimStore]) hcall0 hdec0 hcall1
  simpa [skimBalanceCallsBody] using execBlock_append hlock hfail

theorem uniswapSkimBalanceOfSecondCallDecodeRevert (evm evm0 evm1 : EVM.State)
    (I : ExecutionEnv) {out0 out1 : ByteArray} {balance0 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hguard1 : skimToken1GuardTrue evm0 I balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = none) :
    ExecBlock config { contract := contract, locals := skimStore I } evm
      (lockEnter ++ skimBalanceCallsBody)
      .reverted := by
  have hlock := uniswapSkimLockEnterPrefix evm I hwv hunlocked
  have hfail := uniswapCheckedTokenBalanceOfThisSecondCallDecodeRevert
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (evm1 := evm1)
    (locals := skimStore I) (balance0 := balance0)
    hguard0 hguard1 (by simp [skimStore]) (by simp [skimStore]) hcall0 hdec0 hcall1 hdec1
  simpa [skimBalanceCallsBody] using execBlock_append hlock hfail

theorem evalExpr_skim_excess0 (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256)
    (henough : (uniswapReserve0Word evm).toNat ≤ balance0.toNat) :
    evalExpr? config { contract := contract, locals := skimBalanceStore I balance0 balance1 } evm
      (.binary .sub (.var "balance0") (.storage reserve0Ref)) =
        .ok (skimExcess0Value evm balance0) := by
  have hsub :
      Int.ofNat balance0.toNat - Int.ofNat (uniswapReserve0Word evm).toNat =
        Int.ofNat (balance0.toNat - (uniswapReserve0Word evm).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat :
      (skimExcess0Word evm balance0).toNat =
        balance0.toNat - (uniswapReserve0Word evm).toNat := by
    unfold skimExcess0Word
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) balance0.val.isLt)
  have hreserve := evalExpr_uniswap_reserve0 evm (skimBalanceStore I balance0 balance1)
    (by simp [skimBalanceStore, uniswapBalanceOfStore, skimStore])
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, hreserve]
  rw [skimBalanceStore_balance0]
  simpa [skimBalanceValue, evalBinaryOp?, skimExcess0Value, htoNat] using hsub

theorem evalExpr_skim_first_excess0 (startEvm callEvm : EVM.State) (I : ExecutionEnv)
    (balance0 : UInt256)
    (henough : (uniswapReserve0Word callEvm).toNat ≤ balance0.toNat) :
    evalExpr? config { contract := contract, locals := skimFirstBalanceStore startEvm I balance0 }
      callEvm (u256 (.binary .sub (.var "balance0") (.storage reserve0Ref))) =
        .ok (skimExcess0Value callEvm balance0) := by
  have hsub :
      Int.ofNat balance0.toNat - Int.ofNat (uniswapReserve0Word callEvm).toNat =
        Int.ofNat (balance0.toNat - (uniswapReserve0Word callEvm).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat :
      (skimExcess0Word callEvm balance0).toNat =
        balance0.toNat - (uniswapReserve0Word callEvm).toNat := by
    unfold skimExcess0Word
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) balance0.val.isLt)
  have hfit :
      balance0.toNat - (uniswapReserve0Word callEvm).toNat < UInt256.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) balance0.val.isLt
  have hnotHigh :
      ¬ Int.ofNat (balance0.toNat - (uniswapReserve0Word callEvm).toNat) ≥
        (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hreserve := evalExpr_uniswap_reserve0 callEvm
    (skimFirstBalanceStore startEvm I balance0)
    (by simp [skimFirstBalanceStore, skimTokenStore, skimStore])
  simp only [u256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure, hreserve]
  rw [skimFirstBalanceStore_balance0]
  simp [evalBinaryOp?, skimExcess0Value, htoNat, uint256Int]
  rw [if_neg]
  · simpa [hsub]
  · intro hbad
    rcases hbad with hlow | hhigh
    · omega
    · exact hnotHigh (by
        rw [← hsub]
        exact hhigh)

theorem evalExprs_skim_safeTransfer0_args (startEvm callEvm : EVM.State)
    (I : ExecutionEnv) (balance0 : UInt256) :
    evalExprs? config
      { contract := contract, locals := skimFirstExcessStore startEvm callEvm I balance0 }
      callEvm [.var "_token0", .var "to", .var "excess0"] =
        .ok (safeTransferArgs
          (uniswapAddressAtSlot (uniswapLockEnteredState startEvm) ⟨6⟩)
          (skimToAddress I)
          (skimExcess0Word callEvm balance0)) := by
  simp only [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [skimFirstExcessStore_token0, skimFirstExcessStore_to, skimFirstExcessStore_excess0]

theorem evalExpr_skim_excess1 (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256)
    (henough : (uniswapReserve1Word evm).toNat ≤ balance1.toNat) :
    evalExpr? config { contract := contract, locals := skimExcess0Store evm I balance0 balance1 }
      evm (.binary .sub (.var "balance1") (.storage reserve1Ref)) =
        .ok (skimExcess1Value evm balance1) := by
  have hsub :
      Int.ofNat balance1.toNat - Int.ofNat (uniswapReserve1Word evm).toNat =
        Int.ofNat (balance1.toNat - (uniswapReserve1Word evm).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat :
      (skimExcess1Word evm balance1).toNat =
        balance1.toNat - (uniswapReserve1Word evm).toNat := by
    unfold skimExcess1Word
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) balance1.val.isLt)
  have hreserve := evalExpr_uniswap_reserve1 evm (skimExcess0Store evm I balance0 balance1)
    (by simp [skimExcess0Store, skimBalanceStore, uniswapBalanceOfStore, skimStore])
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, hreserve]
  rw [skimExcess0Store_balance1]
  simpa [skimBalanceValue, evalBinaryOp?, skimExcess1Value, htoNat] using hsub

theorem evalExpr_skim_second_excess1
    (startEvm firstCallEvm secondCallEvm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256)
    (henough : (uniswapReserve1Word secondCallEvm).toNat ≤ balance1.toNat) :
    evalExpr? config
      { contract := contract,
        locals := skimSecondBalanceStore startEvm firstCallEvm I balance0 balance1 }
      secondCallEvm (u256 (.binary .sub (.var "balance1") (.storage reserve1Ref))) =
        .ok (skimExcess1Value secondCallEvm balance1) := by
  have hsub :
      Int.ofNat balance1.toNat - Int.ofNat (uniswapReserve1Word secondCallEvm).toNat =
        Int.ofNat (balance1.toNat - (uniswapReserve1Word secondCallEvm).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat :
      (skimExcess1Word secondCallEvm balance1).toNat =
        balance1.toNat - (uniswapReserve1Word secondCallEvm).toNat := by
    unfold skimExcess1Word
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) balance1.val.isLt)
  have hfit :
      balance1.toNat - (uniswapReserve1Word secondCallEvm).toNat < UInt256.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) balance1.val.isLt
  have hnotHigh :
      ¬ Int.ofNat (balance1.toNat - (uniswapReserve1Word secondCallEvm).toNat) ≥
        (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hreserve := evalExpr_uniswap_reserve1 secondCallEvm
    (skimSecondBalanceStore startEvm firstCallEvm I balance0 balance1)
    (by
      simp [skimSecondBalanceStore, skimFirstSafeTransferStore, skimFirstExcessStore,
        skimFirstBalanceStore, skimTokenStore, skimStore])
  simp only [u256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure, hreserve]
  rw [skimSecondBalanceStore_balance1]
  simp [evalBinaryOp?, skimExcess1Value, htoNat, uint256Int]
  rw [if_neg]
  · simpa [hsub]
  · intro hbad
    rcases hbad with hlow | hhigh
    · omega
    · exact hnotHigh (by
        rw [← hsub]
        exact hhigh)

theorem evalExprs_skim_safeTransfer1_args
    (startEvm firstCallEvm secondCallEvm : EVM.State)
    (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    evalExprs? config
      { contract := contract,
        locals := skimSecondExcessStore startEvm firstCallEvm secondCallEvm I balance0 balance1 }
      secondCallEvm [.var "_token1", .var "to", .var "excess1"] =
        .ok (safeTransferArgs
          (uniswapAddressAtSlot (uniswapLockEnteredState startEvm) ⟨7⟩)
          (skimToAddress I)
          (skimExcess1Word secondCallEvm balance1)) := by
  simp only [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [skimSecondExcessStore_token1, skimSecondExcessStore_to, skimSecondExcessStore_excess1]

abbrev skimExcessPrefixBody : List Stmt :=
  [ .letDecl "excess0" (some uint256)
      (.binary .sub (.var "balance0") (.storage reserve0Ref)),
    .letDecl "excess1" (some uint256)
      (.binary .sub (.var "balance1") (.storage reserve1Ref)) ]

abbrev skimAfterBalanceBody : List Stmt :=
  skimExcessPrefixBody ++
    safeTransferStmts (.storage token0Ref) (.var "to") (.var "excess0") "ok0" "_ret0" ++
    safeTransferStmts (.storage token1Ref) (.var "to") (.var "excess1") "ok1" "_ret1" ++
    lockExit

abbrev skimAfterLockBody : List Stmt :=
  [ .letDecl "_token0" (some addr) (.storage token0Ref),
    .letDecl "_token1" (some addr) (.storage token1Ref) ] ++
  balanceOfThisStmts (.var "_token0") "balance0" ++
    [ .letDecl "excess0" (some uint256)
        (u256 (.binary .sub (.var "balance0") (.storage reserve0Ref))) ] ++
  safeTransferStmts (.var "_token0") (.var "to") (.var "excess0") "ok0" "_ret0" ++
  balanceOfThisStmts (.var "_token1") "balance1" ++
    [ .letDecl "excess1" (some uint256)
        (u256 (.binary .sub (.var "balance1") (.storage reserve1Ref))) ] ++
  safeTransferStmts (.var "_token1") (.var "to") (.var "excess1") "ok1" "_ret1" ++
  lockExit

theorem uniswapSkimFirstSafeTransferPrefix (evm evm0 evm1 : EVM.State)
    (I : ExecutionEnv) {out0 : ByteArray} {balance0 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some (skimBalanceValue balance0))
    (henough0 : (uniswapReserve0Word evm0).toNat ≤ balance0.toNat)
    (hsafe0 :
      ExecStmt config
        { contract := contract, locals := skimFirstExcessStore evm evm0 I balance0 } evm0
        (.internalCall "_safeTransfer" [.var "_token0", .var "to", .var "excess0"] "ok0")
        (.ok { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 }
          evm1)) :
    ExecBlock config { contract := contract, locals := skimStore I } evm
      (lockEnter ++
        [ .letDecl "_token0" (some addr) (.storage token0Ref),
          .letDecl "_token1" (some addr) (.storage token1Ref) ] ++
        balanceOfThisStmts (.var "_token0") "balance0" ++
        [ .letDecl "excess0" (some uint256)
            (u256 (.binary .sub (.var "balance0") (.storage reserve0Ref))) ] ++
        safeTransferStmts (.var "_token0") (.var "to") (.var "excess0") "ok0" "_ret0")
      (.ok { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 }
        evm1) := by
  have hprefix :=
    uniswapSkimCachedFirstCallSuccess evm evm0 I hwv hunlocked hguard0 hcall0 hdec0
  have hexcess :
      ExecBlock config
        { contract := contract, locals := skimFirstBalanceStore evm I balance0 } evm0
        [ .letDecl "excess0" (some uint256)
            (u256 (.binary .sub (.var "balance0") (.storage reserve0Ref))) ]
        (.ok { contract := contract, locals := skimFirstExcessStore evm evm0 I balance0 }
          evm0) := by
    exact ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_skim_first_excess0 evm evm0 I balance0 henough0))
      ExecBlock.nil
  have hsafe :
      ExecBlock config
        { contract := contract, locals := skimFirstExcessStore evm evm0 I balance0 } evm0
        (safeTransferStmts (.var "_token0") (.var "to") (.var "excess0") "ok0" "_ret0")
        (.ok { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 }
          evm1) := by
    change ExecBlock config
      { contract := contract, locals := skimFirstExcessStore evm evm0 I balance0 } evm0
      [ .internalCall "_safeTransfer" [.var "_token0", .var "to", .var "excess0"] "ok0" ]
      (.ok { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 }
        evm1)
    exact ExecBlock.consNormal hsafe0 ExecBlock.nil
  exact execBlock_append (execBlock_append hprefix hexcess) hsafe

/-! ## `skim(address)` source-body wrappers -/

theorem uniswapSkimBodyReverts_nonpayable (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm (skimStore I) skimTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (by
    have hlock := uniswapLockEnterNonpayableRevert evm (skimStore I) hwv
    simpa [skimTransition, skimAfterLockBody, List.append_assoc] using
      (execBlock_append_term
        (s2 := skimAfterLockBody)
        hlock (by intro f e h; cases h)))

theorem uniswapSkimBodyReverts_locked (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (skimStore I) skimTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (by
    have hlock := uniswapLockEnterLockedRevert evm (skimStore I) hwv
      (by simp [skimStore]) hlocked
    simpa [skimTransition, skimAfterLockBody, List.append_assoc] using
      (execBlock_append_term
        (s2 := skimAfterLockBody)
        hlock (by intro f e h; cases h)))

theorem uniswapSkimBodyReverts_firstNoCode (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardFalse evm I) :
    ExecTransitionBody config contract evm (skimStore I) skimTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (by
    have hprefix := uniswapSkimTokenPrefix evm I hwv hunlocked
    have hfirst :
        ExecBlock config { contract := contract, locals := skimTokenStore evm I }
          (uniswapLockEnteredState evm)
          (balanceOfThisStmts (.var "_token0") "balance0") .reverted := by
      exact uniswapCheckedExternalBalanceOfThisVarNoCode
        (evm := uniswapLockEnteredState evm) (locals := skimTokenStore evm I)
        (receiver := "_token0") (retVar := "balance0")
        (skimToken0GuardFalse_cached evm I hguard0)
    have htail :=
      execBlock_append_term
        (s2 :=
          [ .letDecl "excess0" (some uint256)
              (u256 (.binary .sub (.var "balance0") (.storage reserve0Ref))) ] ++
          safeTransferStmts (.var "_token0") (.var "to") (.var "excess0") "ok0" "_ret0" ++
          balanceOfThisStmts (.var "_token1") "balance1" ++
          [ .letDecl "excess1" (some uint256)
              (u256 (.binary .sub (.var "balance1") (.storage reserve1Ref))) ] ++
          safeTransferStmts (.var "_token1") (.var "to") (.var "excess1") "ok1" "_ret1" ++
          lockExit)
        hfirst (by intro f e h; cases h)
    have hbody := execBlock_append hprefix htail
    simpa [skimTransition, skimAfterLockBody, List.append_assoc] using hbody)

theorem uniswapSkimBodyReverts_firstCallFailure (evm evm0 : EVM.State) (I : ExecutionEnv)
    {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (false, evm0, out0) false) :
    ExecTransitionBody config contract evm (skimStore I) skimTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (by
    have hprefix :=
      uniswapSkimCachedFirstCallFailure evm evm0 I hwv hunlocked hguard0 hcall0
    simpa [skimTransition, skimAfterLockBody, List.append_assoc] using
      (execBlock_append_term
        (s2 :=
          [ .letDecl "excess0" (some uint256)
              (u256 (.binary .sub (.var "balance0") (.storage reserve0Ref))) ] ++
          safeTransferStmts (.var "_token0") (.var "to") (.var "excess0") "ok0" "_ret0" ++
          balanceOfThisStmts (.var "_token1") "balance1" ++
          [ .letDecl "excess1" (some uint256)
              (u256 (.binary .sub (.var "balance1") (.storage reserve1Ref))) ] ++
          safeTransferStmts (.var "_token1") (.var "to") (.var "excess1") "ok1" "_ret1" ++
          lockExit)
        hprefix (by intro f e h; cases h)))

theorem uniswapSkimBodyReverts_firstCallDecode (evm evm0 : EVM.State) (I : ExecutionEnv)
    {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = none) :
    ExecTransitionBody config contract evm (skimStore I) skimTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (by
    have hprefix :=
      uniswapSkimCachedFirstCallDecodeRevert evm evm0 I hwv hunlocked hguard0 hcall0 hdec0
    simpa [skimTransition, skimAfterLockBody, List.append_assoc] using
      (execBlock_append_term
        (s2 :=
          [ .letDecl "excess0" (some uint256)
              (u256 (.binary .sub (.var "balance0") (.storage reserve0Ref))) ] ++
          safeTransferStmts (.var "_token0") (.var "to") (.var "excess0") "ok0" "_ret0" ++
          balanceOfThisStmts (.var "_token1") "balance1" ++
          [ .letDecl "excess1" (some uint256)
              (u256 (.binary .sub (.var "balance1") (.storage reserve1Ref))) ] ++
          safeTransferStmts (.var "_token1") (.var "to") (.var "excess1") "ok1" "_ret1" ++
          lockExit)
        hprefix (by intro f e h; cases h)))

theorem uniswapSkimBodyReverts_secondCallFailure (evm evm0 evm1 evm2 : EVM.State)
    (I : ExecutionEnv) {out0 out1 : ByteArray} {balance0 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some (skimBalanceValue balance0))
    (henough0 : (uniswapReserve0Word evm0).toNat ≤ balance0.toNat)
    (hsafe0 :
      ExecStmt config
        { contract := contract, locals := skimFirstExcessStore evm evm0 I balance0 } evm0
        (.internalCall "_safeTransfer" [.var "_token0", .var "to", .var "excess0"] "ok0")
        (.ok { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 }
          evm1))
    (hguard1 :
      evalExpr? config
        { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 } evm1
        (.binary .gt (.extCodeSize (.var "_token1")) (.intLit 0)) = .ok (.bool true))
    (hcall1 : typedCallViaEVM config evm1
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩)) "balanceOf" 0
      [.address evm1.executionEnv.codeOwner] (false, evm2, out1) false) :
    ExecTransitionBody config contract evm (skimStore I) skimTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (by
    have hprefix :=
      uniswapSkimFirstSafeTransferPrefix evm evm0 evm1 I hwv hunlocked hguard0
        hcall0 hdec0 henough0 hsafe0
    have hsecond :
        ExecBlock config
          { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 } evm1
          (balanceOfThisStmts (.var "_token1") "balance1") .reverted := by
      exact uniswapCheckedExternalBalanceOfThisVarFailure
        (evm := evm1) (evm' := evm2)
        (locals := skimFirstSafeTransferStore evm evm0 I balance0)
        (receiver := "_token1") (retVar := "balance1")
        (target := uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩)
        hguard1
        (skimFirstSafeTransferStore_token1 evm evm0 I balance0)
        hcall1
    have hsecondWithRest := execBlock_append_term
      (s2 :=
        [ .letDecl "excess1" (some uint256)
            (u256 (.binary .sub (.var "balance1") (.storage reserve1Ref))) ] ++
        safeTransferStmts (.var "_token1") (.var "to") (.var "excess1") "ok1" "_ret1" ++
        lockExit)
      hsecond (by intro f e h; cases h)
    have hfail := execBlock_append hprefix hsecondWithRest
    simpa [skimTransition, skimAfterLockBody, List.append_assoc] using hfail)

theorem uniswapSkimBodyReverts_secondCallDecode (evm evm0 evm1 evm2 : EVM.State)
    (I : ExecutionEnv) {out0 out1 : ByteArray} {balance0 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some (skimBalanceValue balance0))
    (henough0 : (uniswapReserve0Word evm0).toNat ≤ balance0.toNat)
    (hsafe0 :
      ExecStmt config
        { contract := contract, locals := skimFirstExcessStore evm evm0 I balance0 } evm0
        (.internalCall "_safeTransfer" [.var "_token0", .var "to", .var "excess0"] "ok0")
        (.ok { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 }
          evm1))
    (hguard1 :
      evalExpr? config
        { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 } evm1
        (.binary .gt (.extCodeSize (.var "_token1")) (.intLit 0)) = .ok (.bool true))
    (hcall1 : typedCallViaEVM config evm1
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩)) "balanceOf" 0
      [.address evm1.executionEnv.codeOwner] (true, evm2, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = none) :
    ExecTransitionBody config contract evm (skimStore I) skimTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (by
    have hprefix :=
      uniswapSkimFirstSafeTransferPrefix evm evm0 evm1 I hwv hunlocked hguard0
        hcall0 hdec0 henough0 hsafe0
    have hsecond :
        ExecBlock config
          { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 } evm1
          (balanceOfThisStmts (.var "_token1") "balance1") .reverted := by
      exact uniswapCheckedExternalBalanceOfThisVarDecodeRevert
        (evm := evm1) (evm' := evm2)
        (locals := skimFirstSafeTransferStore evm evm0 I balance0)
        (receiver := "_token1") (retVar := "balance1")
        (target := uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩)
        hguard1
        (skimFirstSafeTransferStore_token1 evm evm0 I balance0)
        hcall1 hdec1
    have hsecondWithRest := execBlock_append_term
      (s2 :=
        [ .letDecl "excess1" (some uint256)
            (u256 (.binary .sub (.var "balance1") (.storage reserve1Ref))) ] ++
        safeTransferStmts (.var "_token1") (.var "to") (.var "excess1") "ok1" "_ret1" ++
        lockExit)
      hsecond (by intro f e h; cases h)
    have hfail := execBlock_append hprefix hsecondWithRest
    simpa [skimTransition, skimAfterLockBody, List.append_assoc] using hfail)

theorem uniswapSkimBodyReverts_firstSafeTransferFailure
    (evm evm0 evm1 : EVM.State) (I : ExecutionEnv)
    {out0 out1 calldata0 : ByteArray} {balance0 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some (skimBalanceValue balance0))
    (henough0 : (uniswapReserve0Word evm0).toNat ≤ balance0.toNat)
    (hdata0 :
      transferCalldata? (skimToAddress I) (skimExcess0Word evm0 balance0) = some calldata0)
    (htransfer0 : callViaEVM evm0
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩)) 0 calldata0
      (false, evm1, out1)) :
    ExecTransitionBody config contract evm (skimStore I) skimTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (by
    have hprefix :=
      uniswapSkimCachedFirstCallSuccess evm evm0 I hwv hunlocked hguard0 hcall0 hdec0
    have hexcess :
        ExecBlock config
          { contract := contract, locals := skimFirstBalanceStore evm I balance0 } evm0
          [ .letDecl "excess0" (some uint256)
              (u256 (.binary .sub (.var "balance0") (.storage reserve0Ref))) ]
          (.ok { contract := contract, locals := skimFirstExcessStore evm evm0 I balance0 }
            evm0) := by
      exact ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_skim_first_excess0 evm evm0 I balance0 henough0))
        ExecBlock.nil
    have hsafeStmt :
        ExecStmt config
          { contract := contract, locals := skimFirstExcessStore evm evm0 I balance0 } evm0
          (.internalCall "_safeTransfer" [.var "_token0", .var "to", .var "excess0"] "ok0")
          .reverted := by
      exact safeTransferInternalCallReverts_callFailure
        (caller := { contract := contract, locals := skimFirstExcessStore evm evm0 I balance0 })
        (evm := evm0) (evm' := evm1)
        (tokenExpr := .var "_token0") (toExpr := .var "to") (valueExpr := .var "excess0")
        (retVar := "ok0")
        (token := uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩)
        (recipient := skimToAddress I)
        (value := skimExcess0Word evm0 balance0)
        (calldata := calldata0) (out := out1)
        rfl
        (evalExprs_skim_safeTransfer0_args evm evm0 I balance0)
        hdata0 htransfer0
    have hsafe :
        ExecBlock config
          { contract := contract, locals := skimFirstExcessStore evm evm0 I balance0 } evm0
          (safeTransferStmts (.var "_token0") (.var "to") (.var "excess0") "ok0" "_ret0")
          .reverted := by
      change ExecBlock config
        { contract := contract, locals := skimFirstExcessStore evm evm0 I balance0 } evm0
        [ .internalCall "_safeTransfer" [.var "_token0", .var "to", .var "excess0"] "ok0" ]
        .reverted
      exact ExecBlock.consRevert hsafeStmt
    have hbeforeSafe := execBlock_append hprefix hexcess
    have hsafeWithRest := execBlock_append_term
      (s2 :=
        balanceOfThisStmts (.var "_token1") "balance1" ++
        [ .letDecl "excess1" (some uint256)
            (u256 (.binary .sub (.var "balance1") (.storage reserve1Ref))) ] ++
        safeTransferStmts (.var "_token1") (.var "to") (.var "excess1") "ok1" "_ret1" ++
        lockExit)
      hsafe (by intro f e h; cases h)
    have hfail := execBlock_append hbeforeSafe hsafeWithRest
    simpa [skimTransition, skimAfterLockBody, List.append_assoc] using hfail)

theorem uniswapSkimBodyReverts_secondSafeTransferFailure
    (evm evm0 evm1 evm2 evm3 : EVM.State) (I : ExecutionEnv)
    {out0 out1 calldata1 out2 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some (skimBalanceValue balance0))
    (henough0 : (uniswapReserve0Word evm0).toNat ≤ balance0.toNat)
    (hsafe0 :
      ExecStmt config
        { contract := contract, locals := skimFirstExcessStore evm evm0 I balance0 } evm0
        (.internalCall "_safeTransfer" [.var "_token0", .var "to", .var "excess0"] "ok0")
        (.ok { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 }
          evm1))
    (hguard1 :
      evalExpr? config
        { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 } evm1
        (.binary .gt (.extCodeSize (.var "_token1")) (.intLit 0)) = .ok (.bool true))
    (hcall1 : typedCallViaEVM config evm1
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩)) "balanceOf" 0
      [.address evm1.executionEnv.codeOwner] (true, evm2, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some (skimBalanceValue balance1))
    (henough1 : (uniswapReserve1Word evm2).toNat ≤ balance1.toNat)
    (hdata1 :
      transferCalldata? (skimToAddress I) (skimExcess1Word evm2 balance1) = some calldata1)
    (htransfer1 : callViaEVM evm2
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩)) 0 calldata1
      (false, evm3, out2)) :
    ExecTransitionBody config contract evm (skimStore I) skimTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (by
    have hprefix :=
      uniswapSkimFirstSafeTransferPrefix evm evm0 evm1 I hwv hunlocked hguard0
        hcall0 hdec0 henough0 hsafe0
    have hsecond :
        ExecBlock config
          { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 } evm1
          (balanceOfThisStmts (.var "_token1") "balance1")
          (.ok
            { contract := contract,
              locals := skimSecondBalanceStore evm evm0 I balance0 balance1 }
            evm2) := by
      exact uniswapCheckedExternalBalanceOfThisVarSuccess
        (evm := evm1) (evm' := evm2)
        (locals := skimFirstSafeTransferStore evm evm0 I balance0)
        (receiver := "_token1") (retVar := "balance1")
        (target := uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩)
        (value := skimBalanceValue balance1)
        hguard1
        (skimFirstSafeTransferStore_token1 evm evm0 I balance0)
        hcall1 hdec1
    have hexcess :
        ExecBlock config
          { contract := contract,
            locals := skimSecondBalanceStore evm evm0 I balance0 balance1 } evm2
          [ .letDecl "excess1" (some uint256)
              (u256 (.binary .sub (.var "balance1") (.storage reserve1Ref))) ]
          (.ok
            { contract := contract,
              locals := skimSecondExcessStore evm evm0 evm2 I balance0 balance1 }
            evm2) := by
      exact ExecBlock.consNormal
        (ExecStmt.letDecl
          (evalExpr_skim_second_excess1 evm evm0 evm2 I balance0 balance1 henough1))
        ExecBlock.nil
    have hsafeStmt :
        ExecStmt config
          { contract := contract,
            locals := skimSecondExcessStore evm evm0 evm2 I balance0 balance1 } evm2
          (.internalCall "_safeTransfer" [.var "_token1", .var "to", .var "excess1"] "ok1")
          .reverted := by
      exact safeTransferInternalCallReverts_callFailure
        (caller :=
          { contract := contract,
            locals := skimSecondExcessStore evm evm0 evm2 I balance0 balance1 })
        (evm := evm2) (evm' := evm3)
        (tokenExpr := .var "_token1") (toExpr := .var "to") (valueExpr := .var "excess1")
        (retVar := "ok1")
        (token := uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩)
        (recipient := skimToAddress I)
        (value := skimExcess1Word evm2 balance1)
        (calldata := calldata1) (out := out2)
        rfl
        (evalExprs_skim_safeTransfer1_args evm evm0 evm2 I balance0 balance1)
        hdata1 htransfer1
    have hsafe :
        ExecBlock config
          { contract := contract,
            locals := skimSecondExcessStore evm evm0 evm2 I balance0 balance1 } evm2
          (safeTransferStmts (.var "_token1") (.var "to") (.var "excess1") "ok1" "_ret1")
          .reverted := by
      change ExecBlock config
        { contract := contract,
          locals := skimSecondExcessStore evm evm0 evm2 I balance0 balance1 } evm2
        [ .internalCall "_safeTransfer" [.var "_token1", .var "to", .var "excess1"] "ok1" ]
        .reverted
      exact ExecBlock.consRevert hsafeStmt
    have hthroughSecond := execBlock_append hprefix hsecond
    have hthroughExcess := execBlock_append hthroughSecond hexcess
    have hsafeWithRest := execBlock_append_term (s2 := lockExit) hsafe
      (by intro f e h; cases h)
    have hfail := execBlock_append hthroughExcess hsafeWithRest
    simpa [skimTransition, skimAfterLockBody, List.append_assoc] using hfail)

theorem uniswapSkimBodyReturns (evm evm0 evm1 evm2 evm3 : EVM.State)
    (I : ExecutionEnv) {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some (skimBalanceValue balance0))
    (henough0 : (uniswapReserve0Word evm0).toNat ≤ balance0.toNat)
    (hsafe0 :
      ExecStmt config
        { contract := contract, locals := skimFirstExcessStore evm evm0 I balance0 } evm0
        (.internalCall "_safeTransfer" [.var "_token0", .var "to", .var "excess0"] "ok0")
        (.ok { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 }
          evm1))
    (hguard1 :
      evalExpr? config
        { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 } evm1
        (.binary .gt (.extCodeSize (.var "_token1")) (.intLit 0)) = .ok (.bool true))
    (hcall1 : typedCallViaEVM config evm1
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩)) "balanceOf" 0
      [.address evm1.executionEnv.codeOwner] (true, evm2, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some (skimBalanceValue balance1))
    (henough1 : (uniswapReserve1Word evm2).toNat ≤ balance1.toNat)
    (hsafe1 :
      ExecStmt config
        { contract := contract,
          locals := skimSecondExcessStore evm evm0 evm2 I balance0 balance1 } evm2
        (.internalCall "_safeTransfer" [.var "_token1", .var "to", .var "excess1"] "ok1")
        (.ok
          { contract := contract,
            locals := skimSecondSafeTransferStore evm evm0 evm2 I balance0 balance1 }
          evm3)) :
    ExecTransitionBody config contract evm (skimStore I) skimTransition.body
      (.returned
        { contract := contract,
          locals := skimSecondSafeTransferStore evm evm0 evm2 I balance0 balance1 }
        (uniswapLockExitedState evm3) none) := by
  exact ExecFuncBody.execBlockOK (by
    have hprefix :=
      uniswapSkimFirstSafeTransferPrefix evm evm0 evm1 I hwv hunlocked hguard0
        hcall0 hdec0 henough0 hsafe0
    have hsecond :
        ExecBlock config
          { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 } evm1
          (balanceOfThisStmts (.var "_token1") "balance1")
          (.ok
            { contract := contract,
              locals := skimSecondBalanceStore evm evm0 I balance0 balance1 }
            evm2) := by
      exact uniswapCheckedExternalBalanceOfThisVarSuccess
        (evm := evm1) (evm' := evm2)
        (locals := skimFirstSafeTransferStore evm evm0 I balance0)
        (receiver := "_token1") (retVar := "balance1")
        (target := uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩)
        (value := skimBalanceValue balance1)
        hguard1
        (skimFirstSafeTransferStore_token1 evm evm0 I balance0)
        hcall1 hdec1
    have hexcess :
        ExecBlock config
          { contract := contract,
            locals := skimSecondBalanceStore evm evm0 I balance0 balance1 } evm2
          [ .letDecl "excess1" (some uint256)
              (u256 (.binary .sub (.var "balance1") (.storage reserve1Ref))) ]
          (.ok
            { contract := contract,
              locals := skimSecondExcessStore evm evm0 evm2 I balance0 balance1 }
            evm2) := by
      exact ExecBlock.consNormal
        (ExecStmt.letDecl
          (evalExpr_skim_second_excess1 evm evm0 evm2 I balance0 balance1 henough1))
        ExecBlock.nil
    have hsafe :
        ExecBlock config
          { contract := contract,
            locals := skimSecondExcessStore evm evm0 evm2 I balance0 balance1 } evm2
          (safeTransferStmts (.var "_token1") (.var "to") (.var "excess1") "ok1" "_ret1")
          (.ok
            { contract := contract,
              locals := skimSecondSafeTransferStore evm evm0 evm2 I balance0 balance1 }
            evm3) := by
      change ExecBlock config
        { contract := contract,
          locals := skimSecondExcessStore evm evm0 evm2 I balance0 balance1 } evm2
        [ .internalCall "_safeTransfer" [.var "_token1", .var "to", .var "excess1"] "ok1" ]
        (.ok
          { contract := contract,
            locals := skimSecondSafeTransferStore evm evm0 evm2 I balance0 balance1 }
          evm3)
      exact ExecBlock.consNormal hsafe1 ExecBlock.nil
    have hlock :
        ExecBlock config
          { contract := contract,
            locals := skimSecondSafeTransferStore evm evm0 evm2 I balance0 balance1 } evm3
          lockExit
          (.ok
            { contract := contract,
              locals := skimSecondSafeTransferStore evm evm0 evm2 I balance0 balance1 }
            (uniswapLockExitedState evm3)) := by
      exact uniswapLockExitSuffix evm3
        (skimSecondSafeTransferStore evm evm0 evm2 I balance0 balance1)
        (by
          simp [skimSecondSafeTransferStore, skimSecondExcessStore, skimSecondBalanceStore,
            skimFirstSafeTransferStore, skimFirstExcessStore, skimFirstBalanceStore,
            skimTokenStore, skimStore])
    have hthroughSecond := execBlock_append hprefix hsecond
    have hthroughExcess := execBlock_append hthroughSecond hexcess
    have hthroughSafe := execBlock_append hthroughExcess hsafe
    have hdone := execBlock_append hthroughSafe hlock
    simpa [skimTransition, skimAfterLockBody, List.append_assoc] using hdone)

end UniswapV2Pair
