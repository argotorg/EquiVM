import Examples.UniswapV2Pair.MintSourceReturns

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
theorem evalExpr_mint_amount0_of_get
    {locals : Store} (reserveEvm callEvm : EVM.State) (balance0 : UInt256)
    (hbalance : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hreserve :
      locals.get? "_reserve0" =
        some (.int (Int.ofNat (uniswapReserve0Word reserveEvm).toNat)))
    (henough : (uniswapReserve0Word reserveEvm).toNat ≤ balance0.toNat) :
    evalExpr? config { contract := contract, locals := locals } callEvm
      (u256 (.binary .sub (.var "balance0") (.var "_reserve0"))) =
        .ok (mintAmount0Value reserveEvm balance0) := by
  have hsub :
      Int.ofNat balance0.toNat - Int.ofNat (uniswapReserve0Word reserveEvm).toNat =
        Int.ofNat (balance0.toNat - (uniswapReserve0Word reserveEvm).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat :
      (mintAmount0Word reserveEvm balance0).toNat =
        balance0.toNat - (uniswapReserve0Word reserveEvm).toNat := by
    exact usub_toNat henough
  have hfit : balance0.toNat - (uniswapReserve0Word reserveEvm).toNat < UInt256.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) balance0.val.isLt
  have hnotHigh :
      ¬ Int.ofNat (balance0.toNat - (uniswapReserve0Word reserveEvm).toNat) ≥
        (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  simp only [u256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [hbalance, hreserve]
  simp [evalBinaryOp?, mintAmount0Value, mintAmount0Word, uniswapUint256Value,
    uint256Value, uint256Int]
  rw [if_neg]
  · have hval :
        (balance0.toNat : Int) - ((uniswapReserve0Word reserveEvm).toNat : Int) =
          ((UInt256.sub balance0 (uniswapReserve0Word reserveEvm)).toNat : Int) := by
      calc
        (balance0.toNat : Int) - ((uniswapReserve0Word reserveEvm).toNat : Int)
            = Int.ofNat (balance0.toNat - (uniswapReserve0Word reserveEvm).toNat) := hsub
        _ = Int.ofNat (mintAmount0Word reserveEvm balance0).toNat := by rw [← htoNat]
        _ = ((UInt256.sub balance0 (uniswapReserve0Word reserveEvm)).toNat : Int) := by
          rfl
    rw [hval]
  · intro hbad
    rcases hbad with hlow | hhigh
    · omega
    · exact hnotHigh (by
        rw [← hsub]
        exact hhigh)

set_option maxHeartbeats 1000000 in
theorem evalExpr_mint_amount1_of_get
    {locals : Store} (reserveEvm callEvm : EVM.State) (balance1 : UInt256)
    (hbalance : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve :
      locals.get? "_reserve1" =
        some (.int (Int.ofNat (uniswapReserve1Word reserveEvm).toNat)))
    (henough : (uniswapReserve1Word reserveEvm).toNat ≤ balance1.toNat) :
    evalExpr? config { contract := contract, locals := locals } callEvm
      (u256 (.binary .sub (.var "balance1") (.var "_reserve1"))) =
        .ok (mintAmount1Value reserveEvm balance1) := by
  have hsub :
      Int.ofNat balance1.toNat - Int.ofNat (uniswapReserve1Word reserveEvm).toNat =
        Int.ofNat (balance1.toNat - (uniswapReserve1Word reserveEvm).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat :
      (mintAmount1Word reserveEvm balance1).toNat =
        balance1.toNat - (uniswapReserve1Word reserveEvm).toNat := by
    exact usub_toNat henough
  have hfit : balance1.toNat - (uniswapReserve1Word reserveEvm).toNat < UInt256.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) balance1.val.isLt
  have hnotHigh :
      ¬ Int.ofNat (balance1.toNat - (uniswapReserve1Word reserveEvm).toNat) ≥
        (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  simp only [u256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [hbalance, hreserve]
  simp [evalBinaryOp?, mintAmount1Value, mintAmount1Word, uniswapUint256Value,
    uint256Value, uint256Int]
  rw [if_neg]
  · have hval :
        (balance1.toNat : Int) - ((uniswapReserve1Word reserveEvm).toNat : Int) =
          ((UInt256.sub balance1 (uniswapReserve1Word reserveEvm)).toNat : Int) := by
      calc
        (balance1.toNat : Int) - ((uniswapReserve1Word reserveEvm).toNat : Int)
            = Int.ofNat (balance1.toNat - (uniswapReserve1Word reserveEvm).toNat) := hsub
        _ = Int.ofNat (mintAmount1Word reserveEvm balance1).toNat := by rw [← htoNat]
        _ = ((UInt256.sub balance1 (uniswapReserve1Word reserveEvm)).toNat : Int) := by
          rfl
    rw [hval]
  · intro hbad
    rcases hbad with hlow | hhigh
    · omega
    · exact hnotHigh (by
        rw [← hsub]
        exact hhigh)

theorem evalExpr_mint_amount0_underflow
    (reserveEvm callEvm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256)
    (hlt : balance0.toNat < (uniswapReserve0Word reserveEvm).toNat) :
    evalExpr? config { contract := contract, locals := mintBalanceStore reserveEvm I balance0 balance1 }
      callEvm (u256 (.binary .sub (.var "balance0") (.var "_reserve0"))) = .revert := by
  have hneg :
      Int.ofNat balance0.toNat - Int.ofNat (uniswapReserve0Word reserveEvm).toNat < 0 := by
    change (balance0.toNat : Int) - ((uniswapReserve0Word reserveEvm).toNat : Int) < 0
    omega
  simp only [u256, evalExpr?, EvalResult.ofOption, mintBalanceStore_balance0,
    mintBalanceStore_reserve0, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  change
    (if Int.ofNat balance0.toNat - Int.ofNat (uniswapReserve0Word reserveEvm).toNat < 0 ||
        Int.ofNat balance0.toNat - Int.ofNat (uniswapReserve0Word reserveEvm).toNat ≥
          (2 : Int) ^ 256 then
       EvalResult.revert
     else
      EvalResult.ok
        (Value.int
          (Int.ofNat balance0.toNat - Int.ofNat (uniswapReserve0Word reserveEvm).toNat))) =
      EvalResult.revert
  have hcond :
      (decide
          (Int.ofNat balance0.toNat -
              Int.ofNat (uniswapReserve0Word reserveEvm).toNat < 0) ||
        decide
          (Int.ofNat balance0.toNat -
              Int.ofNat (uniswapReserve0Word reserveEvm).toNat ≥ (2 : Int) ^ 256)) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl hneg
  rw [if_pos hcond]

theorem evalExpr_mint_amount1_underflow
    (reserveEvm callEvm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256)
    (hlt : balance1.toNat < (uniswapReserve1Word reserveEvm).toNat) :
    evalExpr? config { contract := contract, locals := mintAmount0Store reserveEvm I balance0 balance1 }
      callEvm (u256 (.binary .sub (.var "balance1") (.var "_reserve1"))) = .revert := by
  have hneg :
      Int.ofNat balance1.toNat - Int.ofNat (uniswapReserve1Word reserveEvm).toNat < 0 := by
    change (balance1.toNat : Int) - ((uniswapReserve1Word reserveEvm).toNat : Int) < 0
    omega
  simp only [u256, evalExpr?, EvalResult.ofOption, mintAmount0Store_balance1,
    mintAmount0Store_reserve1, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  change
    (if Int.ofNat balance1.toNat - Int.ofNat (uniswapReserve1Word reserveEvm).toNat < 0 ||
        Int.ofNat balance1.toNat - Int.ofNat (uniswapReserve1Word reserveEvm).toNat ≥
          (2 : Int) ^ 256 then
       EvalResult.revert
     else
      EvalResult.ok
        (Value.int
          (Int.ofNat balance1.toNat - Int.ofNat (uniswapReserve1Word reserveEvm).toNat))) =
      EvalResult.revert
  have hcond :
      (decide
          (Int.ofNat balance1.toNat -
              Int.ofNat (uniswapReserve1Word reserveEvm).toNat < 0) ||
        decide
          (Int.ofNat balance1.toNat -
              Int.ofNat (uniswapReserve1Word reserveEvm).toNat ≥ (2 : Int) ^ 256)) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl hneg
  rw [if_pos hcond]

theorem uniswapMintBalanceCallsPrefix
    (evm evm0 evm1 : EVM.State) (I : ExecutionEnv)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1)) :
    ExecBlock config { contract := contract, locals := mintStore I } evm
      (lockEnter ++
        [ .letDecl "_reserve0" (some uint112) (.storage reserve0Ref),
          .letDecl "_reserve1" (some uint112) (.storage reserve1Ref) ] ++
        pairBalanceOfThisStmts "balance0" "balance1")
      (.ok { contract := contract, locals :=
        mintBalanceStore (uniswapLockEnteredState evm) I balance0 balance1 } evm1) := by
  let evmL := uniswapLockEnteredState evm
  have hprefix := uniswapMintReservePrefix evm I hwv hunlocked
  have hbalances :
      ExecBlock config { contract := contract, locals := mintReserveStore evmL I } evmL
        (pairBalanceOfThisStmts "balance0" "balance1")
        (.ok { contract := contract, locals := mintBalanceStore evmL I balance0 balance1 }
          evm1) := by
    simpa [mintBalanceStore, evmL] using
      uniswapCheckedTokenBalanceOfThisCallsPrefix evmL evm0 evm1 (mintReserveStore evmL I)
        hguard0 hguard1
        (by simp [mintReserveStore, mintStore])
        (by simp [mintReserveStore, mintStore])
        hcall0 hdec0 hcall1 hdec1
  simpa [evmL, List.append_assoc] using execBlock_append hprefix hbalances

theorem uniswapMintBodyReverts_firstNoCode (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool false)) :
    ExecTransitionBody config contract evm (mintStore I) mintTransition.body .reverted := by
  let evmL := uniswapLockEnteredState evm
  have hprefix := uniswapMintReservePrefix evm I hwv hunlocked
  have hfail :
      ExecBlock config { contract := contract, locals := mintReserveStore evmL I } evmL
        (pairBalanceOfThisStmts "balance0" "balance1") .reverted := by
    exact uniswapCheckedTokenBalanceOfThisFirstCallNoCode
      (evm := evmL) (locals := mintReserveStore evmL I) hguard0
  have hthrough := execBlock_append hprefix hfail
  exact ExecFuncBody.execBlockRevert (by
    simpa [mintTransition, evmL, List.append_assoc] using
      (execBlock_append_term hthrough (by intro f e h; cases h)))

theorem uniswapMintBodyReverts_firstCallFailure (evm evm0 : EVM.State) (I : ExecutionEnv)
    {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (false, evm0, out0) false) :
    ExecTransitionBody config contract evm (mintStore I) mintTransition.body .reverted := by
  let evmL := uniswapLockEnteredState evm
  have hprefix := uniswapMintReservePrefix evm I hwv hunlocked
  have hfail :
      ExecBlock config { contract := contract, locals := mintReserveStore evmL I } evmL
        (pairBalanceOfThisStmts "balance0" "balance1") .reverted := by
    exact uniswapCheckedTokenBalanceOfThisFirstCallFailure
      (evm := evmL) (evm0 := evm0) (locals := mintReserveStore evmL I)
      hguard0 (by simp [mintReserveStore, mintStore]) hcall0
  have hthrough := execBlock_append hprefix hfail
  exact ExecFuncBody.execBlockRevert (by
    simpa [mintTransition, evmL, List.append_assoc] using
      (execBlock_append_term hthrough (by intro f e h; cases h)))

theorem uniswapMintBodyReverts_firstCallDecode (evm evm0 : EVM.State) (I : ExecutionEnv)
    {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = none) :
    ExecTransitionBody config contract evm (mintStore I) mintTransition.body .reverted := by
  let evmL := uniswapLockEnteredState evm
  have hprefix := uniswapMintReservePrefix evm I hwv hunlocked
  have hfail :
      ExecBlock config { contract := contract, locals := mintReserveStore evmL I } evmL
        (pairBalanceOfThisStmts "balance0" "balance1") .reverted := by
    exact uniswapCheckedTokenBalanceOfThisFirstCallDecodeRevert
      (evm := evmL) (evm0 := evm0) (locals := mintReserveStore evmL I)
      hguard0 (by simp [mintReserveStore, mintStore]) hcall0 hdec0
  have hthrough := execBlock_append hprefix hfail
  exact ExecFuncBody.execBlockRevert (by
    simpa [mintTransition, evmL, List.append_assoc] using
      (execBlock_append_term hthrough (by intro f e h; cases h)))

theorem uniswapMintBodyReverts_secondNoCode (evm evm0 : EVM.State) (I : ExecutionEnv)
    {out0 : ByteArray} {balance0 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals :=
            (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
              (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool false)) :
    ExecTransitionBody config contract evm (mintStore I) mintTransition.body .reverted := by
  let evmL := uniswapLockEnteredState evm
  have hprefix := uniswapMintReservePrefix evm I hwv hunlocked
  have hfail :
      ExecBlock config { contract := contract, locals := mintReserveStore evmL I } evmL
        (pairBalanceOfThisStmts "balance0" "balance1") .reverted := by
    exact uniswapCheckedTokenBalanceOfThisSecondCallNoCode
      (evm := evmL) (evm0 := evm0) (locals := mintReserveStore evmL I)
      (balance0 := uniswapUint256Value balance0)
      hguard0 hguard1 (by simp [mintReserveStore, mintStore]) hcall0 hdec0
  have hthrough := execBlock_append hprefix hfail
  exact ExecFuncBody.execBlockRevert (by
    simpa [mintTransition, evmL, List.append_assoc] using
      (execBlock_append_term hthrough (by intro f e h; cases h)))

theorem uniswapMintBodyReverts_secondCallFailure
    (evm evm0 evm1 : EVM.State) (I : ExecutionEnv)
    {out0 out1 : ByteArray} {balance0 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals :=
            (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
              (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (false, evm1, out1) false) :
    ExecTransitionBody config contract evm (mintStore I) mintTransition.body .reverted := by
  let evmL := uniswapLockEnteredState evm
  have hprefix := uniswapMintReservePrefix evm I hwv hunlocked
  have hfail :
      ExecBlock config { contract := contract, locals := mintReserveStore evmL I } evmL
        (pairBalanceOfThisStmts "balance0" "balance1") .reverted := by
    exact uniswapCheckedTokenBalanceOfThisSecondCallFailure
      (evm := evmL) (evm0 := evm0) (evm1 := evm1) (locals := mintReserveStore evmL I)
      (balance0 := uniswapUint256Value balance0)
      hguard0 hguard1
      (by simp [mintReserveStore, mintStore])
      (by simp [mintReserveStore, mintStore])
      hcall0 hdec0 hcall1
  have hthrough := execBlock_append hprefix hfail
  exact ExecFuncBody.execBlockRevert (by
    simpa [mintTransition, evmL, List.append_assoc] using
      (execBlock_append_term hthrough (by intro f e h; cases h)))

theorem uniswapMintBodyReverts_secondCallDecode
    (evm evm0 evm1 : EVM.State) (I : ExecutionEnv)
    {out0 out1 : ByteArray} {balance0 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals :=
            (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
              (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = none) :
    ExecTransitionBody config contract evm (mintStore I) mintTransition.body .reverted := by
  let evmL := uniswapLockEnteredState evm
  have hprefix := uniswapMintReservePrefix evm I hwv hunlocked
  have hfail :
      ExecBlock config { contract := contract, locals := mintReserveStore evmL I } evmL
        (pairBalanceOfThisStmts "balance0" "balance1") .reverted := by
    exact uniswapCheckedTokenBalanceOfThisSecondCallDecodeRevert
      (evm := evmL) (evm0 := evm0) (evm1 := evm1) (locals := mintReserveStore evmL I)
      (balance0 := uniswapUint256Value balance0)
      hguard0 hguard1
      (by simp [mintReserveStore, mintStore])
      (by simp [mintReserveStore, mintStore])
      hcall0 hdec0 hcall1 hdec1
  have hthrough := execBlock_append hprefix hfail
  exact ExecFuncBody.execBlockRevert (by
    simpa [mintTransition, evmL, List.append_assoc] using
      (execBlock_append_term hthrough (by intro f e h; cases h)))

theorem uniswapMintBodyReverts_amount0Underflow
    (evm evm0 evm1 : EVM.State) (I : ExecutionEnv)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (hlt0 : balance0.toNat < (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat) :
    ExecTransitionBody config contract evm (mintStore I) mintTransition.body .reverted := by
  let evmL := uniswapLockEnteredState evm
  have hprefix :=
    uniswapMintBalanceCallsPrefix evm evm0 evm1 I hwv hunlocked hguard0 hguard1 hcall0
      hdec0 hcall1 hdec1
  have hamount0 :
      ExecBlock config
        { contract := contract, locals := mintBalanceStore evmL I balance0 balance1 } evm1
        [ .letDecl "amount0" (some uint256)
            (u256 (.binary .sub (.var "balance0") (.var "_reserve0"))) ]
        .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.letDeclRevert
        (evalExpr_mint_amount0_underflow evmL evm1 I balance0 balance1
          (by simpa [evmL] using hlt0)))
  have hthrough := execBlock_append hprefix hamount0
  exact ExecFuncBody.execBlockRevert (by
    simpa [mintTransition, evmL, List.append_assoc] using
      (execBlock_append_term hthrough (by intro f e h; cases h)))

theorem uniswapMintBodyReverts_amount1Underflow
    (evm evm0 evm1 : EVM.State) (I : ExecutionEnv)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (hlt1 : balance1.toNat < (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat) :
    ExecTransitionBody config contract evm (mintStore I) mintTransition.body .reverted := by
  let evmL := uniswapLockEnteredState evm
  have hprefix :=
    uniswapMintBalanceCallsPrefix evm evm0 evm1 I hwv hunlocked hguard0 hguard1 hcall0
      hdec0 hcall1 hdec1
  have hamount0 :
      ExecBlock config
        { contract := contract, locals := mintBalanceStore evmL I balance0 balance1 } evm1
        [ .letDecl "amount0" (some uint256)
            (u256 (.binary .sub (.var "balance0") (.var "_reserve0"))) ]
        (.ok { contract := contract, locals := mintAmount0Store evmL I balance0 balance1 }
          evm1) := by
    exact ExecBlock.consNormal
      (ExecStmt.letDecl
        (evalExpr_mint_amount0_of_get evmL evm1 balance0
          (mintBalanceStore_balance0 evmL I balance0 balance1)
          (mintBalanceStore_reserve0 evmL I balance0 balance1)
          (by simpa [evmL] using henough0)))
      ExecBlock.nil
  have hamount1 :
      ExecBlock config
        { contract := contract, locals := mintAmount0Store evmL I balance0 balance1 } evm1
        [ .letDecl "amount1" (some uint256)
            (u256 (.binary .sub (.var "balance1") (.var "_reserve1"))) ]
        .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.letDeclRevert
        (evalExpr_mint_amount1_underflow evmL evm1 I balance0 balance1
          (by simpa [evmL] using hlt1)))
  have hthrough0 := execBlock_append hprefix hamount0
  have hthrough1 := execBlock_append hthrough0 hamount1
  exact ExecFuncBody.execBlockRevert (by
    simpa [mintTransition, evmL, List.append_assoc] using
      (execBlock_append_term hthrough1 (by intro f e h; cases h)))

theorem uniswapMintAmountsPrefix
    (evm evm0 evm1 : EVM.State) (I : ExecutionEnv)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat) :
    ExecBlock config { contract := contract, locals := mintStore I } evm
      (lockEnter ++
        [ .letDecl "_reserve0" (some uint112) (.storage reserve0Ref),
          .letDecl "_reserve1" (some uint112) (.storage reserve1Ref) ] ++
        pairBalanceOfThisStmts "balance0" "balance1" ++
        [ .letDecl "amount0" (some uint256)
            (u256 (.binary .sub (.var "balance0") (.var "_reserve0"))),
          .letDecl "amount1" (some uint256)
            (u256 (.binary .sub (.var "balance1") (.var "_reserve1"))) ])
      (.ok { contract := contract, locals :=
        mintAmountStore (uniswapLockEnteredState evm) I balance0 balance1 } evm1) := by
  let evmL := uniswapLockEnteredState evm
  have hprefix :=
    uniswapMintBalanceCallsPrefix evm evm0 evm1 I hwv hunlocked hguard0 hguard1 hcall0
      hdec0 hcall1 hdec1
  have hamount0 :
      ExecBlock config
        { contract := contract, locals := mintBalanceStore evmL I balance0 balance1 } evm1
        [ .letDecl "amount0" (some uint256)
            (u256 (.binary .sub (.var "balance0") (.var "_reserve0"))) ]
        (.ok { contract := contract, locals := mintAmount0Store evmL I balance0 balance1 }
          evm1) := by
    exact ExecBlock.consNormal
      (ExecStmt.letDecl
        (evalExpr_mint_amount0_of_get evmL evm1 balance0
          (mintBalanceStore_balance0 evmL I balance0 balance1)
          (mintBalanceStore_reserve0 evmL I balance0 balance1)
          (by simpa [evmL] using henough0)))
      ExecBlock.nil
  have hamount1 :
      ExecBlock config
        { contract := contract, locals := mintAmount0Store evmL I balance0 balance1 } evm1
        [ .letDecl "amount1" (some uint256)
            (u256 (.binary .sub (.var "balance1") (.var "_reserve1"))) ]
        (.ok { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
          evm1) := by
    exact ExecBlock.consNormal
      (ExecStmt.letDecl
        (evalExpr_mint_amount1_of_get evmL evm1 balance1
          (mintAmount0Store_balance1 evmL I balance0 balance1)
          (mintAmount0Store_reserve1 evmL I balance0 balance1)
          (by simpa [evmL] using henough1)))
      ExecBlock.nil
  have hthrough0 := execBlock_append hprefix hamount0
  have hthrough1 := execBlock_append hthrough0 hamount1
  simpa [evmL, List.append_assoc] using hthrough1

theorem uniswapMintBodyReverts_mintFeeNoCode
    (evm evm0 evm1 : EVM.State) (I : ExecutionEnv)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
          (uniswapReserve1Word (uniswapLockEnteredState evm)))
        evm1 (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool false)) :
    ExecTransitionBody config contract evm (mintStore I) mintTransition.body .reverted := by
  let evmL := uniswapLockEnteredState evm
  have hprefix :=
    uniswapMintAmountsPrefix evm evm0 evm1 I hwv hunlocked hguard0 hguard1 hcall0 hdec0
      hcall1 hdec1 henough0 henough1
  have hfee :
      ExecBlock config
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 } evm1
        [ .internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn" ]
        .reverted := by
    exact ExecBlock.consRevert
      (uniswapMintFeeCallFromMint_noCode evmL evm1 I balance0 balance1
        (by simpa [evmL] using hfeeGuard))
  have hthrough := execBlock_append hprefix hfee
  exact ExecFuncBody.execBlockRevert (by
    simpa [mintTransition, evmL, List.append_assoc] using
      (execBlock_append_term hthrough (by intro f e h; cases h)))

theorem uniswapMintBodyReverts_mintFeeCallFailure
    (evm evm0 evm1 evmFee : EVM.State) (I : ExecutionEnv)
    {out0 out1 outFee : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
          (uniswapReserve1Word (uniswapLockEnteredState evm)))
        evm1 (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1 (EVM.address (uniswapAddressAtSlot evm1 ⟨5⟩))
      "feeTo" 0 [] (false, evmFee, outFee) false) :
    ExecTransitionBody config contract evm (mintStore I) mintTransition.body .reverted := by
  let evmL := uniswapLockEnteredState evm
  have hprefix :=
    uniswapMintAmountsPrefix evm evm0 evm1 I hwv hunlocked hguard0 hguard1 hcall0 hdec0
      hcall1 hdec1 henough0 henough1
  have hfee :
      ExecBlock config
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 } evm1
        [ .internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn" ]
        .reverted := by
    exact ExecBlock.consRevert
      (uniswapMintFeeCallFromMint_callFailure evmL evm1 evmFee I balance0 balance1
        (by simpa [evmL] using hfeeGuard) hfeeCall)
  have hthrough := execBlock_append hprefix hfee
  exact ExecFuncBody.execBlockRevert (by
    simpa [mintTransition, evmL, List.append_assoc] using
      (execBlock_append_term hthrough (by intro f e h; cases h)))

theorem uniswapMintBodyReverts_mintFeeDecode
    (evm evm0 evm1 evmFee : EVM.State) (I : ExecutionEnv)
    {out0 out1 outFee : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
          (uniswapReserve1Word (uniswapLockEnteredState evm)))
        evm1 (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1 (EVM.address (uniswapAddressAtSlot evm1 ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = none) :
    ExecTransitionBody config contract evm (mintStore I) mintTransition.body .reverted := by
  let evmL := uniswapLockEnteredState evm
  have hprefix :=
    uniswapMintAmountsPrefix evm evm0 evm1 I hwv hunlocked hguard0 hguard1 hcall0 hdec0
      hcall1 hdec1 henough0 henough1
  have hfee :
      ExecBlock config
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 } evm1
        [ .internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn" ]
        .reverted := by
    exact ExecBlock.consRevert
      (uniswapMintFeeCallFromMint_decodeRevert evmL evm1 evmFee I balance0 balance1
        (by simpa [evmL] using hfeeGuard) hfeeCall hfeeDec)
  have hthrough := execBlock_append hprefix hfee
  exact ExecFuncBody.execBlockRevert (by
    simpa [mintTransition, evmL, List.append_assoc] using
      (execBlock_append_term hthrough (by intro f e h; cases h)))

theorem uniswapMintAfterMintFeePrefix_feeOff_kLastZero
    (evm evm0 evm1 evmFee : EVM.State) (I : ExecutionEnv)
    {out0 out1 outFee : ByteArray} {balance0 balance1 : UInt256} (feeTo : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
          (uniswapReserve1Word (uniswapLockEnteredState evm)))
        evm1 (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1 (EVM.address (uniswapAddressAtSlot evm1 ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeTo : feeTo = AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat = 0) :
    ExecBlock config { contract := contract, locals := mintStore I } evm
      (lockEnter ++
        [ .letDecl "_reserve0" (some uint112) (.storage reserve0Ref),
          .letDecl "_reserve1" (some uint112) (.storage reserve1Ref) ] ++
        pairBalanceOfThisStmts "balance0" "balance1" ++
        [ .letDecl "amount0" (some uint256)
            (u256 (.binary .sub (.var "balance0") (.var "_reserve0"))),
          .letDecl "amount1" (some uint256)
            (u256 (.binary .sub (.var "balance1") (.var "_reserve1"))),
          .internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn" ])
      (.ok
        (resumeAfterInternalCall
          { contract := contract,
            locals := mintAmountStore (uniswapLockEnteredState evm) I balance0 balance1 }
          "feeOn" (some (.bool false)))
        evmFee) := by
  let evmL := uniswapLockEnteredState evm
  have hprefix :=
    uniswapMintAmountsPrefix evm evm0 evm1 I hwv hunlocked hguard0 hguard1 hcall0 hdec0
      hcall1 hdec1 henough0 henough1
  have hfee :
      ExecBlock config
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 } evm1
        [ .internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn" ]
        (.ok
          (resumeAfterInternalCall
            { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
            "feeOn" (some (.bool false)))
          evmFee) := by
    exact ExecBlock.consNormal
      (uniswapMintFeeCallFromMint_feeOff_kLastZero evmL evm1 evmFee I balance0 balance1 feeTo
        (by simpa [evmL] using hfeeGuard) hfeeCall hfeeDec hfeeTo hkLast)
      ExecBlock.nil
  simpa [evmL, List.append_assoc] using execBlock_append hprefix hfee

theorem uniswapMintAfterMintFeePrefix_of_call
    (evm evm0 evm1 evmAfter : EVM.State) (I : ExecutionEnv) (nextFrame : Frame)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfee :
      ExecStmt config
        { contract := contract,
          locals := mintAmountStore (uniswapLockEnteredState evm) I balance0 balance1 }
        evm1 (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok nextFrame evmAfter)) :
    ExecBlock config { contract := contract, locals := mintStore I } evm
      (lockEnter ++
        [ .letDecl "_reserve0" (some uint112) (.storage reserve0Ref),
          .letDecl "_reserve1" (some uint112) (.storage reserve1Ref) ] ++
        pairBalanceOfThisStmts "balance0" "balance1" ++
        [ .letDecl "amount0" (some uint256)
            (u256 (.binary .sub (.var "balance0") (.var "_reserve0"))),
          .letDecl "amount1" (some uint256)
            (u256 (.binary .sub (.var "balance1") (.var "_reserve1"))),
          .internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn" ])
      (.ok nextFrame evmAfter) := by
  let evmL := uniswapLockEnteredState evm
  have hprefix :=
    uniswapMintAmountsPrefix evm evm0 evm1 I hwv hunlocked hguard0 hguard1 hcall0 hdec0
      hcall1 hdec1 henough0 henough1
  have hfeeBlock :
      ExecBlock config
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 } evm1
        [ .internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn" ]
        (.ok nextFrame evmAfter) := by
    exact ExecBlock.consNormal (by simpa [evmL] using hfee) ExecBlock.nil
  simpa [evmL, List.append_assoc] using execBlock_append hprefix hfeeBlock

theorem uniswapMintAfterMintFeeTotalSupplyPrefix_of_call
    (evm evm0 evm1 evmAfter : EVM.State) (I : ExecutionEnv) (nextLocals : Store)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfee :
      ExecStmt config
        { contract := contract,
          locals := mintAmountStore (uniswapLockEnteredState evm) I balance0 balance1 }
        evm1 (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextLocals } evmAfter))
    (hbase : nextLocals.get? "totalSupply" = none) :
    ExecBlock config { contract := contract, locals := mintStore I } evm
      (lockEnter ++
        [ .letDecl "_reserve0" (some uint112) (.storage reserve0Ref),
          .letDecl "_reserve1" (some uint112) (.storage reserve1Ref) ] ++
        pairBalanceOfThisStmts "balance0" "balance1" ++
        [ .letDecl "amount0" (some uint256)
            (u256 (.binary .sub (.var "balance0") (.var "_reserve0"))),
          .letDecl "amount1" (some uint256)
            (u256 (.binary .sub (.var "balance1") (.var "_reserve1"))),
          .internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn",
          .letDecl "_totalSupply" (some uint256) (.storage totalSupplyRef) ])
      (.ok
        { contract := contract,
          locals := nextLocals.insert "_totalSupply"
            (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter)) }
        evmAfter) := by
  let evmL := uniswapLockEnteredState evm
  have hprefix :=
    uniswapMintAfterMintFeePrefix_of_call evm evm0 evm1 evmAfter I
      { contract := contract, locals := nextLocals } hwv hunlocked hguard0 hguard1
      hcall0 hdec0 hcall1 hdec1 henough0 henough1 hfee
  have htotal := uniswapMintTotalSupplyLet evmAfter nextLocals hbase
  simpa [evmL, List.append_assoc] using execBlock_append hprefix htotal

theorem uniswapMintAfterMintFeeInitialSmallRootReverts_of_call
    (evm evm0 evm1 evmAfter : EVM.State) (I : ExecutionEnv) (nextLocals : Store)
    {out0 out1 : ByteArray} {balance0 balance1 amount0 amount1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfee :
      ExecStmt config
        { contract := contract,
          locals := mintAmountStore (uniswapLockEnteredState evm) I balance0 balance1 }
        evm1 (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextLocals } evmAfter))
    (hbase : nextLocals.get? "totalSupply" = none)
    (hamount0 : nextLocals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : nextLocals.get? "amount1" = some (uniswapUint256Value amount1))
    (htotalZero : mintFunctionTotalSupplyWord evmAfter = ⟨0⟩)
    (hfit : mintAmountProductNat amount0 amount1 < UInt256.size)
    (hsmall : (mintAmountProductWord amount0 amount1).toNat ≤ 3) :
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body .reverted := by
  let afterTotalSupplyLocals :=
    nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))
  have hprefix :=
    uniswapMintAfterMintFeeTotalSupplyPrefix_of_call evm evm0 evm1 evmAfter I nextLocals
      hwv hunlocked hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 henough0 henough1 hfee hbase
  have htotal :
      afterTotalSupplyLocals.get? "_totalSupply" =
        some (uniswapUint256Value (⟨0⟩ : UInt256)) := by
    simp [afterTotalSupplyLocals, htotalZero]
  have hamount0' :
      afterTotalSupplyLocals.get? "amount0" = some (uniswapUint256Value amount0) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "amount0" =
        some (uniswapUint256Value amount0)
    rw [store_get_ne _ _ (by decide), hamount0]
  have hamount1' :
      afterTotalSupplyLocals.get? "amount1" = some (uniswapUint256Value amount1) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "amount1" =
        some (uniswapUint256Value amount1)
    rw [store_get_ne _ _ (by decide), hamount1]
  have hbranchStmt :
      ExecStmt config { contract := contract, locals := afterTotalSupplyLocals } evmAfter
        mintLiquidityBranchStmt .reverted :=
    uniswapMintInitialLiquiditySmallRootIteReverts evmAfter amount0 amount1 htotal
      hamount0' hamount1' hfit hsmall
  have hbranch :
      ExecBlock config { contract := contract, locals := afterTotalSupplyLocals } evmAfter
        [mintLiquidityBranchStmt] .reverted :=
    ExecBlock.consRevert hbranchStmt
  have hthrough := execBlock_append hprefix hbranch
  have hfull :=
    execBlock_append_term (s2 := mintAfterLiquidityTailStmts) hthrough
      (by intro f e h; cases h)
  simpa [mintTransition, mintLiquidityBranchStmt, mintInitialLiquidityBranchStmts,
    mintProportionalLiquidityBranchStmts, mintAfterLiquidityTailStmts, List.append_assoc,
    afterTotalSupplyLocals] using hfull

theorem uniswapMintAfterMintFeeProportionalFeeOffReturn_of_call
    (evm evm0 evm1 evmAfter : EVM.State) (I : ExecutionEnv) (nextLocals : Store)
    {out0 out1 : ByteArray} {balance0 balance1 amount0 amount1 liquidity : UInt256}
    (recipient : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfee :
      ExecStmt config
        { contract := contract,
          locals := mintAmountStore (uniswapLockEnteredState evm) I balance0 balance1 }
        evm1 (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextLocals } evmAfter))
    (htotalBase : nextLocals.get? "totalSupply" = none)
    (hto : nextLocals.get? "to" = some (.address recipient))
    (hamount0 : nextLocals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : nextLocals.get? "amount1" = some (uniswapUint256Value amount1))
    (hbalance0 : nextLocals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : nextLocals.get? "balance1" = some (uniswapUint256Value balance1))
    (hfeeOn : nextLocals.get? "feeOn" = some (.bool false))
    (hreserve0 :
      nextLocals.get? "_reserve0" =
        some (.int (Int.ofNat (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat)))
    (hreserve1 :
      nextLocals.get? "_reserve1" =
        some (.int (Int.ofNat (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat)))
    (hreserve0Base : nextLocals.get? "reserve0" = none)
    (hreserve1Base : nextLocals.get? "reserve1" = none)
    (hunlockedBase : nextLocals.get? "unlocked" = none)
    (htotalNonzero : mintFunctionTotalSupplyWord evmAfter ≠ ⟨0⟩)
    (hfit0 : mintAmountProductNat amount0 (mintFunctionTotalSupplyWord evmAfter) < UInt256.size)
    (hfit1 : mintAmountProductNat amount1 (mintFunctionTotalSupplyWord evmAfter) < UInt256.size)
    (hreserve0Nonzero : uniswapReserve0Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hreserve1Nonzero : uniswapReserve1Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord
          (mintProportionalLiquidityWord amount0 (mintFunctionTotalSupplyWord evmAfter)
            (uniswapReserve0Word (uniswapLockEnteredState evm)))
          (mintProportionalLiquidityWord amount1 (mintFunctionTotalSupplyWord evmAfter)
            (uniswapReserve1Word (uniswapLockEnteredState evm))))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply : mintFunctionTotalSupplyNewNat evmAfter liquidity < UInt256.size)
    (hfitBalance : mintFunctionToBalanceNewNat evmAfter recipient liquidity < UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed : syncTimeElapsedInt (mintFunctionPostState evmAfter recipient liquidity) = 0) :
    let totalSupply := mintFunctionTotalSupplyWord evmAfter
    let reserve0 := uniswapReserve0Word (uniswapLockEnteredState evm)
    let reserve1 := uniswapReserve1Word (uniswapLockEnteredState evm)
    let afterTotalSupplyLocals :=
      nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)
    let liquidity0 := mintProportionalLiquidityWord amount0 totalSupply reserve0
    let liquidity1 := mintProportionalLiquidityWord amount1 totalSupply reserve1
    let afterBranch :=
      resumeAfterInternalCall
        { contract := contract,
          locals :=
            (afterTotalSupplyLocals.insert "liquidity0"
              (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert
                "liquidity1"
                (mintProportionalLiquidityValue amount1 totalSupply reserve1) }
        "liquidity" (some (minFunctionResultValue liquidity0 liquidity1))
    let afterMint := resumeAfterInternalCall afterBranch "_mintResult" none
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body
      (.returned afterUpdate
        (uniswapLockExitedState
          (syncUpdatePackedReserveState (mintFunctionPostState evmAfter recipient liquidity)
            balance0 balance1))
        (some (uniswapUint256Value liquidity))) := by
  intro totalSupply reserve0 reserve1 afterTotalSupplyLocals liquidity0 liquidity1 afterBranch
    afterMint afterUpdate
  have hprefix :=
    uniswapMintAfterMintFeeTotalSupplyPrefix_of_call evm evm0 evm1 evmAfter I nextLocals
      hwv hunlocked hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 henough0 henough1 hfee
      htotalBase
  have hto' :
      afterTotalSupplyLocals.get? "to" = some (.address recipient) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get? "to" =
      some (.address recipient)
    rw [store_get_ne _ _ (by decide), hto]
  have htotal' :
      afterTotalSupplyLocals.get? "_totalSupply" =
        some (uniswapUint256Value totalSupply) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "_totalSupply" = some (uniswapUint256Value totalSupply)
    rw [store_get_self]
  have hamount0' :
      afterTotalSupplyLocals.get? "amount0" = some (uniswapUint256Value amount0) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "amount0" = some (uniswapUint256Value amount0)
    rw [store_get_ne _ _ (by decide), hamount0]
  have hamount1' :
      afterTotalSupplyLocals.get? "amount1" = some (uniswapUint256Value amount1) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "amount1" = some (uniswapUint256Value amount1)
    rw [store_get_ne _ _ (by decide), hamount1]
  have hbalance0' :
      afterTotalSupplyLocals.get? "balance0" = some (uniswapUint256Value balance0) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "balance0" = some (uniswapUint256Value balance0)
    rw [store_get_ne _ _ (by decide), hbalance0]
  have hbalance1' :
      afterTotalSupplyLocals.get? "balance1" = some (uniswapUint256Value balance1) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "balance1" = some (uniswapUint256Value balance1)
    rw [store_get_ne _ _ (by decide), hbalance1]
  have hfeeOn' :
      afterTotalSupplyLocals.get? "feeOn" = some (.bool false) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get? "feeOn" =
      some (.bool false)
    rw [store_get_ne _ _ (by decide), hfeeOn]
  have hreserve0' :
      afterTotalSupplyLocals.get? "_reserve0" =
        some (.int (Int.ofNat reserve0.toNat)) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "_reserve0" = some (.int (Int.ofNat reserve0.toNat))
    rw [store_get_ne _ _ (by decide)]
    simpa [reserve0] using hreserve0
  have hreserve1' :
      afterTotalSupplyLocals.get? "_reserve1" =
        some (.int (Int.ofNat reserve1.toNat)) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "_reserve1" = some (.int (Int.ofNat reserve1.toNat))
    rw [store_get_ne _ _ (by decide)]
    simpa [reserve1] using hreserve1
  have hreserve0Base' :
      afterTotalSupplyLocals.get? "reserve0" = none := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "reserve0" = none
    rw [store_get_ne _ _ (by decide), hreserve0Base]
  have hreserve1Base' :
      afterTotalSupplyLocals.get? "reserve1" = none := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "reserve1" = none
    rw [store_get_ne _ _ (by decide), hreserve1Base]
  have hunlockedBase' :
      afterTotalSupplyLocals.get? "unlocked" = none := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "unlocked" = none
    rw [store_get_ne _ _ (by decide), hunlockedBase]
  have htail :
      ExecBlock config { contract := contract, locals := afterTotalSupplyLocals } evmAfter
        ([mintLiquidityBranchStmt] ++ mintAfterLiquidityTailStmts)
        (.returned afterUpdate
          (uniswapLockExitedState
            (syncUpdatePackedReserveState (mintFunctionPostState evmAfter recipient liquidity)
              balance0 balance1))
          (some (uniswapUint256Value liquidity))) := by
    simpa [afterTotalSupplyLocals, totalSupply, reserve0, reserve1, liquidity0, liquidity1,
      afterBranch, afterMint, afterUpdate, mintAfterLiquidityTailStmts, List.append_assoc] using
      uniswapMintProportionalLiquidityUpdateElapsedZeroFeeOffReturn
        (locals := afterTotalSupplyLocals) evmAfter recipient amount0 amount1 totalSupply
        reserve0 reserve1 balance0 balance1 liquidity hto' htotal'
        (by simpa [totalSupply] using htotalNonzero) hamount0' hamount1' hbalance0'
        hbalance1' hfeeOn' hreserve0' hreserve1' hreserve0Base' hreserve1Base'
        hunlockedBase' (by simpa [totalSupply] using hfit0)
        (by simpa [totalSupply] using hfit1)
        (by simpa [reserve0] using hreserve0Nonzero)
        (by simpa [reserve1] using hreserve1Nonzero)
        (by simpa [totalSupply, reserve0, reserve1] using hliquidity) hliqNonzero
        hfitSupply hfitBalance hbound0 hbound1 helapsed
  have hthrough := execBlock_append hprefix htail
  simpa [mintTransition, mintLiquidityBranchStmt, mintInitialLiquidityBranchStmts,
    mintProportionalLiquidityBranchStmts, mintAfterLiquidityTailStmts, List.append_assoc,
    afterTotalSupplyLocals, totalSupply, reserve0, reserve1] using hthrough

theorem uniswapMintAfterMintFeeProportionalFeeOnReturn_of_call
    (evm evm0 evm1 evmAfter : EVM.State) (I : ExecutionEnv) (nextLocals : Store)
    {out0 out1 : ByteArray} {balance0 balance1 amount0 amount1 liquidity : UInt256}
    (recipient : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfee :
      ExecStmt config
        { contract := contract,
          locals := mintAmountStore (uniswapLockEnteredState evm) I balance0 balance1 }
        evm1 (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextLocals } evmAfter))
    (htotalBase : nextLocals.get? "totalSupply" = none)
    (hto : nextLocals.get? "to" = some (.address recipient))
    (hamount0 : nextLocals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : nextLocals.get? "amount1" = some (uniswapUint256Value amount1))
    (hbalance0 : nextLocals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : nextLocals.get? "balance1" = some (uniswapUint256Value balance1))
    (hfeeOn : nextLocals.get? "feeOn" = some (.bool true))
    (hreserve0 :
      nextLocals.get? "_reserve0" =
        some (.int (Int.ofNat (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat)))
    (hreserve1 :
      nextLocals.get? "_reserve1" =
        some (.int (Int.ofNat (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat)))
    (hreserve0Base : nextLocals.get? "reserve0" = none)
    (hreserve1Base : nextLocals.get? "reserve1" = none)
    (hkLastBase : nextLocals.get? "kLast" = none)
    (hunlockedBase : nextLocals.get? "unlocked" = none)
    (htotalNonzero : mintFunctionTotalSupplyWord evmAfter ≠ ⟨0⟩)
    (hfit0 : mintAmountProductNat amount0 (mintFunctionTotalSupplyWord evmAfter) < UInt256.size)
    (hfit1 : mintAmountProductNat amount1 (mintFunctionTotalSupplyWord evmAfter) < UInt256.size)
    (hreserve0Nonzero : uniswapReserve0Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hreserve1Nonzero : uniswapReserve1Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord
          (mintProportionalLiquidityWord amount0 (mintFunctionTotalSupplyWord evmAfter)
            (uniswapReserve0Word (uniswapLockEnteredState evm)))
          (mintProportionalLiquidityWord amount1 (mintFunctionTotalSupplyWord evmAfter)
            (uniswapReserve1Word (uniswapLockEnteredState evm))))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply : mintFunctionTotalSupplyNewNat evmAfter liquidity < UInt256.size)
    (hfitBalance : mintFunctionToBalanceNewNat evmAfter recipient liquidity < UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed : syncTimeElapsedInt (mintFunctionPostState evmAfter recipient liquidity) = 0)
    (hfitKLast :
      mintFeeReserveProductNat
          (uniswapReserve0Word
            (syncUpdatePackedReserveState (mintFunctionPostState evmAfter recipient liquidity)
              balance0 balance1))
          (uniswapReserve1Word
            (syncUpdatePackedReserveState (mintFunctionPostState evmAfter recipient liquidity)
              balance0 balance1)) < UInt256.size) :
    let totalSupply := mintFunctionTotalSupplyWord evmAfter
    let reserve0 := uniswapReserve0Word (uniswapLockEnteredState evm)
    let reserve1 := uniswapReserve1Word (uniswapLockEnteredState evm)
    let afterTotalSupplyLocals :=
      nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)
    let liquidity0 := mintProportionalLiquidityWord amount0 totalSupply reserve0
    let liquidity1 := mintProportionalLiquidityWord amount1 totalSupply reserve1
    let afterBranch :=
      resumeAfterInternalCall
        { contract := contract,
          locals :=
            (afterTotalSupplyLocals.insert "liquidity0"
              (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert
                "liquidity1"
                (mintProportionalLiquidityValue amount1 totalSupply reserve1) }
        "liquidity" (some (minFunctionResultValue liquidity0 liquidity1))
    let afterMint := resumeAfterInternalCall afterBranch "_mintResult" none
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body
      (.returned afterUpdate
        (uniswapLockExitedState
          (mintKLastUpdatedState
            (syncUpdatePackedReserveState (mintFunctionPostState evmAfter recipient liquidity)
              balance0 balance1)))
        (some (uniswapUint256Value liquidity))) := by
  intro totalSupply reserve0 reserve1 afterTotalSupplyLocals liquidity0 liquidity1 afterBranch
    afterMint afterUpdate
  have hprefix :=
    uniswapMintAfterMintFeeTotalSupplyPrefix_of_call evm evm0 evm1 evmAfter I nextLocals
      hwv hunlocked hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 henough0 henough1 hfee
      htotalBase
  have hto' :
      afterTotalSupplyLocals.get? "to" = some (.address recipient) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get? "to" =
      some (.address recipient)
    rw [store_get_ne _ _ (by decide), hto]
  have htotal' :
      afterTotalSupplyLocals.get? "_totalSupply" =
        some (uniswapUint256Value totalSupply) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "_totalSupply" = some (uniswapUint256Value totalSupply)
    rw [store_get_self]
  have hamount0' :
      afterTotalSupplyLocals.get? "amount0" = some (uniswapUint256Value amount0) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "amount0" = some (uniswapUint256Value amount0)
    rw [store_get_ne _ _ (by decide), hamount0]
  have hamount1' :
      afterTotalSupplyLocals.get? "amount1" = some (uniswapUint256Value amount1) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "amount1" = some (uniswapUint256Value amount1)
    rw [store_get_ne _ _ (by decide), hamount1]
  have hbalance0' :
      afterTotalSupplyLocals.get? "balance0" = some (uniswapUint256Value balance0) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "balance0" = some (uniswapUint256Value balance0)
    rw [store_get_ne _ _ (by decide), hbalance0]
  have hbalance1' :
      afterTotalSupplyLocals.get? "balance1" = some (uniswapUint256Value balance1) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "balance1" = some (uniswapUint256Value balance1)
    rw [store_get_ne _ _ (by decide), hbalance1]
  have hfeeOn' :
      afterTotalSupplyLocals.get? "feeOn" = some (.bool true) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get? "feeOn" =
      some (.bool true)
    rw [store_get_ne _ _ (by decide), hfeeOn]
  have hreserve0' :
      afterTotalSupplyLocals.get? "_reserve0" =
        some (.int (Int.ofNat reserve0.toNat)) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "_reserve0" = some (.int (Int.ofNat reserve0.toNat))
    rw [store_get_ne _ _ (by decide)]
    simpa [reserve0] using hreserve0
  have hreserve1' :
      afterTotalSupplyLocals.get? "_reserve1" =
        some (.int (Int.ofNat reserve1.toNat)) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "_reserve1" = some (.int (Int.ofNat reserve1.toNat))
    rw [store_get_ne _ _ (by decide)]
    simpa [reserve1] using hreserve1
  have hreserve0Base' :
      afterTotalSupplyLocals.get? "reserve0" = none := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "reserve0" = none
    rw [store_get_ne _ _ (by decide), hreserve0Base]
  have hreserve1Base' :
      afterTotalSupplyLocals.get? "reserve1" = none := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "reserve1" = none
    rw [store_get_ne _ _ (by decide), hreserve1Base]
  have hkLastBase' :
      afterTotalSupplyLocals.get? "kLast" = none := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "kLast" = none
    rw [store_get_ne _ _ (by decide), hkLastBase]
  have hunlockedBase' :
      afterTotalSupplyLocals.get? "unlocked" = none := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "unlocked" = none
    rw [store_get_ne _ _ (by decide), hunlockedBase]
  have htail :
      ExecBlock config { contract := contract, locals := afterTotalSupplyLocals } evmAfter
        ([mintLiquidityBranchStmt] ++ mintAfterLiquidityTailStmts)
        (.returned afterUpdate
          (uniswapLockExitedState
            (mintKLastUpdatedState
              (syncUpdatePackedReserveState (mintFunctionPostState evmAfter recipient liquidity)
                balance0 balance1)))
          (some (uniswapUint256Value liquidity))) := by
    simpa [afterTotalSupplyLocals, totalSupply, reserve0, reserve1, liquidity0, liquidity1,
      afterBranch, afterMint, afterUpdate, mintAfterLiquidityTailStmts, List.append_assoc] using
      uniswapMintProportionalLiquidityUpdateElapsedZeroFeeOnReturn
        (locals := afterTotalSupplyLocals) evmAfter recipient amount0 amount1 totalSupply
        reserve0 reserve1 balance0 balance1 liquidity hto' htotal'
        (by simpa [totalSupply] using htotalNonzero) hamount0' hamount1' hbalance0'
        hbalance1' hfeeOn' hreserve0' hreserve1' hreserve0Base' hreserve1Base'
        hkLastBase' hunlockedBase' (by simpa [totalSupply] using hfit0)
        (by simpa [totalSupply] using hfit1)
        (by simpa [reserve0] using hreserve0Nonzero)
        (by simpa [reserve1] using hreserve1Nonzero)
        (by simpa [totalSupply, reserve0, reserve1] using hliquidity) hliqNonzero
        hfitSupply hfitBalance hbound0 hbound1 helapsed hfitKLast
  have hthrough := execBlock_append hprefix htail
  simpa [mintTransition, mintLiquidityBranchStmt, mintInitialLiquidityBranchStmts,
    mintProportionalLiquidityBranchStmts, mintAfterLiquidityTailStmts, List.append_assoc,
    afterTotalSupplyLocals, totalSupply, reserve0, reserve1] using hthrough


end UniswapV2Pair
