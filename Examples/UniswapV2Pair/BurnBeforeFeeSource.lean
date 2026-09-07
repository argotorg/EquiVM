import Examples.UniswapV2Pair.BurnFeeEntryRuntime
import Examples.UniswapV2Pair.BurnInitialSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev burnBalanceStore (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) : Store :=
  (burnBalance0Store evm I balance0).insert "balance1" (uniswapUint256Value balance1)

abbrev burnLiquidityWord (evm : EVM.State) : UInt256 :=
  burnFunctionFromBalanceWord evm evm.executionEnv.codeOwner

abbrev burnLiquidityStore (reserveEvm callEvm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) : Store :=
  (burnBalanceStore reserveEvm I balance0 balance1).insert "liquidity"
    (uniswapUint256Value (burnLiquidityWord callEvm))

theorem evalExpr_burn_liquidity (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "balanceOf" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (balanceOfRef this)) = .ok (uniswapUint256Value (burnLiquidityWord evm)) := by
  have her : evalStorageRef config { contract := contract, locals := locals } evm
      (balanceOfRef this) = .ok (burnFunctionFromEvaledRef evm.executionEnv.codeOwner) := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, balanceOfRef,
      burnFunctionFromEvaledRef, burnFunctionFromKey, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr_uniswap_this]
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := hbase) (her := her)
    (hty := by simp [storageTypeAt?, burnFunctionFromEvaledRef, contract, storageDecls,
      uint256St, storageTypeStep?]) (hloc := by rfl)]
  simp [burnLiquidityWord, burnFunctionFromSlot, burnFunctionFromBalanceWord,
    uniswapStorageLocLoad_uint256]

theorem burnLiquidityStore_reserve0
    (reserveEvm callEvm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (burnLiquidityStore reserveEvm callEvm I balance0 balance1).get? "_reserve0" =
      some (uniswapUint256Value (uniswapReserve0Word reserveEvm)) := by
  unfold burnLiquidityStore burnBalanceStore burnBalance0Store burnCacheStore burnReserveStore
  repeat' first | rw [store_get_self] | rw [store_get_ne _ _ (by decide)]

theorem burnLiquidityStore_reserve1
    (reserveEvm callEvm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (burnLiquidityStore reserveEvm callEvm I balance0 balance1).get? "_reserve1" =
      some (uniswapUint256Value (uniswapReserve1Word reserveEvm)) := by
  unfold burnLiquidityStore burnBalanceStore burnBalance0Store burnCacheStore burnReserveStore
  repeat' first | rw [store_get_self] | rw [store_get_ne _ _ (by decide)]

theorem evalExprs_burn_mintFeeArgs
    (reserveEvm callEvm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    evalExprs? config
      { contract := contract, locals := burnLiquidityStore reserveEvm callEvm I balance0 balance1 }
      callEvm [.var "_reserve0", .var "_reserve1"] =
      .ok [mintFeeReserve0Value (uniswapReserve0Word reserveEvm),
        mintFeeReserve1Value (uniswapReserve1Word reserveEvm)] := by
  simp only [evalExprs?, evalExpr?, EvalResult.ofOption, burnLiquidityStore_reserve0,
    burnLiquidityStore_reserve1, EvalResult.bind, bind, pure]

theorem uniswapBurnLiquidityLoaded
    (reserveEvm callEvm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    ExecBlock config
      { contract := contract, locals := burnBalanceStore reserveEvm I balance0 balance1 }
      callEvm [.letDecl "liquidity" (some uint256) (.storage (balanceOfRef this))]
      (.ok { contract := contract, locals := burnLiquidityStore reserveEvm callEvm I balance0 balance1 }
        callEvm) := by
  exact ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_burn_liquidity callEvm _
      (by simp [burnBalanceStore, burnBalance0Store, burnCacheStore, burnReserveStore, burnStore])))
    ExecBlock.nil

theorem burnLiquidityWord_eq_runtime
    {σ : AccountMap} {I : ExecutionEnv} {evm : EVM.State} {mem : ByteArray}
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I)
    (hmem : 64 ≤ mem.size) :
    burnLiquidityWord evm = uniswapCodeOwnerStorageWord I σ
      (uniswapInternalMintBalanceHashSlot (UInt256.ofNat I.codeOwner.val) mem) := by
  have hsize : I.codeOwner.val < UInt256.size :=
    lt_trans I.codeOwner.isLt (by native_decide : 2 ^ 160 < UInt256.size)
  have hholder : evm.executionEnv.codeOwner =
      AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat := by
    rw [henv, UInt256.toNat_ofNat_of_lt hsize]
    apply Fin.ext
    simp [AccountAddress.ofNat, Nat.mod_eq_of_lt I.codeOwner.isLt]
  rw [uniswapInternalMintBalanceHashSlot_eq_mapSlot (UInt256.ofNat I.codeOwner.val) hmem]
  exact burnFunctionFromBalanceWord_eq_runtime hAccounts henv hholder

abbrev burnBeforeFeePrefix : List Stmt :=
  burnCachePrefix ++ balanceOfThisStmts (.var "_token0") "balance0" ++
    balanceOfThisStmts (.var "_token1") "balance1" ++
    [.letDecl "liquidity" (some uint256) (.storage (balanceOfRef this))]

theorem uniswapBurnBeforeFeePrefix
    (evm evm0 evm1 : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hfirst : ExecBlock config
      { contract := contract, locals := burnCacheStore (uniswapLockEnteredState evm) I }
      (uniswapLockEnteredState evm) (balanceOfThisStmts (.var "_token0") "balance0")
      (.ok { contract := contract, locals :=
        burnBalance0Store (uniswapLockEnteredState evm) I balance0 } evm0))
    (hsecond : ExecBlock config
      { contract := contract, locals := burnBalance0Store (uniswapLockEnteredState evm) I balance0 }
      evm0 (balanceOfThisStmts (.var "_token1") "balance1")
      (.ok { contract := contract, locals :=
        burnBalanceStore (uniswapLockEnteredState evm) I balance0 balance1 } evm1)) :
    ExecBlock config { contract := contract, locals := burnStore I } evm burnBeforeFeePrefix
      (.ok { contract := contract, locals :=
        burnLiquidityStore (uniswapLockEnteredState evm) evm1 I balance0 balance1 } evm1) := by
  exact execBlock_append
    (execBlock_append (execBlock_append (uniswapBurnCachePrefix evm I hwv hunlocked) hfirst) hsecond)
    (uniswapBurnLiquidityLoaded (uniswapLockEnteredState evm) evm1 I balance0 balance1)

theorem uniswapBurnBodyReverts_mintFeeBlock
    (evm evm1 : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256)
    (hprefix : ExecBlock config { contract := contract, locals := burnStore I } evm burnBeforeFeePrefix
      (.ok { contract := contract, locals :=
        burnLiquidityStore (uniswapLockEnteredState evm) evm1 I balance0 balance1 } evm1))
    (hfee : ExecStmt config
      { contract := contract, locals :=
        burnLiquidityStore (uniswapLockEnteredState evm) evm1 I balance0 balance1 } evm1
      (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn") .reverted) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body .reverted := by
  have hfeeBlock : ExecBlock config
      { contract := contract, locals :=
        burnLiquidityStore (uniswapLockEnteredState evm) evm1 I balance0 balance1 } evm1
      [.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn"] .reverted :=
    ExecBlock.consRevert hfee
  exact ExecFuncBody.execBlockRevert (by
    simpa only [burnTransition, burnBeforeFeePrefix, burnCachePrefix, List.append_assoc] using
      execBlock_append_term (execBlock_append hprefix hfeeBlock) (by intro f e h; cases h))

end UniswapV2Pair
