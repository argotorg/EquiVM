import Examples.UniswapV2Pair.MintFeeSqrtLoopBridge
import Examples.UniswapV2Pair.MintRuntimeAfterFee

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

theorem evalExpr_mint_initialLiquidity_sub_ok
    {solm : Frame} (evm : EVM.State) (rootLiquidity : Int) (liquidity : UInt256)
    (hroot : solm.locals.get? "rootLiquidity" = some (.int rootLiquidity))
    (hge : minimumLiquidity ≤ rootLiquidity)
    (hfit : rootLiquidity - minimumLiquidity < (2 : Int) ^ 256)
    (hliquidity : liquidity = UInt256.ofNat (rootLiquidity - minimumLiquidity).toNat) :
    evalExpr? config solm evm
      (u256 (.binary .sub (.var "rootLiquidity") (.intLit minimumLiquidity))) =
        .ok (uniswapUint256Value liquidity) := by
  have hnonneg : 0 ≤ rootLiquidity - minimumLiquidity := by omega
  simp only [u256, evalExpr?, EvalResult.ofOption, hroot, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  change
    (if rootLiquidity - minimumLiquidity < 0 ||
        rootLiquidity - minimumLiquidity ≥ (2 : Int) ^ 256 then
       EvalResult.revert
     else EvalResult.ok (Value.int (rootLiquidity - minimumLiquidity))) =
      EvalResult.ok (uniswapUint256Value liquidity)
  have hltFalse : decide (rootLiquidity - minimumLiquidity < 0) = false := by
    rw [decide_eq_false_iff_not]
    omega
  have hhighFalse :
      decide (rootLiquidity - minimumLiquidity ≥ (2 : Int) ^ 256) = false := by
    rw [decide_eq_false_iff_not]
    omega
  have hnatFit : (rootLiquidity - minimumLiquidity).toNat < UInt256.size := by
    have h' : (rootLiquidity - minimumLiquidity).toNat < 2 ^ 256 := by
      exact_mod_cast (by simpa [Int.toNat_of_nonneg hnonneg] using hfit)
    simpa [UInt256.size] using h'
  have htoNat :
      (UInt256.ofNat (rootLiquidity - minimumLiquidity).toNat).toNat =
        (rootLiquidity - minimumLiquidity).toNat :=
    ulit_toNat' _ hnatFit
  rw [hltFalse, hhighFalse]
  simp [uniswapUint256Value, uint256Value, hliquidity, htoNat,
    Int.toNat_of_nonneg hnonneg]

theorem evalExprs_mint_minimumMintArgs (evm : EVM.State) (caller : Frame) :
    evalExprs? config caller evm [zeroAddr, .intLit minimumLiquidity] =
      .ok [mintFunctionToValue (AccountAddress.ofNat 0),
        mintFunctionValueValue (⟨1000⟩ : UInt256)] := by
  simp only [evalExprs?, EvalResult.bind, bind, pure]
  rw [evalExpr_mintFee_zeroAddr caller evm]
  simp [evalExpr?, minimumLiquidity, mintFunctionToValue, mintFunctionValueValue,
    uniswapUint256Value, uint256Value]
  native_decide

theorem uniswapMintInitialLiquidityBranchPrefix
    {locals : Store} (evm : EVM.State) (rootLiquidity : Int) (liquidity : UInt256)
    (hsqrt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
          "rootLiquidity")
        (.ok
          (resumeAfterInternalCall { contract := contract, locals := locals }
            "rootLiquidity" (some [.int rootLiquidity]))
          evm))
    (hge : minimumLiquidity ≤ rootLiquidity)
    (hfit : rootLiquidity - minimumLiquidity < (2 : Int) ^ 256)
    (hliquidity : liquidity = UInt256.ofNat (rootLiquidity - minimumLiquidity).toNat)
    (hfitSupplyMin :
      mintFunctionTotalSupplyNewNat evm (⟨1000⟩ : UInt256) < UInt256.size)
    (hfitBalanceMin :
      mintFunctionToBalanceNewNat evm (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256) <
        UInt256.size) :
    let caller : Frame := { contract := contract, locals := locals }
    let afterRoot := resumeAfterInternalCall caller "rootLiquidity" (some [.int rootLiquidity])
    let afterLiquidity : Frame :=
      { contract := contract,
        locals := afterRoot.locals.insert "liquidity" (uniswapUint256Value liquidity) }
    ExecBlock config caller evm mintInitialLiquidityBranchStmts
      (.ok (resumeAfterInternalCall afterLiquidity "_minimumMint" none)
        (mintFunctionPostState evm (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))) := by
  intro caller afterRoot afterLiquidity
  refine ExecBlock.consNormal hsqrt ?_
  have hroot :
      afterRoot.locals.get? "rootLiquidity" = some (.int rootLiquidity) := by
    simp [afterRoot, caller, resumeAfterInternalCall, collapseReturns]
  have hliqEval :
      evalExpr? config afterRoot evm
        (u256 (.binary .sub (.var "rootLiquidity") (.intLit minimumLiquidity))) =
          .ok (uniswapUint256Value liquidity) :=
    evalExpr_mint_initialLiquidity_sub_ok evm rootLiquidity liquidity hroot hge hfit
      hliquidity
  refine ExecBlock.consNormal (ExecStmt.letDecl hliqEval) ?_
  have hmint :
      ExecStmt config afterLiquidity evm
        (.internalCall "_mint" [zeroAddr, .intLit minimumLiquidity] "_minimumMint")
        (.ok (resumeAfterInternalCall afterLiquidity "_minimumMint" none)
          (mintFunctionPostState evm (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))) := by
    exact uniswapMintFunctionCallSuccess (caller := afterLiquidity) (evm := evm)
      (recipient := AccountAddress.ofNat 0) (value := (⟨1000⟩ : UInt256))
      (args := [zeroAddr, .intLit minimumLiquidity]) (retVar := "_minimumMint")
      rfl (evalExprs_mint_minimumMintArgs evm afterLiquidity) hfitSupplyMin hfitBalanceMin
  exact ExecBlock.consNormal hmint ExecBlock.nil

theorem uniswapMintInitialLiquidityBranchStmtPrefix
    {locals : Store} (evm : EVM.State) (rootLiquidity : Int) (liquidity : UInt256)
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value (⟨0⟩ : UInt256)))
    (hsqrt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
          "rootLiquidity")
        (.ok
          (resumeAfterInternalCall { contract := contract, locals := locals }
            "rootLiquidity" (some [.int rootLiquidity]))
          evm))
    (hge : minimumLiquidity ≤ rootLiquidity)
    (hfit : rootLiquidity - minimumLiquidity < (2 : Int) ^ 256)
    (hliquidity : liquidity = UInt256.ofNat (rootLiquidity - minimumLiquidity).toNat)
    (hfitSupplyMin :
      mintFunctionTotalSupplyNewNat evm (⟨1000⟩ : UInt256) < UInt256.size)
    (hfitBalanceMin :
      mintFunctionToBalanceNewNat evm (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256) <
        UInt256.size) :
    let caller : Frame := { contract := contract, locals := locals }
    let afterRoot := resumeAfterInternalCall caller "rootLiquidity" (some [.int rootLiquidity])
    let afterLiquidity : Frame :=
      { contract := contract,
        locals := afterRoot.locals.insert "liquidity" (uniswapUint256Value liquidity) }
    ExecStmt config caller evm mintLiquidityBranchStmt
      (.ok (resumeAfterInternalCall afterLiquidity "_minimumMint" none)
        (mintFunctionPostState evm (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))) := by
  intro caller afterRoot afterLiquidity
  have hcond := evalExpr_mint_totalSupply_eq_zero_true evm htotal
  exact ExecStmt.iteTrue hcond
    (uniswapMintInitialLiquidityBranchPrefix evm rootLiquidity liquidity hsqrt hge hfit
      hliquidity hfitSupplyMin hfitBalanceMin)

theorem uniswapMintInitialLiquidityBranchStmtUnderflowReverts
    {locals : Store} (evm : EVM.State) (rootLiquidity : Int)
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value (⟨0⟩ : UInt256)))
    (hsqrt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
          "rootLiquidity")
        (.ok
          (resumeAfterInternalCall { contract := contract, locals := locals }
            "rootLiquidity" (some [.int rootLiquidity]))
          evm))
    (hlt : rootLiquidity < minimumLiquidity) :
    ExecStmt config { contract := contract, locals := locals } evm mintLiquidityBranchStmt
      .reverted := by
  let caller : Frame := { contract := contract, locals := locals }
  let afterRoot := resumeAfterInternalCall caller "rootLiquidity" (some [.int rootLiquidity])
  have hcond := evalExpr_mint_totalSupply_eq_zero_true evm htotal
  have hroot :
      afterRoot.locals.get? "rootLiquidity" = some (.int rootLiquidity) := by
    simp [afterRoot, caller, resumeAfterInternalCall, collapseReturns]
  have hbranch :
      ExecBlock config caller evm mintInitialLiquidityBranchStmts .reverted := by
    refine ExecBlock.consNormal hsqrt ?_
    exact ExecBlock.consRevert
      (ExecStmt.letDeclRevert
        (evalExpr_mint_initialLiquidity_sub_underflow evm rootLiquidity hroot hlt))
  exact ExecStmt.iteTrue hcond hbranch

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialLiquidityUpdateElapsedZeroFeeOffReturn
    {locals : Store} (evm : EVM.State) (rootLiquidity : Int)
    (recipient : AccountAddress) (balance0 balance1 reserve0 reserve1 liquidity : UInt256)
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value (⟨0⟩ : UInt256)))
    (hto : locals.get? "to" = some (.address recipient))
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0 : locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hfeeOn : locals.get? "feeOn" = some (.bool false))
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none)
    (hunlockedBase : locals.get? "unlocked" = none)
    (hsqrt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
          "rootLiquidity")
        (.ok
          (resumeAfterInternalCall { contract := contract, locals := locals }
            "rootLiquidity" (some [.int rootLiquidity]))
          evm))
    (hge : minimumLiquidity ≤ rootLiquidity)
    (hfit : rootLiquidity - minimumLiquidity < (2 : Int) ^ 256)
    (hliquidity : liquidity = UInt256.ofNat (rootLiquidity - minimumLiquidity).toNat)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupplyMin :
      mintFunctionTotalSupplyNewNat evm (⟨1000⟩ : UInt256) < UInt256.size)
    (hfitBalanceMin :
      mintFunctionToBalanceNewNat evm (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256) <
        UInt256.size)
    (hfitSupply :
      mintFunctionTotalSupplyNewNat
          (mintFunctionPostState evm (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          liquidity <
        UInt256.size)
    (hfitBalance :
      mintFunctionToBalanceNewNat
          (mintFunctionPostState evm (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          recipient liquidity <
        UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      syncTimeElapsedInt
          (mintFunctionPostState
            (mintFunctionPostState evm (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
            recipient liquidity) =
        0) :
    let caller : Frame := { contract := contract, locals := locals }
    let afterRoot := resumeAfterInternalCall caller "rootLiquidity" (some [.int rootLiquidity])
    let afterLiquidity : Frame :=
      { contract := contract,
        locals := afterRoot.locals.insert "liquidity" (uniswapUint256Value liquidity) }
    let afterMinimum := resumeAfterInternalCall afterLiquidity "_minimumMint" none
    let evmMinimum := mintFunctionPostState evm (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256)
    let afterMint := resumeAfterInternalCall afterMinimum "_mintResult" none
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config caller evm ([mintLiquidityBranchStmt] ++ mintAfterLiquidityTailStmts)
      (.returned afterUpdate
        (uniswapLockExitedState
          (syncUpdatePackedReserveState
            (mintFunctionPostState evmMinimum recipient liquidity) balance0 balance1))
        (some [uniswapUint256Value liquidity])) := by
  intro caller afterRoot afterLiquidity afterMinimum evmMinimum afterMint afterUpdate
  have hbranchStmt :=
    uniswapMintInitialLiquidityBranchStmtPrefix evm rootLiquidity liquidity htotal hsqrt hge
      hfit hliquidity hfitSupplyMin hfitBalanceMin
  have hbranch :
      ExecBlock config caller evm [mintLiquidityBranchStmt] (.ok afterMinimum evmMinimum) := by
    exact ExecBlock.consNormal hbranchStmt ExecBlock.nil
  have htoAfter :
      afterMinimum.locals.get? "to" = some (.address recipient) := by
    change (((locals.insert "rootLiquidity" (.int rootLiquidity)).insert "liquidity"
      (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get? "to" =
        some (.address recipient)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hto]
  have hliqAfter :
      afterMinimum.locals.get? "liquidity" = some (uniswapUint256Value liquidity) := by
    change (((locals.insert "rootLiquidity" (.int rootLiquidity)).insert "liquidity"
      (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get? "liquidity" =
        some (uniswapUint256Value liquidity)
    rw [store_get_ne _ _ (by decide), store_get_self]
  have hbalance0After :
      afterMinimum.locals.get? "balance0" = some (uniswapUint256Value balance0) := by
    change (((locals.insert "rootLiquidity" (.int rootLiquidity)).insert "liquidity"
      (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get? "balance0" =
        some (uniswapUint256Value balance0)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hbalance0]
  have hbalance1After :
      afterMinimum.locals.get? "balance1" = some (uniswapUint256Value balance1) := by
    change (((locals.insert "rootLiquidity" (.int rootLiquidity)).insert "liquidity"
      (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get? "balance1" =
        some (uniswapUint256Value balance1)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hbalance1]
  have hfeeOnAfter :
      afterMinimum.locals.get? "feeOn" = some (.bool false) := by
    change (((locals.insert "rootLiquidity" (.int rootLiquidity)).insert "liquidity"
      (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get? "feeOn" =
        some (.bool false)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hfeeOn]
  have hreserve0After :
      afterMinimum.locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)) := by
    change (((locals.insert "rootLiquidity" (.int rootLiquidity)).insert "liquidity"
      (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get? "_reserve0" =
        some (.int (Int.ofNat reserve0.toNat))
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve0]
  have hreserve1After :
      afterMinimum.locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)) := by
    change (((locals.insert "rootLiquidity" (.int rootLiquidity)).insert "liquidity"
      (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get? "_reserve1" =
        some (.int (Int.ofNat reserve1.toNat))
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve1]
  have hreserve0BaseAfter : afterMinimum.locals.get? "reserve0" = none := by
    change (((locals.insert "rootLiquidity" (.int rootLiquidity)).insert "liquidity"
      (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get? "reserve0" =
        none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve0Base]
  have hreserve1BaseAfter : afterMinimum.locals.get? "reserve1" = none := by
    change (((locals.insert "rootLiquidity" (.int rootLiquidity)).insert "liquidity"
      (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get? "reserve1" =
        none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve1Base]
  have hunlockedBaseAfter : afterMinimum.locals.get? "unlocked" = none := by
    change (((locals.insert "rootLiquidity" (.int rootLiquidity)).insert "liquidity"
      (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get? "unlocked" =
        none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hunlockedBase]
  have htail :
      ExecBlock config afterMinimum evmMinimum mintAfterLiquidityTailStmts
        (.returned afterUpdate
          (uniswapLockExitedState
            (syncUpdatePackedReserveState
              (mintFunctionPostState evmMinimum recipient liquidity) balance0 balance1))
          (some [uniswapUint256Value liquidity])) := by
    simpa [mintAfterLiquidityTailStmts, afterMint, afterUpdate] using
      uniswapMintLiquidityMintUpdateElapsedZeroFeeOffReturn
        (locals := afterMinimum.locals) evmMinimum recipient balance0 balance1 reserve0 reserve1
        liquidity htoAfter hliqAfter hbalance0After hbalance1After hfeeOnAfter
        hreserve0After hreserve1After hreserve0BaseAfter hreserve1BaseAfter hunlockedBaseAfter
        hliqNonzero hfitSupply hfitBalance hbound0 hbound1 helapsed
  simpa [List.append_assoc] using execBlock_append hbranch htail

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialLiquidityUpdateElapsedZeroFeeOnReturn
    {locals : Store} (evm : EVM.State) (rootLiquidity : Int)
    (recipient : AccountAddress) (balance0 balance1 reserve0 reserve1 liquidity : UInt256)
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value (⟨0⟩ : UInt256)))
    (hto : locals.get? "to" = some (.address recipient))
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0 : locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hfeeOn : locals.get? "feeOn" = some (.bool true))
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none)
    (hkLastBase : locals.get? "kLast" = none)
    (hunlockedBase : locals.get? "unlocked" = none)
    (hsqrt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
          "rootLiquidity")
        (.ok
          (resumeAfterInternalCall { contract := contract, locals := locals }
            "rootLiquidity" (some [.int rootLiquidity]))
          evm))
    (hge : minimumLiquidity ≤ rootLiquidity)
    (hfit : rootLiquidity - minimumLiquidity < (2 : Int) ^ 256)
    (hliquidity : liquidity = UInt256.ofNat (rootLiquidity - minimumLiquidity).toNat)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupplyMin :
      mintFunctionTotalSupplyNewNat evm (⟨1000⟩ : UInt256) < UInt256.size)
    (hfitBalanceMin :
      mintFunctionToBalanceNewNat evm (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256) <
        UInt256.size)
    (hfitSupply :
      mintFunctionTotalSupplyNewNat
          (mintFunctionPostState evm (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          liquidity <
        UInt256.size)
    (hfitBalance :
      mintFunctionToBalanceNewNat
          (mintFunctionPostState evm (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          recipient liquidity <
        UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      syncTimeElapsedInt
          (mintFunctionPostState
            (mintFunctionPostState evm (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
            recipient liquidity) =
        0)
    (hfitKLast :
      mintFeeReserveProductNat
          (uniswapReserve0Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState
                (mintFunctionPostState evm (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
                recipient liquidity)
              balance0 balance1))
          (uniswapReserve1Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState
                (mintFunctionPostState evm (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
                recipient liquidity)
              balance0 balance1)) <
        UInt256.size) :
    let caller : Frame := { contract := contract, locals := locals }
    let afterRoot := resumeAfterInternalCall caller "rootLiquidity" (some [.int rootLiquidity])
    let afterLiquidity : Frame :=
      { contract := contract,
        locals := afterRoot.locals.insert "liquidity" (uniswapUint256Value liquidity) }
    let afterMinimum := resumeAfterInternalCall afterLiquidity "_minimumMint" none
    let evmMinimum := mintFunctionPostState evm (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256)
    let afterMint := resumeAfterInternalCall afterMinimum "_mintResult" none
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config caller evm ([mintLiquidityBranchStmt] ++ mintAfterLiquidityTailStmts)
      (.returned afterUpdate
        (uniswapLockExitedState
          (mintKLastUpdatedState
            (syncUpdatePackedReserveState
              (mintFunctionPostState evmMinimum recipient liquidity) balance0 balance1)))
        (some [uniswapUint256Value liquidity])) := by
  intro caller afterRoot afterLiquidity afterMinimum evmMinimum afterMint afterUpdate
  have hbranchStmt :=
    uniswapMintInitialLiquidityBranchStmtPrefix evm rootLiquidity liquidity htotal hsqrt hge
      hfit hliquidity hfitSupplyMin hfitBalanceMin
  have hbranch :
      ExecBlock config caller evm [mintLiquidityBranchStmt] (.ok afterMinimum evmMinimum) := by
    exact ExecBlock.consNormal hbranchStmt ExecBlock.nil
  have htoAfter :
      afterMinimum.locals.get? "to" = some (.address recipient) := by
    change (((locals.insert "rootLiquidity" (.int rootLiquidity)).insert "liquidity"
      (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get? "to" =
        some (.address recipient)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hto]
  have hliqAfter :
      afterMinimum.locals.get? "liquidity" = some (uniswapUint256Value liquidity) := by
    change (((locals.insert "rootLiquidity" (.int rootLiquidity)).insert "liquidity"
      (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get? "liquidity" =
        some (uniswapUint256Value liquidity)
    rw [store_get_ne _ _ (by decide), store_get_self]
  have hbalance0After :
      afterMinimum.locals.get? "balance0" = some (uniswapUint256Value balance0) := by
    change (((locals.insert "rootLiquidity" (.int rootLiquidity)).insert "liquidity"
      (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get? "balance0" =
        some (uniswapUint256Value balance0)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hbalance0]
  have hbalance1After :
      afterMinimum.locals.get? "balance1" = some (uniswapUint256Value balance1) := by
    change (((locals.insert "rootLiquidity" (.int rootLiquidity)).insert "liquidity"
      (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get? "balance1" =
        some (uniswapUint256Value balance1)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hbalance1]
  have hfeeOnAfter :
      afterMinimum.locals.get? "feeOn" = some (.bool true) := by
    change (((locals.insert "rootLiquidity" (.int rootLiquidity)).insert "liquidity"
      (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get? "feeOn" =
        some (.bool true)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hfeeOn]
  have hreserve0After :
      afterMinimum.locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)) := by
    change (((locals.insert "rootLiquidity" (.int rootLiquidity)).insert "liquidity"
      (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get? "_reserve0" =
        some (.int (Int.ofNat reserve0.toNat))
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve0]
  have hreserve1After :
      afterMinimum.locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)) := by
    change (((locals.insert "rootLiquidity" (.int rootLiquidity)).insert "liquidity"
      (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get? "_reserve1" =
        some (.int (Int.ofNat reserve1.toNat))
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve1]
  have hreserve0BaseAfter : afterMinimum.locals.get? "reserve0" = none := by
    change (((locals.insert "rootLiquidity" (.int rootLiquidity)).insert "liquidity"
      (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get? "reserve0" =
        none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve0Base]
  have hreserve1BaseAfter : afterMinimum.locals.get? "reserve1" = none := by
    change (((locals.insert "rootLiquidity" (.int rootLiquidity)).insert "liquidity"
      (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get? "reserve1" =
        none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve1Base]
  have hkLastBaseAfter : afterMinimum.locals.get? "kLast" = none := by
    change (((locals.insert "rootLiquidity" (.int rootLiquidity)).insert "liquidity"
      (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get? "kLast" =
        none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hkLastBase]
  have hunlockedBaseAfter : afterMinimum.locals.get? "unlocked" = none := by
    change (((locals.insert "rootLiquidity" (.int rootLiquidity)).insert "liquidity"
      (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit).get? "unlocked" =
        none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hunlockedBase]
  have htail :
      ExecBlock config afterMinimum evmMinimum mintAfterLiquidityTailStmts
        (.returned afterUpdate
          (uniswapLockExitedState
            (mintKLastUpdatedState
              (syncUpdatePackedReserveState
                (mintFunctionPostState evmMinimum recipient liquidity) balance0 balance1)))
          (some [uniswapUint256Value liquidity])) := by
    simpa [mintAfterLiquidityTailStmts, afterMint, afterUpdate] using
      uniswapMintLiquidityMintUpdateElapsedZeroFeeOnReturn
        (locals := afterMinimum.locals) evmMinimum recipient balance0 balance1 reserve0 reserve1
        liquidity htoAfter hliqAfter hbalance0After hbalance1After hfeeOnAfter
        hreserve0After hreserve1After hreserve0BaseAfter hreserve1BaseAfter hkLastBaseAfter
        hunlockedBaseAfter hliqNonzero hfitSupply hfitBalance hbound0 hbound1 helapsed
        hfitKLast
  simpa [List.append_assoc] using execBlock_append hbranch htail

set_option maxHeartbeats 1000000 in
theorem uniswapMintRuntimeInitialLiquidityAfterRootUnderflowReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {root feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd2531 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2531⟩
      [root, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hrootLt : root.toNat < (⟨1000⟩ : UInt256).toNat)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have rd6879pre := evm_run rd2531 with [
    jumpdest, swap1, push4 ⟨0xffffffff⟩, push2 ⟨6879⟩, and]
  rw [show UInt256.land (⟨6879⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6879⟩ from by decide]
    at rd6879pre
  have rd6879 := rd6879pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.uniswapSafeMathSubUnderflow_aw6_size164_shared
    (by simpa [feeToStaticcallActiveWords, balanceOfThisStaticcallActiveWords] using rd6879)
    hrootLt hmem hmem64
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem mintInitialLiquiditySqrtPrefixRuntimeBounded
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (caller : Frame) (evm : EVM.State)
    (hcontract : caller.contract = contract)
    (hargs :
      evalExprs? config caller evm
        [u256 (.binary .mul (.var "amount0") (.var "amount1"))] =
          .ok [sqrtFunctionYValue (mintAmountProductWord amount0 amount1)])
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOn, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (htotalZero : uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩)
    (hfit : mintAmountProductNat amount0 amount1 < UInt256.size) :
    ∃ root k' C',
      ExecStmt config caller evm
        (.internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
          "rootLiquidity")
        (.ok (resumeAfterInternalCall caller "rootLiquidity" (some [.int root])) evm) ∧
      0 ≤ root ∧ root.toNat < UInt256.size ∧
      RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2531⟩
        [UInt256.ofNat root.toNat, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1, amount0,
          balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
        mem aw rdata (cAFee, σFee) k' C' := by
  obtain ⟨_, _, rd3713⟩ :=
    uniswapMintRuntimeAfterMintFeeTotalSupplyZero rd3701 htotalZero
  obtain ⟨k8046, C8046, rd8046Raw⟩ :=
    uniswapMintRuntimeInitialLiquidityRootEntry rd3713
      (by simpa [mintAmountProductNat] using hfit)
  have hprodWord :
      mintAmountProductWord amount0 amount1 = UInt256.mul amount0 amount1 :=
    mintAmountProductWord_eq_mul amount0 amount1 hfit
  have rd8046 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8046⟩
      [mintAmountProductWord amount0 amount1, ⟨2531⟩, ⟨1000⟩, ⟨3742⟩, ⟨0⟩,
        feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k8046 C8046 := by
    simpa [hprodWord] using rd8046Raw
  obtain ⟨root, k', C', hstmt, hrootNonneg, hrootSize, rd2531⟩ :=
    uniswapSqrtFunctionCallRuntimeSuccessIntBounded
      (caller := caller) (evm := evm) (y := mintAmountProductWord amount0 amount1)
      (ret := ⟨2531⟩)
      (R := [⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel])
      hcontract hargs rd8046 (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨root, k', C', hstmt, hrootNonneg, hrootSize, rd2531⟩

end UniswapV2Pair
