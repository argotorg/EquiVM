import Examples.UniswapV2Pair.UpdateDynamicCallRuntimeCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

theorem uniswapMintUpdateCallReturns_conditionFalse_packed_with
    {locals : Store} (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0 :
      locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 :
      locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (hskip : syncTimeElapsedInt evm = 0 ∨ reserve0 = ⟨0⟩ ∨ reserve1 = ⟨0⟩) :
    ExecStmt config { contract := contract, locals := locals } evm
      (.internalCall "_update"
        [ .var "balance0", .var "balance1", .var "_reserve0", .var "_reserve1" ]
        "_updateResult")
      (.ok
        (resumeAfterInternalCall { contract := contract, locals := locals }
          "_updateResult" none)
        (syncUpdatePackedReserveState evm balance0 balance1)) := by
  exact uniswapUpdateCallReturnsConditionFalse evm balance0 balance1 reserve0 reserve1
    (evalExprs_mint_updateCallArgsWith_of_get evm balance0 balance1 reserve0 reserve1
      hbalance0 hbalance1 hreserve0 hreserve1) hbound0 hbound1 hskip


set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem uniswapUpdateCallRuntimeCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv} {k C : ℕ}
    {reserve1 reserve0 balance1 balance0 ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {locals : Store} (evm : EVM.State)
    (rd6959 : RD uniswapV2PairBytecode I g s0 ⟨6959⟩
      (reserve1 :: reserve0 :: balance1 :: balance0 :: ret :: R)
      mem feeToStaticcallActiveWords rdata (cA, σ) k C)
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (henv : evm.executionEnv = I)
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0 : locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hperm : I.perm = true)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 21 ≤ 1024) :
    (ExecStmt config { contract := contract, locals := locals } evm
      (.internalCall "_update"
        [.var "balance0", .var "balance1", .var "_reserve0", .var "_reserve1"]
        "_updateResult") .reverted ∧ RDrev uniswapV2PairBytecode g s0) ∨
    (∃ evm' σ' packed k' C',
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "_update"
          [.var "balance0", .var "balance1", .var "_reserve0", .var "_reserve1"]
          "_updateResult")
        (.ok (resumeAfterInternalCall { contract := contract, locals := locals }
          "_updateResult" none) evm') ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.executionEnv = I ∧
      evm'.createdAccounts = evm.createdAccounts ∧
      RD uniswapV2PairBytecode I g s0 ret R (uniswapSyncLogMem packed mem)
        feeToStaticcallActiveWords rdata (cA, σ') k' C' ∧
      (uniswapSyncLogMem packed mem).size = 192 ∧
      (uniswapSyncLogMem packed mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) := by
  rcases uniswapUpdateCallRuntimeCases_dynamic evm rd6959 hAccounts henv
      (evalExprs_mint_updateCallArgsWith_of_get evm balance0 balance1 reserve0 reserve1
        hbalance0 hbalance1 hreserve0 hreserve1)
      hclean0 hclean1 hperm (by rw [hmem]; decide) (by decide)
      (by rw [hmem]; native_decide) (by native_decide) (by native_decide) (by decide)
      hmem64 hret hov with hrev | ⟨evm', σ', packed, k', C', hcall, ha, he, hc, rd, hs, hm⟩
  · exact Or.inl hrev
  · refine Or.inr ⟨evm', σ', packed, k', C', hcall, ha, he, hc, rd, ?_, hm⟩
    simpa only [hmem] using hs

end UniswapV2Pair
