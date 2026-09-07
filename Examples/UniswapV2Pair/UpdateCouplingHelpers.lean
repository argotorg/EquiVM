import Examples.UniswapV2Pair.MintRuntimeFinalize

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair


theorem evalExpr_sync_update_condition_false_with
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (hskip : syncTimeElapsedInt evm = 0 ∨ reserve0 = ⟨0⟩ ∨ reserve1 = ⟨0⟩) :
    evalExpr? config
      { contract := contract,
        locals := syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1 }
      evm
      (.binary .and
        (.binary .gt (.var "timeElapsed") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "_reserve0") (.intLit 0))
          (.binary .ne (.var "_reserve1") (.intLit 0)))) = .ok (.bool false) := by
  rcases hskip with ht | hr | hr
  · exact evalExpr_sync_update_condition_false_elapsed_zero_with evm balance0 balance1
      reserve0 reserve1 ht
  all_goals
    simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    rw [syncUpdateTimeElapsedStoreWith_timeElapsed, syncUpdateTimeElapsedStoreWith_reserve0,
      syncUpdateTimeElapsedStoreWith_reserve1]
    cases ht : decide (0 < syncTimeElapsedInt evm) <;>
      cases hne : ((Value.int (Int.ofNat reserve0.toNat)) == Value.int 0) <;>
      simp only [evalBinaryOp?, hr, pure, ht, hne, Bool.not_true, Bool.not_false]
    all_goals rfl

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem RD.uniswapUpdateConditionFalseSkipsCumulatives
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {reserve1 reserve0 balance1 balance0 : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd : RD uniswapV2PairBytecode ee g s0 ⟨7060⟩
      (reserve1 :: reserve0 :: balance1 :: balance0 :: R) mem aw rdata (cA, σ) k C)
    (hskip :
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σ ee) ee) reserve32Mask = ⟨0⟩ ∨
      UInt256.land reserve0 reserve112Mask = ⟨0⟩ ∨
      UInt256.land reserve1 reserve112Mask = ⟨0⟩)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ⟨7241⟩
      (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σ ee) ee ::
        uniswapUpdateTimestampWord ee :: reserve1 :: reserve0 :: balance1 :: balance0 :: R)
      mem aw rdata (cA, σ) k' C' := by
  by_cases ht : UInt256.land
      (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σ ee) ee) reserve32Mask = ⟨0⟩
  · simpa only [uniswapUpdateElapsedWord, uniswapUpdateTimestampWord, uniswapSlotWord] using
      (RD.uniswapUpdateElapsedZeroSkipsCumulatives
        (reserve0 := reserve0) (reserve1 := reserve1) (R := R) rd ht hov)
  by_cases hr0 : UInt256.land reserve0 reserve112Mask = ⟨0⟩
  · simpa only [uniswapUpdateElapsedWord, uniswapUpdateTimestampWord, uniswapSlotWord] using
      (RD.uniswapUpdateReserve0ZeroSkipsCumulatives
        (reserve0 := reserve0) (reserve1 := reserve1) (R := R) rd ht hr0 hov)
  have hr1 : UInt256.land reserve1 reserve112Mask = ⟨0⟩ := by tauto
  simpa only [uniswapUpdateElapsedWord, uniswapUpdateTimestampWord, uniswapSlotWord] using
    (RD.uniswapUpdateReserve1ZeroSkipsCumulatives
      (reserve0 := reserve0) (reserve1 := reserve1) (R := R) rd ht hr0 hr1 hov)

set_option maxRecDepth 2000000 in
theorem RD.uniswapUpdateEmitSyncAndJump_aw6
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {packed elapsed timestamp reserve1 reserve0 balance1 balance0 ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD uniswapV2PairBytecode ee g s0 ⟨7339⟩
      (reserve112Shift :: reserve112Mask :: packed :: elapsed :: timestamp :: reserve1 ::
        reserve0 :: balance1 :: balance0 :: ret :: R)
      mem feeToStaticcallActiveWords rdata acc k C)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : ee.perm = true)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ret R
      (uniswapSyncLogMem packed mem) feeToStaticcallActiveWords rdata acc k' C' := by
  exact RD.uniswapUpdateEmitSyncAndJump
    (awLoad := feeToStaticcallActiveWords) (awLog := feeToStaticcallActiveWords)
    (mcostLoad := 0) (mcostStore0 := 0) (mcostStore1 := 0) (mcostLoadLog := 0)
    (mcostLog := 0) rd
    (by intro s haw hstk; simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk];
        native_decide)
    (mloadFreePtrValue (by rw [hmem]; omega) (by native_decide) hmem64)
    (by native_decide)
    (by intro s haw hstk; simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk];
        native_decide)
    (by native_decide)
    (by intro s haw hstk; simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk];
        native_decide)
    (by native_decide)
    (by intro s haw hstk; simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk];
        native_decide)
    (uniswapMintSyncLogMem_mload64_of_size_le packed (by rw [hmem]; omega)
      (by rw [hmem]; omega) hmem64)
    (by native_decide)
    (by intro s haw hstk; simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk];
        native_decide)
    (by native_decide) hperm hret hov

end UniswapV2Pair
