import Examples.UniswapV2Pair.SwapAdjustmentSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapSwapAdjustmentsCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw ptr amount1In amount0In balance1 balance0 : UInt256}
    {R : List UInt256} {k C : Nat} {caller : Frame} (evm : EVM.State)
    (rd2491 : RD uniswapV2PairBytecode I g s0 ⟨2491⟩
      (amount1In :: amount0In :: balance1 :: balance0 :: R) mem aw rdata acc k C)
    (hb0 : caller.locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hb1 : caller.locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hi0 : caller.locals.get? "amount0In" = some (uniswapUint256Value amount0In))
    (hi1 : caller.locals.get? "amount1In" = some (uniswapUint256Value amount1In))
    (hle0 : amount0In.toNat ≤ balance0.toNat) (hle1 : amount1In.toNat ≤ balance1.toNat)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfitPtr : ptr.toNat + 131 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hawLo : 96 ≤ aw.toNat * 32) (hread : mem.readWithPadding 64 32 = ptr.toByteArray)
    (hov : R.length + 20 ≤ 1024) :
    (ExecBlock config caller evm swapAdjustmentStmts .reverted ∧ RDrev uniswapV2PairBytecode g s0) ∨
    (ExecBlock config caller evm swapAdjustmentStmts
        (.ok (swapAfterAdjustmentsFrame caller (swapAdjustedWord balance0 amount0In)
          (swapAdjustedWord balance1 amount1In)) evm) ∧
      balance0.toNat * 1000 < UInt256.size ∧ balance1.toNat * 1000 < UInt256.size ∧ ∃ k' C',
      RD uniswapV2PairBytecode I g s0 ⟨2570⟩
        (swapAdjustedWord balance1 amount1In :: swapAdjustedWord balance0 amount0In ::
          amount1In :: amount0In :: balance1 :: balance0 :: R) mem aw rdata acc k' C') := by
  have rd2492 := evm_run rd2491 with [jumpdest]
  rcases uniswapSwapAdjustmentRuntimeCases (second := false) rd2492 hle0
      hin hlo hgap hfitPtr haw hawLo hread (by omega) with
    ⟨hover0, rdRev⟩ | ⟨hfit0, _, _, rd2543⟩
  · exact Or.inl ⟨uniswapSwapAdjustmentsRevert0 evm balance0 hb0 hover0, rdRev⟩
  · have rd2546 := evm_run rd2543 with [jumpdest, swap1, pop]
    rcases uniswapSwapAdjustmentRuntimeCases (second := true) rd2546 hle1
        hin hlo hgap hfitPtr haw hawLo hread (by simp only [List.length_cons]; omega) with
      ⟨hover1, rdRev⟩ | ⟨hfit1, _, _, rd2567⟩
    · exact Or.inl ⟨uniswapSwapAdjustmentsRevert1 evm balance0 balance1 amount0In
        hb0 hb1 hi0 hle0 hfit0 hover1, rdRev⟩
    · have rd2570 := evm_run rd2567 with [jumpdest, swap1, pop]
      exact Or.inr ⟨uniswapSwapAdjustmentsSource evm balance0 balance1 amount0In amount1In
        hb0 hb1 hi0 hi1 hle0 hle1 hfit0 hfit1, hfit0, hfit1, _, _, rd2570⟩

end UniswapV2Pair
