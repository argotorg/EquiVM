import Examples.UniswapV2Pair.PairBalanceCallRuntime
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPairBalanceDepthReverts
    {g : Sat256} {s0 : State} {I : ExecutionEnv} {site : PairBalanceCallSite}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {aw ptr target endPtr selector : UInt256} {R : List UInt256} {k C : Nat}
    (rd : RD uniswapV2PairBytecode I g s0 site.pc
      (target :: target :: ptr :: ⟨36⟩ :: ptr :: ⟨32⟩ :: endPtr :: selector :: target :: R)
      mem aw rdata (cA, σ) k C)
    (hcode : extCodeSizeWord σ target ≠ ⟨0⟩) (hdepth : I.depth = 1024)
    (hov : R.length + 12 ≤ 1024) : RDrev uniswapV2PairBytecode g s0 := by
  obtain ⟨_, _, _, rdCall⟩ := RD.solcExtcodesizeGuardOkGas (okPc := site.pc + ⟨12⟩) rd hcode
    (by cases site <;> native_decide) (by cases site <;> native_decide)
    (by cases site <;> native_decide) (by cases site <;> native_decide)
    (by cases site <;> native_decide) (by cases site <;> native_decide)
    (by cases site <;> native_decide) (by cases site <;> native_decide)
    (by cases site <;> native_decide) (by cases site <;> native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdResult⟩ := RD.solcStaticcallDepthLimit rdCall (by cases site <;> native_decide)
    hdepth (by simp only [List.length_cons]; omega)
  exact RD.solcCallSuccessGuardMissing (okPc := site.pc + ⟨32⟩) rdResult rfl
    (by cases site <;> native_decide) (by cases site <;> native_decide)
    (by cases site <;> native_decide) (by cases site <;> native_decide)
    (by cases site <;> native_decide) (by cases site <;> native_decide)
    (by cases site <;> native_decide) (by cases site <;> native_decide)
    (by cases site <;> native_decide) (by cases site <;> native_decide)
    (by cases site <;> native_decide) (by cases site <;> native_decide)
    (by decide) (by simp only [List.length_cons]; omega)

end UniswapV2Pair
