import Benchmarks.UniswapV4PoolManager.PoolSwapFeeInitSource
import Benchmarks.UniswapV4PoolManager.ProtocolSwapFeeTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapFeeInitTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw protocol lpFee x1 x2 x3 x4 x5 x6 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+12 ≤ 1024)
    (hp : protocol.toNat < 2^16) (hl : lpFee.toNat < 2^24)
    (h : RD (deployedRuntime v) I g s0 ⟨18941⟩
      (lpFee :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: protocol :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨18951⟩
      (poolSwapEffectiveFee protocol lpFee :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: protocol :: R)
      mem aw rdata σ k' C' := by
  have hclean : UInt256.land protocol (UInt256.ofNat 65535) = protocol :=
    u256LandMaskCleanOfToNat _ _ rfl hp
  by_cases hz : protocol = ⟨0⟩
  · have rd := poolManagerBlocks.poolManager_block_18941_fallthrough (by omega) (by rw [hclean, hz]; rfl) h
    rw [poolSwapEffectiveFee, if_pos hz]
    exact ⟨_, _, by omega, rd⟩
  · have rd := poolManagerBlocks.poolManager_block_18941_taken (by omega) (by rw [hclean]; exact hz)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    rw [poolSwapEffectiveFee, if_neg hz]
    exact ⟨_, _, by omega, protocolSwapFeeTrace v hstack hl rd⟩

end Benchmarks.UniswapV4PoolManager
