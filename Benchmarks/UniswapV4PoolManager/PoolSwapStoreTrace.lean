import Benchmarks.UniswapV4PoolManager.PoolSwapSlot0StoreTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapStoreStatic
import Benchmarks.UniswapV4PoolManager.PoolSwapMemoryFields
import Benchmarks.UniswapV4PoolManager.ReachCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapGrowthStoreTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id growth step dummy : UInt256} {zeroForOne : Bool}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+5 ≤ 1024)
    (hI : evm.executionEnv = I) (hperm : I.perm = true)
    (hm : memLoad (step+UInt256.ofNat 224) mem = growth)
    (h : RD (deployedRuntime v) I g s0 ⟨21698⟩
      (dummy :: step :: poolSlot id :: UInt256.fromBool (!zeroForOne) :: R) mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨21716⟩ (UInt256.fromBool (!zeroForOne) :: R)
      mem (M aw (step+UInt256.ofNat 224) ⟨32⟩) rdata (poolSwapGrowthPost evm id growth zeroForOne).accountMap k' C' := by
  cases zeroForOne
  · have rd1 := poolManagerBlocks.poolManager_block_21698_fallthrough hstack (by rfl) h
    simp only [poolManagerBlocks.poolManager_block_21698_fallthrough_stack] at rd1
    obtain ⟨k2, C2, rd2⟩ := poolManagerBlocks.poolManager_block_21706
      (by change R.length+1+4 ≤ 1024; omega) hperm rd1
    simp only [poolManagerBlocks.poolManager_block_21706_stack, hm] at rd2
    refine ⟨k2, C2, ?_⟩
    rw [poolSwapGrowthPost, storageStore_accountMap, hI]
    exact rd2
  · have rd1 := poolManagerBlocks.poolManager_block_21698_taken hstack (by decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_21698_taken_stack] at rd1
    obtain ⟨k2, C2, rd2⟩ := poolManagerBlocks.poolManager_block_21798
      (by change R.length+1+4 ≤ 1024; omega) hperm
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_21798_stack, hm] at rd2
    refine ⟨k2, C2, ?_⟩
    rw [poolSwapGrowthPost, storageStore_accountMap, hI]
    exact rd2

def poolSwapStoreAW (aw state step : UInt256) : UInt256 :=
  M (poolSwapSlot0AW aw state) (step+UInt256.ofNat 224) ⟨32⟩

theorem poolSwapStoreTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id packed remaining ret params calculated fee protocol amount step state : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+15 ≤ 1024)
    (hI : evm.executionEnv = I) (hm : PoolSwapMemoryView mem step state params s r p)
    (hp : r.price.toNat < 2^160) (hl : r.liquidity.toNat < 2^128)
    (h : RD (deployedRuntime v) I g s0 ⟨21536⟩
      ([remaining, ret, params, calculated, packed, fee, protocol, amount,
        UInt256.fromBool (!p.zeroForOne), step, poolSlot id, state]++R) mem aw rdata evm.accountMap k C) :
    if I.perm = false then RDstatic (deployedRuntime v) g s0 else
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨21716⟩
        ([UInt256.fromBool (!p.zeroForOne), remaining, params, calculated, state, fee, amount, ret]++R)
        mem (poolSwapStoreAW aw state step) rdata (poolSwapFinishPost evm id packed s r p.zeroForOne).accountMap k' C' := by
  by_cases hperm : I.perm = false
  · rw [if_pos hperm]
    exact poolSwapStoreStatic hstack hperm h
  · rw [if_neg hperm]
    apply RD_retainCost (h := h)
    intro budget start hin
    obtain ⟨dummy, k1, C1, rd1⟩ := poolSwapSlot0StoreTrace v hstack hI
      (Bool.eq_true_of_not_eq_false hperm) hp hl hm.price hm.tick hm.liquidity hin
    have hIp := (poolSwapLiquidityPost_executionEnv (poolSwapSlot0Post evm id packed r) id r.liquidity).trans
      ((poolSwapSlot0Post_executionEnv evm id packed r).trans hI)
    exact poolSwapGrowthStoreTrace v (by change R.length+7+5 ≤ 1024; omega) hIp
      (Bool.eq_true_of_not_eq_false hperm) hm.growth rd1

end Benchmarks.UniswapV4PoolManager
