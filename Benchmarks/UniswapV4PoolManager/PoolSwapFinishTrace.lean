import Benchmarks.UniswapV4PoolManager.PoolSwapFinishSource
import Benchmarks.UniswapV4PoolManager.PoolSwapStoreTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapDeltaTrace
import Benchmarks.UniswapV4PoolManager.FunctionResultTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapOriginalAccounts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapFinishAW (aw state step params : UInt256) (p : PoolSwapParamsWords) : UInt256 :=
  poolSwapDeltaAW (poolSwapStoreAW aw state step) params (poolSwapCalculatedFirst p.zeroForOne p.amountSpecified)

theorem poolSwapFinishTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} (f : Frame)
    {mem rdata : ByteArray} {aw id packed remaining ret params calculated fee protocol amount step state : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+15 ≤ 1024)
    (hI : evm.executionEnv = I) (hm : PoolSwapMemoryView mem step state params s r p)
    (hp : r.price.toNat < 2^160) (hl : r.liquidity.toNat < 2^128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨21536⟩
      ([remaining, ret, params, calculated, packed, fee, protocol, amount,
        UInt256.fromBool (!p.zeroForOne), step, poolSlot id, state]++R) mem aw rdata evm.accountMap k C) :
    let delta := poolSwapDeltaWord (poolSwapCalculatedFirst p.zeroForOne p.amountSpecified) p.amountSpecified remaining calculated
    functionResultTrace (deployedRuntime v) g s0 (fun post values =>
      post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧ values = some (poolSwapReturnValues delta fee amount r) ∧
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ret ([state, fee, amount, delta]++R)
        mem (poolSwapFinishAW aw state step params p) rdata post.accountMap k' C')
      (poolSwapFinishResult f evm id packed s r p remaining calculated fee amount) := by
  have hs := poolSwapStoreTrace v hstack hI hm hp hl h
  dsimp only [poolSwapFinishResult]
  rw [hI]
  by_cases hperm : I.perm = false
  · rw [if_pos hperm] at hs ⊢
    exact hs
  · rw [if_neg hperm] at hs ⊢
    obtain ⟨k1, C1, hC1, rd1⟩ := hs
    have hd := poolSwapDeltaTrace v (by omega) hm.specified hret rd1
    dsimp only at hd
    by_cases hf : poolSwapDeltaFits (poolSwapCalculatedFirst p.zeroForOne p.amountSpecified) p.amountSpecified remaining calculated
    · rw [if_pos hf] at hd ⊢
      obtain ⟨k2, C2, hC2, rd2⟩ := hd
      exact ⟨(poolSwapFinishPost_executionEnv evm id packed s r p.zeroForOne).trans hI,
        poolSwapFinishPost_σ₀ .., rfl, k2, C2, by omega, rd2⟩
    · rw [if_neg hf] at hd ⊢
      exact hd

end Benchmarks.UniswapV4PoolManager
