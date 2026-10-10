import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_053
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_063
import Benchmarks.UniswapV4PoolManager.Values

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapZeroTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw state fee price ret params specified calculated protocol amount inv packed pool : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (hm : memLoad params mem = specified) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨18970⟩
      ([state, fee, price, ret, params, specified, calculated, fee, protocol, amount, inv, packed, pool, state]++R)
      mem aw rdata σ k C) :
    if specified = ⟨0⟩ then
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ret ([state, fee, ⟨0⟩, ⟨0⟩]++R)
        mem (M aw params ⟨32⟩) rdata σ k' C'
    else ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨18978⟩
      ([state, fee, price, ret, params, specified, calculated, fee, protocol, amount, inv, packed, pool, state]++R)
      mem (M aw params ⟨32⟩) rdata σ k' C' := by
  by_cases hz : specified = ⟨0⟩
  · rw [if_pos hz]
    have rd1 := poolManagerBlocks.poolManager_block_18970_taken
      (by change R.length+9+7 ≤ 1024; omega) (by rw [hm, hz]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManagerBlocks.poolManager_block_22148 (by change R.length+14 ≤ 1024; omega) hret rd1
    simp only [poolManagerBlocks.poolManager_block_22148_stack] at rd2
    exact ⟨_, _, by omega, rd2⟩
  · rw [if_neg hz]
    have rd := poolManagerBlocks.poolManager_block_18970_fallthrough
      (by change R.length+9+7 ≤ 1024; omega) (by rw [hm, isZero_eq_zero_of_ne hz]; rfl) h
    exact ⟨_, _, by omega, rd⟩

end Benchmarks.UniswapV4PoolManager
