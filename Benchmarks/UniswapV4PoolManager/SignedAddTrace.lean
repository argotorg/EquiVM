import Benchmarks.UniswapV4PoolManager.SignedArithmetic
import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_022
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_042

/-! The checked signed-256 addition routine shared by currency accounting paths. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem checkedSignedAddPass {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 6 ≤ 1024) (hfit : int256Fits (EVM.signed a + EVM.signed b))
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨15145⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret ((a + b) :: R) mem aw rdata σ k' C' := by
  have hnext := poolManagerBlocks.poolManager_block_15145_fallthrough hstack
    (by rw [signedAddGuard, decide_eq_false (not_not.mpr hfit)]; rfl) h
  exact ⟨_, _, poolManagerBlocks.poolManager_block_15171
    (by simp only [List.length_cons]; omega) hret hnext⟩

theorem checkedSignedAddReverts {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 6 ≤ 1024) (hfit : ¬int256Fits (EVM.signed a + EVM.signed b))
    (h : RD (deployedRuntime v) I g s0 ⟨15145⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 7572) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have hnext := poolManagerBlocks.poolManager_block_15145_taken hstack
    (by rw [signedAddGuard, decide_eq_true hfit]; decide) hj h
  exact poolManagerBlocks.poolManager_block_7572
    (by simp only [poolManagerBlocks.poolManager_block_15145_taken_stack, List.length_cons]; omega) hnext

end Benchmarks.UniswapV4PoolManager
