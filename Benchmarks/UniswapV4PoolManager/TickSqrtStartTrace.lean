import Benchmarks.UniswapV4PoolManager.TickSqrtConditionalTrace
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_046
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_049

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickSqrtInitialEncoded (absTick : UInt256) :
    UInt256.xor (UInt256.ofNat 340282366920938463463374607431768211456)
      (UInt256.mul (UInt256.ofNat 680547720999483427021191124463843360769)
        (UInt256.land absTick (UInt256.ofNat 1))) = tickSqrtInitial absTick := by
  unfold tickSqrtInitial
  by_cases hn : UInt256.land absTick (UInt256.ofNat 1) ≠ ⟨0⟩
  · rw [if_pos hn]
    have he := land_one_eq_one_of_ne_zero hn
    change UInt256.land absTick (UInt256.ofNat 1) = UInt256.ofNat 1 at he
    rw [he]
    decide
  · rw [if_neg hn, not_not.mp hn]
    decide

def tickSqrtFirstStage (absTick : UInt256) : UInt256 :=
  tickSqrtStage absTick (tickSqrtInitial absTick) (UInt256.ofNat 2)
    (UInt256.ofNat 340248342086729790484326174814286782778)

theorem tickSqrtStartTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret absTick tick : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 7 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨16751⟩ (absTick :: ret :: tick :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16809⟩
      (absTick :: tick :: tickSqrtFirstStage absTick :: UInt256.ofNat 4294967295 :: ret :: R)
      mem aw rdata σ k' C' := by
  apply tickSqrtConditionalTrace (fun p => absTick :: tick :: p :: UInt256.ofNat 4294967295 :: ret :: R)
  · intro hz
    have rd1 := poolManagerBlocks.poolManager_block_16751_fallthrough hstack hz h
    simp only [poolManagerBlocks.poolManager_block_16751_fallthrough_stack, tickSqrtInitialEncoded] at rd1
    exact ⟨_, _, rd1⟩
  · intro hn
    have rd1 := poolManagerBlocks.poolManager_block_16751_taken hstack hn
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_16751_taken_stack, tickSqrtInitialEncoded] at rd1
    have rd2 := poolManagerBlocks.poolManager_block_17538 (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    change RD (deployedRuntime v) I g s0 ⟨16809⟩
      (absTick :: tick :: UInt256.shiftRight
        (UInt256.mul (UInt256.ofNat 340248342086729790484326174814286782778) (tickSqrtInitial absTick))
        (UInt256.ofNat 128) :: UInt256.ofNat 4294967295 :: ret :: R) mem aw rdata σ _ _ at rd2
    rw [u256_mul_comm (UInt256.ofNat 340248342086729790484326174814286782778) (tickSqrtInitial absTick)] at rd2
    exact ⟨_, _, rd2⟩

end Benchmarks.UniswapV4PoolManager
