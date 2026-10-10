import Benchmarks.UniswapV4PoolManager.PoolModifyFeeDelta
import Benchmarks.UniswapV4PoolManager.BalanceDeltaTrace
import Benchmarks.UniswapV4PoolManager.BlockResultTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolModifyFeeDeltaTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw a b x2 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {delta : Int}
    {k C : Nat} {R : List UInt256} (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+17 ≤ 1024)
    (hlo : -(2^127 : Int) ≤ delta) (hhi : delta < 2^127)
    (h : RD (deployedRuntime v) I g s0 ⟨12458⟩
      (a :: ⟨5993⟩ :: ⟨5999⟩ :: b :: x2 :: EVM.wordOfInt delta :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post => post = evm ∧ ∃ k' C',
      RD (deployedRuntime v) I g s0 (if delta < 0 then ⟨6620⟩ else ⟨6036⟩)
        (balanceDeltaOutputStack a b x2 (EVM.wordOfInt delta) x4 x5 x6 x7 x8 x9 x10 x11 x12 R)
        mem aw rdata post.accountMap k' C') (fun _ _ => False) (poolModifyFeeDeltaResult f evm a b) := by
  by_cases ha : a.toNat < 2^127
  · obtain ⟨k1, C1, rd1⟩ := uintToInt128Trace v (by simp only [List.length_cons]; omega) ha
      (by rw [deployedRuntime_jumps]; jump_dest) h
    have rd2 := poolManagerBlocks.poolManager_block_5993 (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_5993_stack] at rd2
    by_cases hb : b.toNat < 2^127
    · rw [poolModifyFeeDeltaResult, if_pos (show a.toNat < 2^127 ∧ b.toNat < 2^127 from ⟨ha, hb⟩)]
      obtain ⟨k3, C3, rd3⟩ := uintToInt128Trace v (by simp only [List.length_cons]; omega) hb
        (by rw [deployedRuntime_jumps]; jump_dest) rd2
      exact ⟨rfl, balanceDeltaFeeTrace v (by omega) hlo hhi rd3⟩
    · rw [poolModifyFeeDeltaResult, if_neg (show ¬(a.toNat < 2^127 ∧ b.toNat < 2^127) from fun hh => hb hh.2)]
      exact uintToInt128TraceReverts v (by simp only [List.length_cons]; omega) hb rd2
  · rw [poolModifyFeeDeltaResult, if_neg (show ¬(a.toNat < 2^127 ∧ b.toNat < 2^127) from fun hh => ha hh.1)]
    exact uintToInt128TraceReverts v (by simp only [List.length_cons]; omega) ha h

end Benchmarks.UniswapV4PoolManager
