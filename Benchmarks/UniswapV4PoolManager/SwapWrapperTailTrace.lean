import Benchmarks.UniswapV4PoolManager.SwapWrapperTailMemory
import Benchmarks.UniswapV4PoolManager.SwapWrapperEventTrace
import Benchmarks.UniswapV4PoolManager.SwapWrapperSource
import Benchmarks.UniswapV4PoolManager.FunctionResultTrace
import Benchmarks.UniswapV4PoolManager.ProtocolFeesUpdatePaidTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def swapWrapperTailReturn (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 evm : State)
    (mem rdata : ByteArray) (free delta fee amount params x8 x9 x10 x11 x12 x13 hookPtr junk : UInt256)
    (currency : AccountAddress) (r : PoolSwapResultWords) (R : List UInt256)
    (post : State) (values : Option (List Value)) : Prop :=
  post = swapWrapperFeePost evm currency amount ∧ values = some [.int (EVM.signed delta)] ∧
    ∃ aw k C, Cₘ aw ≤ C ∧ RD (deployedRuntime v) I g s0 ⟨1930⟩
      ([memLoad hookPtr (swapWrapperTailMemory mem free delta fee amount currency r),
        UInt256.ofNat 1461501637330902918203684832716283019655932542975,
        x12, params, delta, x8, x9, x10, x11, x12, x13, hookPtr, UInt256.ofNat 32, junk]++R)
      (swapWrapperTailMemory mem free delta fee amount currency r) aw rdata post.accountMap k C

theorem swapWrapperTailTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {free aw state delta fee amount id params x8 x9 x10 x11 x12 x13 hookPtr junk : UInt256}
    {currency : AccountAddress} {r : PoolSwapResultWords} {R : List UInt256} {k C : Nat}
    (v : PoolManagerImmutables) (hstack : R.length+21 ≤ 1024) (hI : evm.executionEnv = I)
    (hr : WordStructView mem state (poolSwapResultWordList r)) (hp : r.price.toNat < 2^160)
    (hl : r.liquidity.toNat < 2^128) (ht : int24Canonical r.tick) (he : fee.toNat < 2^24)
    (hf : free.toNat+192 < UInt256.size) (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (hstate : 96 ≤ state.toNat) (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 ⟨1755⟩
      ([state, fee, amount, delta, id, UInt256.ofNat 16777215, params, accountWord currency,
        x8, x9, x10, x11, x12, x13, hookPtr, UInt256.ofNat 32, junk]++R)
      mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0
      (swapWrapperTailReturn v I g s0 evm mem rdata free delta fee amount params x8 x9 x10 x11 x12 x13 hookPtr junk currency r R)
      (swapWrapperTailResult f evm currency delta amount) := by
  have hmem : 96 ≤ mem.size := by have hh := hr.inBounds; change state.toNat+96 ≤ mem.size at hh; omega
  by_cases hz : 0 < amount.toNat
  · have hn : amount ≠ UInt256.ofNat 0 := by
      intro hh
      have hh' : amount.toNat = 0 := congrArg UInt256.toNat hh
      omega
    have rd1 := poolManagerBlocks.poolManager_block_1755_taken (by change R.length+9+10 ≤ 1024; omega) hn
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    change RD _ _ _ _ ⟨2003⟩
      ([accountWord currency, amount, fee, UInt256.ofNat 16777215, id, state, params, delta,
        x8, x9, x10, x11, x12, x13, hookPtr, UInt256.ofNat 32, junk]++R) mem aw rdata evm.accountMap _ _ at rd1
    by_cases hperm : evm.executionEnv.perm = false
    · simp only [swapWrapperTailResult, if_pos hperm, functionResultTrace]
      exact protocolFeesUpdateStatic (by change R.length+18 ≤ 1024; omega) (by rw [← hI]; exact hperm) rd1
    · have hperm' : I.perm = true := by rw [← hI]; exact Bool.eq_true_of_not_eq_false hperm
      obtain ⟨k2, C2, hp2, rd2⟩ := protocolFeesUpdatePaidTrace v (by omega) hI hperm' (by omega) rd1
      have hr' := swapWrapperFeeMemory_result hr currency amount (by omega)
      have hfree' := (swapWrapperFeeMemory_free mem currency amount hmem).trans hfree
      simp only [swapWrapperFeeMemory, if_pos hz] at hr' hfree'
      obtain ⟨aw3, k3, C3, _, hp3, rd3⟩ := swapWrapperEventTrace (R := junk :: R) v
        (by change R.length+1+20 ≤ 1024; omega) hperm' hr' hp hl ht he hf hfree' rd2
      simp only [swapWrapperTailResult, if_neg hperm, functionResultTrace]
      refine ⟨rfl, rfl, aw3, k3, C3, by omega, ?_⟩
      simpa only [swapWrapperFeePost, swapWrapperTailMemory, swapWrapperFeeMemory, if_pos hz] using rd3
  · have ha0 : amount = UInt256.ofNat 0 := uint256_toNat_eq_zero (by omega)
    have rd1 := poolManagerBlocks.poolManager_block_1755_fallthrough
      (by change R.length+9+10 ≤ 1024; omega) ha0 h
    change RD _ _ _ _ ⟨1766⟩
      ([accountWord currency, amount, fee, UInt256.ofNat 16777215, id, state, params, delta,
        x8, x9, x10, x11, x12, x13, hookPtr, UInt256.ofNat 32, junk]++R) mem aw rdata evm.accountMap _ _ at rd1
    by_cases hperm : evm.executionEnv.perm = false
    · simp only [swapWrapperTailResult, if_pos hperm, functionResultTrace]
      exact swapWrapperEventStatic (R := junk :: R) (by change R.length+1+20 ≤ 1024; omega)
        (by rw [← hI]; exact hperm) rd1
    · have hperm' : I.perm = true := by rw [← hI]; exact Bool.eq_true_of_not_eq_false hperm
      obtain ⟨aw2, k2, C2, _, hp2, rd2⟩ := swapWrapperEventTrace (R := junk :: R) v
        (by change R.length+1+20 ≤ 1024; omega) hperm' hr hp hl ht he hf hfree rd1
      simp only [swapWrapperTailResult, if_neg hperm, functionResultTrace]
      refine ⟨rfl, rfl, aw2, k2, C2, by omega, ?_⟩
      simpa only [swapWrapperFeePost, swapWrapperTailMemory, swapWrapperFeeMemory, if_neg hz] using rd2

end Benchmarks.UniswapV4PoolManager
