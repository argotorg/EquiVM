import Benchmarks.UniswapV4PoolManager.PoolModifyPricePrelude
import Benchmarks.UniswapV4PoolManager.Signed128Range
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_018
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_019

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolModifyAmountGuardTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw junk lower upper : UInt256} {delta : Int}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+5 ≤ 1024) (hd : signedFits ⟨128, by decide⟩ delta)
    (h : RD (deployedRuntime v) I g s0 ⟨6036⟩ (junk :: lower :: upper :: EVM.wordOfInt delta :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 (if delta ≠ 0 then ⟨6296⟩ else ⟨6046⟩)
      (lower :: upper :: EVM.wordOfInt delta :: R) mem aw rdata σ k' C' := by
  have hc : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt delta) = EVM.wordOfInt delta :=
    signextend128_wordOfInt hd.1 hd.2
  by_cases hz : delta ≠ 0
  · rw [if_pos hz]
    have rd1 := poolManagerBlocks.poolManager_block_6036_taken hstack
      (by rw [hc]; exact fun hh => hz ((wordOfInt_eq_zero_iff (signedFits128_int256 hd)).mp hh))
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact ⟨_, _, rd1⟩
  · rw [if_neg hz]
    have rd1 := poolManagerBlocks.poolManager_block_6036_fallthrough hstack
      (by rw [hc]; exact (wordOfInt_eq_zero_iff (signedFits128_int256 hd)).mpr (by omega)) h
    exact ⟨_, _, rd1⟩

theorem poolModifyPriceExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id lower upper delta oldDelta : UInt256}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+7 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (h : RD (deployedRuntime v) I g s0 ⟨6296⟩ (lower :: upper :: delta :: oldDelta :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0
      (if poolCurrentTick evm id < EVM.signed lower then ⟨6344⟩ else ⟨6398⟩)
      (slot0TickWord (poolSlot0Word evm id) :: poolSqrtPriceWord evm id :: lower :: upper :: delta :: R)
      mem (M aw (UInt256.ofNat 128) ⟨32⟩) rdata evm.accountMap k' C' := by
  have hs : solcSlotWordAt (memLoad (UInt256.ofNat 128) mem) evm.accountMap I = poolSlot0Word evm id := by
    rw [hm]
    exact (storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])).symm
  dsimp only [solcSlotWordAt, solcSlotWord] at hs
  by_cases hb : poolCurrentTick evm id < EVM.signed lower
  · rw [if_pos hb]
    dsimp only [poolCurrentTick] at hb
    have hg : UInt256.isZero (UInt256.slt (slot0TickWord (poolSlot0Word evm id)) lower) = UInt256.ofNat 0 := by
      rw [slt_signed, decide_eq_true hb]
      rfl
    obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_6296_fallthrough hstack (by rw [hs]; exact hg) h
    simp only [poolManagerBlocks.poolManager_block_6296_fallthrough_stack, hs] at rd1
    exact ⟨k1, C1, rd1⟩
  · rw [if_neg hb]
    dsimp only [poolCurrentTick] at hb
    have hg : UInt256.isZero (UInt256.slt (slot0TickWord (poolSlot0Word evm id)) lower) ≠ UInt256.ofNat 0 := by
      rw [slt_signed, decide_eq_false hb]
      decide
    obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_6296_taken hstack (by rw [hs]; exact hg)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_6296_taken_stack, hs] at rd1
    exact ⟨k1, C1, rd1⟩

theorem poolModifyPriceTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id lower upper delta oldDelta : UInt256}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+7 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (h : RD (deployedRuntime v) I g s0 ⟨6296⟩ (lower :: upper :: delta :: oldDelta :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0
      (if poolCurrentTick evm id < EVM.signed lower then ⟨6344⟩ else ⟨6398⟩)
      (slot0TickWord (poolSlot0Word evm id) :: poolSqrtPriceWord evm id :: lower :: upper :: delta :: R)
      mem aw' rdata evm.accountMap k' C' := by
  obtain ⟨k', C', rd⟩ := poolModifyPriceExactTrace v hstack hI hm h
  exact ⟨_, k', C', rd⟩

theorem poolModifyUpperRegionTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw tick sqrtPrice lower upper : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+5 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨6398⟩
      (tick :: sqrtPrice :: lower :: upper :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0
      (if EVM.signed tick < EVM.signed upper then ⟨6410⟩ else ⟨6569⟩)
      (upper :: lower :: sqrtPrice :: R) mem aw rdata σ k' C' := by
  by_cases ht : EVM.signed tick < EVM.signed upper
  · rw [if_pos ht]
    exact ⟨_, _, poolManagerBlocks.poolManager_block_6398_fallthrough hstack
      (by rw [slt_signed, decide_eq_true ht]; decide) h⟩
  · rw [if_neg ht]
    exact ⟨_, _, poolManagerBlocks.poolManager_block_6398_taken hstack
      (by rw [slt_signed, decide_eq_false ht]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h⟩

end Benchmarks.UniswapV4PoolManager
