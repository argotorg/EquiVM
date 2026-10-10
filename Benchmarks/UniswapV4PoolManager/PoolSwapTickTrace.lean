import Benchmarks.UniswapV4PoolManager.PoolSwapTickSource
import Benchmarks.UniswapV4PoolManager.PoolSwapTickBranchTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapCrossTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapBoundaryTickTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapRepriceTrace
import Benchmarks.UniswapV4PoolManager.BlockResultTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapTickMemory (mem : ByteArray) (id state : UInt256) (evm : State)
    (s : PoolSwapStepWords) (r : PoolSwapResultWords) (zeroForOne : Bool) : ByteArray :=
  if r.price = s.priceNext then
    (poolSwapBoundaryTick zeroForOne s.tickNext).toByteArray.write 0
      (if s.initialized then poolSwapCrossMemory mem id state s evm zeroForOne r.liquidity else mem)
      (state+UInt256.ofNat 32).toNat 32
  else if r.price = s.priceStart then mem
  else match tickPriceResult r.price with
    | none => mem
    | some tick => tick.toByteArray.write 0 mem (state+UInt256.ofNat 32).toNat 32

def poolSwapTickAW (aw step state : UInt256) (s : PoolSwapStepWords) (r : PoolSwapResultWords) : UInt256 :=
  let base := poolSwapTickBranchAW aw step state
  if r.price = s.priceNext then
    M (M (if s.initialized then poolSwapCrossAW (M base (step+UInt256.ofNat 64) ⟨32⟩) step state
      else M base (step+UInt256.ofNat 64) ⟨32⟩) (step+UInt256.ofNat 32) ⟨32⟩) (state+UInt256.ofNat 32) ⟨32⟩
  else if r.price = s.priceStart then M base step ⟨32⟩
  else M (M base step ⟨32⟩) (state+UInt256.ofNat 32) ⟨32⟩

theorem poolSwapTickTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {s : PoolSwapStepWords} {r : PoolSwapResultWords}
    {aw step state id x0 tag x1 params remaining calculated fee protocol amount : UInt256}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (zeroForOne : Bool) (hstack : R.length+34 ≤ 1024)
    (hI : evm.executionEnv = I) (htc : int24Canonical s.tickNext) (hlc : r.liquidity.toNat < 2^128)
    (hpc : r.price.toNat < 2^160) (hnc : s.priceNext.toNat < 2^160) (hsc : s.priceStart.toNat < 2^160)
    (hp : memLoad state mem = r.price) (hn : memLoad (step+UInt256.ofNat 96) mem = s.priceNext)
    (hs : memLoad step mem = s.priceStart) (hi : memLoad (step+UInt256.ofNat 64) mem = UInt256.fromBool s.initialized)
    (hg : memLoad (step+UInt256.ofNat 224) mem = s.feeGrowthGlobal)
    (ht : memLoad (step+UInt256.ofNat 32) mem = s.tickNext)
    (hl : memLoad (state+UInt256.ofNat 64) (tickCrossMemory mem id s.tickNext) = r.liquidity)
    (ht' : memLoad (step+UInt256.ofNat 32) (poolSwapCrossMemory mem id state s evm zeroForOne r.liquidity) = s.tickNext)
    (h : RD (deployedRuntime v) I g s0 ⟨19833⟩
      ([x0, tag, x1, params, remaining, calculated, fee, protocol, amount, UInt256.fromBool (!zeroForOne), step, poolSlot id, state] ++ R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0
      (fun _ post => ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19964⟩
        ([tag, x1, params, remaining, calculated, fee, protocol, amount, UInt256.fromBool (!zeroForOne), step, poolSlot id, state] ++ R)
        (poolSwapTickMemory mem id state evm s r zeroForOne) (poolSwapTickAW aw step state s r)
        rdata post.accountMap k' C') (fun _ _ => False) (poolSwapTickResult f evm id s r zeroForOne) := by
  obtain ⟨k1, C1, hC1, rd1⟩ := poolSwapTickBranchTrace v (by omega) hpc hnc hp hn h
  unfold poolSwapTickResult
  by_cases he : r.price = s.priceNext
  · rw [if_pos he] at rd1 ⊢
    by_cases hinit : s.initialized = true
    · rw [if_pos hinit]
      have rd2 := poolManagerBlocks.poolManager_block_19894_taken
        (by change R.length+2+12 ≤ 1024; omega) (by rw [hi, hinit]; decide)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      simp only [poolManagerBlocks.poolManager_block_19894_taken_stack] at rd2
      have hcross := poolSwapCrossTrace v zeroForOne (by omega) hI htc hlc hg ht hl rd2
      by_cases hperm : evm.executionEnv.perm = false
      · rw [if_pos hperm] at hcross ⊢
        exact hcross
      · rw [if_neg hperm] at hcross ⊢
        by_cases hfit : liquidityAddFits r.liquidity (EVM.signed (poolSwapCrossDelta zeroForOne (poolSwapCrossNet evm id s zeroForOne)))
        · rw [if_pos hfit] at hcross ⊢
          obtain ⟨k3, C3, hC3, rd3⟩ := hcross
          obtain ⟨k4, C4, hC4, rd4⟩ := poolSwapBoundaryTickTrace v zeroForOne (by omega) htc ht' rd3
          simp only [blockResultTrace, poolSwapTickMemory, poolSwapTickAW, if_pos he, if_pos hinit]
          exact ⟨k4, C4, by omega, rd4⟩
        · rw [if_neg hfit] at hcross ⊢
          exact hcross
    · rw [if_neg hinit]
      have hfalse : s.initialized = false := Bool.eq_false_of_not_eq_true hinit
      have rd2 := poolManagerBlocks.poolManager_block_19894_fallthrough
        (by change R.length+2+12 ≤ 1024; omega) (by rw [hi, hfalse]; rfl) rd1
      simp only [poolManagerBlocks.poolManager_block_19894_fallthrough_stack] at rd2
      obtain ⟨k3, C3, hC3, rd3⟩ := poolSwapBoundaryTickTrace v zeroForOne (by omega) htc ht rd2
      simp only [blockResultTrace, poolSwapTickMemory, poolSwapTickAW, if_pos he, if_neg hinit]
      exact ⟨k3, C3, by omega, rd3⟩
  · rw [if_neg he] at rd1 ⊢
    have hprice := poolSwapRepriceTrace v hstack hpc hsc hs rd1
    unfold poolSwapRepriceResult
    by_cases hsame : r.price = s.priceStart
    · rw [if_pos hsame] at hprice ⊢
      obtain ⟨k2, C2, hC2, rd2⟩ := hprice
      simp only [blockResultTrace, poolSwapTickMemory, poolSwapTickAW, if_neg he, if_pos hsame]
      exact ⟨k2, C2, hC1.trans hC2, rd2⟩
    · rw [if_neg hsame] at hprice ⊢
      cases hresult : tickPriceResult r.price with
      | none =>
        rw [hresult] at hprice
        exact hprice
      | some tick =>
        rw [hresult] at hprice
        obtain ⟨k2, C2, hC2, rd2⟩ := hprice
        simp only [blockResultTrace, poolSwapTickMemory, poolSwapTickAW, if_neg he, if_neg hsame, hresult]
        exact ⟨k2, C2, hC1.trans hC2, rd2⟩

end Benchmarks.UniswapV4PoolManager
