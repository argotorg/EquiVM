import Benchmarks.UniswapV4PoolManager.Allocate160Trace
import Benchmarks.UniswapV4PoolManager.SwapPoolMemory
import Benchmarks.UniswapV4PoolManager.PoolKeyView
import Benchmarks.UniswapV4PoolManager.MemoryAccessCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapPoolAllocateTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {σ : AccountMap}
    {mem rdata : ByteArray} {aw free rawFee before amount src len id keyPtr paramsPtr junk : UInt256}
    {key : PoolKeyWords} {p : SwapParamsWords} {R : List UInt256} {k C : Nat}
    (v : PoolManagerImmutables) (hstack : R.length+20 ≤ 1024)
    (hkey : PoolKeyView mem keyPtr key)
    (hp : MemorySlice mem paramsPtr.toNat (wordBytes (swapParamsWordList p)))
    (hspacing : int24Canonical key.tickSpacing) (hlimit : p.priceLimit.toNat < 2^160)
    (hpf : paramsPtr.toNat+96 < UInt256.size) (hf : free.toNat+160 ≤ solcMaxU64)
    (hfree : memLoad (UInt256.ofNat 64) mem = free) (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 ⟨1614⟩
      ([rawFee, before, amount, src, len, poolSlot id, paramsPtr+UInt256.ofNat 64,
        keyPtr, id, keyPtr+UInt256.ofNat 128, paramsPtr, junk]++R) mem aw rdata σ k C) :
    ∃ aw' k' C', Cₘ aw' ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨1669⟩
      ([amount, key.tickSpacing, UInt256.fromBool p.zeroForOne, p.priceLimit, rawFee,
        poolSlot id, src, len, before, free, keyPtr, id, keyPtr+UInt256.ofNat 128, paramsPtr, junk]++R)
      (writeWord mem 64 (free+UInt256.ofNat 160)) aw' rdata σ k' C' := by
  have hz : UInt256.isZero (UInt256.isZero (memLoad paramsPtr mem)) = UInt256.fromBool p.zeroForOne := by
    rw [hp.word_load (i := 0) (word := UInt256.fromBool p.zeroForOne) rfl (by omega)]
    cases p.zeroForOne <;> rfl
  have hl : memLoad (paramsPtr+UInt256.ofNat 64) mem = p.priceLimit :=
    hp.word_load (i := 2) rfl (uadd_word_ofNat_toNat paramsPtr 64 (by omega))
  have hs : UInt256.signextend (UInt256.ofNat 2) key.tickSpacing = key.tickSpacing :=
    (signextend24_eq_iff _).mpr hspacing
  have hmask : UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) p.priceLimit = p.priceLimit :=
    (u256_land_comm _ _).trans (solcAddrMask_clean hlimit)
  have rd1 := poolManagerBlocks.poolManager_block_1614 (R := junk::R)
    (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_1614_stack,
    hkey.load (i := 3) rfl, hs, hz, hl, hmask, hfree] at rd1
  have rd2 := allocate160CostTrace (ret := UInt256.ofNat 1669)
    (R := [amount, key.tickSpacing, UInt256.fromBool p.zeroForOne, p.priceLimit, rawFee,
      poolSlot id, src, len, before, free, keyPtr, id, keyPtr+UInt256.ofNat 128, paramsPtr, junk]++R)
    v (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hf
    (by rw [deployedRuntime_jumps]; jump_dest) rd1
  have hc := memoryAccessCost_covers aw
    [(keyPtr+UInt256.ofNat 96, ⟨32⟩), (paramsPtr, ⟨32⟩), (paramsPtr+UInt256.ofNat 64, ⟨32⟩),
      (UInt256.ofNat 64, ⟨32⟩), (UInt256.ofNat 64, ⟨32⟩)]
  dsimp only [memoryAccessWords, memoryAccessCost] at hc
  exact ⟨_, _, _, by omega, rd2⟩

end Benchmarks.UniswapV4PoolManager
