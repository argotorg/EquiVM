import Benchmarks.UniswapV4PoolManager.PoolFeeInsideMemory
import Benchmarks.UniswapV4PoolManager.SignedComparison
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_017
import Benchmarks.UniswapV4PoolManager.MemoryGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolFeeInsideStartStack (evm : State) (id lower upper x0 x1 x2 x3 x4 x5 delta : UInt256)
    (R : List UInt256) : List UInt256 :=
  slot0TickWord (poolSlot0Word evm id) :: tickSlot id (EVM.signed upper) :: delta ::
    x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: upper :: tickSlot id (EVM.signed lower) :: lower :: R

open poolManagerBlocks in
theorem poolFeeInsideStartExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id lower upper x0 x1 x2 x3 x4 x5 delta : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+14 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hl : int24Canonical lower) (hu : int24Canonical upper)
    (h : RD (deployedRuntime v) I g s0 ⟨5722⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: upper :: delta :: lower :: R) mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0
      (if poolCurrentTick evm id < EVM.signed lower then ⟨5777⟩ else ⟨6863⟩)
      (poolFeeInsideStartStack evm id lower upper x0 x1 x2 x3 x4 x5 delta R)
      (poolFeeInsideMemory mem id lower upper) (M aw (UInt256.ofNat 128) ⟨32⟩) rdata evm.accountMap k' C' := by
  have hl' : UInt256.signextend (UInt256.ofNat 2) lower = lower := (signextend24_eq_iff lower).mpr hl
  have hu' : UInt256.signextend (UInt256.ofNat 2) upper = upper := (signextend24_eq_iff upper).mpr hu
  have hmem' : poolManager_block_5722_fallthrough_memory (mem := mem) (x6 := upper) (x8 := lower) =
      poolFeeInsideMemory mem id lower upper := by
    simp only [poolManager_block_5722_fallthrough_memory, hl', hu', hm]
    rfl
  have hm' : memLoad (UInt256.ofNat 128) (poolFeeInsideMemory mem id lower upper) = poolSlot id := by
    have hp := poolFeeInsideMemory_load (mem := mem) id lower upper (UInt256.ofNat 128) (by decide) hmem
    rw [hp]
    exact hm
  have hslot : solcSlotWordAt
      (memLoad (UInt256.ofNat 128) (poolManager_block_5722_fallthrough_memory
        (mem := mem) (x6 := upper) (x8 := lower))) evm.accountMap I = poolSlot0Word evm id := by
    rw [hmem', hm']
    exact (storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])).symm
  dsimp only [solcSlotWordAt, solcSlotWord, poolManager_block_5722_fallthrough_memory] at hslot
  have hlohash := tickHashMem_slot id lower mem
  have hhihash := tickHashMem_slot id upper (twoWordHashMem lower (poolSlot id+⟨4⟩) mem)
  change keccakWord ⟨0⟩ (UInt256.ofNat 64) ((poolSlot id+UInt256.ofNat 4).toByteArray.write 0
    (lower.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) = _ at hlohash
  change keccakWord ⟨0⟩ (UInt256.ofNat 64) ((poolSlot id+UInt256.ofNat 4).toByteArray.write 0
    (upper.toByteArray.write 0 ((poolSlot id+UInt256.ofNat 4).toByteArray.write 0
      (lower.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)
      (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) = _ at hhihash
  have h5 : 5 ≤ (M aw (UInt256.ofNat 128) ⟨32⟩).toNat :=
    memoryWords_ge_span aw (UInt256.ofNat 128) ⟨32⟩ (by decide)
  have h0 : M (M aw (UInt256.ofNat 128) ⟨32⟩) ⟨0⟩ ⟨32⟩ = M aw (UInt256.ofNat 128) ⟨32⟩ :=
    memoryWords_eq_self (by change 0+32 ≤ _*32; omega)
  have h32 : M (M aw (UInt256.ofNat 128) ⟨32⟩) (UInt256.ofNat 32) ⟨32⟩ = M aw (UInt256.ofNat 128) ⟨32⟩ :=
    memoryWords_eq_self (by change 32+32 ≤ _*32; omega)
  have h64 : M (M aw (UInt256.ofNat 128) ⟨32⟩) ⟨0⟩ (UInt256.ofNat 64) = M aw (UInt256.ofNat 128) ⟨32⟩ :=
    memoryWords_eq_self (by change 0+64 ≤ _*32; omega)
  by_cases hb : poolCurrentTick evm id < EVM.signed lower
  · rw [if_pos hb]
    dsimp only [poolCurrentTick] at hb
    have hg : UInt256.eq ⟨0⟩ (UInt256.slt (slot0TickWord (poolSlot0Word evm id)) lower) = UInt256.ofNat 0 := by
      rw [slt_signed, decide_eq_true hb]
      rfl
    obtain ⟨k1, C1, rd1⟩ := poolManager_block_5722_fallthrough hstack (by rw [hslot]; exact hg) h
    dsimp only [poolManager_block_5722_fallthrough_stack] at rd1
    rw [hslot] at rd1
    simp only [hl', hu', hm] at rd1
    rw [hlohash, hhihash] at rd1
    rw [hmem'] at rd1
    simp only [h0, h32, h64, memoryWords_idem] at rd1
    exact ⟨k1, C1, rd1⟩
  · rw [if_neg hb]
    dsimp only [poolCurrentTick] at hb
    have hg : UInt256.eq ⟨0⟩ (UInt256.slt (slot0TickWord (poolSlot0Word evm id)) lower) ≠ UInt256.ofNat 0 := by
      rw [slt_signed, decide_eq_false hb]
      decide
    obtain ⟨k1, C1, rd1⟩ := poolManager_block_5722_taken hstack (by rw [hslot]; exact hg)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    dsimp only [poolManager_block_5722_taken_stack] at rd1
    rw [hslot] at rd1
    simp only [hl', hu', hm] at rd1
    rw [hlohash, hhihash] at rd1
    rw [show poolManager_block_5722_taken_memory (mem := mem) (x6 := upper) (x8 := lower) =
      poolFeeInsideMemory mem id lower upper from hmem'] at rd1
    simp only [h0, h32, h64, memoryWords_idem] at rd1
    exact ⟨k1, C1, rd1⟩

theorem poolFeeInsideStartTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id lower upper x0 x1 x2 x3 x4 x5 delta : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+14 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hl : int24Canonical lower) (hu : int24Canonical upper)
    (h : RD (deployedRuntime v) I g s0 ⟨5722⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: upper :: delta :: lower :: R) mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0
      (if poolCurrentTick evm id < EVM.signed lower then ⟨5777⟩ else ⟨6863⟩)
      (poolFeeInsideStartStack evm id lower upper x0 x1 x2 x3 x4 x5 delta R)
      (poolFeeInsideMemory mem id lower upper) aw' rdata evm.accountMap k' C' := by
  obtain ⟨k', C', hr⟩ := poolFeeInsideStartExactTrace v hstack hI hm hmem hl hu h
  exact ⟨_, k', C', hr⟩

end Benchmarks.UniswapV4PoolManager
