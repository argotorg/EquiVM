import Benchmarks.UniswapV4PoolManager.WordRangeSourceStep
import Benchmarks.UniswapV4PoolManager.WordReadTraceReturn
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_027

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 3000

def wordRangeTraceValue (I : ExecutionEnv) (σ : AccountMap) (start : UInt256) (i : Nat) : UInt256 :=
  solcSlotWordAt (wordRangeSlot start i) σ I

theorem wordRangeSlot_next (start : UInt256) (i : Nat) :
    wordRangeSlot start i + UInt256.ofNat 1 = wordRangeSlot start (i+1) := by
  change (start + UInt256.ofNat i) + (⟨1⟩ : UInt256) = _
  rw [u256_add_comm, uadd_ofNat_succ]
  rfl

theorem wordRangeTraceStep {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} {n i : Nat} {start : UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 9 ≤ 1024) (hn : 224+32*n < UInt256.size) (hi : i < max 1 n)
    (h : RD (deployedRuntime v) I g s0 ⟨9781⟩ (wordReadTraceStack (wordRangeSlot start) ⟨1⟩ n i R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0
      (if i+1 < n then ⟨9781⟩ else ⟨2508⟩)
      (if i+1 < n then wordReadTraceStack (wordRangeSlot start) ⟨1⟩ n (i+1) R
        else wordReadTraceExitStack (wordRangeSlot start) n (i+1) R)
      (writeWord mem (224+32*i) (wordRangeTraceValue I σ start i)) aw' rdata σ k' C' := by
  have houtfit : 224+32*(i+1) < UInt256.size := by
    have : 256 < UInt256.size := by decide
    omega
  have houtadd := wordArrayStepWord 224 i
  have hslotadd : wordRangeSlot start i + (⟨1⟩ : UInt256) = wordRangeSlot start (i+1) :=
    wordRangeSlot_next start i
  have hmemory : poolManagerBlocks.poolManager_block_9781_taken_memory (ee := I) (σ := σ)
      (mem := mem) (x0 := UInt256.ofNat (224+32*i)) (x3 := wordRangeSlot start i) =
      writeWord mem (224+32*i) (wordRangeTraceValue I σ start i) := by
    change (solcSlotWordAt (wordRangeSlot start i) σ I).toByteArray.write 0 mem
      (UInt256.ofNat (224+32*i)).toNat 32 = _
    rw [UInt256.toNat_ofNat_of_lt (by omega : 224+32*i < UInt256.size)]
    rfl
  unfold wordReadTraceStack at h
  by_cases hnext : i+1 < n
  · simp only [if_pos hnext]
    obtain ⟨aw1, k1, C1, rd⟩ := poolManagerBlocks.poolManager_block_9781_fallthrough_packed hstack
      (by rw [houtadd, ult_one (by rw [UInt256.toNat_ofNat_of_lt houtfit,
        UInt256.toNat_ofNat_of_lt hn]; omega)]; rfl) h
    change RD _ _ _ _ ⟨9799⟩
      (UInt256.ofNat 160 :: (UInt256.ofNat (224+32*i) + UInt256.ofNat 32) ::
        (wordRangeSlot start i + (⟨1⟩ : UInt256)) ::
        UInt256.ofNat (224+32*n) :: UInt256.ofNat (160+32*n) :: UInt256.ofNat 160 :: R)
      (poolManagerBlocks.poolManager_block_9781_taken_memory (ee := I) (σ := σ) (mem := mem)
        (x0 := UInt256.ofNat (224+32*i)) (x3 := wordRangeSlot start i)) _ _ _ _ _ at rd
    rw [houtadd, hslotadd, hmemory] at rd
    obtain ⟨aw2, k2, C2, rd2⟩ := poolManagerBlocks.poolManager_block_9799_packed
      (by simp; omega) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨aw2, k2, C2, rd2⟩
  · simp only [if_neg hnext]
    obtain ⟨aw1, k1, C1, rd⟩ := poolManagerBlocks.poolManager_block_9781_taken_packed hstack
      (by rw [houtadd, ult_zero (by rw [UInt256.toNat_ofNat_of_lt houtfit,
        UInt256.toNat_ofNat_of_lt hn]; omega)]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    refine ⟨aw1, k1, C1, ?_⟩
    simpa only [poolManagerBlocks.poolManager_block_9781_taken_stack, houtadd, hslotadd,
      hmemory, wordReadTraceExitStack] using rd

theorem wordRangePrepareTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 9 ≤ 1024)
    (hn : 224+32*(calldataWord I.calldata 36).toNat < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 ⟨9741⟩ R entryMemory aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨9781⟩
      (wordReadTraceStack (wordRangeSlot (calldataWord I.calldata 4)) ⟨1⟩ (calldataWord I.calldata 36).toNat 0 R)
      (arrayHeaderMemory (calldataWord I.calldata 36).toNat) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd⟩ := poolManagerBlocks.poolManager_block_9741_packed (by omega) h
  have hs : UInt256.shiftLeft (calldataWord I.calldata 36) (UInt256.ofNat 5) =
      UInt256.ofNat (32*(calldataWord I.calldata 36).toNat) := by
    have hh := shiftLeft5_ofNat_eq (n := (calldataWord I.calldata 36).toNat) (by omega)
    simpa only [u256_ofNat_toNat] using hh
  have hf : memLoad (UInt256.ofNat 64) entryMemory = UInt256.ofNat 160 := entryMemory_load64
  have hw : UInt256.ofNat (calldataWord I.calldata 36).toNat = calldataWord I.calldata 36 := u256_ofNat_toNat _
  have hm : poolManagerBlocks.poolManager_block_9741_memory (ee := I) (mem := entryMemory) =
      arrayHeaderMemory (calldataWord I.calldata 36).toNat := by
    unfold poolManagerBlocks.poolManager_block_9741_memory
    rw [hf]
    change (calldataWord I.calldata 36).toByteArray.write 0
      ((UInt256.ofNat 32).toByteArray.write 0 entryMemory 160 32) 192 32 = _
    unfold arrayHeaderMemory Reasoning.Theory.writeWord
    rw [hw]
  have hst : poolManagerBlocks.poolManager_block_9741_stack (ee := I) (mem := entryMemory) (R := R) =
      wordReadTraceStack (wordRangeSlot (calldataWord I.calldata 4)) ⟨1⟩ (calldataWord I.calldata 36).toNat 0 R := by
    unfold poolManagerBlocks.poolManager_block_9741_stack
    rw [hf]
    change (UInt256.ofNat 160 + UInt256.ofNat 64) :: UInt256.ofNat 32 :: UInt256.ofNat 1 ::
      calldataWord I.calldata 4 ::
      ((UInt256.ofNat 160 + UInt256.shiftLeft (calldataWord I.calldata 36) (UInt256.ofNat 5)) + UInt256.ofNat 64) ::
      (UInt256.ofNat 160 + UInt256.shiftLeft (calldataWord I.calldata 36) (UInt256.ofNat 5)) ::
      UInt256.ofNat 160 :: R = _
    rw [hs]
    simp only [ofNat_add_words, show 160+32*(calldataWord I.calldata 36).toNat+64 =
      224+32*(calldataWord I.calldata 36).toNat by omega, wordReadTraceStack, wordRangeSlot,
      Nat.mul_zero, Nat.add_zero]
    rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, uadd_zero_r]
    rfl
  exact ⟨aw1, k1, C1, by rw [hst, hm] at rd; exact rd⟩

theorem wordRangeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 9 ≤ 1024)
    (hn : 224+32*(calldataWord I.calldata 36).toNat < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 ⟨9741⟩ R entryMemory aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ
      (wordBytes ([UInt256.ofNat 32, calldataWord I.calldata 36] ++
        wordArrayWords (wordRangeTraceValue I σ (calldataWord I.calldata 4)) 0 (calldataWord I.calldata 36).toNat)) := by
  obtain ⟨aw1, k1, C1, rd⟩ := wordRangePrepareTrace v hstack hn h
  have hr := wordReadTraceReturn v hstack hn
    (fun _ _ _ _ _ hi h => wordRangeTraceStep v hstack hn hi h) rd
  simpa only [u256_ofNat_toNat] using hr

end Benchmarks.UniswapV4PoolManager
