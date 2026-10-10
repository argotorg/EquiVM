import Benchmarks.Morpho.MetaMorphoV1_1.Uint128AllocationSource
import Benchmarks.Morpho.MetaMorphoV1_1.MorphoSlotAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsMemory
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_055
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_088

/-! Allocation, range checking, and both reverts of the compiler's uint128 cast. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def uint128ErrorWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 156113407705867659558375029309965657412092893529) ⟨98⟩

def uint128CastMemory (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  writeWord (writeWord (writeWord mem 64 (nextCursor ptr ⟨64⟩)) ptr.toNat ⟨20⟩)
    (ptr.toNat + 32) uint128ErrorWord

theorem uint128CastMemory_size (mem : ByteArray) (ptr : UInt256) (hlo : 96 ≤ ptr.toNat) :
    (uint128CastMemory mem ptr).size = max mem.size (ptr.toNat + 64) := by
  simp only [uint128CastMemory, writeWord_sparse_size]
  omega

theorem uint128CastMemory_free (mem : ByteArray) (ptr : UInt256) (hlo : 96 ≤ ptr.toNat) :
    memLoad ⟨64⟩ (uint128CastMemory mem ptr) = nextCursor ptr ⟨64⟩ := by
  unfold uint128CastMemory
  have h64 : (⟨64⟩ : UInt256).toNat = 64 := rfl
  rw [memLoad_write_above _ _ _ _
      (by simp only [h64, writeWord_sparse_size]; omega) (by rw [h64]; omega),
    memLoad_write_above _ _ _ _ (by rw [h64, writeWord_sparse_size]; omega) hlo]
  apply loadedWord_of_read
  · rw [h64, writeWord_sparse_size]; omega
  · exact writeWord_sparse_read_back _ _ _

theorem uint128CastMemory_prefix (mem : ByteArray) (ptr : UInt256) :
    MemoryPrefix mem (uint128CastMemory mem ptr) ptr.toNat :=
  (memoryPrefix_sparse_writeWord _ 64 _ _ (.inr (by decide))).trans
    ((memoryPrefix_sparse_writeWord _ ptr.toNat _ _ (.inl (le_refl _))).trans
      (memoryPrefix_sparse_writeWord _ (ptr.toNat + 32) _ _ (.inl (by omega))))

set_option maxRecDepth 2000 in
theorem uint128OverflowRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr x ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 12 ≤ 1024)
    (hover : 2 ^ 128 ≤ x.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨19381⟩ (ptr :: x :: ret :: R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_19381_taken (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by intro hz; have hle := ugt_eq_zero_to_le hz
        change x.toNat ≤ 2 ^ 128 - 1 at hle; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have h2 := metaMorphoV1_1_block_19441 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  have h3 := metaMorphoV1_1_block_11086 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
  exact metaMorphoV1_1_block_19477 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) h3

set_option maxRecDepth 2000 in
theorem uint128CastReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr x ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 12 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (halloc : allocationFits ptr ⟨64⟩)
    (hfit : x.toNat < 2 ^ 128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨19367⟩ (x :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (x :: R)
      (uint128CastMemory mem ptr) aw' rdata σ k' C' := by
  have h0 := metaMorphoV1_1_block_19367 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  simp only [metaMorphoV1_1_block_19367_stack, hf] at h0
  obtain ⟨aw1, k1, C1, h1⟩ := allocateRoundedReturn v
    (by simp only [List.length_cons]; omega) halloc
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h0
  have h2 := metaMorphoV1_1_block_19381_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (ugt_zero (by change x.toNat ≤ 2 ^ 128 - 1; omega)) h1
  obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_19429_packed
    (immWords := wordsOf (immStore v)) (by omega) hret h2
  have hclean : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
        (UInt256.ofNat 1)) x = x := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat x _ (by decide +kernel) hfit
  have hp := (allocationFits_aligned ptr ⟨64⟩ (by decide +kernel)).mp halloc
  have hadd : (ptr + UInt256.ofNat 32).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)
  refine ⟨aw3, k3, C3, ?_⟩
  simpa only [metaMorphoV1_1_block_19429_stack, hclean,
    metaMorphoV1_1_block_19381_fallthrough_memory, hadd] using h3

set_option maxRecDepth 2000 in
theorem uint128CastRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr x ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 12 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr)
    (hbad : ¬ allocationFits ptr ⟨64⟩ ∨ 2 ^ 128 ≤ x.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨19367⟩ (x :: ret :: R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  have h0 := metaMorphoV1_1_block_19367 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  simp only [metaMorphoV1_1_block_19367_stack, hf] at h0
  by_cases halloc : allocationFits ptr ⟨64⟩
  · obtain ⟨aw1, k1, C1, h1⟩ := allocateRoundedReturn v
      (by simp only [List.length_cons]; omega) halloc
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h0
    exact uint128OverflowRevert v hstack (hbad.resolve_left (not_not.mpr halloc)) h1
  · exact allocateRoundedRevert v (by simp only [List.length_cons]; omega) halloc h0

theorem uint128CastSimulation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr x ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (imms : Store) (evm : State)
    (hstack : R.length + 12 ≤ 1024) (hlo : 96 ≤ ptr.toNat)
    (hfree : memLoad ⟨64⟩ mem = ptr)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨19367⟩ (x :: ret :: R)
      mem aw rdata σ k C) :
    (ExecFuncBody config (allocatedToUint128Frame imms x ptr) evm
        allocatedToUint128Function.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (allocationFits ptr ⟨64⟩ ∧ x.toNat < 2 ^ 128 ∧
      ExecFuncBody config (allocatedToUint128Frame imms x ptr) evm
        allocatedToUint128Function.body
        (.returned (allocatedToUint128ResultFrame imms x ptr) evm
          [uint256Value x, uint256Value (nextCursor ptr ⟨64⟩)]) ∧
      memLoad ⟨64⟩ (uint128CastMemory mem ptr) = nextCursor ptr ⟨64⟩ ∧
      (nextCursor ptr ⟨64⟩).toNat ≤ (uint128CastMemory mem ptr).size ∧
      MemoryPrefix mem (uint128CastMemory mem ptr) ptr.toNat ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (x :: R)
        (uint128CastMemory mem ptr) aw' rdata σ k' C') := by
  by_cases halloc : allocationFits ptr ⟨64⟩
  · by_cases hfit : x.toNat < 2 ^ 128
    · refine .inr ⟨halloc, hfit, allocatedToUint128Body imms x ptr evm halloc hfit,
        uint128CastMemory_free mem ptr hlo, ?_, uint128CastMemory_prefix mem ptr,
        uint128CastReturn v hstack hfree halloc hfit hret rd⟩
      have hp := (allocationFits_aligned ptr ⟨64⟩ (by decide +kernel)).mp halloc
      have hn : (nextCursor ptr ⟨64⟩).toNat = ptr.toNat + 64 :=
        uadd_word_ofNat_toNat ptr 64 (by change _ < 2 ^ 256; omega)
      rw [hn, uint128CastMemory_size mem ptr hlo]
      exact Nat.le_max_right _ _
    · have hover := Nat.le_of_not_lt hfit
      exact .inl ⟨allocatedToUint128BodyOverflowReverts imms x ptr evm halloc hover,
        uint128CastRevert v hstack hfree (.inr hover) rd⟩
  · exact .inl ⟨allocatedToUint128BodyAllocationReverts imms x ptr evm halloc,
      uint128CastRevert v hstack hfree (.inl halloc) rd⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
