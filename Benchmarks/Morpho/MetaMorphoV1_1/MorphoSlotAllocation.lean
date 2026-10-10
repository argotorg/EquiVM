import Benchmarks.Morpho.MetaMorphoV1_1.MorphoSlotRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationRoutines

/-! The supply-share reader's fixed allocation prefix, including all allocation failures. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem allocationFits_aligned (ptr size : UInt256) (hround : roundedSize size = size) :
    allocationFits ptr size ↔ ptr.toNat + size.toNat < 2 ^ 64 := by
  rw [allocationFits_iff_sum_lt, hround]

set_option maxRecDepth 2000 in
theorem supplySharesPrefixAllocationRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr morpho id user : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 13 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlower : 96 ≤ ptr.toNat)
    (hfit : ¬ ptr.toNat + 256 < 2 ^ 64)
    (rd : RD (deployedRuntime v) I g s0 ⟨14078⟩ (morpho :: id :: user :: R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  by_cases hfirst : ptr.toNat + 96 < 2 ^ 64
  · by_cases hsecond : ptr.toNat + 192 < 2 ^ 64
    · obtain ⟨_, _, _, harray⟩ := positionSlotReachArray v hstack hfree hlower hsecond rd
      have hcursor : memLoad ⟨64⟩ (positionSlotHashMem mem ptr id user) = ptr + ⟨192⟩ := by
        rw [positionSlotHashMem, packedPairAllocMem_free, u256_add_assoc]
        rfl
      have halloc := metaMorphoV1_1_block_16791
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) harray
      change RD _ _ _ _ _
        (memLoad ⟨64⟩ (positionSlotHashMem mem ptr id user) :: ⟨64⟩ :: ⟨16806⟩ :: _)
        _ _ _ _ _ _ at halloc
      rw [hcursor] at halloc
      apply allocateRoundedRevert v (by simp only [List.length_cons]; omega) ?_ halloc
      rw [allocationFits_aligned _ _ (by decide +kernel)]
      have h192 : (ptr + ⟨192⟩).toNat = ptr.toNat + 192 :=
        uadd_word_ofNat_toNat ptr 192 (lt_trans hsecond (by decide))
      change ¬ (ptr + ⟨192⟩).toNat + 64 < 2 ^ 64
      rw [h192]
      omega
    · obtain ⟨_, _, _, hhash⟩ := positionSlotReachFirstHash v hstack hfree hfirst rd
      have hcursor : memLoad (UInt256.ofNat 64) (packedPairAllocMem mem ptr id ⟨2⟩) =
          ptr + ⟨96⟩ := packedPairAllocMem_free mem ptr id ⟨2⟩
      have halloc := metaMorphoV1_1_block_14119
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hhash
      simp only [metaMorphoV1_1_block_14119_stack, hcursor] at halloc
      apply allocateRoundedRevert v (by simp only [List.length_cons]; omega) ?_ halloc
      rw [allocationFits_aligned _ _ (by decide +kernel)]
      have h96 : (ptr + ⟨96⟩).toNat = ptr.toNat + 96 :=
        uadd_word_ofNat_toNat ptr 96 (lt_trans hfirst (by decide))
      change ¬ (ptr + ⟨96⟩).toNat + 96 < 2 ^ 64
      rw [h96]
      omega
  · have hfree' : memLoad (UInt256.ofNat 64) mem = ptr := hfree
    have halloc := metaMorphoV1_1_block_14078
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [metaMorphoV1_1_block_14078_stack, hfree'] at halloc
    apply allocateRoundedRevert v (by simp only [List.length_cons]; omega) ?_ halloc
    rw [allocationFits_aligned _ _ (by decide +kernel)]
    exact hfirst

theorem supplySharesPrefixAllocationCases {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr morpho id user : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 13 ≤ 1024)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlower : 96 ≤ ptr.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨14078⟩ (morpho :: id :: user :: R)
      mem aw rdata σ k C) :
    (¬ allocationFits ptr ⟨256⟩ ∧ RDrev (deployedRuntime v) g s0) ∨
      (allocationFits ptr ⟨256⟩ ∧ ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨14169⟩
        ((ptr + ⟨192⟩) :: morpho :: ⟨0⟩ :: ⟨14197⟩ :: R)
        (positionSlotArrayMem mem I.calldata ptr id user) aw' rdata σ k' C') := by
  have heq : allocationFits ptr ⟨256⟩ ↔ ptr.toNat + 256 < 2 ^ 64 :=
    allocationFits_aligned ptr ⟨256⟩ (by decide +kernel)
  by_cases hfit : ptr.toNat + 256 < 2 ^ 64
  · exact .inr ⟨heq.mpr hfit,
      supplySharesReachEncoding v hstack hcalldata hfree hlower hfit rd⟩
  · exact .inl ⟨fun h => hfit (heq.mp h),
      supplySharesPrefixAllocationRevert v hstack hfree hlower hfit rd⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
