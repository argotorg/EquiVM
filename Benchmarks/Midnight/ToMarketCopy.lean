import Benchmarks.Midnight.ToMarketCodeMemory
import Benchmarks.Midnight.BytesAllocation
import Benchmarks.Midnight.ExtCodeCopy
import Benchmarks.Midnight.AddressDecode

variable {fork : Ethereum.Fork}

/-! The stored-market reader through EXTCODECOPY and its bounded allocation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem toMarketCodeFreePtr_toNat {len : UInt256} (hs : len.toNat < 2^64) :
    (toMarketCodeFreePtr len).toNat = 1088 + returnDataAllocation len.toNat := by
  apply uadd_word_ofNat_toNat (UInt256.ofNat 1088)
  change 1088 + returnDataAllocation len.toNat < 2^256
  dsimp only [returnDataAllocation]
  omega

theorem toMarketCodeAllocation_end {len : UInt256} (hs : len.toNat < 2^64) :
    allocationEnd ⟨1088⟩ (UInt256.ofNat (returnDataAllocation len.toNat)) =
      toMarketCodeFreePtr len := by
  apply bytesAllocationEnd
  · change len.toNat + 94 < 2^256; omega
  · change 1088 + returnDataAllocation len.toNat < 2^256
    dsimp only [returnDataAllocation]; omega

theorem toMarketCodeAllocation_ok {len : UInt256} (hs : len.toNat ≤ 18446744073709550464) :
    allocationCheck ⟨1088⟩ (allocationEnd ⟨1088⟩
      (UInt256.ofNat (returnDataAllocation len.toNat))) = ⟨0⟩ := by
  have hb : len.toNat < 2^64 := by omega
  rw [toMarketCodeAllocation_end hb]
  apply allocationCheck_ok
  · rw [toMarketCodeFreePtr_toNat hb]
    dsimp only [returnDataAllocation]; omega
  · rw [toMarketCodeFreePtr_toNat hb]
    change 1088 ≤ _; omega

theorem toMarketCodeAllocation_bad {len : UInt256} (hs : len.toNat < 2^64)
    (hlarge : ¬ len.toNat ≤ 18446744073709550464) :
    allocationCheck ⟨1088⟩ (allocationEnd ⟨1088⟩
      (UInt256.ofNat (returnDataAllocation len.toNat))) ≠ ⟨0⟩ := by
  rw [toMarketCodeAllocation_end hs]
  have hgt : UInt256.gt (toMarketCodeFreePtr len)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)) =
      ⟨1⟩ := by
    apply ugt_one
    rw [toMarketCodeFreePtr_toNat hs]
    change 18446744073709551615 < 1088 + returnDataAllocation len.toNat
    dsimp only [returnDataAllocation]; omega
  have hlt : UInt256.lt (toMarketCodeFreePtr len) ⟨1088⟩ = ⟨0⟩ := by
    apply ult_zero
    rw [toMarketCodeFreePtr_toNat hs]
    change 1088 ≤ _; omega
  rw [allocationCheck, hgt, hlt]
  decide

theorem midnightToMarketGetTick {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (rd : RD fork midnightBytecode I g s0 ⟨737⟩ R midnightEntryMemory aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ⟨846⟩
      (marketTickSpacing (solcSlotWordAt (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4) + ⟨2⟩)
        σ I) :: calldataWord I.calldata 4 :: R)
      (toMarketInitialMemory (calldataWord I.calldata 4)) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_737 (by omega) (by jump_dest) rd
  have hf : memLoad (UInt256.ofNat 64) midnightEntryMemory = ⟨832⟩ := midnightEntryMemory_freePtr
  simp only [midnightBlocks.midnight_block_737_stack, hf] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := midnightAllocate256
    (by simp only [List.length_cons]; omega) (by decide +kernel) (by jump_dest) rd1
  exact midnightToMarketInitialize (by omega) rd2

theorem midnightToMarketCodeSize {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw id : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (rd : RD fork midnightBytecode I g s0 ⟨851⟩ (id :: R) mem aw rdata σ k C) :
    ∃ k' C', RD fork midnightBytecode I g s0 ⟨19016⟩
      (extCodeSizeWord σ id :: ⟨870⟩ :: extCodeSizeWord σ id ::
        UInt256.land solcAddrMask id :: R) mem aw rdata σ k' C' := by
  obtain ⟨k1, C1, rd1⟩ := midnightBlocks.midnight_block_851 hstack (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_851_stack, addressMask_computed,
    extCodeSizeWord_mask] at rd1
  exact ⟨k1, C1, rd1⟩

theorem midnightToMarketCodeTooLarge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw id : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hlarge : ¬ (extCodeSizeWord σ id).toNat ≤ 18446744073709550464)
    (rd : RD fork midnightBytecode I g s0 ⟨851⟩ (id :: R)
      (toMarketInitialMemory id) aw rdata σ k C) :
    RDrev fork midnightBytecode g s0 := by
  obtain ⟨k1, C1, rd1⟩ := midnightToMarketCodeSize (by omega) rd
  by_cases hs : (extCodeSizeWord σ id).toNat < 2^64
  · obtain ⟨k2, C2, rd2⟩ := midnightBytesAllocationSize hs
      (by simp only [List.length_cons]; omega) (by jump_dest) rd1
    have rd3 := midnightBlocks.midnight_block_870 (by simp only [List.length_cons]; omega)
      (by jump_dest) rd2
    simp only [midnightBlocks.midnight_block_870_stack,
      (toMarketInitialMemory_properties id).2.2.1] at rd3
    exact midnightAllocateRevert (by simp only [List.length_cons]; omega)
      (toMarketCodeAllocation_bad hs hlarge) rd3
  · exact midnightBytesLengthTooLarge (by omega) (by simp only [List.length_cons]; omega) rd1

theorem midnightToMarketCodeCopy {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw id : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hsmall : (extCodeSizeWord σ id).toNat ≤ 18446744073709550464)
    (rd : RD fork midnightBytecode I g s0 ⟨851⟩ (id :: R)
      (toMarketInitialMemory id) aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ⟨900⟩ (⟨1088⟩ :: ⟨1120⟩ :: R)
      (toMarketCodeMemory σ id) aw' rdata σ k' C' := by
  have hs : (extCodeSizeWord σ id).toNat < 2^64 := by omega
  obtain ⟨k1, C1, rd1⟩ := midnightToMarketCodeSize (by omega) rd
  obtain ⟨k2, C2, rd2⟩ := midnightBytesAllocationSize hs
    (by simp only [List.length_cons]; omega) (by jump_dest) rd1
  have rd3 := midnightBlocks.midnight_block_870 (by simp only [List.length_cons]; omega)
    (by jump_dest) rd2
  simp only [midnightBlocks.midnight_block_870_stack,
    (toMarketInitialMemory_properties id).2.2.1] at rd3
  obtain ⟨aw4, k4, C4, rd4⟩ := midnightAllocate (by simp only [List.length_cons]; omega)
    (toMarketCodeAllocation_ok hsmall) (by jump_dest) rd3
  rw [toMarketCodeAllocation_end hs] at rd4
  have rd5 := midnightBlocks.midnight_block_884 (by omega) rd4
  simp only [midnightBlocks.midnight_block_884_stack,
    midnightBlocks.midnight_block_884_memory] at rd5
  change RD fork midnightBytecode I g s0 ⟨899⟩
    (UInt256.land solcAddrMask id :: ⟨1120⟩ ::
      memLoad (UInt256.ofNat 800) (toMarketCodeBase id (extCodeSizeWord σ id)) ::
      extCodeSizeWord σ id :: ⟨1088⟩ :: ⟨1120⟩ :: R)
    (toMarketCodeBase id (extCodeSizeWord σ id)) _ rdata σ _ _ at rd5
  rw [(toMarketCodeBase_properties id _).2.2.2] at rd5
  obtain ⟨k6, C6, rd6⟩ := extCodeCopyReach rd5 (by native_decide)
    (by simp only [List.length_cons]; omega)
  simp only [externalCode_mask] at rd6
  change RD fork midnightBytecode I g s0 ⟨900⟩ (⟨1088⟩ :: ⟨1120⟩ :: R)
    ((externalCode σ id).write 0 (toMarketCodeBase id (extCodeSizeWord σ id))
      1120 (extCodeSizeWord σ id).toNat) _ rdata σ k6 C6 at rd6
  rw [toMarketCodeCopy_eq] at rd6
  exact ⟨_, k6, C6, rd6⟩

end Benchmarks.Midnight
