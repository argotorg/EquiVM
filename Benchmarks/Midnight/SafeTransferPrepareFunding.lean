import Benchmarks.Midnight.SafeTransferPrepare
import Benchmarks.Midnight.AllocationFunding
import Benchmarks.Midnight.AccountAccessGas

/-! Safe-transfer calldata construction retaining prior non-memory work. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem safeTransferPrepareCall_funded (isFrom : Bool) {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw ptr : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {token sender recipient : AccountAddress} {value : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024) (hl : 96 ≤ ptr.toNat)
    (hfit : ptr.toNat + safeTransferCallAllocation isFrom < 2 ^ 64)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (hcode : extCodeSizeWord σ (UInt256.ofNat token.val) ≠ ⟨0⟩)
    (ha0 : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 (safeTransferEntryPC isFrom)
      (safeTransferEntryStack isFrom token sender recipient value R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C',
      MemoryFunding credit (safeTransferCallMem isFrom sender recipient value mem ptr) aw' C' ∧
      RD midnightBytecode I g s0 (safeTransferCallPC isFrom)
      (gasArg :: UInt256.ofNat token.val :: ⟨0⟩ :: (ptr + UInt256.ofNat 32) ::
        UInt256.ofNat (safeTransferCallSize isFrom) :: ⟨0⟩ :: ⟨0⟩ :: R)
      (safeTransferCallMem isFrom sender recipient value mem ptr) aw' rdata σ k' C' := by
  have ha (n : Nat) (hn : n ≤ safeTransferCallAllocation isFrom) :
      (ptr + UInt256.ofNat n).toNat = ptr.toNat + n :=
    uadd_word_ofNat_toNat ptr n (by change _ < 2 ^ 256; omega)
  have hm := safeTransferCallMem_properties isFrom sender recipient value mem ptr hl
  have hclean (a : AccountAddress) : UInt256.land (UInt256.ofNat a.val)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = UInt256.ofNat a.val :=
    addressMaskLiteral_clean_of_canonical (addressWord_canonical a)
  have hs := hclean sender
  have hr := hclean recipient
  cases isFrom with
  | false =>
    change RD _ _ _ _ ⟨23236⟩
      (UInt256.ofNat token.val :: UInt256.ofNat recipient.val :: value :: R) _ _ _ _ _ _ at rd
    have hend : allocationEnd ptr (UInt256.ofNat 100) = ptr + UInt256.ofNat 128 :=
      safeTransferAllocationEnd false ptr
    let r0 := rd
    have r1 := r0.jumpdest (by native_decide) (by evm_ov)
    have r2 := r1.swap2 (by native_decide) (by evm_ov)
    have r3 := r2.swap1 (by native_decide) (by evm_ov)
    have r4 := r3.swap2 (by native_decide) (by evm_ov)
    have r5 := r4.dup1 (by native_decide) (by evm_ov)
    obtain ⟨_, _, hC1, r6⟩ := extcodesizeMono r5 (by native_decide) (by evm_ov)
    have r7 := r6.iszero (by native_decide) (by evm_ov)
    have r8 := r7.push2 (UInt256.ofNat 23388) (by native_decide) (by evm_ov)
    have r9 := r8.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hcode) (by evm_ov)
    have rd1 := RD.normalizePC (pc' := (UInt256.ofNat 23247)) r9 (by native_decide)
    have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha0)
    have rd2 := midnightBlocks.midnight_block_23247 (by omega) (by jump_dest) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by
      unfold midnightBlocks.midnight_block_23247_memory
      memory_fund ha1)
    simp only [midnightBlocks.midnight_block_23247_stack, hfree] at rd2 ha2
    have hd : UInt256.sub (ptr + UInt256.ofNat 100) ptr = UInt256.ofNat 100 := by
      exact word_add_sub_left ptr (UInt256.ofNat 100)
    have rd3 := midnightBlocks.midnight_block_12824 (by simp only [List.length_cons]; omega)
      (by jump_dest) rd2
    have ha3 := memoryFundingAt (credit := credit) rd3 (by
      unfold midnightBlocks.midnight_block_12824_memory
      memory_fund ha2)
    simp only [midnightBlocks.midnight_block_12824_stack, hd] at rd3 ha3
    obtain ⟨aw4, k4, C4, ha4, rd4⟩ := midnightAllocate_funded (by simp only [List.length_cons]; omega)
      (safeTransferAllocationCheck false ptr hfit) (by jump_dest) ha3 rd3
    have hm4 : writeWord (midnightBlocks.midnight_block_12824_memory
        (mem := midnightBlocks.midnight_block_23247_memory
          (mem := mem) (x1 := value) (x2 := UInt256.ofNat recipient.val))
        (x0 := ptr + UInt256.ofNat 100) (x1 := ptr) (x3 := ptr)) 64
        (allocationEnd ptr (UInt256.ofNat 100)) =
        safeTransferCallMem false sender recipient value mem ptr := by
      simp only [midnightBlocks.midnight_block_12824_memory,
        midnightBlocks.midnight_block_23247_memory, hfree, hd, hr,
        hend, ha 32 (by decide), ha 36 (by decide), ha 68 (by decide)]
      have hsel : UInt256.shiftLeft (UInt256.ofNat 2835717307) (UInt256.ofNat 224) =
          safeTransferSelectorWord false := by decide +kernel
      have hlen : UInt256.ofNat 100 + UInt256.lnot (UInt256.ofNat 31) = UInt256.ofNat 68 :=
        by decide +kernel
      rw [hsel, hlen]
      rfl
    rw [show 32 + safeTransferCallSize false = 100 from rfl, hm4] at rd4 ha4
    have rd5 := midnightBlocks.midnight_block_23307 (by simp only [List.length_cons]; omega) rd4
    have ha5 := memoryFundingAt (credit := credit) rd5 (by memory_fund ha4)
    simp only [midnightBlocks.midnight_block_23307_stack, hm.2.2.1] at rd5 ha5
    exact ⟨_, _, _, _, ha5, rd5⟩
  | true =>
    change RD _ _ _ _ ⟨23444⟩
      (UInt256.ofNat token.val :: UInt256.ofNat sender.val :: UInt256.ofNat recipient.val ::
        value :: R) _ _ _ _ _ _ at rd
    have hend : allocationEnd ptr (UInt256.ofNat 132) = ptr + UInt256.ofNat 160 :=
      safeTransferAllocationEnd true ptr
    let r0 := rd
    have r1 := r0.jumpdest (by native_decide) (by evm_ov)
    have r2 := r1.swap1 (by native_decide) (by evm_ov)
    have r3 := r2.dup2 (by native_decide) (by evm_ov)
    obtain ⟨_, _, hC1, r4⟩ := extcodesizeMono r3 (by native_decide) (by evm_ov)
    have r5 := r4.iszero (by native_decide) (by evm_ov)
    have r6 := r5.push2 (UInt256.ofNat 23388) (by native_decide) (by evm_ov)
    have r7 := r6.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hcode) (by evm_ov)
    have rd1 := RD.normalizePC (pc' := (UInt256.ofNat 23453)) r7 (by native_decide)
    have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha0)
    have rd2 := midnightBlocks.midnight_block_23453 (by omega) (by jump_dest) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by
      unfold midnightBlocks.midnight_block_23453_memory
      memory_fund ha1)
    simp only [midnightBlocks.midnight_block_23453_stack, hfree] at rd2 ha2
    obtain ⟨aw3, k3, C3, ha3, rd3⟩ := midnightAllocate_funded (by simp only [List.length_cons]; omega)
      (safeTransferAllocationCheck true ptr hfit) (by jump_dest) ha2 rd2
    have hm3 : writeWord (midnightBlocks.midnight_block_23453_memory
        (mem := mem) (x0 := UInt256.ofNat sender.val) (x2 := UInt256.ofNat recipient.val)
        (x3 := value)) 64 (allocationEnd ptr (UInt256.ofNat 132)) =
        safeTransferCallMem true sender recipient value mem ptr := by
      simp only [midnightBlocks.midnight_block_23453_memory, hfree, hs, hr,
        hend, ha 32 (by decide), ha 36 (by decide),
        ha 68 (by decide), ha 100 (by decide)]
      have hsel : UInt256.shiftLeft (UInt256.ofNat 599290589) (UInt256.ofNat 224) =
          safeTransferSelectorWord true := by decide +kernel
      rw [hsel]
      rfl
    rw [show 32 + safeTransferCallSize true = 132 from rfl, hm3] at rd3 ha3
    have rd4 := midnightBlocks.midnight_block_23518 (by simp only [List.length_cons]; omega) rd3
    have ha4 := memoryFundingAt (credit := credit) rd4 (by memory_fund ha3)
    simp only [midnightBlocks.midnight_block_23518_stack, hm.2.2.1] at rd4 ha4
    exact ⟨_, _, _, _, ha4, rd4⟩

end Benchmarks.Midnight
