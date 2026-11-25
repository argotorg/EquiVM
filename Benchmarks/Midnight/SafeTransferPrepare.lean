import Benchmarks.Midnight.SafeTransferMemory
import Benchmarks.Midnight.AllocationArithmetic

variable {fork : Ethereum.Fork}

/-! The safe-transfer bytecode prefix, through calldata construction and allocation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def safeTransferEntryPC (isFrom : Bool) : UInt256 := if isFrom then ⟨23444⟩ else ⟨23236⟩
def safeTransferCallPC (isFrom : Bool) : UInt256 := if isFrom then ⟨23522⟩ else ⟨23311⟩
def safeTransferLoadPC (isFrom : Bool) : UInt256 := if isFrom then ⟨23518⟩ else ⟨23307⟩

def safeTransferEntryStack (isFrom : Bool) (token sender recipient : AccountAddress)
    (value : UInt256) (R : List UInt256) : List UInt256 :=
  UInt256.ofNat token.val :: safeTransferCallWords isFrom sender recipient value ++ R

theorem safeTransferAllocationEnd (isFrom : Bool) (ptr : UInt256) :
    allocationEnd ptr (UInt256.ofNat (32 + safeTransferCallSize isFrom)) =
      ptr + UInt256.ofNat (safeTransferCallAllocation isFrom) := by
  unfold allocationEnd
  congr 1
  cases isFrom <;> decide +kernel

theorem safeTransferAllocationCheck (isFrom : Bool) (ptr : UInt256)
    (hfit : ptr.toNat + safeTransferCallAllocation isFrom < 2 ^ 64) :
    allocationCheck ptr (allocationEnd ptr (UInt256.ofNat (32 + safeTransferCallSize isFrom))) =
      ⟨0⟩ := by
  rw [safeTransferAllocationEnd]
  have hp := uadd_word_ofNat_toNat ptr (safeTransferCallAllocation isFrom)
    (by change _ < 2 ^ 256; omega)
  exact allocationCheck_ok (by rw [hp]; exact hfit) (by rw [hp]; omega)

theorem safeTransferPrepareCall (isFrom : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw ptr : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {token sender recipient : AccountAddress} {value : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024) (hl : 96 ≤ ptr.toNat)
    (hfit : ptr.toNat + safeTransferCallAllocation isFrom < 2 ^ 64)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (hcode : extCodeSizeWord σ (UInt256.ofNat token.val) ≠ ⟨0⟩)
    (rd : RD fork midnightBytecode I g s0 (safeTransferEntryPC isFrom)
      (safeTransferEntryStack isFrom token sender recipient value R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C', RD fork midnightBytecode I g s0 (safeTransferCallPC isFrom)
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
    change RD fork _ _ _ _ ⟨23236⟩
      (UInt256.ofNat token.val :: UInt256.ofNat recipient.val :: value :: R) _ _ _ _ _ _ at rd
    have hend : allocationEnd ptr (UInt256.ofNat 100) = ptr + UInt256.ofNat 128 :=
      safeTransferAllocationEnd false ptr
    obtain ⟨k1, C1, rd1⟩ := midnightBlocks.midnight_block_23236_fallthrough
      (by simpa using (show R.length + 5 ≤ 1024 by omega)) (isZero_eq_zero_of_ne hcode) rd
    have rd2 := midnightBlocks.midnight_block_23247 (by omega) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_23247_stack, hfree] at rd2
    have hd : UInt256.sub (ptr + UInt256.ofNat 100) ptr = UInt256.ofNat 100 := by
      exact word_add_sub_left ptr (UInt256.ofNat 100)
    have rd3 := midnightBlocks.midnight_block_12824 (by simp only [List.length_cons]; omega)
      (by jump_dest) rd2
    simp only [midnightBlocks.midnight_block_12824_stack, hd] at rd3
    obtain ⟨aw4, k4, C4, rd4⟩ := midnightAllocate (by simp only [List.length_cons]; omega)
      (safeTransferAllocationCheck false ptr hfit) (by jump_dest) rd3
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
    rw [show 32 + safeTransferCallSize false = 100 from rfl, hm4] at rd4
    have rd5 := midnightBlocks.midnight_block_23307 (by simp only [List.length_cons]; omega) rd4
    simp only [midnightBlocks.midnight_block_23307_stack, hm.2.2.1] at rd5
    exact ⟨_, _, _, _, rd5⟩
  | true =>
    change RD fork _ _ _ _ ⟨23444⟩
      (UInt256.ofNat token.val :: UInt256.ofNat sender.val :: UInt256.ofNat recipient.val ::
        value :: R) _ _ _ _ _ _ at rd
    have hend : allocationEnd ptr (UInt256.ofNat 132) = ptr + UInt256.ofNat 160 :=
      safeTransferAllocationEnd true ptr
    obtain ⟨k1, C1, rd1⟩ := midnightBlocks.midnight_block_23444_fallthrough
      (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hcode) rd
    have rd2 := midnightBlocks.midnight_block_23453 (by omega) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_23453_stack, hfree] at rd2
    obtain ⟨aw3, k3, C3, rd3⟩ := midnightAllocate (by simp only [List.length_cons]; omega)
      (safeTransferAllocationCheck true ptr hfit) (by jump_dest) rd2
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
    rw [show 32 + safeTransferCallSize true = 132 from rfl, hm3] at rd3
    have rd4 := midnightBlocks.midnight_block_23518 (by simp only [List.length_cons]; omega) rd3
    simp only [midnightBlocks.midnight_block_23518_stack, hm.2.2.1] at rd4
    exact ⟨_, _, _, _, rd4⟩

theorem safeTransferRevertNoCode (isFrom : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {token sender recipient : AccountAddress} {value : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcode : extCodeSizeWord σ (UInt256.ofNat token.val) = ⟨0⟩)
    (rd : RD fork midnightBytecode I g s0 (safeTransferEntryPC isFrom)
      (safeTransferEntryStack isFrom token sender recipient value R) mem aw rdata σ k C) :
    RDrev fork midnightBytecode g s0 := by
  cases isFrom with
  | false =>
    change RD fork _ _ _ _ ⟨23236⟩
      (UInt256.ofNat token.val :: UInt256.ofNat recipient.val :: value :: R) _ _ _ _ _ _ at rd
    obtain ⟨k1, C1, rd1⟩ := midnightBlocks.midnight_block_23236_taken
      (by omega) (by rw [hcode]; decide) (by jump_dest) rd
    exact midnightBlocks.midnight_block_23388
      (by simp only [midnightBlocks.midnight_block_23236_taken_stack, List.length_cons]; omega) rd1
  | true =>
    change RD fork _ _ _ _ ⟨23444⟩
      (UInt256.ofNat token.val :: UInt256.ofNat sender.val :: UInt256.ofNat recipient.val ::
        value :: R) _ _ _ _ _ _ at rd
    obtain ⟨k1, C1, rd1⟩ := midnightBlocks.midnight_block_23444_taken
      (by simp only [List.length_cons]; omega) (by rw [hcode]; decide) (by jump_dest) rd
    exact midnightBlocks.midnight_block_23388
      (by simp only [midnightBlocks.midnight_block_23444_taken_stack, List.length_cons]; omega) rd1

end Benchmarks.Midnight
