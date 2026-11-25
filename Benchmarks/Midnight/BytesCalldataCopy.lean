import Benchmarks.Midnight.BytesAllocation
import Benchmarks.Midnight.CalldataBytesEncodeMemory
import Benchmarks.Midnight.CalldataSliceBounds
import Benchmarks.Midnight.RuntimeBlocks_073

variable {fork : Ethereum.Fork}

/-! The checked materialized byte-string copy, including its memory payment. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightBytesCalldataCopy_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw head len ptr ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 10 ≤ 1024)
    (hhead : head.toNat < 2^128) (hlen : len.toNat < 2^64) (hptr : ptr.toNat < 2^64)
    (hsize : I.calldata.size < UInt256.size)
    (hbound : head.toNat + 32 + len.toNat ≤ I.calldata.size)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨19080⟩
      (UInt256.ofNat I.calldata.size :: head :: len :: ptr :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', C ≤ C' ∧
      MemoryFunding (credit + 3 * ((len.toNat + 31) / 32))
        (calldataBytesEncodeMemory mem I.calldata ptr.toNat (head.toNat + 32) len.toNat)
        aw' C' ∧
      RD fork midnightBytecode I g s0 ret (ptr :: R)
        (calldataBytesEncodeMemory mem I.calldata ptr.toNat (head.toNat + 32) len.toNat)
        aw' rdata σ k' C' := by
  have he := calldataSliceEnd_toNat true hhead hlen
  simp only [calldataSliceEndWord, calldataSliceStride, if_true, Nat.one_mul] at he
  have hc : UInt256.gt (head + len + UInt256.ofNat 32)
      (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    apply ugt_zero
    rw [he, UInt256.toNat_ofNat_of_lt hsize]
    exact hbound
  have rd1 := midnightBlocks.midnight_block_19080_fallthrough
    (by simp only [List.length_cons]; omega) hc rd
  have ha1 := memoryFundingAt (credit := credit) rd1 (by
    unfold midnightBlocks.midnight_block_19080_fallthrough_memory
    memory_fund ha)
  have rd2 := midnightBlocks.midnight_block_19095 (by omega) hret rd1
  have ha2 := memoryFundingAt (credit := credit + 3 * ((len.toNat + 31) / 32)) rd2 (by
    unfold midnightBlocks.midnight_block_19095_memory
    memory_fund ha1)
  have hh : (head + UInt256.ofNat 32).toNat = head.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hp : (ptr + UInt256.ofNat 32).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hz : (ptr + len + UInt256.ofNat 32).toNat = ptr.toNat + 32 + len.toNat := by
    simpa only [calldataSliceEndWord, calldataSliceStride, if_true, Nat.one_mul] using
      calldataSliceEnd_toNat true (by omega : ptr.toNat < 2^128) hlen
  simp only [midnightBlocks.midnight_block_19095_stack,
    midnightBlocks.midnight_block_19095_memory,
    midnightBlocks.midnight_block_19080_fallthrough_memory, hh, hp, hz] at rd2 ha2
  simp only [calldataBytesEncodeMemory, copyZeroMemory, Reasoning.Theory.writeWord,
    u256_ofNat_toNat]
  exact ⟨_, _, _, by omega, ha2, rd2⟩

end Benchmarks.Midnight
