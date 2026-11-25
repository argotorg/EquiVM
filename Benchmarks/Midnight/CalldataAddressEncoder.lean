import Benchmarks.Midnight.MemoryFunding
import Benchmarks.Midnight.CalldataAddressEncodeLoop
import Benchmarks.Midnight.RuntimeBlocks_074

variable {fork : Ethereum.Fork}

/-! The complete calldata address-array encoder, used for events and external calls. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def calldataArrayEncodeMemory (mem : ByteArray) (output : Nat) (bytes : ByteArray)
    (ptr n : Nat) : ByteArray :=
  writeWordArray mem output (UInt256.ofNat n :: calldataArrayWords bytes n ptr)

theorem midnightCalldataAddressEncoderFunded {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw count ptr output ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 15 ≤ 1024)
    (hptr : ptr.toNat + 32 * count.toNat < UInt256.size)
    (hout : output.toNat + 32 + 32 * count.toNat < UInt256.size)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨19549⟩ (ptr :: count :: output :: ret :: R)
      mem aw rdata σ k C) :
    (¬ CanonicalAddressWords (calldataArrayWords I.calldata count.toNat ptr.toNat) ∧
      RDrev fork midnightBytecode g s0) ∨
    (CanonicalAddressWords (calldataArrayWords I.calldata count.toNat ptr.toNat) ∧
      ∃ aw' k' C', C ≤ C' ∧
      MemoryFunding credit
        (calldataArrayEncodeMemory mem output.toNat I.calldata ptr.toNat count.toNat) aw' C' ∧
      RD fork midnightBytecode I g s0 ret ((output + UInt256.ofNat (32 + 32 * count.toNat)) :: R)
        (calldataArrayEncodeMemory mem output.toNat I.calldata ptr.toNat count.toNat)
        aw' rdata σ k' C') := by
  have rd1 := midnightBlocks.midnight_block_19549
    (by simp only [List.length_cons]; omega) rd
  simp only [midnightBlocks.midnight_block_19549_stack,
    midnightBlocks.midnight_block_19549_memory] at rd1
  have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
  have ho : (output + UInt256.ofNat 32).toNat = output.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  rcases midnightCalldataAddressEncodeLoopFunded count.toNat hstack
      (by change count.toNat = 0 + count.toNat; omega) hptr (by rw [ho]; exact hout)
      hret ha1 rd1 with
    ⟨hn, hr⟩ | ⟨hc, aw2, k2, C2, hC2, ha2, rd2⟩
  · exact Or.inl ⟨hn, hr⟩
  · refine Or.inr ⟨hc, aw2, k2, C2, by omega, ?_⟩
    simpa only [calldataArrayEncodeMemory, writeWordArray, u256_ofNat_toNat, ho,
      wordAddNat_add] using And.intro ha2 rd2

theorem midnightCalldataAddressEncoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw count ptr output ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 15 ≤ 1024)
    (hptr : ptr.toNat + 32 * count.toNat < UInt256.size)
    (hout : output.toNat + 32 + 32 * count.toNat < UInt256.size)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryAccounting mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨19549⟩ (ptr :: count :: output :: ret :: R)
      mem aw rdata σ k C) :
    (¬ CanonicalAddressWords (calldataArrayWords I.calldata count.toNat ptr.toNat) ∧
      RDrev fork midnightBytecode g s0) ∨
    (CanonicalAddressWords (calldataArrayWords I.calldata count.toNat ptr.toNat) ∧
      ∃ aw' k' C', C ≤ C' ∧
      MemoryAccounting
        (calldataArrayEncodeMemory mem output.toNat I.calldata ptr.toNat count.toNat) aw' C' ∧
      RD fork midnightBytecode I g s0 ret ((output + UInt256.ofNat (32 + 32 * count.toNat)) :: R)
        (calldataArrayEncodeMemory mem output.toNat I.calldata ptr.toNat count.toNat)
        aw' rdata σ k' C') := by
  rcases midnightCalldataAddressEncoderFunded hstack hptr hout hret (MemoryFunding.of_accounting ha) rd with
    hrev | ⟨hc, aw', k', C', hC, ha', rd'⟩
  · exact Or.inl hrev
  · exact Or.inr ⟨hc, aw', k', C', hC, ha'.accounting, rd'⟩

end Benchmarks.Midnight
