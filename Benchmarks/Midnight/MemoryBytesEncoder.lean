import Benchmarks.Midnight.MemoryByteString
import Benchmarks.Midnight.RuntimeBlocks_077

variable {fork : Ethereum.Fork}

/-! The memory bytes ABI encoder, retaining its copy charge as memory funding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def memoryBytesEncodeMemory (mem : ByteArray) (ptr output len : Nat) : ByteArray :=
  let header := writeWord mem output (UInt256.ofNat len)
  copyZeroMemory header header (ptr + 32) (output + 32) len

theorem midnightMemoryBytesEncoder_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw ptr output ret : UInt256} {σ : AccountMap}
    {k C len : Nat} {R : List UInt256} (hstack : R.length + 8 ≤ 1024)
    (hlen : len < 2^64) (hptr : ptr.toNat + 32 < UInt256.size)
    (hout : output.toNat + len + 96 < UInt256.size)
    (hload : memLoad ptr mem = UInt256.ofNat len)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨20095⟩ (ptr :: output :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding (credit + 3 * ((len + 31) / 32))
        (memoryBytesEncodeMemory mem ptr.toNat output.toNat len) aw' C' ∧
      RD fork midnightBytecode I g s0 ret
        ((output + UInt256.ofNat (returnDataAllocation len)) :: R)
        (memoryBytesEncodeMemory mem ptr.toNat output.toNat len) aw' rdata σ k' C' := by
  have hlenWord : (UInt256.ofNat len).toNat = len := UInt256.toNat_ofNat_of_lt (by
    change len < 2^256; omega)
  have rd1 := midnightBlocks.midnight_block_20095 hstack hret rd
  have ha1 := memoryFundingAt (credit := credit + 3 * ((len + 31) / 32)) rd1 (by
    constructor
    · have hp := ha.paid
      simp only [memExpansionCost, mcopyExpansionCost, hload, hlenWord] at hp ⊢
      omega
    · exact (((ha.covered.expand ptr ⟨32⟩).write32 (memLoad ptr mem).toByteArray 0 output).copy
        _ ((UInt256.ofNat 32) + ptr).toNat (output + UInt256.ofNat 32)
        (UInt256.ofNat 32 + ptr) (memLoad ptr mem)).write32 (⟨0⟩ : UInt256).toByteArray 0
          (UInt256.ofNat 32 + (memLoad ptr mem + output)))
  have ho : (output + UInt256.ofNat 32).toNat = output.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have hi : (UInt256.ofNat 32 + ptr).toNat = ptr.toNat + 32 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat _ _ hptr]
  have hz : (UInt256.ofNat 32 + (UInt256.ofNat len + output)).toNat =
      output.toNat + 32 + len := by
    rw [u256_add_comm (UInt256.ofNat 32), u256_add_comm (UInt256.ofNat len),
      uadd_word_ofNat_toNat _ _ (by
        rw [uadd_toNat, hlenWord, Nat.mod_eq_of_lt (by omega)]; omega),
      uadd_word_ofNat_toNat _ _ (by omega)]
    omega
  have he : (UInt256.land (UInt256.lnot (UInt256.ofNat 31))
        (UInt256.ofNat 31 + UInt256.ofNat len) + output) + UInt256.ofNat 32 =
      output + UInt256.ofNat (returnDataAllocation len) := by
    rw [u256_add_comm _ output, u256_add_assoc,
      u256_add_comm _ (UInt256.ofNat 32), returnDataAllocation_word (by omega)]
  have hf := And.intro ha1 rd1
  simp only [midnightBlocks.midnight_block_20095_stack,
    midnightBlocks.midnight_block_20095_memory, hload, hlenWord, he, ho, hi, hz] at hf
  exact ⟨_, _, _, by
    simpa only [memoryBytesEncodeMemory, copyZeroMemory, Reasoning.Theory.writeWord] using hf⟩

end Benchmarks.Midnight
