import Benchmarks.Midnight.MemoryFunding
import Benchmarks.Midnight.CalldataAddressEncoder
import Benchmarks.Midnight.MemoryArrayIndex

/-! The bulk-copy encoder for a calldata array of uint256 words. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def calldataArrayCopyMemory (mem : ByteArray) (output : Nat) (bytes : ByteArray)
    (ptr n : Nat) : ByteArray :=
  bytes.write ptr (writeWord mem output (UInt256.ofNat n)) (output + 32) (32 * n)

theorem midnightCalldataWordArrayEncoderFunded {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw count ptr output ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 8 ≤ 1024)
    (hcount : count.toNat < 2^64)
    (hout : output.toNat + 32 + 32 * count.toNat < UInt256.size)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨19614⟩ (ptr :: count :: output :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', C ≤ C' ∧
      MemoryFunding credit
        (calldataArrayCopyMemory mem output.toNat I.calldata ptr.toNat count.toNat) aw' C' ∧
      RD midnightBytecode I g s0 ret ((output + UInt256.ofNat (32 + 32 * count.toNat)) :: R)
        (calldataArrayCopyMemory mem output.toNat I.calldata ptr.toNat count.toNat)
        aw' rdata σ k' C' := by
  have hc : UInt256.gt count
      (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) =
      ⟨0⟩ := ugt_zero (by change count.toNat ≤ 2^251 - 1; omega)
  have rd1 := midnightBlocks.midnight_block_19614_fallthrough
    (by simp only [List.length_cons]; omega) hc rd
  have rd2 := midnightBlocks.midnight_block_19659 hstack hret rd1
  have ha2 := memoryFundingAt (credit := credit) rd2 (by
    constructor
    · have hp := ha.paid
      simp only [memExpansionCost] at hp ⊢
      omega
    · exact (ha.covered.write32 count.toByteArray 0 output).write I.calldata ptr.toNat
        (output + UInt256.ofNat 32) (UInt256.shiftLeft count (UInt256.ofNat 5)))
  have ho : (output + UInt256.ofNat 32).toNat = output.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have hn : (UInt256.shiftLeft count (UInt256.ofNat 5)).toNat = 32 * count.toNat := by
    simpa only [u256_ofNat_toNat] using ushl5_ofNat_toNat count.toNat (by omega)
  have he : output + UInt256.shiftLeft count (UInt256.ofNat 5) + UInt256.ofNat 32 =
      output + UInt256.ofNat (32 + 32 * count.toNat) := by
    rw [u256_add_comm output, arrayIndexWord hcount, wordAddNat_add]
  have hf := And.intro ha2 rd2
  simp only [midnightBlocks.midnight_block_19659_stack,
    midnightBlocks.midnight_block_19659_memory,
    midnightBlocks.midnight_block_19614_fallthrough_memory, hn, ho, he] at hf
  simp only [calldataArrayCopyMemory, u256_ofNat_toNat]
  refine ⟨_, _, _, ?_, hf⟩
  omega

theorem midnightCalldataWordArrayEncoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw count ptr output ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 8 ≤ 1024)
    (hcount : count.toNat < 2^64)
    (hout : output.toNat + 32 + 32 * count.toNat < UInt256.size)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryAccounting mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨19614⟩ (ptr :: count :: output :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', C ≤ C' ∧
      MemoryAccounting
        (calldataArrayCopyMemory mem output.toNat I.calldata ptr.toNat count.toNat) aw' C' ∧
      RD midnightBytecode I g s0 ret ((output + UInt256.ofNat (32 + 32 * count.toNat)) :: R)
        (calldataArrayCopyMemory mem output.toNat I.calldata ptr.toNat count.toNat)
        aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', hC, ha', rd'⟩ := midnightCalldataWordArrayEncoderFunded hstack hcount hout hret (MemoryFunding.of_accounting ha) rd
  exact ⟨aw', k', C', hC, ha'.accounting, rd'⟩

end Benchmarks.Midnight
