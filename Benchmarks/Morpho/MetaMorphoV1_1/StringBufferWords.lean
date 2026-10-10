import Benchmarks.Morpho.MetaMorphoV1_1.StringBuffer
import Benchmarks.Morpho.MetaMorphoV1_1.WordWindow

/-! Word reads from the abstract string buffer used by the storage writer. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: full-word reads from a string buffer agree with its source byte array.
theorem StringBuffer.word {mem bytes : ByteArray} {ptr : UInt256}
    (buffer : StringBuffer mem ptr.toNat bytes)
    (hfit : ptr.toNat + 32 + bytes.size < UInt256.size) (off : Nat)
    (hoff : off + 32 ≤ bytes.size) :
    memLoad (ptr + UInt256.ofNat (32 + off)) mem =
      uInt256OfByteArray (bytes.readWithPadding off 32) := by
  have hptr : (ptr + (⟨32⟩ : UInt256)).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat ptr 32 (by omega)
  have hmem : ptr.toNat + 32 + bytes.size ≤ mem.size := by
    have hcover := buffer.size
    unfold paddedSize at hcover
    omega
  have hw := SourceMemory.wordWindowLoad_of_read (src := ptr + ⟨32⟩) (len := bytes.size)
    (le_refl _) (by rw [hptr]; exact hmem) (by rw [hptr]; exact hfit)
    (by rw [hptr, buffer.data,
          readWithPadding_eq_extract_unbounded bytes 0 bytes.size (by omega) (by omega)]
        simpa only [Nat.zero_add] using (byteArray_extract_self bytes).symm) off hoff
  have hadd : (ptr + (⟨32⟩ : UInt256)) + UInt256.ofNat off =
      ptr + UInt256.ofNat (32 + off) := by
    rw [u256_add_assoc]
    change ptr + (UInt256.ofNat 32 + UInt256.ofNat off) = _
    rw [ofNat_add_words]
  rw [hadd] at hw
  rw [hw, readWithPadding_eq_extract _ _ hoff, ← calldataWord_bytes_at hoff]
  exact (uInt256OfByteArray_toByteArray _).symm

end Benchmarks.Morpho.MetaMorphoV1_1
