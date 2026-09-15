import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- GENERALIZES the Reasoning.Solc error-string memory helpers to a second payload word.
noncomputable def errorStringMem4 (len first second : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray second).write 0 (solcErrorStringMem3 len first mem) 228 32

theorem errorStringMem4_size (len first second : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) : (errorStringMem4 len first second mem).size = 260 := by
  exact toByteArray_write32_size_of_ge _ second 228 228 260
    (solcErrorStringMem3_size len first hmem) (by decide)
    (lt_usize _ (by norm_num)) (by decide)

theorem errorStringMem4_read64 (len first second : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (errorStringMem4 len first second mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold errorStringMem4
  rw [toByteArray_write_read_below_of_gap second _ 228 64
    (by rw [solcErrorStringMem3_size len first hmem]; decide) (by decide)
    (by rw [solcErrorStringMem3_size len first hmem]; exact lt_usize _ (by norm_num))]
  exact solcErrorStringMem3_read64 len first hmem hread

theorem errorStringMem4_mload64 (len first second : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (errorStringMem4 len first second mem).size ∨
        (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩ else
      UInt256.ofNat (fromByteArrayBigEndian
        ((errorStringMem4 len first second mem).readWithPadding 64 32))) = ⟨128⟩ := by
  exact mloadFreePtrValue (by rw [errorStringMem4_size len first second hmem]; decide)
    (by decide) (errorStringMem4_read64 len first second hmem hread)

end Auction
