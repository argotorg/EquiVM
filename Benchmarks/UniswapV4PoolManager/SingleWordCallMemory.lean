import Benchmarks.UniswapV4PoolManager.Values

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

-- LIBRARY CANDIDATE: the common four-byte selector followed by one ABI word.
def singleWordCallMemory (base : ByteArray) (off : Nat) (selector arg : UInt256) : ByteArray :=
  writeWord (writeWord base off selector) (off+4) arg

theorem singleWordCallMemory_size (base : ByteArray) (off : Nat) (selector arg : UInt256)
    (hgap : off-base.size < USize.size) :
    (singleWordCallMemory base off selector arg).size = max base.size (off+36) := by
  have hs := writeWord_size base off selector hgap
  exact toByteArray_write32_size_of_le (writeWord base off selector) arg (off+4)
    (max base.size (off+32)) (max base.size (off+36)) hs (by rw [hs]; omega) (by omega)

theorem singleWordCallMemory_read (base : ByteArray) (off : Nat) (selector arg : UInt256)
    (hgap : off-base.size < USize.size) :
    (singleWordCallMemory base off selector arg).readWithPadding off 36 =
      selector.toByteArray.extract 0 4 ++ arg.toByteArray := by
  have hs := writeWord_size base off selector hgap
  have h4 : (singleWordCallMemory base off selector arg).readWithPadding off 4 =
      selector.toByteArray.extract 0 4 := by
    unfold singleWordCallMemory
    change (arg.toByteArray.write 0 (writeWord base off selector) (off+4) 32).readWithPadding off 4 = _
    rw [write32_read_below_len _ _ (off+4) off 4 (by rw [toByteArray_size])
      (by rw [hs]; omega) (by omega) (by rw [hs]; omega) (by decide) (by decide)]
    exact (by simpa only [Nat.add_zero] using
      toByteArray_write_read_window_of_gap selector base off 0 4 (by decide) (by decide) (by decide) hgap)
  have hword : (singleWordCallMemory base off selector arg).readWithPadding (off+4) 32 = arg.toByteArray :=
    toByteArray_write32_read_back (writeWord base off selector) arg (off+4) (by rw [hs]; omega)
  rw [byteArray_readWithPadding_split _ off 4 32 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [singleWordCallMemory_size _ _ _ _ hgap]; omega), h4, hword]

-- LIBRARY CANDIDATE: a successful one-word output copy overwrites the request prefix.
theorem copiedReturnWord_read {out base : ByteArray} {off : Nat}
    (hlo : 32 ≤ out.size) (hhi : out.size < UInt256.size) (hdest : off ≤ base.size) :
    (out.write 0 base off (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat).readWithPadding off 32 =
      (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))).toByteArray := by
  have hn : (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (by decide) hlo hhi
  rw [hn, writeReturnCopy_read32 out base off 32 off hlo hdest (by omega) (by omega)]
  simp only [Nat.sub_self, Nat.zero_add]
  exact (readWithPadding_eq_extract out 0 (by omega)).symm.trans
    (readWithPadding_eq_toByteArray_ofNat out 0 (by omega))

end Benchmarks.UniswapV4PoolManager
