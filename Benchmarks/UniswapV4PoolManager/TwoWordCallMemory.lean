import Benchmarks.UniswapV4PoolManager.SingleWordCallMemory
import Benchmarks.UniswapV4PoolManager.MappingMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: a four-byte selector followed by two ABI words.
def twoWordCallMemory (base : ByteArray) (off : Nat) (selector arg₀ arg₁ : UInt256) : ByteArray :=
  writeWord (singleWordCallMemory base off selector arg₀) (off+36) arg₁

theorem twoWordCallMemory_size (base : ByteArray) (off : Nat) (selector arg₀ arg₁ : UInt256)
    (hgap : off-base.size < USize.size) :
    (twoWordCallMemory base off selector arg₀ arg₁).size = max base.size (off+68) := by
  have hs := singleWordCallMemory_size base off selector arg₀ hgap
  exact toByteArray_write32_size_of_le _ arg₁ (off+36)
    (max base.size (off+36)) (max base.size (off+68)) hs (by rw [hs]; omega) (by omega)

theorem twoWordCallMemory_read (base : ByteArray) (off : Nat) (selector arg₀ arg₁ : UInt256)
    (hgap : off-base.size < USize.size) :
    (twoWordCallMemory base off selector arg₀ arg₁).readWithPadding off 68 =
      (selector.toByteArray.extract 0 4 ++ arg₀.toByteArray) ++ arg₁.toByteArray := by
  have hs := singleWordCallMemory_size base off selector arg₀ hgap
  have h36 : (twoWordCallMemory base off selector arg₀ arg₁).readWithPadding off 36 =
      selector.toByteArray.extract 0 4 ++ arg₀.toByteArray := by
    unfold twoWordCallMemory
    change (arg₁.toByteArray.write 0 (singleWordCallMemory base off selector arg₀) (off+36) 32).readWithPadding off 36 = _
    rw [write32_read_below_len _ _ (off+36) off 36 (by rw [toByteArray_size])
      (by rw [hs]; omega) (by omega) (by rw [hs]; omega) (by decide) (by decide)]
    exact singleWordCallMemory_read _ _ _ _ hgap
  have hword : (twoWordCallMemory base off selector arg₀ arg₁).readWithPadding (off+36) 32 = arg₁.toByteArray :=
    toByteArray_write32_read_back _ arg₁ (off+36) (by rw [hs]; omega)
  rw [byteArray_readWithPadding_split _ off 36 32 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [twoWordCallMemory_size _ _ _ _ _ hgap]; omega), h36, hword]

-- LIBRARY CANDIDATE: a two-word ABI request preserves earlier, disjoint memory loads.
theorem twoWordCallMemory_load_below (mem : ByteArray) (read : UInt256) (off : Nat)
    (selector arg₀ arg₁ : UInt256) (hread : read.toNat+32 ≤ mem.size)
    (hbefore : read.toNat+32 ≤ off) (hgap : off-mem.size < USize.size) :
    memLoad read (twoWordCallMemory mem off selector arg₀ arg₁) = memLoad read mem := by
  have hs₁ := writeWord_size mem off selector hgap
  have hg₂ : off+4-(writeWord mem off selector).size < USize.size := by
    rw [Nat.sub_eq_zero_of_le (by omega)]; exact USize.size_pos
  have hs₂ := singleWordCallMemory_size mem off selector arg₀ hgap
  have hg₃ : off+36-(singleWordCallMemory mem off selector arg₀).size < USize.size := by
    rw [Nat.sub_eq_zero_of_le (by omega)]; exact USize.size_pos
  rw [twoWordCallMemory, memLoad_writeWord_below _ read _ _ (by omega) (by omega) hg₃,
    singleWordCallMemory, memLoad_writeWord_below _ read _ _ (by omega) (by omega) hg₂,
    memLoad_writeWord_below _ read _ _ hread hbefore hgap]

end Benchmarks.UniswapV4PoolManager
