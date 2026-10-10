import Benchmarks.UniswapV4PoolManager.BytesMemory
import Benchmarks.UniswapV4PoolManager.WordArrayMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: a raw return-data copy followed by updating the Solidity free pointer.
def copiedReturnMemory (out mem : ByteArray) (base : Nat) (next : UInt256) : ByteArray :=
  writeWord (out.write 0 mem base out.size) 64 next

theorem copiedReturnMemory_size (out mem : ByteArray) (base : Nat) (next : UInt256)
    (hmem : 96 ≤ mem.size) (hbase : base ≤ mem.size) :
    (copiedReturnMemory out mem base next).size = max mem.size (base+out.size) := by
  rw [copiedReturnMemory, writeWord_sparse_size, byteArray_write_all_size out mem base hbase]
  omega

theorem copiedReturnMemory_free (out mem : ByteArray) (base : Nat) (next : UInt256) :
    memLoad ⟨64⟩ (copiedReturnMemory out mem base next) = next := by
  apply mloadWordValue_of_readWithPadding
  · change 64 < (copiedReturnMemory out mem base next).size
    rw [copiedReturnMemory, writeWord_sparse_size]; omega
  · exact writeWord_sparse_read_back _ 64 next

theorem copiedReturnMemory_read (out mem : ByteArray) (base off count : Nat) (next : UInt256)
    (hmem : 96 ≤ mem.size) (hbase : base ≤ mem.size) (hlo : 96 ≤ base)
    (hb : off+count ≤ out.size) :
    (copiedReturnMemory out mem base next).readWithPadding (base+off) count =
      out.extract off (off+count) := by
  by_cases hz : count = 0
  · subst count
    rw [byteArray_readWithPadding_zero, Nat.add_zero, byteArray_extract_empty_of_le out (by omega)]
  have ho : out.size ≠ 0 := by omega
  rw [copiedReturnMemory, writeWord_sparse_read_preserved_unbounded _ _ _ _ _
      (by rw [byteArray_write_all_size out mem base hbase]; omega) (.inr (by omega)),
    readWithPadding_eq_extract_any _ _ _ (by rw [byteArray_write_all_size out mem base hbase]; omega)]
  simpa only [Nat.zero_add] using copyWindow_extract out mem 0 base out.size off count ho
    (by omega) hbase hb

theorem copiedReturnMemory_load (out mem : ByteArray) (base off : Nat) (next read : UInt256)
    (hmem : 96 ≤ mem.size) (hbase : base ≤ mem.size) (hlo : 96 ≤ base)
    (hb : off+32 ≤ out.size) (hread : read.toNat = base+off) :
    memLoad read (copiedReturnMemory out mem base next) = calldataWord out off := by
  rw [memLoad, if_neg (by rw [copiedReturnMemory_size _ _ _ _ hmem hbase, hread]; omega),
    hread, copiedReturnMemory_read _ _ _ _ _ _ hmem hbase hlo hb]
  exact (bytesToWord_drop_take32_eq_extract' out off).symm.trans (decode_word_at_eq_any out off hb)

end Benchmarks.UniswapV4PoolManager
