import Benchmarks.Midnight.MappingMemory

/-! A mapping hash can reuse its slot word while replacing only the key. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: hash a new key using the slot already stored at memory offset 32.
theorem writeWord_zero_mappingHash {mem : ByteArray} (key slot : UInt256)
    (hm : 64 ≤ mem.size) (hs : mem.readWithPadding 32 32 = slot.toByteArray) :
    keccakWord ⟨0⟩ (UInt256.ofNat 64) (writeWord mem 0 key) = solcMappingSlot slot key := by
  have hm' : 64 ≤ (writeWord mem 0 key).size := by rw [writeWord_sparse_size]; omega
  have hl : (writeWord mem 0 key).extract 0 32 = key.toByteArray := by
    rw [← readWithPadding_eq_extract _ 0 (by omega)]
    exact writeWord_sparse_read_back mem 0 key
  have hr : (writeWord mem 0 key).extract 32 64 = slot.toByteArray := by
    rw [← readWithPadding_eq_extract _ 32 (by omega),
      writeWord_sparse_read_preserved mem 0 32 key (Or.inr ⟨by decide, hm⟩), hs]
  have hread : (writeWord mem 0 key).readWithPadding 0 64 = key.toByteArray ++ slot.toByteArray := by
    rw [readWithPadding_eq_extract' _ 0 64 (by decide) (by decide) (by omega)]
    rw [show (writeWord mem 0 key).extract 0 64 =
        (writeWord mem 0 key).extract 0 32 ++ (writeWord mem 0 key).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
    rw [hl, hr]
  change UInt256.ofNat (fromByteArrayBigEndian
    (KEC ((writeWord mem 0 key).readWithPadding 0 64))) = _
  rw [hread]
  exact mappingSlot_single key slot

end Benchmarks.Midnight
