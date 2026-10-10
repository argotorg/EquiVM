import Benchmarks.UniswapV3.Pool.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- GENERALIZES Reasoning.Solc.wordAt0Mem_twoWordHashMem_solcMappingSlot to arbitrary memory.
theorem wordAt0Mem_twoWordHashMem_slot_any (slot key oldKey : UInt256) (mem : ByteArray) :
    keccakWord ⟨0⟩ ⟨64⟩ (wordAt0Mem key (twoWordHashMem oldKey slot mem)) =
      solcMappingSlot slot key := by
  have hb := twoWordHashMem_size_ge_64 oldKey slot mem
  have hs : 64 ≤ (wordAt0Mem key (twoWordHashMem oldKey slot mem)).size := by
    rw [wordAt0Mem_size_of_ge64 key hb]
    exact hb
  have hr : (wordAt0Mem key (twoWordHashMem oldKey slot mem)).readWithPadding 32 32 =
      slot.toByteArray := by
    unfold wordAt0Mem
    rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size]) (by omega) (by omega) hb]
    exact twoWordHashMem_read32_any oldKey slot mem
  have hall : (wordAt0Mem key (twoWordHashMem oldKey slot mem)).readWithPadding 0 64 =
      key.toByteArray ++ slot.toByteArray := by
    rw [byteArray_readWithPadding_split _ 0 32 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simpa using hs)]
    rw [wordAt0Mem_read0, hr]
  change UInt256.ofNat (fromByteArrayBigEndian (KEC
    ((wordAt0Mem key (twoWordHashMem oldKey slot mem)).readWithPadding 0 64))) = _
  rw [hall]
  exact mappingSlot_single key slot

end Benchmarks.UniswapV3.Pool
