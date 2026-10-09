import Benchmarks.Morpho.MorphoBlue.MarketParamsMemory
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000


-- LIBRARY CANDIDATE: an empty result leaves the reserved return word unchanged.
theorem callOutput32_empty (mem : ByteArray) (off : UInt256) :
    callOutputMem mem ByteArray.empty off (UInt256.ofNat 32) = mem := by
  change ByteArray.empty.write 0 mem off.toNat 0 = mem
  exact byteArray_write_len_zero _ _ _ _

-- LIBRARY CANDIDATE: a full returned word is a single word write.
theorem callOutput32_word (mem out : ByteArray) (off : UInt256) (hs : out.size = 32) :
    callOutputMem mem out off (UInt256.ofNat 32) = writeWord mem off.toNat (calldataWord out 0) := by
  have hb : (calldataWord out 0).toByteArray = out := by
    rw [calldataWord_bytes (by omega), ← hs, byteArray_extract_self]
  simp only [callOutputMem, hs]
  change out.write 0 mem off.toNat 32 = (calldataWord out 0).toByteArray.write 0 mem off.toNat 32
  rw [hb]

end Benchmarks.Morpho.MorphoBlue
