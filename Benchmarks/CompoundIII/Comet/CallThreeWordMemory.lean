import Benchmarks.CompoundIII.Comet.CallWordsMemory

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES callTwoWordMemory to a selector followed by three ABI words.
def callThreeWordMemory (mem : ByteArray) (ptr selector first second third : UInt256) : ByteArray :=
  writeWord (callTwoWordMemory mem ptr selector first second) (ptr + UInt256.ofNat 68).toNat third

theorem callThreeWordMemory_size {mem : ByteArray} {ptr selector first second third : UInt256}
    (hb : ptr.toNat + 100 < UInt256.size) :
    (callThreeWordMemory mem ptr selector first second third).size = max mem.size (ptr.toNat + 100) := by
  rw [callThreeWordMemory, writeWord_sparse_size, callTwoWordMemory_size (by omega),
    uadd_word_ofNat_toNat ptr 68 (by omega)]
  omega

theorem callThreeWordMemory_payload {mem : ByteArray} {ptr selector first second third : UInt256}
    (hb : ptr.toNat + 100 < 2^64) :
    (callThreeWordMemory mem ptr selector first second third).readWithPadding ptr.toNat 100 =
      ((selector.toByteArray.extract 0 4 ++ first.toByteArray) ++ second.toByteArray) ++
        third.toByteArray := by
  have hu : ptr.toNat + 100 < UInt256.size := by change _ < 2^256; omega
  rw [callThreeWordMemory, uadd_word_ofNat_toNat ptr 68 (by omega)]
  rw [memoryPayload_append_word (len := 68) (by decide)
    (by rw [callTwoWordMemory_size (by omega)]; omega) (by omega)]
  rw [callTwoWordMemory_payload (by omega)]

end Benchmarks.CompoundIII.Comet
