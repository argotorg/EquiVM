import Benchmarks.CompoundIII.Comet.TransferReturnEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES transferOutputMemory_size to arbitrary call-input memory.
theorem transferReplyMemory_size {mem out : ByteArray} (hm : 32 ≤ mem.size)
    (hv : TransferReturnValid out) : (transferReplyMemory mem out).size = mem.size := by
  unfold transferReplyMemory
  split_ifs with hz
  · rfl
  · have h32 : out.size = 32 := (hv.resolve_left hz).1
    rw [copyWindow_size out mem 0 0 32 (by decide) (by omega) (by omega)]
    omega

-- GENERALIZES transferOutputMemory_free to arbitrary call-input memory.
theorem transferReplyMemory_free {mem out : ByteArray} {ptr : UInt256}
    (hv : TransferReturnValid out) :
    memLoad ⟨64⟩ (transferReplyMemory (writeWord mem 64 ptr) out) = ptr := by
  apply loadedWord_of_read
  · rw [transferReplyMemory_size (by rw [writeWord_sparse_size]; omega) hv,
      writeWord_sparse_size]
    change 64 + 32 ≤ _
    omega
  · unfold transferReplyMemory
    split_ifs with hz
    · exact writeWord_sparse_read_back _ _ _
    · have h32 : out.size = 32 := (hv.resolve_left hz).1
      change (out.write 0 (writeWord mem 64 ptr) 0 32).readWithPadding 64 32 = _
      rw [copyWindow_read_preserved out _ 0 0 32 64 (by decide) (by omega) (by omega)
        (by rw [writeWord_sparse_size]; omega) (Or.inr (by decide))]
      exact writeWord_sparse_read_back _ _ _

end Benchmarks.CompoundIII.Comet
