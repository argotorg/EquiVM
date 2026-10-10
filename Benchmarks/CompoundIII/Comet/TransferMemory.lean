import Benchmarks.CompoundIII.Comet.TransferPayload
import Benchmarks.CompoundIII.Comet.TransferReplyMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def transferOutputMemory (mem : ByteArray) (ptr : UInt256) (recipient : AccountAddress)
    (amount : UInt256) (out : ByteArray) : ByteArray :=
  transferReplyMemory (writeWord (transferInputMemory mem ptr recipient amount) 64 ptr) out

theorem transferOutputMemory_size {mem out : ByteArray} {ptr amount : UInt256}
    {recipient : AccountAddress} (hlo : 96 ≤ ptr.toNat) (hb : ptr.toNat + 68 < UInt256.size)
    (hv : TransferReturnValid out) :
    (transferOutputMemory mem ptr recipient amount out).size =
      max mem.size (ptr.toNat + 68) := by
  rw [transferOutputMemory, transferReplyMemory_size
    (by rw [writeWord_sparse_size]; omega) hv, writeWord_sparse_size,
    transferInputMemory, callTwoWordMemory_size hb]
  omega

theorem transferOutputMemory_free {mem out : ByteArray} {ptr amount : UInt256}
    {recipient : AccountAddress} (hv : TransferReturnValid out) :
    memLoad ⟨64⟩ (transferOutputMemory mem ptr recipient amount out) = ptr := by
  exact transferReplyMemory_free hv

end Benchmarks.CompoundIII.Comet
