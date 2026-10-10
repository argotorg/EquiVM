import Benchmarks.CompoundIII.Comet.TransferFromPayload
import Benchmarks.CompoundIII.Comet.TransferReplyMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def transferFromOutputMemory (mem : ByteArray) (ptr : UInt256) (sender recipient : AccountAddress)
    (amount : UInt256) (out : ByteArray) : ByteArray :=
  transferReplyMemory (writeWord (transferFromInputMemory mem ptr sender recipient amount) 64 ptr) out

theorem transferFromOutputMemory_size {mem out : ByteArray} {ptr amount : UInt256}
    {sender recipient : AccountAddress} (hlo : 96 ≤ ptr.toNat)
    (hb : ptr.toNat + 100 < UInt256.size) (hv : TransferReturnValid out) :
    (transferFromOutputMemory mem ptr sender recipient amount out).size =
      max mem.size (ptr.toNat + 100) := by
  rw [transferFromOutputMemory, transferReplyMemory_size
    (by rw [writeWord_sparse_size]; omega) hv, writeWord_sparse_size,
    transferFromInputMemory, callThreeWordMemory_size hb]
  omega

theorem transferFromOutputMemory_free {mem out : ByteArray} {ptr amount : UInt256}
    {sender recipient : AccountAddress} (hv : TransferReturnValid out) :
    memLoad ⟨64⟩ (transferFromOutputMemory mem ptr sender recipient amount out) = ptr :=
  transferReplyMemory_free hv

end Benchmarks.CompoundIII.Comet
