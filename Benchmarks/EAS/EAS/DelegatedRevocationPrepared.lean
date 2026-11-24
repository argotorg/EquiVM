import Benchmarks.EAS.EAS.DelegatedRevocationAssembleMemory
import Benchmarks.EAS.EAS.DelegatedRevocationDecodeFacts
import Benchmarks.EAS.EAS.CopySignatureArrayRun
import Benchmarks.EAS.EAS.RevocationArrayInvalid

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def delegatedRevocationNext (heap : UInt256) (r : DelegatedRevocationBatch) : Nat :=
  heap.toNat+192+96*r.data.length+128*r.signatures.length
def delegatedRevocationDataPtr (heap : UInt256) : UInt256 := UInt256.ofNat (heap.toNat+128)
def delegatedRevocationSigPtr (heap : UInt256) (rs : List RevocationRequestRecord) : UInt256 :=
  UInt256.ofNat (heap.toNat+160+96*rs.length)

def DelegatedRevocationPrepared (fork : Ethereum.Fork) (v : EASImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (mem : ByteArray) (out : ByteArray) (σ : AccountMap) (heap a b c d : UInt256) (R : List UInt256)
    (r : DelegatedRevocationBatch) : Prop :=
  ∃ mem' aw' k' C',
    let final := delegatedRevocationSetRevoker mem' heap (UInt256.ofNat r.revoker.val)
    MemoryPrefix (recordPadding mem heap.toNat) final heap.toNat ∧
    DelegatedRevocationBatchMemoryView final heap (delegatedRevocationDataPtr heap)
      (delegatedRevocationSigPtr heap r.data) r (delegatedRevocationNext heap r) ∧
    memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat (delegatedRevocationNext heap r) ∧
    memLoad (UInt256.ofNat 64) final = UInt256.ofNat (delegatedRevocationNext heap r) ∧
    RD fork (deployedRuntime v) ee g s0 ⟨1521⟩
      (UInt256.ofNat r.revoker.val::b::a::d::(heap+UInt256.ofNat 32)::
        (heap+UInt256.ofNat 64)::delegatedRevocationSigPtr heap r.data::c::heap::R)
      mem' aw' out σ k' C'

theorem delegatedRevocationLinkData_free {mem : ByteArray} {row data word : UInt256}
    (hlo : 96 ≤ row.toNat) (hb : row.toNat+32 < UInt256.size) (hmem : 96 ≤ mem.size)
    (hf : memLoad (UInt256.ofNat 64) mem = word) :
    memLoad (UInt256.ofNat 64) (delegatedRevocationLinkData mem row data) = word := by
  exact (memLoad_write_below mem (row+UInt256.ofNat 32).toNat (UInt256.ofNat 64) data
    (by rw [uadd_word_ofNat_toNat _ _ hb]; change 96 ≤ row.toNat+32; omega) hmem).trans hf

theorem delegatedRevocationLinkSignatures_free {mem : ByteArray} {row sig word : UInt256}
    (hlo : 96 ≤ row.toNat) (hb : row.toNat+64 < UInt256.size) (hmem : 96 ≤ mem.size)
    (hf : memLoad (UInt256.ofNat 64) mem = word) :
    memLoad (UInt256.ofNat 64) (delegatedRevocationLinkSignatures mem row sig) = word := by
  exact (memLoad_write_below mem (row+UInt256.ofNat 64).toNat (UInt256.ofNat 64) sig
    (by rw [uadd_word_ofNat_toNat _ _ hb]; change 96 ≤ row.toNat+64; omega) hmem).trans hf

end Benchmarks.EAS.EAS
