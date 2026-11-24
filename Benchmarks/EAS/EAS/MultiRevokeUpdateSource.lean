import Benchmarks.EAS.EAS.MultiRevokeSource
import Benchmarks.EAS.EAS.SpendAndIncrementSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem MultiRevokeLocals.allocated {L : Store} {requests : List Value}
    {available : UInt256} {heap i : Nat} (h : MultiRevokeLocals L requests available heap i)
    (rs : List RevocationRequestRecord) (next : Nat) :
    MultiRevokeLocals (multiRevokeAllocatedLocals L rs next) requests available next i := by
  constructor <;> simp (disch := decide) only [multiRevokeAllocatedLocals,allocateBlockLocals_get,store_get_ne,
    allocateBlockLocals,unpackHeapLocals,store_get_self] <;>
    first | exact h.requests | exact h.available | exact h.index

def multiRevokeCallLocals (L : Store) (used : UInt256) (heap : Nat) : Store :=
  heapResultLocals L "__c0$allocation" "__c0" "$EAS.freeMemory" (.int (Int.ofNat used.toNat)) heap

theorem MultiRevokeLocals.called {L : Store} {requests : List Value}
    {available : UInt256} {heap i : Nat} (h : MultiRevokeLocals L requests available heap i)
    (used : UInt256) (next : Nat) :
    MultiRevokeLocals (multiRevokeCallLocals L used next) requests available next i := by
  constructor <;> simp (disch := decide) only [multiRevokeCallLocals,heapResultLocals_get,heapResultLocals_heap] <;>
    first | exact h.requests | exact h.available | exact h.index

def multiRevokeNextLocals (L : Store) (available used : UInt256) (i : Nat) : Store :=
  L.insert "availableValue" (.int (Int.ofNat (UInt256.sub available used).toNat)) |>.insert "i" (.int (Int.ofNat (i+1)))

theorem MultiRevokeLocals.next {L : Store} {requests : List Value}
    {available : UInt256} {heap i : Nat} (h : MultiRevokeLocals L requests available heap i) (used : UInt256) :
    MultiRevokeLocals (multiRevokeNextLocals L available used i) requests (UInt256.sub available used) heap (i+1) := by
  constructor
  · simpa (disch := decide) only [multiRevokeNextLocals,store_get_ne] using h.requests
  · simp (disch := decide) only [multiRevokeNextLocals,store_get_ne,store_get_self]
  · simpa (disch := decide) only [multiRevokeNextLocals,store_get_ne] using h.heap
  · exact store_get_self _ _ _

theorem multiRevokeUpdateSource {L imms : Store} {evm : EVM.State} {requests : List Value}
    {available used : UInt256} {heap i : Nat} (h : MultiRevokeLocals L requests available heap i)
    (hr : L.get? "__c0" = some (.int (Int.ofNat used.toNat))) (hi : i+1<UInt256.size)
    (hu : used.toNat ≤ available.toNat) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiRevokeUpdate
      (.ok {contract := contract,locals := multiRevokeNextLocals L available used i,immutables := imms} evm) := by
  exact spendAndIncrementSource h.available hr h.index hi hu

end Benchmarks.EAS.EAS
