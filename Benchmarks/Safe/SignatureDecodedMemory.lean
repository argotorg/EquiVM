import Benchmarks.Safe.BytesMemory
import Benchmarks.Safe.PaddedWordMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem memoryBytesDecoded_zero (payload : ByteArray) :
    memLoad ⟨96⟩ (memoryBytesDecoded payload) = ⟨0⟩ := by
  rw [memLoadReadWord, memoryBytesDecoded_preserved _ _ _ (by decide)]
  simp only [show (⟨96⟩ : UInt256).toNat = 96 from rfl]
  unfold memoryBytesInitialHeader
  rw [writeWord_read_disjoint_padded _ 128 96 _
    (.inr (by rw [writeWord_sparse_size, solcFreePtrMem_size]; decide)) (.inl (by decide)),
    writeWord_read_disjoint_padded _ 64 96 _
      (.inr (by rw [solcFreePtrMem_size])) (.inr (by decide)),
    readPastMemory _ _ _ (by rw [solcFreePtrMem_size])]
  decide +kernel

theorem memoryBytesInitialEnd_contains (len : Nat) :
    128 + 32 + len ≤ memoryBytesInitialEnd len := by
  unfold memoryBytesInitialEnd ABI.paddedSize
  omega

end Benchmarks.Safe
