import Benchmarks.EAS.EAS.CopyStoredPadding
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem copyStoredCallRun {L : Store} {args : List Expr} {retVar : Ident}
    {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {word heap ret : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+13 ≤ 1024)
    (hs : SourceState s0 ee σ evm)
    (he : evalExprs? config {contract := contract,locals := L,immutables := immStore v} evm args =
      .ok [wordBytes32Value word,.int (Int.ofNat heap.toNat)])
    (hlo : 96 ≤ heap.toNat) (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨6501⟩ (dbSlot word::ret::R) mem aw rdata σ k C) :
    (∃ mem' aw' k' C' next dataPtr,
      heap.toNat ≤ next ∧ next ≤ 2^64-1 ∧ MemoryPrefix mem mem' heap.toNat ∧
      MemoryPrefix (recordPadding mem heap.toNat) mem' heap.toNat ∧ dataPtr.toNat = heap.toNat+320 ∧
      AttestationMemoryView mem' heap dataPtr (storedAttestationRecord evm word) ∧
      heap.toNat+320 ≤ next ∧
      dataPtr.toNat+32+32*(((storedAttestationRecord evm word).data.size+31)/32) ≤ next ∧
      memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat next ∧
      ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm
        (.internalCall "_copyStoredAttestation" args retVar)
        (.ok (resumeAfterInternalCall {contract := contract,locals := L,immutables := immStore v} retVar
          (some [(storedAttestationRecord evm word).value,.int (Int.ofNat next)])) evm) ∧
      RD fork (deployedRuntime v) ee g s0 ret (heap::R) mem' aw' rdata σ k' C') ∨
    (ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm
      (.internalCall "_copyStoredAttestation" args retVar) .reverted ∧ RDrev fork (deployedRuntime v) g s0) := by
  have hrd := easCopyStored (evm := evm) (word := word) v hstack hfree hlo hret
    (by simpa only [hs.env,← hs.accounts] using rd)
  by_cases hv : copyStoredValid evm word heap.toNat
  · rw [if_pos hv] at hrd
    obtain ⟨aw',k',C',rd'⟩ := hrd
    have hn := copyStoredNext_eq evm word heap.toNat hv.1
    rw [← attestationPayload_size] at hn
    have hp := copyStoredBytePtr_nat (heap := heap) hv.1
    refine Or.inl ⟨_,aw',k',C',copyStoredNext heap.toNat (attestationPayload evm word),
      copyStoredBytePtr heap, le_trans hv.1.2 hv.2.2.2,hv.2.2.1,
      copyStoredOutputMemory_preserve evm word heap mem hv,
      copyStoredOutputMemory_padding evm word heap mem hv,hp,
      copyStoredOutputMemory_view evm word heap mem hlo hv, ?_, ?_,
      copyStoredOutputMemory_heap evm word heap mem hlo, ?_, ?_⟩
    · rw [hn]; unfold bytesAllocation; omega
    · change (copyStoredBytePtr heap).toNat+32+32*(((attestationPayload evm word).size+31)/32) ≤ _
      rw [hp,hn]; unfold bytesAllocation; omega
    · simpa only [storedAttestationRecord_value] using copyStoredCall_ok he hv
    · simpa only [hs.env,← hs.accounts] using rd'
  · rw [if_neg hv] at hrd
    exact Or.inr ⟨copyStoredCall_revert he hv, hrd⟩

end Benchmarks.EAS.EAS
