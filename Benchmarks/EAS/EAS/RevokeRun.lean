import Benchmarks.EAS.EAS.RevokeSchemaRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem revokeRun {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw schema data available ret heap : UInt256}
    {σ : AccountMap} {k C : Nat} {rs : List RevocationRequestRecord} {revoker : AccountAddress} {last : Bool} {R : List UInt256}
    (v : EASImmutables) (kind : RevokeKind) (hstack : R.length+37 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hdata : RevocationRequestArrayMemoryView mem data rs heap.toNat)
    (hh : heap.toNat ≤ 2^64-1) (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩) (hlast : kind = .single → last = true)
    (hcd : ee.calldata.size < UInt256.size) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 kind.entryPC
      (revokeEntryStack kind schema data (UInt256.ofNat revoker.val) available last.toUInt256 ret R) mem aw rdata σ k C) :
    ∃ used : UInt256, HeapReturnPostOrStatic fork (used.toNat ≤ available.toNat)
      config (deployedRuntime v) ee g s0
      {contract := contract,locals := revokeArgs schema rs revoker available last heap.toNat,immutables := immStore v}
      evm revokeFunction.body (.int (Int.ofNat used.toNat)) ret (used::R) mem heap.toNat := by
  have hdlo := hdata.low
  have hdspan := hdata.span
  have hdcovered := hdata.covered
  have hlo : 128 ≤ heap.toNat := by omega
  have hin : 128 ≤ mem.size := by omega
  have hp : MemoryPrefix mem (getSchemaCallMemory mem heap schema) heap.toNat := selectorArgumentMemory_prefix _ _ _ _
  obtain ⟨gasArg,a1,k1,C1,rd1⟩ := easRevokeSchemaPrepare v kind (by omega)
    (by change heap.toNat+4 < 2^256; omega) hfree rd
  have hz : memLoad (UInt256.ofNat 96) (getSchemaCallMemory mem heap schema) = ⟨0⟩ :=
    (memLoad_of_prefix hp (UInt256.ofNat 96) (by decide) hlo hin).trans hzero
  obtain ⟨used,hr⟩ := revokeSchemaRun v kind hstack hs (hdata.preserve hp heap.val.isLt) hh
    (by unfold getSchemaCallMemory; rw [selectorArgumentMemory_size]; omega) hz hlast
    (getSchemaCallMemory_read mem heap schema) hcd hret rd1
  exact ⟨used,hr.prepend ExecBlock.nil hp (le_refl _)⟩

theorem revokeCallRun {L : Store} {args : List Expr} {retVar : Ident}
    {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw schema data available ret heap : UInt256}
    {σ : AccountMap} {k C : Nat} {rs : List RevocationRequestRecord} {revoker : AccountAddress} {last : Bool} {R : List UInt256}
    (v : EASImmutables) (kind : RevokeKind) (hstack : R.length+37 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (he : evalExprs? config {contract := contract,locals := L,immutables := immStore v} evm args =
      .ok [wordBytes32Value schema,.array (rs.map RevocationRequestRecord.tuple),.address revoker,
        .int (Int.ofNat available.toNat),.bool last,.int (Int.ofNat heap.toNat)])
    (hdata : RevocationRequestArrayMemoryView mem data rs heap.toNat)
    (hh : heap.toNat ≤ 2^64-1) (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩) (hlast : kind = .single → last = true)
    (hcd : ee.calldata.size < UInt256.size) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 kind.entryPC
      (revokeEntryStack kind schema data (UInt256.ofNat revoker.val) available last.toUInt256 ret R) mem aw rdata σ k C) :
    ∃ used : UInt256, HeapCallPostOrStatic fork (used.toNat ≤ available.toNat)
      config (deployedRuntime v) ee g s0 {contract := contract,locals := L,immutables := immStore v} evm
      "_revoke" args retVar (.int (Int.ofNat used.toNat)) ret (used::R) mem heap.toNat := by
  obtain ⟨used,hr⟩ := revokeRun v kind hstack hs hdata hh hfree hzero hlast hcd hret rd
  exact ⟨used,hr.call he revoke_lookup (revoke_bind schema rs revoker available last heap.toNat)⟩

end Benchmarks.EAS.EAS
