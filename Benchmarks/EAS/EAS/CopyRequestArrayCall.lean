import Benchmarks.EAS.EAS.CopyRequestArrayRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem copyRequestArrayCallRun {L : Store} {args : List Expr} {retVar : Ident}
    {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {offset heap ret : UInt256} {rs : List AttestationRequestRecord} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+23 ≤ 1024)
    (he : evalExprs? config {contract := contract,locals := L,immutables := immStore v} evm args =
      .ok [.array (rs.map AttestationRequestRecord.tuple),.int (Int.ofNat heap.toNat)])
    (hc : RequestArrayCalldataView ee.calldata offset rs) (hsize : ee.calldata.size < 2^255+4)
    (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5544⟩ (offset::UInt256.ofNat rs.length::UInt256.ofNat ee.calldata.size::ret::R) mem aw rdata σ k C) :
    (∃ mem' aw' k' C' next,
      heap.toNat ≤ next ∧ next ≤ 2^64-1 ∧ MemoryPrefix mem mem' heap.toNat ∧
      AttestationRequestArrayRegion mem' heap rs heap.toNat next ∧
      memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat next ∧
      ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm
        (.internalCall "_copyAttestationArray" args retVar)
        (.ok (resumeAfterInternalCall {contract := contract,locals := L,immutables := immStore v} retVar
          (some [.tuple [],.int (Int.ofNat next)])) evm) ∧
      RD fork (deployedRuntime v) ee g s0 ret (heap::R) mem' aw' rdata σ k' C') ∨
    (ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm
      (.internalCall "_copyAttestationArray" args retVar) .reverted ∧ RDrev fork (deployedRuntime v) g s0) := by
  have hd : (copyRequestArrayArgs rs heap.toNat).get? "data" = some (.array (rs.map AttestationRequestRecord.tuple)) := store_get_self _ _ _
  have hf : (copyRequestArrayArgs rs heap.toNat).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap.toNat)) := by
    simp (disch := decide) only [copyRequestArrayArgs,store_get_ne,store_get_self]
  rcases copyRequestArrayRun (evm := evm) v hstack hc hsize hd hf hlo hh hfree hret rd with
    ⟨L',m,a,j,D,next,hlo',hhi',hp,hm,hfree',hsol,hr⟩ | ⟨hsol,hrev⟩
  · exact Or.inl ⟨m,a,j,D,next,hlo',hhi',hp,hm,hfree',
      internalCallFunctionReturn he copyRequestArray_lookup (copyRequestArray_bind rs heap.toNat) hsol,hr⟩
  · exact Or.inr ⟨internalCallFunctionRevert he copyRequestArray_lookup (copyRequestArray_bind rs heap.toNat) hsol,hrev⟩

end Benchmarks.EAS.EAS
