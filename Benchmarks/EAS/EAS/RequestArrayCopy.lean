import Benchmarks.EAS.EAS.RequestArrayDecode
import Benchmarks.EAS.EAS.CopyRequestArrayReject
import Benchmarks.EAS.EAS.CopyRequestArrayCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem easCopyRequestArrayDecodeReject {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {header heap ret : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+23 ≤ 1024)
    (hsize : ee.calldata.size < 2^255+4) (hbad : decodeRequestArray ee.calldata header = none)
    (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5544⟩
      ((header+UInt256.ofNat 32)::calldataWord ee.calldata header.toNat::UInt256.ofNat ee.calldata.size::ret::R) mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  by_cases hv : requestArrayHeaderValid ee.calldata header
  · have hc := calldataArrayExtent_complete hsize hv.1 hv.2
    rw [decodeRequestArray,if_pos hv] at hbad
    apply easCopyRequestArrayReject v hstack hc hsize hbad hlo hh hfree
    simpa only [u256_ofNat_toNat] using rd
  · exact (easCopyRequestArrayHead v (by omega) hfree rd).2 (fun h => hv ⟨h.1,h.2.2⟩)

theorem requestArrayCopyCallRun {L : Store} {args : List Expr} {retVar : Ident}
    {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {header heap ret : UInt256} {rs : List AttestationRequestRecord} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+23 ≤ 1024)
    (he : evalExprs? config {contract := contract,locals := L,immutables := immStore v} evm args =
      .ok [.array (rs.map AttestationRequestRecord.tuple),.int (Int.ofNat heap.toNat)])
    (hd : decodeRequestArray ee.calldata header = some rs) (hsize : ee.calldata.size < 2^255+4)
    (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5544⟩
      ((header+UInt256.ofNat 32)::calldataWord ee.calldata header.toNat::UInt256.ofNat ee.calldata.size::ret::R) mem aw rdata σ k C) :
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
  obtain ⟨_,hlen,hc⟩ := decodeRequestArray_facts hsize hd
  apply copyRequestArrayCallRun v hstack he hc hsize hlo hh hfree hret
  simpa only [hlen,u256_ofNat_toNat] using rd

end Benchmarks.EAS.EAS
