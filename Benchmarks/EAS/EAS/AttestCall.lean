import Benchmarks.EAS.EAS.AttestRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem attestCallRun {locals : Store} {args : List Expr} {retVar : Ident}
    {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw schema data available ret heap : UInt256}
    {σ : AccountMap} {k C : Nat} {rs : List AttestationRequestRecord}
    {attester : AccountAddress} {last : Bool} {R : List UInt256}
    (v : EASImmutables) (kind : AttestCallKind)
    (he : evalExprs? config {contract := contract,locals := locals,immutables := immStore v} evm args =
      .ok [wordBytes32Value schema,.array (rs.map AttestationRequestRecord.tuple),.address attester,
        .int (Int.ofNat available.toNat),.bool last,.int (Int.ofNat heap.toNat)])
    (hstack : R.length+38 ≤ 1024) (hstate : SourceState s0 ee σ evm)
    (hdata : AttestationRequestArrayRegion mem data rs 224 heap.toNat)
    (hh : heap.toNat ≤ 2^64-1) (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩) (hlast : kind = .single → last = true)
    (hcd : ee.calldata.size < UInt256.size) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 kind.entryPC
      (attestEntryStack kind schema data (UInt256.ofNat attester.val) available last.toUInt256 ret R) mem aw rdata σ k C) :
    let result := UInt256.ofNat (allocateNext heap.toNat 64)
    let uid := UInt256.ofNat (allocateNext heap.toNat 128)
    (∃ (evm' : EVM.State) (σ' : AccountMap) (mem' out : ByteArray) (aw' : UInt256)
        (k' C' heap' : Nat) (uids : List UInt256) (used : UInt256),
      SourceState s0 ee σ' evm' ∧ heap.toNat ≤ heap' ∧ heap' ≤ 2^64-1 ∧ uids.length = rs.length ∧ used.toNat ≤ available.toNat ∧
      MemoryPrefix (attestAllocationMemory kind mem heap data (UInt256.ofNat attester.val)) mem' heap.toNat ∧
      AttestResultMemoryView mem' result uid uids used heap' ∧
      memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat heap' ∧
      ExecStmt fork config {contract := contract,locals := locals,immutables := immStore v} evm
        (.internalCall "_attest" args retVar)
        (.ok (resumeAfterInternalCall {contract := contract,locals := locals,immutables := immStore v}
          retVar (some [attestationsResultValue uids used,.int (Int.ofNat heap')])) evm') ∧
      RD fork (deployedRuntime v) ee g s0 ret (result::R) mem' aw' out σ' k' C') ∨
    (ExecStmt fork config {contract := contract,locals := locals,immutables := immStore v} evm
      (.internalCall "_attest" args retVar) .reverted ∧ RDrev fork (deployedRuntime v) g s0) ∨
    (ExecStmt fork config {contract := contract,locals := locals,immutables := immStore v} evm
      (.internalCall "_attest" args retVar) .staticViolation ∧ RDstatic fork (deployedRuntime v) g s0) := by
  have h := attestRun v kind hstack hstate hdata hh hheap hzero hlast hcd hret rd
  rcases h with ⟨L',e',σ',m',out,a',j,D,n,us,used,hs,hlo,hhi,hlen,hbudget,hmem,hview,hfree,hsrc,hr⟩ | ⟨hsrc,hr⟩ | ⟨hsrc,hr⟩
  · exact Or.inl ⟨e',σ',m',out,a',j,D,n,us,used,hs,hlo,hhi,hlen,hbudget,hmem,hview,hfree,
      internalCallFunctionReturn he attest_lookup (attest_bind schema rs attester available last heap.toNat) hsrc,hr⟩
  · exact Or.inr (Or.inl ⟨internalCallFunctionRevert he attest_lookup (attest_bind schema rs attester available last heap.toNat) hsrc,hr⟩)
  · exact Or.inr (Or.inr ⟨internalCallFunctionStatic he attest_lookup (attest_bind schema rs attester available last heap.toNat) hsrc,hr⟩)

end Benchmarks.EAS.EAS
