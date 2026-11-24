import Benchmarks.EAS.EAS.RevokeRun
import Benchmarks.EAS.EAS.RevokePublicSource
import Benchmarks.EAS.EAS.RevokePublicMemory
import Benchmarks.EAS.EAS.RuntimeBlocks_006

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def revokePublicTail : Body := revokePublicRequests ++ ([revokePublicCall] ++ revokePublicFinish)

theorem revokePublicRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+37 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hreq : L.get? "request" = some (revokeRequestValue ee.calldata))
    (hheap : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat 416))) (hcd : ee.calldata.size < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨12085⟩
      (calldataWord ee.calldata 4::UInt256.ofNat 224::UInt256.ofNat ee.source.val::ee.weiValue::UInt256.ofNat 1180::R)
      (revokePublicInputMemory ee.calldata) aw rdata σ k C) :
    (∃ (L' : Store) (evm' : EVM.State) (σ' : AccountMap),
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm revokePublicTail
        (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      SourceState s0 ee σ' evm' ∧ RDret fork (deployedRuntime v) g s0 σ' ByteArray.empty) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm revokePublicTail .reverted ∧ RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm revokePublicTail .staticViolation ∧ RDstatic fork (deployedRuntime v) g s0) := by
  let r := revocationDataRecord ee.calldata 36
  let L1 := revokePublicRequestsLocals L r
  have hreq1 : L1.get? "request" = some (revokeRequestValue ee.calldata) := by
    simpa only [L1,revokePublicRequestsLocals,store_get_ne _ _ (by decide : ("requests" == "request") = false)] using hreq
  have hh1 : L1.get? "$EAS.freeMemory" = some (.int (Int.ofNat 416)) := by
    simpa only [L1,revokePublicRequestsLocals,store_get_ne _ _ (by decide : ("requests" == "$EAS.freeMemory") = false)] using hheap
  have hr1 : L1.get? "requests" = some (.array [r.tuple]) := store_get_self _ _ _
  have hsrc := revokePublicRequestsSource (fork := fork) (imms := immStore v) (evm := evm) hreq
  have he : evalExprs? config {contract := contract,locals := L1,immutables := immStore v} evm attestPublicCallArgs =
      .ok [wordBytes32Value (calldataWord ee.calldata 4),.array ([r].map RevocationRequestRecord.tuple),.address ee.source,
        .int (Int.ofNat ee.weiValue.toNat),.bool true,.int (Int.ofNat (UInt256.ofNat 416).toNat)] := by
    simp only [attestPublicCallArgs,evalExprs?,evalExpr?,hreq1,hh1,hr1,EvalResult.ofOption,bind,EvalResult.bind,pure,
      envValue,hs.env,revokeRequestValue]
    rfl
  obtain ⟨used,hcall⟩ := revokeCallRun (heap := UInt256.ofNat 416) (retVar := "__c0$allocation")
    v .single hstack hs he (revokePublicInputMemory_view ee.calldata).1 (by decide)
    (revokePublicInputMemory_view ee.calldata).2.1 (revokePublicInputMemory_view ee.calldata).2.2
    (fun _ => rfl) hcd (by rw [easPatchedValidJumps v]; jump_dest) rd
  have hr : HeapCallOrStatic fork config (deployedRuntime v) ee g s0
      {contract := contract,locals := L1,immutables := immStore v} evm "_revoke" attestPublicCallArgs "__c0$allocation"
      (.int (Int.ofNat used.toNat)) (UInt256.ofNat 1180) (used::R) (revokePublicInputMemory ee.calldata) 416 := by
    rcases hcall with (⟨_,h⟩ | h) | h
    · exact Or.inl h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  rcases hr with (⟨e1,σ1,m1,out,a1,k1,C1,heap1,hs1,_,_,_,_,hcall,r1⟩ | ⟨hcall,hrev⟩) | ⟨hcall,hstatic⟩
  · have hu := unpackHeapResult (fork := fork) (cfg := config) (evm := e1)
      (frame := {contract := contract,locals := L1.insert "__c0$allocation" (.tuple [.int (Int.ofNat used.toNat),.int (Int.ofNat heap1)]),immutables := immStore v})
      (tmp := "__c0$allocation") (cursor := "$EAS.freeMemory") (result := "__c0") (store_get_self _ _ _)
      (by simpa only [store_get_ne _ _ (by decide : ("__c0$allocation" == "$EAS.freeMemory") = false)] using hh1)
      (by decide) (by decide)
    let Lfinal := unpackHeapLocals
      (L1.insert "__c0$allocation" (.tuple [.int (Int.ofNat used.toNat),.int (Int.ofNat heap1)]))
      "__c0" "$EAS.freeMemory" (.int (Int.ofNat used.toNat)) heap1
    refine Or.inl ⟨Lfinal,e1,σ1,?_,hs1,?_⟩
    · exact execBlock_append hsrc (ExecBlock.consNormal hcall hu)
    · exact easBlocks.eas_block_1180 (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) r1
  · exact Or.inr (Or.inl ⟨execBlock_append hsrc (ExecBlock.consRevert hcall),hrev⟩)
  · exact Or.inr (Or.inr ⟨execBlock_append hsrc (ExecBlock.consStatic hcall),hstatic⟩)

end Benchmarks.EAS.EAS
