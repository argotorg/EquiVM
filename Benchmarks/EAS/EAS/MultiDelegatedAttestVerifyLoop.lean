import Benchmarks.EAS.EAS.MultiDelegatedAttestVerifyIteration
import Benchmarks.EAS.EAS.WhileInvariant

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiDelegatedAttestVerifyLoop : Stmt := .while (localArrayGuard "j" "data") multiDelegatedAttestVerifyIteration

theorem multiDelegatedAttestVerifyLoopRun {L : Store} {evm : EVM.State}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {requests : List Value} {groups : List (List UInt256)}
    {n i : Nat} {base available groupsPtr root : UInt256} {initial : ByteArray} {start : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+40 ≤ 1024) (hsize : ee.calldata.size<2^255) (hlo : 96≤start)
    (hb : DelegatedAttestationBatchReady ee.calldata root)
    (h : MultiDelegatedAttestVerifyAt fork v ee g s0 requests groups n i base available groupsPtr root initial start R 0 L evm) :
    (∃ L' evm', ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedAttestVerifyLoop
      (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      MultiDelegatedAttestVerifyAt fork v ee g s0 requests groups n i base available groupsPtr root initial start R (delegatedAttestationDataLength ee.calldata root).toNat L' evm') ∨
    (ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedAttestVerifyLoop .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedAttestVerifyLoop .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  apply execWhile_invariant
    (MultiDelegatedAttestVerifyAt fork v ee g s0 requests groups n i base available groupsPtr root initial start R)
    (MultiDelegatedAttestVerifyAt fork v ee g s0 requests groups n i base available groupsPtr root initial start R (delegatedAttestationDataLength ee.calldata root).toNat)
    (RDrev fork (deployedRuntime v) g s0) (RDstatic fork (deployedRuntime v) g s0)
    ?_ (fun _ _ h => h) ?_ (delegatedAttestationDataLength ee.calldata root).toNat 0 L evm (by omega) h
  · rintro j L1 e1 _ ⟨σ,mem,out,aw,k,C,heap,_,_,_,_,hf,_,_,_,_⟩
    simpa only [delegatedAttestationDataList_length] using evalLocalArrayGuard (cfg := config)
      (frame := {contract := contract,locals := L1,immutables := immStore v}) (evm := e1) hf.index hf.data
  · intro j L1 e1 hj h1
    exact multiDelegatedAttestVerifyIterationRun v hstack hsize hlo hb hj h1

end Benchmarks.EAS.EAS
