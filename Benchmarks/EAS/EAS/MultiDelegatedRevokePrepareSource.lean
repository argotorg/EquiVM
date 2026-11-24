import Benchmarks.EAS.EAS.MultiDelegatedRevokeVerifySource
import Benchmarks.EAS.EAS.MultiDelegatedRevokeAllocateSource
import Benchmarks.EAS.EAS.MultiDelegatedRevokeGuardSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiDelegatedRevokePrepareRow : Body := multiDelegatedRevokeFields ++ multiDelegatedRevokeAllocate ++
  [multiDelegatedRevokeGuard,multiDelegatedRevokeJInit]

theorem MultiDelegatedRevokeLocals.read {L : Store} {requests : List Value} {available : UInt256} {heap i : Nat}
    (h : MultiDelegatedRevokeLocals L requests available heap i) (last : Bool) (row : Value) :
    MultiDelegatedRevokeLocals (batchRowReadLocals L "multiDelegatedRequest" last row) requests available heap i := by
  constructor <;> simp (disch := decide) only [batchRowReadLocals,store_get_ne] <;>
    first | exact h.requests | exact h.available | exact h.heap | exact h.index

theorem multiDelegatedRevokePrepareRowSource {L imms : Store} {evm : EVM.State} {requests : List Value}
    {available : UInt256} {heap i : Nat} {last : Bool} {r : DelegatedRevocationBatch}
    (hf : MultiDelegatedRevokeLocals L requests available heap i)
    (hr : L.get? "multiDelegatedRequest" = some r.tuple) (hlast : L.get? "last" = some (.bool last))
    (hh : heap ≤ 2^64-1) (hdlen : r.data.length ≤ 2^64-1) (hslen : r.signatures.length ≤ 2^64-1) :
    if heap+192+96*r.data.length+128*r.signatures.length ≤ 2^64-1 then
      if 0<r.data.length ∧ r.data.length=r.signatures.length then
        ∃ L', ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedRevokePrepareRow
          (.ok {contract := contract,locals := L',immutables := imms} evm) ∧
          MultiDelegatedRevokeVerifyLocals L' requests available
            (heap+192+96*r.data.length+128*r.signatures.length) i 0 last r
      else ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedRevokePrepareRow .reverted
    else ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedRevokePrepareRow .reverted := by
  let L1 := multiDelegatedRevokeFieldLocals L r
  have hsol1 := multiDelegatedRevokeFieldsSource (fork := fork) (imms := imms) (evm := evm) hr
  have hd1 : L1.get? "data"=some (.array (r.data.map RevocationRequestRecord.tuple)) := by
    simp (disch := decide) only [L1,multiDelegatedRevokeFieldLocals,store_get_ne,store_get_self]
  have hs1 : L1.get? "signatures"=some (.array (r.signatures.map SignatureRecord.tuple)) := store_get_self _ _ _
  have hf1 : L1.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap)) := by
    simpa (disch := decide) only [L1,multiDelegatedRevokeFieldLocals,store_get_ne] using hf.heap
  have hsol2 := multiDelegatedRevokeAllocateSource (fork := fork) (imms := imms) (evm := evm) hd1 hs1 hf1 hh hdlen hslen
  by_cases ha : heap+192+96*r.data.length+128*r.signatures.length ≤ 2^64-1
  · rw [if_pos ha] at hsol2 ⊢
    let L2 := multiDelegatedRevokeAllocatedLocals L1 r heap
    have hd2 : L2.get? "data"=some (.array (r.data.map RevocationRequestRecord.tuple)) := by
      simpa (disch := decide) only [L2,multiDelegatedRevokeAllocatedLocals,allocateBlockLocals_get] using hd1
    have hs2 : L2.get? "signatures"=some (.array (r.signatures.map SignatureRecord.tuple)) := by
      simpa (disch := decide) only [L2,multiDelegatedRevokeAllocatedLocals,allocateBlockLocals_get] using hs1
    have hsol3 := multiDelegatedRevokeGuardSource (fork := fork) (imms := imms) (evm := evm) hd2 hs2
    by_cases hg : 0<r.data.length ∧ r.data.length=r.signatures.length
    · rw [if_pos hg] at hsol3 ⊢
      let L3 := L2.insert "j" (.int (Int.ofNat 0))
      have hsol4 : ExecStmt fork config {contract := contract,locals := L2,immutables := imms} evm multiDelegatedRevokeJInit
          (.ok {contract := contract,locals := L3,immutables := imms} evm) :=
        ExecStmt.letDecl (by simp only [evalExpr?,pure]; rfl)
      refine ⟨L3,execBlock_append (execBlock_append hsol1 hsol2)
        (ExecBlock.consNormal hsol3 (ExecBlock.consNormal hsol4 ExecBlock.nil)),?_,?_,?_,?_,?_,store_get_self _ _ _⟩
      · constructor <;> simp (disch := decide) only [L3,L2,multiDelegatedRevokeAllocatedLocals,
          allocateBlockLocals_get,store_get_ne,L1,multiDelegatedRevokeFieldLocals,
          allocateBlockLocals,unpackHeapLocals,store_get_self] <;>
          first | exact hf.requests | exact hf.available | exact hf.index
      all_goals simp (disch := decide) only [L3,L2,multiDelegatedRevokeAllocatedLocals,
        allocateBlockLocals_get,store_get_ne,L1,multiDelegatedRevokeFieldLocals,store_get_self]
      all_goals first | exact hr | exact hlast
    · rw [if_neg hg] at hsol3 ⊢
      exact execBlock_append (execBlock_append hsol1 hsol2) (ExecBlock.consRevert hsol3)
  · rw [if_neg ha] at hsol2 ⊢
    simpa only [multiDelegatedRevokePrepareRow,List.append_assoc] using execBlock_append hsol1
      (execBlock_append_term (s2 := [multiDelegatedRevokeGuard,multiDelegatedRevokeJInit]) hsol2 (by intros; exact nofun))

end Benchmarks.EAS.EAS
