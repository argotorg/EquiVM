import Benchmarks.EAS.EAS.MultiRequestRead
import Benchmarks.EAS.EAS.MultiRevocationDecode
import Benchmarks.EAS.EAS.RevokeRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiRevokeInitial : Body := [
  .letDecl "availableValue" (some abiUInt256) (.env .callvalue),
  .letDecl "i" (some abiUInt256) (.intLit 0)]
def multiRevokeRead : Body := multiRequestRead multiRevocationABI
def multiRevokeAllocate : Body := [
  .letDecl "data" (some (.dynamicArray revocationDataABI)) (.tupleGet (.var "multiRequest") 1)] ++
  arrayAllocateExprBlock (.arrayLength .localVar {base := "data"}) 96
def multiRevokeCall : Body := heapResultBlock "_revoke" multiAttestCallArgs "__c0$allocation" "__c0" "$EAS.freeMemory"
def multiRevokeUpdate : Body := [
  .assign .localVar {base := "availableValue"} (.inRange abiUInt256Int (.binary .sub (.var "availableValue") (.var "__c0"))),
  localCastIncrement "i"]
def multiRevokeIteration : Body := multiRevokeRead ++ [multiAttestCheck] ++ multiRevokeAllocate ++ multiRevokeCall ++ multiRevokeUpdate

theorem multiRevoke_body : multiRevokeTransition.body = easPayableEntryPrefix ++ multiRevokeInitial ++
    [.while (localArrayGuard "i" "multiRequests") multiRevokeIteration] := by native_decide

structure MultiRevokeLocals (L : Store) (requests : List Value) (available : UInt256) (heap i : Nat) : Prop where
  requests : L.get? "multiRequests" = some (.array requests)
  available : L.get? "availableValue" = some (.int (Int.ofNat available.toNat))
  heap : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))
  index : L.get? "i" = some (.int (Int.ofNat i))

def multiRevokeInitialLocals (L : Store) (available : UInt256) : Store :=
  L.insert "availableValue" (.int (Int.ofNat available.toNat)) |>.insert "i" (.int 0)

theorem multiRevokeInitialSource {L imms : Store} {evm : EVM.State} {requests : List Value} {heap : Nat}
    (hd : L.get? "multiRequests" = some (.array requests))
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiRevokeInitial
      (.ok {contract := contract,locals := multiRevokeInitialLocals L evm.executionEnv.weiValue,immutables := imms} evm) ∧
    MultiRevokeLocals (multiRevokeInitialLocals L evm.executionEnv.weiValue) requests evm.executionEnv.weiValue heap 0 := by
  constructor
  · exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?,pure,envValue]; rfl))
      (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?,pure])) ExecBlock.nil)
  · constructor
    · simpa (disch := decide) only [multiRevokeInitialLocals,store_get_ne] using hd
    · simp (disch := decide) only [multiRevokeInitialLocals,store_get_self,store_get_ne]
    · simpa (disch := decide) only [multiRevokeInitialLocals,store_get_ne] using hh
    · exact store_get_self _ _ _

theorem MultiRevokeLocals.read {L : Store} {requests : List Value} {available : UInt256} {heap i : Nat}
    (h : MultiRevokeLocals L requests available heap i) (last : Bool) (row : Value) :
    MultiRevokeLocals (multiAttestReadLocals L last row) requests available heap i := by
  constructor <;> simp (disch := decide) only [multiAttestReadLocals,store_get_ne] <;>
    first | exact h.requests | exact h.available | exact h.heap | exact h.index

def multiRevokeAllocatedLocals (L : Store) (rs : List RevocationRequestRecord) (next : Nat) : Store :=
  allocateBlockLocals (L.insert "data" (.array (rs.map RevocationRequestRecord.tuple))) next

theorem multiRevokeAllocateSource {L imms : Store} {evm : EVM.State} {schema : UInt256}
    {rs : List RevocationRequestRecord} {heap : Nat}
    (hr : L.get? "multiRequest" = some (multiRevocationTuple schema rs))
    (hf : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hlen : rs.length ≤ 2^64-1) (hh : heap ≤ 2^64-1) :
    if heap+32+96*rs.length ≤ 2^64-1 then
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiRevokeAllocate
        (.ok {contract := contract,locals := multiRevokeAllocatedLocals L rs (heap+32+96*rs.length),immutables := imms} evm)
    else ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiRevokeAllocate .reverted := by
  let L1 := L.insert "data" (.array (rs.map RevocationRequestRecord.tuple))
  have hd : ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm
      (.letDecl "data" (some (.dynamicArray revocationDataABI)) (.tupleGet (.var "multiRequest") 1))
      (.ok {contract := contract,locals := L1,immutables := imms} evm) := by
    apply ExecStmt.letDecl
    simp only [evalExpr?,hr,multiRevocationTuple,EvalResult.ofOption,bind,EvalResult.bind,pure]
    rfl
  have hh1 : L1.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) := by
    simpa (disch := decide) only [L1,store_get_ne] using hf
  have ha := arrayAllocateExprSource (fork := fork) (cfg := config) (imms := imms) (evm := evm)
    (evalLocalArrayLength (store_get_self L "data" (.array (rs.map RevocationRequestRecord.tuple)))) hh1 96
  have hn : allocateNext heap (32+96*rs.length) = heap+32+96*rs.length := by
    rw [allocateNext_small hh (by omega)]
    omega
  simp only [List.length_map,if_pos hlen,hn] at ha
  by_cases hg : heap+32+96*rs.length ≤ 2^64-1
  · rw [if_pos hg]
    rw [if_pos ⟨hg,by omega⟩] at ha
    exact ExecBlock.consNormal hd ha
  · rw [if_neg hg]
    rw [if_neg (fun h => hg h.1)] at ha
    exact ExecBlock.consNormal hd ha

end Benchmarks.EAS.EAS
