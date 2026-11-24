import Benchmarks.EAS.EAS.ArrayNewExpr
import Benchmarks.EAS.EAS.AttestPublicSource
import Benchmarks.EAS.EAS.MultiRequestArrayDecode
import Benchmarks.EAS.EAS.MergeUIDSource
import Benchmarks.EAS.EAS.HeapResultBlock

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiAttestLength : Expr := .arrayLength .localVar {base := "multiRequests"}
def multiAttestInitial : Body := [
  .letDecl "totalUids" (some (.dynamicArray (.dynamicArray abiBytes32)))
    (.newArray (.dynamicArray (.elem (.bytes abiBytes32Width))) multiAttestLength),
  .letDecl "totalUidsCount" (some abiUInt256) (.intLit 0),
  .letDecl "availableValue" (some abiUInt256) (.env .callvalue),
  .letDecl "i" (some abiUInt256) (.intLit 0)]
def multiAttestAllocateBody : Body := arrayAllocateExprBlock multiAttestLength 32 ++ multiAttestInitial

def multiAttestLast : Expr := .binary .eq (.var "i")
  (.cast (.binary .sub multiAttestLength (.intLit 1)) (.elem (.int abiUInt256Int)))
def multiAttestRead : Body := [
  .letDecl "last" (some (.elem .bool)) (.boolLit false),
  .assign .localVar {base := "last"} multiAttestLast,
  .letDecl "multiRequest" (some multiRequestABI) (.index (.var "multiRequests") (.var "i"))]
def multiAttestCheck : Stmt := .require (.binary .ne (.var "multiRequest")
  (.structLit ABI.Solc08Calldata.decodeFailureTag []))
def multiAttestCopyArgs : List Expr := [.tupleGet (.var "multiRequest") 1,.var "$EAS.freeMemory"]
def multiAttestCopy : Body := heapResultBlock "_copyAttestationArray" multiAttestCopyArgs "allocation$allocation" "allocation" "$EAS.freeMemory"
def multiAttestCallArgs : List Expr := [
  .tupleGet (.var "multiRequest") 0,.tupleGet (.var "multiRequest") 1,.env .caller,
  .var "availableValue",.var "last",.var "$EAS.freeMemory"]
def multiAttestCall : Body := heapResultBlock "_attest" multiAttestCallArgs "res$allocation" "res" "$EAS.freeMemory"
def multiAttestUpdate : Body := [
  .assign .localVar {base := "availableValue"}
    (.inRange abiUInt256Int (.binary .sub (.var "availableValue") (.field (.var "res") "usedValue"))),
  .assign .localVar {base := "totalUids",steps := [.aindex (.var "i")]} (.field (.var "res") "uids"),
  .assign .localVar {base := "totalUidsCount"}
    (.cast (.binary .add (.var "totalUidsCount") (.arrayLength .localVar {base := "res",steps := [.field "uids"]})) (.elem (.int abiUInt256Int))),
  localCastIncrement "i"]
def multiAttestIteration : Body := multiAttestRead ++ [multiAttestCheck] ++ multiAttestCopy ++ multiAttestCall ++ multiAttestUpdate
def multiAttestMergeArgs : List Expr := [.var "totalUids",.var "totalUidsCount",.var "$EAS.freeMemory"]
def multiAttestFinish : Body := heapResultBlock "_mergeUIDs" multiAttestMergeArgs "__c1$allocation" "__c1" "$EAS.freeMemory" ++ [.return [.var "__c1"]]

theorem multiAttest_body : multiAttestTransition.body = easPayableEntryPrefix ++ multiAttestAllocateBody ++
    [.while (localArrayGuard "i" "multiRequests") multiAttestIteration] ++ multiAttestFinish := by native_decide

structure MultiAttestLocals (L : Store) (requests : List Value) (uidLists : List (List UInt256))
    (available : UInt256) (heap i : Nat) : Prop where
  requests : L.get? "multiRequests" = some (.array requests)
  groups : L.get? "totalUids" = some (.array (uidLists.map wordListValue))
  count : L.get? "totalUidsCount" = some (.int (Int.ofNat uidLists.flatten.length))
  available : L.get? "availableValue" = some (.int (Int.ofNat available.toNat))
  heap : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))
  index : L.get? "i" = some (.int (Int.ofNat i))

def multiAttestInitialLocals (L : Store) (n heap : Nat) (available : UInt256) : Store :=
  (allocateBlockLocals L heap).insert "totalUids" (.array ((List.replicate n []).map wordListValue))
    |>.insert "totalUidsCount" (.int 0) |>.insert "availableValue" (.int (Int.ofNat available.toNat)) |>.insert "i" (.int 0)

-- GENERALIZES the batch allocation prefix to either attestation request variable.
def batchAttestAllocateBody (length : Expr) : Body := arrayAllocateExprBlock length 32 ++ [
  .letDecl "totalUids" (some (.dynamicArray (.dynamicArray abiBytes32)))
    (.newArray (.dynamicArray (.elem (.bytes abiBytes32Width))) length),
  .letDecl "totalUidsCount" (some abiUInt256) (.intLit 0),
  .letDecl "availableValue" (some abiUInt256) (.env .callvalue),.letDecl "i" (some abiUInt256) (.intLit 0)]

theorem batchAttestAllocateSource {L imms : Store} {evm : EVM.State} {length : Expr} {n heap : Nat}
    (he : evalExpr? config {contract := contract,locals := L,immutables := imms} evm length=.ok (.int (Int.ofNat n)))
    (he' : ∀ next, evalExpr? config {contract := contract,locals := allocateBlockLocals L next,immutables := imms} evm length=.ok (.int (Int.ofNat n)))
    (hh : L.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap))) (hlen : n≤2^64-1) :
    let next := allocateNext heap (32+32*n)
    if next≤2^64-1 ∧ heap≤next then
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm (batchAttestAllocateBody length)
        (.ok {contract := contract,locals := multiAttestInitialLocals L n next evm.executionEnv.weiValue,immutables := imms} evm)
    else ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm (batchAttestAllocateBody length) .reverted := by
  dsimp only
  have ha := arrayAllocateExprSource (fork := fork) he hh 32
  rw [if_pos hlen] at ha
  split <;> rename_i hg
  · rw [if_pos hg] at ha
    have heNew : evalExpr? config {contract := contract,locals := allocateBlockLocals L (allocateNext heap (32+32*n)),immutables := imms} evm
        (.newArray (.dynamicArray (.elem (.bytes abiBytes32Width))) length)=.ok (.array ((List.replicate n []).map wordListValue)) := by
      simp only [List.map_replicate,wordListValue,List.map_nil]
      exact evalNewArrayExpr (he' _) (by native_decide)
    exact execBlock_append ha (ExecBlock.consNormal (ExecStmt.letDecl heNew)
      (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?,pure]))
        (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?,pure,envValue];rfl))
          (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?,pure])) ExecBlock.nil))))
  · rw [if_neg hg] at ha
    exact execBlock_append_term ha (by intros;exact nofun)

theorem multiAttestAllocateSource {L imms : Store} {evm : EVM.State} {requests : List Value} {heap : Nat}
    (hd : L.get? "multiRequests" = some (.array requests))
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hlen : requests.length ≤ 2^64-1) :
    let next := allocateNext heap (32+32*requests.length)
    if next ≤ 2^64-1 ∧ heap ≤ next then
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiAttestAllocateBody
        (.ok {contract := contract,locals := multiAttestInitialLocals L requests.length next evm.executionEnv.weiValue,immutables := imms} evm) ∧
      MultiAttestLocals (multiAttestInitialLocals L requests.length next evm.executionEnv.weiValue)
        requests (List.replicate requests.length []) evm.executionEnv.weiValue next 0
    else ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiAttestAllocateBody .reverted := by
  dsimp only
  have hd' (next : Nat) : (allocateBlockLocals L next).get? "multiRequests"=some (.array requests) := by
    simpa (disch := decide) only [allocateBlockLocals_get] using hd
  have hs := batchAttestAllocateSource (fork := fork) (length := multiAttestLength) (evalLocalArrayLength (cfg := config) (stele := {contract := contract,locals := L,immutables := imms}) (evm := evm) hd)
    (fun next => evalLocalArrayLength (hd' next)) hh hlen
  dsimp only at hs
  split <;> rename_i hg
  · rw [if_pos hg] at hs
    refine ⟨hs,?_⟩
    constructor
    · simpa (disch := decide) only [multiAttestInitialLocals,store_get_ne] using hd' _
    · simp (disch := decide) only [multiAttestInitialLocals,store_get_self,store_get_ne]
    · simp (disch := decide) only [multiAttestInitialLocals,store_get_self,store_get_ne,List.flatten_replicate_nil,List.length_nil,Int.ofNat_eq_natCast,Nat.cast_zero]
    · simp (disch := decide) only [multiAttestInitialLocals,store_get_self,store_get_ne]
    · simp (disch := decide) only [multiAttestInitialLocals,allocateBlockLocals,unpackHeapLocals,store_get_self,store_get_ne]
    · exact store_get_self _ _ _
  · simpa only [if_neg hg] using hs

end Benchmarks.EAS.EAS
