import Benchmarks.EAS.EAS.RevokePublicSource
import Benchmarks.EAS.EAS.VerifyRevokeSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def delegatedRevokeRecordStmt : Stmt := .letDecl "delegatedRequest" none
  (.structLit "DelegatedRevocationRequest" [("schema",.tupleGet (.var "delegatedRequest") 0),
    ("data",.tupleGet (.var "delegatedRequest") 1),("signature",.tupleGet (.var "delegatedRequest") 2),
    ("revoker",.tupleGet (.var "delegatedRequest") 3)])
def delegatedRevokePrefix : Body := easPayableEntryPrefix ++ allocateBlock (.intLit 288) ++ [delegatedRevokeRecordStmt]
def delegatedRevokePrefixLocals (L : Store) (cd : ByteArray) (r : DelegatedRevocationRecord) : Store :=
  (allocateBlockLocals (easEntryLocals L cd) 512).insert "delegatedRequest" r.struct
def delegatedRevokeVerifyArgs : List Expr := [.var "delegatedRequest",.var "$EAS.freeMemory"]
def delegatedRevokeVerify : Body := heapResultBlock "_verifyRevoke" delegatedRevokeVerifyArgs
  "__c0$allocation" "__c0" "$EAS.freeMemory"
def delegatedRevokeData : Body := [
  .letDecl "data" (some (.dynamicArray revocationDataABI)) (.newArray revocationDataType (.intLit 1)),
  .assign .localVar {base := "data",steps := [.aindex (.intLit 0)]} (.field (.var "delegatedRequest") "data")]
def delegatedRevokeDataLocals (L : Store) (r : RevocationRequestRecord) : Store :=
  (L.insert "data" (.array [defaultRevocationRecord.struct])).insert "data" (.array [r.tuple])
def delegatedRevokeCallArgs : List Expr := [.field (.var "delegatedRequest") "schema",.var "data",
  .field (.var "delegatedRequest") "revoker",.env .callvalue,.boolLit true,.var "$EAS.freeMemory"]
def delegatedRevokeCall : Body := heapResultBlock "_revoke" delegatedRevokeCallArgs
  "__c1$allocation" "__c1" "$EAS.freeMemory"
def delegatedRevokeTail : Body := allocateBlock (.intLit 192) ++ delegatedRevokeData ++ delegatedRevokeCall

theorem delegatedRevoke_body : revokeByDelegationTransition.body = delegatedRevokePrefix ++ delegatedRevokeVerify ++ delegatedRevokeTail := by native_decide

theorem delegatedRevokePrefixSource {L imms : Store} {evm : EVM.State} {r : DelegatedRevocationRecord}
    (hr : L.get? "delegatedRequest" = some r.tuple)
    (hsz : 4 ≤ evm.executionEnv.calldata.size) (hsize : evm.executionEnv.calldata.size < UInt256.size)
    (hguard : evm.executionEnv.calldata.size-4 < 2^255) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm delegatedRevokePrefix
      (.ok {contract := contract,locals := delegatedRevokePrefixLocals L evm.executionEnv.calldata r,immutables := imms} evm) := by
  rw [delegatedRevokePrefix,List.append_assoc]
  apply execBlock_append (easPayableEntryPrefix_ok hsz hsize hguard)
  have ha := allocateBlock_ok (fork := fork) (cfg := config) (evm := evm) (locals := easEntryLocals L evm.executionEnv.calldata)
    (imms := imms) (size := .intLit 288) (n := 288) (heap := 224)
    (by simp only [evalExpr?,pure]; rfl)
    (by simp (disch := decide) only [easEntryLocals,store_get_ne,store_get_self]; rfl) (by decide)
  simp only [show allocateNext 224 288 = 512 by native_decide] at ha
  apply execBlock_append ha
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := r.struct) ?_) ExecBlock.nil
  have hr' : (allocateBlockLocals (easEntryLocals L evm.executionEnv.calldata) 512).get? "delegatedRequest" = some r.tuple := by
    simpa (disch := decide) only [allocateBlockLocals_get,easEntryLocals,store_get_ne] using hr
  simp only [evalExpr?,evalStructFields?,hr',DelegatedRevocationRecord.tuple,DelegatedRevocationRecord.struct,
    EvalResult.ofOption,bind,EvalResult.bind,pure]
  rfl

theorem delegatedRevokeDataSource {L imms : Store} {evm : EVM.State} {r : DelegatedRevocationRecord}
    (hr : L.get? "delegatedRequest" = some r.struct) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm delegatedRevokeData
      (.ok {contract := contract,locals := delegatedRevokeDataLocals L r.data,immutables := imms} evm) := by
  have hd : defaultValue? revocationDataType = .ok defaultRevocationRecord.struct := by native_decide
  have he : evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.newArray revocationDataType (.intLit 1)) = .ok (.array [defaultRevocationRecord.struct]) := by
    simp only [evalExpr?,pure,bind,EvalResult.bind,show ¬ (1 : Int) < 0 by decide,if_false,hd]
    rfl
  apply ExecBlock.consNormal (ExecStmt.letDecl he)
  apply ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (value := r.data.tuple) ?_ ?_) ExecBlock.nil
  · apply evalRecordField (record := r.struct) ?_ rfl
    simp only [evalExpr?,store_get_ne _ _ (by decide : ("data" == "delegatedRequest") = false),hr,EvalResult.ofOption]
  · exact assignLocalArrayExpr (cfg := config) (evm := evm)
      (frame := {contract := contract,locals := L.insert "data" (.array [defaultRevocationRecord.struct]),immutables := imms})
      (name := "data") (values := [defaultRevocationRecord.struct]) (index := .intLit 0) (i := 0) (value := r.data.tuple)
      (store_get_self _ _ _) (by simp only [evalExpr?,pure]; rfl) (by simp)

end Benchmarks.EAS.EAS
