import Benchmarks.EAS.EAS.BatchRowRead
import Benchmarks.EAS.EAS.DelegatedRevocationDecodeFacts
import Benchmarks.EAS.EAS.VerifyRevokeRun
import Benchmarks.EAS.EAS.ArrayAllocateSource
import Benchmarks.EAS.EAS.RevokeRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiDelegatedRevokeInitial : Body := [
  .letDecl "availableValue" (some abiUInt256) (.env .callvalue),.letDecl "i" (some abiUInt256) (.intLit 0)]
def multiDelegatedRevokeRead : Body := batchRowRead DelegatedBatchSite.revoke.abi "multiDelegatedRequests" "multiDelegatedRequest"
def multiDelegatedRevokeCheck : Stmt :=
  .require (.binary .ne (.var "multiDelegatedRequest") (.structLit "$solc08Calldata.decodeFailure" []))
def multiDelegatedRevokeFields : Body := [
  .letDecl "data" (some (.dynamicArray revocationDataABI)) (.tupleGet (.var "multiDelegatedRequest") 1),
  .letDecl "signatures" (some (.dynamicArray signatureABI)) (.tupleGet (.var "multiDelegatedRequest") 2)]
def multiDelegatedRevokeAllocate : Body := allocateBlock (.intLit 128) ++
  arrayAllocateExprBlock (.arrayLength .localVar {base := "data"}) 96 ++
  arrayAllocateExprBlock (.arrayLength .localVar {base := "signatures"}) 128
def multiDelegatedRevokeGuard : Stmt := .require (.unary .not (.binary .or
  (.binary .eq (.arrayLength .localVar {base := "data"}) (.intLit 0))
  (.binary .ne (.arrayLength .localVar {base := "data"}) (.arrayLength .localVar {base := "signatures"}))))
def multiDelegatedRevokeJInit : Stmt := .letDecl "j" (some abiUInt256) (.intLit 0)
def multiDelegatedRevokeVerifyArgs : List Expr := [
  .structLit "DelegatedRevocationRequest" [
    ("schema",.tupleGet (.var "multiDelegatedRequest") 0),
    ("data",.index (.var "data") (.var "j")),
    ("signature",.index (.var "signatures") (.var "j")),
    ("revoker",.tupleGet (.var "multiDelegatedRequest") 3)],.var "$EAS.freeMemory"]
def multiDelegatedRevokeVerify : Body := heapResultBlock "_verifyRevoke" multiDelegatedRevokeVerifyArgs
  "__c0$allocation" "__c0" "$EAS.freeMemory"
def multiDelegatedRevokeVerifyIteration : Body := allocateBlock (.intLit 128) ++
  multiDelegatedRevokeVerify ++ [localCastIncrement "j"]
def multiDelegatedRevokeCallArgs : List Expr := [
  .tupleGet (.var "multiDelegatedRequest") 0,.var "data",.tupleGet (.var "multiDelegatedRequest") 3,
  .var "availableValue",.var "last",.var "$EAS.freeMemory"]
def multiDelegatedRevokeCall : Body := heapResultBlock "_revoke" multiDelegatedRevokeCallArgs
  "__c1$allocation" "__c1" "$EAS.freeMemory"
def multiDelegatedRevokeUpdate : Body := [
  .assign .localVar {base := "availableValue"} (.inRange abiUInt256Int (.binary .sub (.var "availableValue") (.var "__c1"))),
  localCastIncrement "i"]
def multiDelegatedRevokePrepare : Body := multiDelegatedRevokeRead ++ [multiDelegatedRevokeCheck] ++
  multiDelegatedRevokeFields ++ multiDelegatedRevokeAllocate ++ [multiDelegatedRevokeGuard,multiDelegatedRevokeJInit]
def multiDelegatedRevokeIteration : Body := multiDelegatedRevokePrepare ++
  [.while (localArrayGuard "j" "data") multiDelegatedRevokeVerifyIteration] ++ multiDelegatedRevokeCall ++ multiDelegatedRevokeUpdate

theorem multiDelegatedRevoke_body : multiRevokeByDelegationTransition.body = easPayableEntryPrefix ++
    multiDelegatedRevokeInitial ++ [.while (localArrayGuard "i" "multiDelegatedRequests") multiDelegatedRevokeIteration] := by native_decide

def multiDelegatedRevokeFieldLocals (L : Store) (r : DelegatedRevocationBatch) : Store :=
  L.insert "data" (.array (r.data.map RevocationRequestRecord.tuple)) |>.insert "signatures" (.array (r.signatures.map SignatureRecord.tuple))

theorem multiDelegatedRevokeFieldsSource {L imms : Store} {evm : EVM.State} {r : DelegatedRevocationBatch}
    (hr : L.get? "multiDelegatedRequest" = some r.tuple) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedRevokeFields
      (.ok {contract := contract,locals := multiDelegatedRevokeFieldLocals L r,immutables := imms} evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl ?_) (ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil)
  · simp only [evalExpr?,hr,DelegatedRevocationBatch.tuple,EvalResult.ofOption,bind,EvalResult.bind,pure]
    rfl
  · simp (disch := decide) only [evalExpr?,store_get_ne,hr,DelegatedRevocationBatch.tuple,EvalResult.ofOption,bind,EvalResult.bind,pure]
    rfl

theorem multiDelegatedRevokeCheck_ok {L imms : Store} {evm : EVM.State} {r : DelegatedRevocationBatch}
    (hr : L.get? "multiDelegatedRequest" = some r.tuple) :
    ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedRevokeCheck
      (.ok {contract := contract,locals := L,immutables := imms} evm) := by
  apply ExecStmt.requireTrue
  simp only [evalExpr?,hr,EvalResult.ofOption,bind,EvalResult.bind,pure,evalStructFields?,multiDelegatedRevokeCheck]
  rfl

theorem multiDelegatedRevokeCheck_bad {L imms : Store} {evm : EVM.State}
    (hr : L.get? "multiDelegatedRequest" = some ABI.Solc08Calldata.decodeFailure) :
    ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedRevokeCheck .reverted := by
  apply ExecStmt.requireFalse
  simp only [evalExpr?,hr,EvalResult.ofOption,bind,EvalResult.bind,pure,evalStructFields?,multiDelegatedRevokeCheck]
  rfl

end Benchmarks.EAS.EAS
