import Benchmarks.EAS.EAS.GetUIDSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

structure AttestationRequestRecord where
  recipient : AccountAddress
  expirationTime : UInt256
  revocable : Bool
  refUID : UInt256
  data : ByteArray
  value : UInt256

def AttestationRequestRecord.tuple (r : AttestationRequestRecord) : Value := .tuple [
  .address r.recipient,.int (Int.ofNat r.expirationTime.toNat),.bool r.revocable,
  wordBytes32Value r.refUID,.bytes r.data,.int (Int.ofNat r.value.toNat)]
def AttestationRequestRecord.struct (r : AttestationRequestRecord) : Value := .struct "AttestationRequestData" [
  ("recipient",.address r.recipient),("expirationTime",.int (Int.ofNat r.expirationTime.toNat)),("revocable",.bool r.revocable),
  ("refUID",wordBytes32Value r.refUID),("data",.bytes r.data),("value",.int (Int.ofNat r.value.toNat))]

abbrev decodeAttestationDataFunction : FunctionDecl := contract.functions[4]!
def decodeAttestationDataExpr : Expr := .structLit "AttestationRequestData" [
  ("recipient",.tupleGet (.var "data") 0),("expirationTime",.tupleGet (.var "data") 1),
  ("revocable",.tupleGet (.var "data") 2),("refUID",.tupleGet (.var "data") 3),
  ("data",.tupleGet (.var "data") 4),("value",.tupleGet (.var "data") 5)]
theorem decodeAttestationData_body : decodeAttestationDataFunction.body = [
    .return [decodeAttestationDataExpr,.var "$EAS.freeMemory"],.return [.tupleLit [],.var "$EAS.freeMemory"]] := by native_decide

theorem decodeAttestationDataExpr_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {r : AttestationRequestRecord}
    (h : frame.locals.get? "data" = some r.tuple) :
    evalExpr? cfg frame evm decodeAttestationDataExpr = .ok r.struct := by
  simp only [decodeAttestationDataExpr,evalExpr?,evalStructFields?,h,EvalResult.ofOption,EvalResult.bind,bind,pure,
    AttestationRequestRecord.tuple,AttestationRequestRecord.struct]
  rfl

theorem decodeAttestationDataSource {cfg : Config} {frame : Frame} {evm : EVM.State} {r : AttestationRequestRecord} {heap : Nat}
    (hd : frame.locals.get? "data" = some r.tuple)
    (hh : frame.locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    ExecFuncBody fork cfg frame evm decodeAttestationDataFunction.body
      (.returned frame evm (some [r.struct,.int (Int.ofNat heap)])) := by
  rw [decodeAttestationData_body]
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?,decodeAttestationDataExpr_eval hd,EvalResult.bind,bind,pure]
  simp only [evalExpr?,hh,EvalResult.ofOption,EvalResult.bind,bind,pure]

def decodeAttestationDataArgs (r : AttestationRequestRecord) (heap : Nat) : Store :=
  (∅ : Store).insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "data" r.tuple
theorem decodeAttestationData_lookup : lookupCallable? contract "_decodeAttestationData" = some decodeAttestationDataFunction.toCallable := rfl
theorem decodeAttestationData_bind (r : AttestationRequestRecord) (heap : Nat) :
    bindParams? decodeAttestationDataFunction.params [r.tuple,.int (Int.ofNat heap)] = some (decodeAttestationDataArgs r heap) := rfl

theorem decodeAttestationDataCall {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {args : List Expr} {retVar : Ident} {r : AttestationRequestRecord} {heap : Nat}
    (he : evalExprs? cfg {contract := contract,locals := locals,immutables := imms} evm args =
      .ok [r.tuple,.int (Int.ofNat heap)]) :
    ExecStmt fork cfg {contract := contract,locals := locals,immutables := imms} evm
      (.internalCall "_decodeAttestationData" args retVar)
      (.ok (resumeAfterInternalCall {contract := contract,locals := locals,immutables := imms} retVar
        (some [r.struct,.int (Int.ofNat heap)])) evm) := by
  exact internalCallFunctionReturn he decodeAttestationData_lookup (decodeAttestationData_bind r heap)
    (decodeAttestationDataSource (by simp only [decodeAttestationDataArgs,store_get_self])
      (by simp only [decodeAttestationDataArgs,store_get_ne _ _ (by decide : ("data" == "$EAS.freeMemory") = false),store_get_self]))

end Benchmarks.EAS.EAS
