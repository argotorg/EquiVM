import Benchmarks.EAS.EAS.AttestationRequest

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

structure RevocationRequestRecord where
  uid : UInt256
  value : UInt256

def RevocationRequestRecord.tuple (r : RevocationRequestRecord) : Value :=
  .tuple [wordBytes32Value r.uid,.int (Int.ofNat r.value.toNat)]
def RevocationRequestRecord.struct (r : RevocationRequestRecord) : Value :=
  .struct "RevocationRequestData" [("uid",wordBytes32Value r.uid),("value",.int (Int.ofNat r.value.toNat))]

abbrev decodeRevocationDataFunction : FunctionDecl := contract.functions[5]!
def decodeRevocationDataExpr : Expr := .structLit "RevocationRequestData"
  [("uid",.tupleGet (.var "data") 0),("value",.tupleGet (.var "data") 1)]
theorem decodeRevocationData_body : decodeRevocationDataFunction.body = [
    .return [decodeRevocationDataExpr,.var "$EAS.freeMemory"],.return [.tupleLit [],.var "$EAS.freeMemory"]] := by native_decide

theorem decodeRevocationDataExpr_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {r : RevocationRequestRecord}
    (h : frame.locals.get? "data" = some r.tuple) :
    evalExpr? cfg frame evm decodeRevocationDataExpr = .ok r.struct := by
  simp only [decodeRevocationDataExpr,evalExpr?,evalStructFields?,h,EvalResult.ofOption,EvalResult.bind,bind,pure,
    RevocationRequestRecord.tuple,RevocationRequestRecord.struct]
  rfl

theorem decodeRevocationDataSource {cfg : Config} {frame : Frame} {evm : EVM.State} {r : RevocationRequestRecord} {heap : Nat}
    (hd : frame.locals.get? "data" = some r.tuple)
    (hh : frame.locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    ExecFuncBody fork cfg frame evm decodeRevocationDataFunction.body
      (.returned frame evm (some [r.struct,.int (Int.ofNat heap)])) := by
  rw [decodeRevocationData_body]
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?,decodeRevocationDataExpr_eval hd,EvalResult.bind,bind,pure]
  simp only [evalExpr?,hh,EvalResult.ofOption,EvalResult.bind,bind,pure]

def decodeRevocationDataArgs (r : RevocationRequestRecord) (heap : Nat) : Store :=
  (∅ : Store).insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "data" r.tuple
theorem decodeRevocationData_lookup : lookupCallable? contract "_decodeRevocationData" = some decodeRevocationDataFunction.toCallable := rfl
theorem decodeRevocationData_bind (r : RevocationRequestRecord) (heap : Nat) :
    bindParams? decodeRevocationDataFunction.params [r.tuple,.int (Int.ofNat heap)] = some (decodeRevocationDataArgs r heap) := rfl

theorem decodeRevocationDataCall {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {args : List Expr} {retVar : Ident} {r : RevocationRequestRecord} {heap : Nat}
    (he : evalExprs? cfg {contract := contract,locals := locals,immutables := imms} evm args =
      .ok [r.tuple,.int (Int.ofNat heap)]) :
    ExecStmt fork cfg {contract := contract,locals := locals,immutables := imms} evm
      (.internalCall "_decodeRevocationData" args retVar)
      (.ok (resumeAfterInternalCall {contract := contract,locals := locals,immutables := imms} retVar
        (some [r.struct,.int (Int.ofNat heap)])) evm) := by
  exact internalCallFunctionReturn he decodeRevocationData_lookup (decodeRevocationData_bind r heap)
    (decodeRevocationDataSource (by simp only [decodeRevocationDataArgs,store_get_self])
      (by simp only [decodeRevocationDataArgs,store_get_ne _ _ (by decide : ("data" == "$EAS.freeMemory") = false),store_get_self]))

end Benchmarks.EAS.EAS
