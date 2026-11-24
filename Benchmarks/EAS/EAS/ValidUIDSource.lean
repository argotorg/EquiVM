import Benchmarks.EAS.EAS.AttestationRequest
import Benchmarks.EAS.EAS.Storage

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

abbrev validUIDFunction : FunctionDecl := contract.functions[25]!
def validUIDArgs (word : UInt256) (heap : Nat) : Store :=
  (∅ : Store).insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "uid" (wordBytes32Value word)

theorem validUID_body : validUIDFunction.body = [
    .return [attestationValidExpr,.var "$EAS.freeMemory"],.return [.tupleLit [],.var "$EAS.freeMemory"]] := by native_decide

theorem validUID_lookup : lookupCallable? contract "isAttestationValid_body" = some validUIDFunction.toCallable := rfl
theorem validUID_bind (word : UInt256) (heap : Nat) :
    bindParams? validUIDFunction.params [wordBytes32Value word,.int (Int.ofNat heap)] = some (validUIDArgs word heap) := rfl

theorem validUIDSource (imms : Store) (evm : EVM.State) (word : UInt256) (heap : Nat) :
    ExecFuncBody fork config {contract := contract,locals := validUIDArgs word heap,immutables := imms} evm validUIDFunction.body
      (.returned {contract := contract,locals := validUIDArgs word heap,immutables := imms} evm
        (some [.bool (decide (dbUIDWord evm word ≠ ⟨0⟩)),.int (Int.ofNat heap)])) := by
  rw [validUID_body]
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn
  apply ExecStmt.return
  have hv := attestationValid_eval (evm := evm) (imms := imms) (word := word)
    (locals := validUIDArgs word heap)
    (by simp only [validUIDArgs,store_get_ne _ _ (by decide : ("uid" == "_db") = false),
      store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "_db") = false),store_get_empty])
    (by simp only [validUIDArgs,store_get_self])
  simp only [evalExprs?,hv,EvalResult.bind,bind,pure]
  simp only [evalExpr?,validUIDArgs,store_get_ne _ _ (by decide : ("uid" == "$EAS.freeMemory") = false),
    store_get_self,EvalResult.ofOption,EvalResult.bind,bind,pure]

theorem validUIDCall {L imms : Store} {evm : EVM.State} {args : List Expr} {retVar : Ident} {word : UInt256} {heap : Nat}
    (he : evalExprs? config {contract := contract,locals := L,immutables := imms} evm args =
      .ok [wordBytes32Value word,.int (Int.ofNat heap)]) :
    ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm
      (.internalCall "isAttestationValid_body" args retVar)
      (.ok (resumeAfterInternalCall {contract := contract,locals := L,immutables := imms} retVar
        (some [.bool (decide (dbUIDWord evm word ≠ ⟨0⟩)),.int (Int.ofNat heap)])) evm) :=
  internalCallFunctionReturn he validUID_lookup (validUID_bind word heap) (validUIDSource imms evm word heap)

end Benchmarks.EAS.EAS
