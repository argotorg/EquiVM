import Benchmarks.EAS.EAS.TypedDataSource
import Benchmarks.EAS.EAS.HeapResultBlock

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

abbrev hashTypedFunction : FunctionDecl := contract.functions[27]!
def hashTypedPrefix : Body :=
  heapResultBlock "_domainSeparatorV4" [.var "$EAS.freeMemory"] "__c0$allocation" "__c0" "$EAS.freeMemory"
def hashTypedCallArgs : List Expr := [.var "__c0",.var "structHash",.var "$EAS.freeMemory"]
def hashTypedTail : Body :=
  heapResultBlock "ECDSA_toTypedDataHash" hashTypedCallArgs "__c1$allocation" "__c1" "$EAS.freeMemory" ++ [
    .return [.var "__c1",.var "$EAS.freeMemory"],.return [.tupleLit [],.var "$EAS.freeMemory"]]
theorem hashTyped_body : hashTypedFunction.body = hashTypedPrefix ++ hashTypedTail := by native_decide

theorem hashTypedTailSource {L imms : Store} {evm evm' : EVM.State} {result : Value} {heap : Nat} {oldHeap : Value}
    (hh : L.get? "$EAS.freeMemory" = some oldHeap)
    (hc : ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm
      (.internalCall "ECDSA_toTypedDataHash" hashTypedCallArgs "__c1$allocation")
      (.ok (resumeAfterInternalCall {contract := contract,locals := L,immutables := imms} "__c1$allocation"
        (some [result,.int (Int.ofNat heap)])) evm')) :
    ExecFuncBody fork config {contract := contract,locals := L,immutables := imms} evm hashTypedTail
      (.returned {contract := contract,locals := heapResultLocals L "__c1$allocation" "__c1" "$EAS.freeMemory" result heap,immutables := imms} evm' (some [result,.int (Int.ofNat heap)])) := by
  apply ExecFuncBody.execBlockRet
  apply execBlock_append (heapResultBlock_ok hc hh (by decide) (by decide) (by decide))
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp (disch := decide) only [evalExprs?,evalExpr?,heapResultLocals,unpackHeapLocals,
    store_get_ne,store_get_self,EvalResult.ofOption,EvalResult.bind,bind,pure]

def hashTypedArgs (structHash : UInt256) (heap : Nat) : Store :=
  (∅ : Store).insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "structHash" (wordBytes32Value structHash)
theorem hashTyped_lookup : lookupCallable? contract "_hashTypedDataV4" = some hashTypedFunction.toCallable := rfl
theorem hashTyped_bind (structHash : UInt256) (heap : Nat) :
    bindParams? hashTypedFunction.params [wordBytes32Value structHash,.int (Int.ofNat heap)] =
      some (hashTypedArgs structHash heap) := rfl

end Benchmarks.EAS.EAS
