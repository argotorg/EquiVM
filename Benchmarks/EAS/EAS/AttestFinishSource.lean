import Benchmarks.EAS.EAS.AttestLoopLocals
import Benchmarks.EAS.EAS.AttestIterationSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def attestResolveArgs : List Expr := [.var "schemaRecord",.var "attestations",.var "values",
  .boolLit false,.var "availableValue",.var "last",.var "$EAS.freeMemory"]
def attestResolveBlock : Body := heapResultBlock "_resolveAttestations" attestResolveArgs
  "__c5$allocation" "__c5" "$EAS.freeMemory"
def attestFinishBody : Body := attestResolveBlock ++ [
  .assign .localVar {base := "res",steps := [.field "usedValue"]} (.var "__c5"),
  .return [.var "res",.var "$EAS.freeMemory"],
  .return [.tupleLit [],.var "$EAS.freeMemory"]]

theorem attestFinishBody_eq : attestFunction.body.drop 27 = attestFinishBody := by native_decide

def attestFinishLocals (L : Store) (uids : List UInt256) (used : UInt256) (heap : Nat) : Store :=
  (heapResultLocals L "__c5$allocation" "__c5" "$EAS.freeMemory" (.int (Int.ofNat used.toNat)) heap).insert
    "res" (attestationsResultValue uids used)

theorem attestFinishSource {L imms : Store} {evm evm' : EVM.State} {old heap : Nat}
    {uids : List UInt256} {oldUsed used : UInt256}
    (hr : L.get? "res" = some (attestationsResultValue uids oldUsed))
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat old)))
    (hc : ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm
      (.internalCall "_resolveAttestations" attestResolveArgs "__c5$allocation")
      (.ok (resumeAfterInternalCall {contract := contract,locals := L,immutables := imms} "__c5$allocation"
        (some [.int (Int.ofNat used.toNat),.int (Int.ofNat heap)])) evm')) :
    ExecFuncBody fork config {contract := contract,locals := L,immutables := imms} evm attestFinishBody
      (.returned {contract := contract,locals := attestFinishLocals L uids used heap,immutables := imms} evm'
        (some [attestationsResultValue uids used,.int (Int.ofNat heap)])) := by
  have hcall := heapResultBlock_ok (result := "__c5") hc hh (by decide) (by decide) (by decide)
  apply execFuncBody_append hcall
  apply ExecFuncBody.execBlockRet
  let L1 := heapResultLocals L "__c5$allocation" "__c5" "$EAS.freeMemory" (.int (Int.ofNat used.toNat)) heap
  have hr1 : L1.get? "res" = some (attestationsResultValue uids oldUsed) :=
    (heapResultLocals_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans hr
  have hv1 : L1.get? "__c5" = some (.int (Int.ofNat used.toNat)) := heapResultLocals_result _ _ _ _ _ _ (by decide)
  have hh1 : L1.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) := heapResultLocals_heap _ _ _ _ _ _
  change ExecBlock fork config {contract := contract,locals := L1,immutables := imms} evm' _
    (.returned {contract := contract,locals := L1.insert "res" (attestationsResultValue uids used),immutables := imms}
      evm' (some [attestationsResultValue uids used,.int (Int.ofNat heap)]))
  refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (value := .int (Int.ofNat used.toNat))
    (stele' := {contract := contract,locals := L1.insert "res" (attestationsResultValue uids used),immutables := imms})
    (evm' := evm')
    (by simp only [evalExpr?,hv1,EvalResult.ofOption]) ?_) ?_
  · simp only [assignStorageRef?,hr1,updateLocalPath?,attestationsResultValue,lookupField?,
      EvalResult.ofOption,EvalResult.bind,bind,pure]
    rfl
  · apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp only [evalExprs?,evalExpr?,store_get_self,store_get_ne _ _ (by decide : ("res" == "$EAS.freeMemory") = false),
      hh1,EvalResult.ofOption,EvalResult.bind,bind,pure]

end Benchmarks.EAS.EAS
