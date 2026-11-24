import Benchmarks.EAS.EAS.TimeEntry

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem timeEntry_data (locals : Store) (ee : ExecutionEnv) :
    (timeEntryLocals locals ee).get? "data" = locals.get? "data" := by
  simp only [timeEntryLocals, unpackHeapLocals, easEntryLocals,
    store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "data") = false),
    store_get_ne _ _ (by decide : ("time" == "data") = false),
    store_get_ne _ _ (by decide : ("time$allocation" == "data") = false),
    store_get_ne _ _ (by decide : ("__calldata" == "data") = false)]

def timePublicFinalLocals (locals : Store) (ee : ExecutionEnv) : Store :=
  unpackHeapLocals ((timeEntryLocals locals ee).insert "__c1$allocation" (.tuple [.tuple [], .int 224]))
    "__c1" "$EAS.freeMemory" (.tuple []) 224

/-- Finish either single-word time entry after its state-changing internal call. -/
theorem timePublicFinish {evm evm' : EVM.State} {locals imms : Store} {stmt : Stmt}
    (hcall : ExecStmt fork config {contract := contract, locals := timeEntryLocals locals evm.executionEnv, immutables := imms}
      evm stmt (.ok {
        contract := contract
        locals := (timeEntryLocals locals evm.executionEnv).insert "__c1$allocation" (.tuple [.tuple [], .int 224])
        immutables := imms} evm')) :
    ExecBlock fork config {contract := contract, locals := timeEntryLocals locals evm.executionEnv, immutables := imms} evm
      [stmt, .letDecl "__c1" none (.tupleGet (.var "__c1$allocation") 0),
        .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "__c1$allocation") 1), .return [.var "time"]]
      (.returned {contract := contract, locals := timePublicFinalLocals locals evm.executionEnv, immutables := imms}
        evm' (some [.int (Int.ofNat (easTimeWord evm.executionEnv).toNat)])) := by
  apply ExecBlock.consNormal hcall
  have hh : (timeEntryLocals locals evm.executionEnv).get? "$EAS.freeMemory" = some (.int (Int.ofNat (224 : Nat))) :=
    store_get_self _ _ _
  have hunpack := unpackHeapResult (fork := fork) (cfg := config) (evm := evm')
    (frame := {
      contract := contract
      locals := (timeEntryLocals locals evm.executionEnv).insert "__c1$allocation" (.tuple [.tuple [], .int 224])
      immutables := imms}) (result := "__c1") (cursor := "$EAS.freeMemory") (old := .int 224)
    (store_get_self _ _ _)
    (by simpa only [store_get_ne _ _ (by decide : ("__c1$allocation" == "$EAS.freeMemory") = false)] using hh)
    (by decide) (by decide)
  apply execBlock_append hunpack
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [unpackHeapLocals, evalExprs?, evalExpr?,
    store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "time") = false),
    store_get_ne _ _ (by decide : ("__c1" == "time") = false),
    store_get_ne _ _ (by decide : ("__c1$allocation" == "time") = false), timeEntry_time,
    EvalResult.ofOption, EvalResult.bind, bind, pure]

end Benchmarks.EAS.EAS
