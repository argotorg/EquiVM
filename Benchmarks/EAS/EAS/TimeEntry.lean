import Benchmarks.EAS.EAS.Time

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def timeEntryCall : Body := [
  .internalCall "_time" [.var "$EAS.freeMemory"] "time$allocation",
  .letDecl "time" none (.tupleGet (.var "time$allocation") 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "time$allocation") 1)]

def timeEntryLocals (locals : Store) (ee : ExecutionEnv) : Store :=
  unpackHeapLocals ((easEntryLocals locals ee.calldata).insert "time$allocation"
    (.tuple [.int (Int.ofNat (easTimeWord ee).toNat), .int 224])) "time" "$EAS.freeMemory"
    (.int (Int.ofNat (easTimeWord ee).toNat)) 224

theorem timeEntrySource {evm : EVM.State} {locals imms : Store}
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz : 4 ≤ evm.executionEnv.calldata.size)
    (hsize : evm.executionEnv.calldata.size < UInt256.size)
    (hs : evm.executionEnv.calldata.size - 4 < 2^255) :
    ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm
      (easEntryPrefix ++ timeEntryCall)
      (.ok {contract := contract, locals := timeEntryLocals locals evm.executionEnv, immutables := imms} evm) := by
  apply execBlock_append (easEntryPrefix_ok hv hsz hsize hs)
  have hh : (easEntryLocals locals evm.executionEnv.calldata).get? "$EAS.freeMemory" = some (.int (Int.ofNat (224 : Nat))) := by
    simp only [easEntryLocals, store_get_ne _ _ (by decide : ("__calldata" == "$EAS.freeMemory") = false), store_get_self]
    rfl
  refine ExecBlock.consNormal (timeCall (heap := 224) ?_) ?_
  · simp only [evalExpr?, hh, EvalResult.ofOption]
  exact unpackHeapResult (store_get_self _ _ _)
    (by simpa only [store_get_ne _ _ (by decide : ("time$allocation" == "$EAS.freeMemory") = false)] using hh)
    (by decide) (by decide)

theorem timeEntry_time (locals : Store) (ee : ExecutionEnv) :
    (timeEntryLocals locals ee).get? "time" = some (.int (Int.ofNat (easTimeWord ee).toNat)) := by
  simp only [timeEntryLocals, unpackHeapLocals,
    store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "time") = false), store_get_self]

end Benchmarks.EAS.EAS
