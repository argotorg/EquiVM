import Benchmarks.EAS.EAS.TimeArray

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def timeArrayInit : Body := [
  .letDecl "length" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.arrayLength .localVar {base := "data"}),
  .letDecl "i" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0)]

def timeArrayPrefix : Body := (easEntryPrefix ++ timeEntryCall) ++ timeArrayInit

def timeArrayLocals (locals : Store) (ee : ExecutionEnv) (words : List UInt256) : Store :=
  ((timeEntryLocals locals ee).insert "length" (.int (Int.ofNat words.length))).insert "i" (.int 0)

theorem timeArrayPrefixSource {evm : EVM.State} {locals imms : Store} {words : List UInt256}
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hsz : 4 ≤ evm.executionEnv.calldata.size)
    (hsize : evm.executionEnv.calldata.size < UInt256.size) (hs : evm.executionEnv.calldata.size - 4 < 2^255)
    (hd : locals.get? "data" = some (.array (words.map wordBytes32Value))) :
    ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm timeArrayPrefix
      (.ok {contract := contract, locals := timeArrayLocals locals evm.executionEnv words, immutables := imms} evm) := by
  apply execBlock_append (timeEntrySource hv hsz hsize hs)
  have hd' : (timeEntryLocals locals evm.executionEnv).get? "data" = some (.array (words.map wordBytes32Value)) := by
    simpa [timeEntryLocals, unpackHeapLocals, easEntryLocals, Std.HashMap.getElem?_insert] using hd
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int (Int.ofNat words.length)) ?_) ?_
  · simp only [evalExpr?, hd', readLocalPath?, EvalResult.bind, bind, List.length_map, pure]
    rfl
  · exact ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ExecBlock.nil

theorem timeArrayInitialInv {locals : Store} {ee : ExecutionEnv} {words : List UInt256}
    (hd : locals.get? "data" = some (.array (words.map wordBytes32Value))) :
    TimeArrayInv (timeArrayLocals locals ee words) words (easTimeWord ee) 224 0 := by
  constructor
  · simpa [timeArrayLocals, timeEntryLocals, unpackHeapLocals, easEntryLocals, Std.HashMap.getElem?_insert] using hd
  · simp only [timeArrayLocals, store_get_ne _ _ (by decide : ("i" == "length") = false), store_get_self]
  · simpa [timeArrayLocals, Std.HashMap.getElem?_insert] using timeEntry_time locals ee
  · simp only [timeArrayLocals,
      store_get_ne _ _ (by decide : ("i" == "$EAS.freeMemory") = false),
      store_get_ne _ _ (by decide : ("length" == "$EAS.freeMemory") = false), timeEntryLocals, unpackHeapLocals, store_get_self]
  · exact store_get_self _ _ _

end Benchmarks.EAS.EAS
