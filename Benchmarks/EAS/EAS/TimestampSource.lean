import Benchmarks.EAS.EAS.WordExpr
import Benchmarks.EAS.EAS.Time
import Benchmarks.EAS.EAS.LowPacked

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def timestampStore (evm : EVM.State) (word time : UInt256) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner (timestampSlot word)
    (setLowWord (EVM.storageLoad evm evm.executionEnv.codeOwner (timestampSlot word)) time 64)

theorem timestamp_write {evm : EVM.State} {locals imms : Store} {word time : UInt256}
    (hnone : locals.get? "_timestamps" = none)
    (hkey : locals.get? "data" = some (wordBytes32Value word)) :
    assignStorageRef? config {contract := contract, locals := locals, immutables := imms} evm
      .storage timestampRef (.int (Int.ofNat time.toNat)) =
      .ok ({contract := contract, locals := locals, immutables := imms}, timestampStore evm word time) := by
  exact assignStorageRef_storage_scalar_value (loc := timestampLoc word)
    (ty := .elem (.int (.uint ⟨64, by decide⟩))) hnone (timestamp_evalRef hkey) rfl easStorageBackend
    (timestamp_layout word) (Or.inl ⟨_, rfl⟩)
    (storageLocStore_uint_offset0_word evm (timestampSlot word) time 8 ⟨64, by decide⟩ rfl (by decide))


abbrev timestampFunction : FunctionDecl := contract.functions[20]!

def timestampGuard : Expr := .binary .eq (.storage timestampRef) (.intLit 0)

theorem timestamp_body : timestampFunction.body = [
    .require timestampGuard, .assign .storage timestampRef (.var "time"),
    .emit "Timestamped" [.var "data", .var "time"], .return [.tupleLit [], .var "$EAS.freeMemory"]] := by native_decide

theorem timestampSource_ok {evm : EVM.State} {locals imms : Store} {word time : UInt256} {heap : Nat}
    (hnone : locals.get? "_timestamps" = none)
    (hkey : locals.get? "data" = some (wordBytes32Value word))
    (ht : locals.get? "time" = some (.int (Int.ofNat time.toNat)))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hz : timestampWord evm word = ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    ExecFuncBody fork config {contract := contract, locals := locals, immutables := imms} evm timestampFunction.body
      (.returned {contract := contract, locals := locals, immutables := imms} (timestampStore evm word time)
        (some [.tuple [], .int (Int.ofNat heap)])) := by
  rw [timestamp_body]
  apply ExecFuncBody.execBlockRet
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [timestampGuard, hz, decide_true] using evalWordEqZero (timestamp_read (evm := evm) (imms := imms) hnone hkey)
  refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := Or.inr hperm) (value := .int (Int.ofNat time.toNat))
    (by simp only [evalExpr?, ht, EvalResult.ofOption]) (timestamp_write (time := time) hnone hkey)) ?_
  refine ExecBlock.consNormal (ExecStmt.emit (fork := fork) (hperm := by simpa only [timestampStore, storageStore_executionEnv] using hperm) (vals := [wordBytes32Value word, .int (Int.ofNat time.toNat)]) ?_) ?_
  · simp only [evalExprs?, evalExpr?, hkey, ht, EvalResult.ofOption, EvalResult.bind, bind, pure]
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?, evalExpr?, evalExprList?, hh, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem timestampSource_revert {evm : EVM.State} {locals imms : Store} {word : UInt256}
    (hnone : locals.get? "_timestamps" = none)
    (hkey : locals.get? "data" = some (wordBytes32Value word))
    (hz : timestampWord evm word ≠ ⟨0⟩) :
    ExecFuncBody fork config {contract := contract, locals := locals, immutables := imms} evm timestampFunction.body .reverted := by
  rw [timestamp_body]
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [timestampGuard, hz, decide_false] using evalWordEqZero (timestamp_read (evm := evm) (imms := imms) hnone hkey)

theorem timestampSource_static {evm : EVM.State} {locals imms : Store} {word time : UInt256}
    (hnone : locals.get? "_timestamps" = none)
    (hkey : locals.get? "data" = some (wordBytes32Value word))
    (ht : locals.get? "time" = some (.int (Int.ofNat time.toNat)))
    (hz : timestampWord evm word = ⟨0⟩) (hp : evm.executionEnv.perm = false) :
    ExecFuncBody fork config {contract := contract, locals := locals, immutables := imms} evm timestampFunction.body .staticViolation := by
  rw [timestamp_body]
  apply ExecFuncBody.execBlockStatic
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [timestampGuard, hz, decide_true] using evalWordEqZero (timestamp_read (evm := evm) (imms := imms) hnone hkey)
  apply ExecBlock.consStatic
  exact ExecStmt.assignStatic (by simp only [evalExpr?, ht, EvalResult.ofOption]) (timestamp_write (time := time) hnone hkey) hp


def timestampArgs (word time : UInt256) (heap : Nat) : Store :=
  (∅ : Store) |>.insert "$EAS.freeMemory" (.int (Int.ofNat heap))
    |>.insert "time" (.int (Int.ofNat time.toNat)) |>.insert "data" (wordBytes32Value word)

theorem timestampArgs_facts (word time : UInt256) (heap : Nat) :
    (timestampArgs word time heap).get? "_timestamps" = none ∧
    (timestampArgs word time heap).get? "data" = some (wordBytes32Value word) ∧
    (timestampArgs word time heap).get? "time" = some (.int (Int.ofNat time.toNat)) ∧
    (timestampArgs word time heap).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) := by
  simp only [timestampArgs,
    store_get_ne _ _ (by decide : ("data" == "_timestamps") = false),
    store_get_ne _ _ (by decide : ("time" == "_timestamps") = false),
    store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "_timestamps") = false),
    store_get_ne _ _ (by decide : ("data" == "time") = false),
    store_get_ne _ _ (by decide : ("data" == "$EAS.freeMemory") = false),
    store_get_ne _ _ (by decide : ("time" == "$EAS.freeMemory") = false),
    store_get_self, store_get_empty, and_self]

theorem timestamp_lookup : lookupCallable? contract "_timestamp" = some timestampFunction.toCallable := by rfl

theorem timestamp_bind (word time : UInt256) (heap : Nat) :
    bindParams? timestampFunction.params [wordBytes32Value word, .int (Int.ofNat time.toNat), .int (Int.ofNat heap)] =
      some (timestampArgs word time heap) := by rfl

theorem timestampCall_ok {locals imms : Store} {evm : EVM.State}
    {args : List Expr} {word time : UInt256} {heap : Nat} {retVar : Ident}
    (hargs : evalExprs? config {contract := contract, locals := locals, immutables := imms} evm args =
      .ok [wordBytes32Value word, .int (Int.ofNat time.toNat), .int (Int.ofNat heap)])
    (hz : timestampWord evm word = ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm
      (.internalCall "_timestamp" args retVar)
      (.ok {contract := contract, locals := locals.insert retVar (.tuple [.tuple [], .int (Int.ofNat heap)]), immutables := imms}
        (timestampStore evm word time)) := by
  have hf := timestampArgs_facts word time heap
  exact internalCallFunctionReturn hargs timestamp_lookup (timestamp_bind word time heap)
    (timestampSource_ok (fork := fork) (hperm := by assumption) hf.1 hf.2.1 hf.2.2.1 hf.2.2.2 hz)

theorem timestampCall_revert {locals imms : Store} {evm : EVM.State}
    {args : List Expr} {word time : UInt256} {heap : Nat} {retVar : Ident}
    (hargs : evalExprs? config {contract := contract, locals := locals, immutables := imms} evm args =
      .ok [wordBytes32Value word, .int (Int.ofNat time.toNat), .int (Int.ofNat heap)])
    (hz : timestampWord evm word ≠ ⟨0⟩) :
    ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm
      (.internalCall "_timestamp" args retVar) .reverted := by
  have hf := timestampArgs_facts word time heap
  exact internalCallFunctionRevert hargs timestamp_lookup (timestamp_bind word time heap)
    (timestampSource_revert hf.1 hf.2.1 hz)

-- GENERALIZES Reasoning.SteleBody.internalCallFunctionRevert: propagate a callee's static violation.
theorem internalCallFunctionStatic {cfg : Config} {caller : Frame} {evm : EVM.State}
    {name retVar : Ident} {args : List Expr} {argVals : List Value}
    {callee : FunctionDecl} {locals : Store}
    (hargs : evalExprs? cfg caller evm args = .ok argVals)
    (hlookup : lookupCallable? caller.contract name = some callee.toCallable)
    (hbind : bindParams? callee.params argVals = some locals)
    (hbody : ExecFuncBody fork cfg {caller with locals := locals} evm callee.body .staticViolation) :
    ExecStmt fork cfg caller evm (.internalCall name args retVar) .staticViolation := by
  exact ExecStmt.internalCallStatic hargs hlookup hbind hbody

theorem timestampCall_static {locals imms : Store} {evm : EVM.State}
    {args : List Expr} {word time : UInt256} {heap : Nat} {retVar : Ident}
    (hargs : evalExprs? config {contract := contract, locals := locals, immutables := imms} evm args =
      .ok [wordBytes32Value word, .int (Int.ofNat time.toNat), .int (Int.ofNat heap)])
    (hz : timestampWord evm word = ⟨0⟩) (hp : evm.executionEnv.perm = false) :
    ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm
      (.internalCall "_timestamp" args retVar) .staticViolation := by
  have hf := timestampArgs_facts word time heap
  exact internalCallFunctionStatic hargs timestamp_lookup (timestamp_bind word time heap)
    (timestampSource_static hf.1 hf.2.1 hf.2.2.1 hz hp)

end Benchmarks.EAS.EAS
