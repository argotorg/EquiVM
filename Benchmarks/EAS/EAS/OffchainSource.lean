import Benchmarks.EAS.EAS.OffchainStorage
import Benchmarks.EAS.EAS.TimestampSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

abbrev offchainFunction : FunctionDecl := contract.functions[21]!
def offchainGuard : Expr := .binary .eq (.storage offchainAliasRef) (.intLit 0)
def offchainLocals (locals : Store) (revoker : AccountAddress) : Store :=
  locals.insert "revocations" (.storageRef (offchainAliasRoot revoker) offchainAliasType)

theorem offchain_body : offchainFunction.body = [
    .letStorage "revocations" offchainRootRef,
    .require offchainGuard, .assign .storage offchainAliasRef (.var "time"),
    .emit "RevokedOffchain" [.var "revoker", .var "data", .var "time"],
    .return [.tupleLit [], .var "$EAS.freeMemory"]] := by native_decide

theorem offchainLocals_get {locals : Store} {revoker : AccountAddress} {name : Ident}
    (hne : ("revocations" == name) = false) :
    (offchainLocals locals revoker).get? name = locals.get? name := store_get_ne _ _ hne

theorem offchainSource_ok {evm : EVM.State} {locals imms : Store} {revoker : AccountAddress} {word time : UInt256} {heap : Nat}
    (hnone : locals.get? "_revocationsOffchain" = none)
    (hwho : locals.get? "revoker" = some (.address revoker))
    (hkey : locals.get? "data" = some (wordBytes32Value word))
    (ht : locals.get? "time" = some (.int (Int.ofNat time.toNat)))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hz : offchainWord evm revoker word = ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    ExecFuncBody fork config {contract := contract, locals := locals, immutables := imms} evm offchainFunction.body
      (.returned {contract := contract, locals := offchainLocals locals revoker, immutables := imms}
        (offchainStore evm revoker word time) (some [.tuple [], .int (Int.ofNat heap)])) := by
  have ha : (offchainLocals locals revoker).get? "revocations" =
      some (.storageRef (offchainAliasRoot revoker) offchainAliasType) := store_get_self _ _ _
  have hw := (offchainLocals_get (locals := locals) (revoker := revoker) (by decide : ("revocations" == "revoker") = false)).trans hwho
  have hk := (offchainLocals_get (locals := locals) (revoker := revoker) (by decide : ("revocations" == "data") = false)).trans hkey
  have htt := (offchainLocals_get (locals := locals) (revoker := revoker) (by decide : ("revocations" == "time") = false)).trans ht
  have hhh := (offchainLocals_get (locals := locals) (revoker := revoker) (by decide : ("revocations" == "$EAS.freeMemory") = false)).trans hh
  dsimp only [offchainLocals] at hw hk htt hhh
  rw [offchain_body]
  apply ExecFuncBody.execBlockRet
  refine ExecBlock.consNormal (ExecStmt.letStorage (offchain_root_resolve hnone hwho)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [offchainGuard, hz, decide_true] using evalWordEqZero (offchain_alias_read (evm := evm) (imms := imms) ha hk)
  refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := Or.inr hperm) (value := .int (Int.ofNat time.toNat))
    (by simp only [evalExpr?, htt, EvalResult.ofOption]) (offchain_alias_write (time := time) ha hk)) ?_
  refine ExecBlock.consNormal (ExecStmt.emit (fork := fork) (hperm := by simpa only [offchainStore, storageStore_executionEnv] using hperm) (vals := [.address revoker, wordBytes32Value word, .int (Int.ofNat time.toNat)]) ?_) ?_
  · simp only [evalExprs?, evalExpr?, hw, hk, htt, EvalResult.ofOption, EvalResult.bind, bind, pure]
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?, evalExpr?, evalExprList?, hhh, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem offchainSource_revert {evm : EVM.State} {locals imms : Store} {revoker : AccountAddress} {word : UInt256}
    (hnone : locals.get? "_revocationsOffchain" = none)
    (hwho : locals.get? "revoker" = some (.address revoker))
    (hkey : locals.get? "data" = some (wordBytes32Value word))
    (hz : offchainWord evm revoker word ≠ ⟨0⟩) :
    ExecFuncBody fork config {contract := contract, locals := locals, immutables := imms} evm offchainFunction.body .reverted := by
  have ha : (offchainLocals locals revoker).get? "revocations" =
      some (.storageRef (offchainAliasRoot revoker) offchainAliasType) := store_get_self _ _ _
  have hk := (offchainLocals_get (locals := locals) (revoker := revoker) (by decide : ("revocations" == "data") = false)).trans hkey
  rw [offchain_body]
  apply ExecFuncBody.execBlockRevert
  refine ExecBlock.consNormal (ExecStmt.letStorage (offchain_root_resolve hnone hwho)) ?_
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [offchainGuard, hz, decide_false] using evalWordEqZero (offchain_alias_read (evm := evm) (imms := imms) ha hk)

theorem offchainSource_static {evm : EVM.State} {locals imms : Store} {revoker : AccountAddress} {word time : UInt256}
    (hnone : locals.get? "_revocationsOffchain" = none)
    (hwho : locals.get? "revoker" = some (.address revoker))
    (hkey : locals.get? "data" = some (wordBytes32Value word))
    (ht : locals.get? "time" = some (.int (Int.ofNat time.toNat)))
    (hz : offchainWord evm revoker word = ⟨0⟩) (hp : evm.executionEnv.perm = false) :
    ExecFuncBody fork config {contract := contract, locals := locals, immutables := imms} evm offchainFunction.body .staticViolation := by
  have ha : (offchainLocals locals revoker).get? "revocations" =
      some (.storageRef (offchainAliasRoot revoker) offchainAliasType) := store_get_self _ _ _
  have hk := (offchainLocals_get (locals := locals) (revoker := revoker) (by decide : ("revocations" == "data") = false)).trans hkey
  have htt := (offchainLocals_get (locals := locals) (revoker := revoker) (by decide : ("revocations" == "time") = false)).trans ht
  dsimp only [offchainLocals] at htt
  rw [offchain_body]
  apply ExecFuncBody.execBlockStatic
  refine ExecBlock.consNormal (ExecStmt.letStorage (offchain_root_resolve hnone hwho)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [offchainGuard, hz, decide_true] using evalWordEqZero (offchain_alias_read (evm := evm) (imms := imms) ha hk)
  apply ExecBlock.consStatic
  exact ExecStmt.assignStatic (by simp only [evalExpr?, htt, EvalResult.ofOption]) (offchain_alias_write (time := time) ha hk) hp

def offchainArgs (revoker : AccountAddress) (word time : UInt256) (heap : Nat) : Store :=
  (∅ : Store) |>.insert "$EAS.freeMemory" (.int (Int.ofNat heap))
    |>.insert "time" (.int (Int.ofNat time.toNat)) |>.insert "data" (wordBytes32Value word)
    |>.insert "revoker" (.address revoker)

theorem offchainArgs_facts (revoker : AccountAddress) (word time : UInt256) (heap : Nat) :
    (offchainArgs revoker word time heap).get? "_revocationsOffchain" = none ∧
    (offchainArgs revoker word time heap).get? "revoker" = some (.address revoker) ∧
    (offchainArgs revoker word time heap).get? "data" = some (wordBytes32Value word) ∧
    (offchainArgs revoker word time heap).get? "time" = some (.int (Int.ofNat time.toNat)) ∧
    (offchainArgs revoker word time heap).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) := by
  simp only [offchainArgs,
    store_get_ne _ _ (by decide : ("revoker" == "data") = false),
    store_get_ne _ _ (by decide : ("revoker" == "time") = false),
    store_get_ne _ _ (by decide : ("revoker" == "$EAS.freeMemory") = false),
    store_get_ne _ _ (by decide : ("revoker" == "_revocationsOffchain") = false),
    store_get_ne _ _ (by decide : ("data" == "revoker") = false),
    store_get_ne _ _ (by decide : ("data" == "time") = false),
    store_get_ne _ _ (by decide : ("data" == "$EAS.freeMemory") = false),
    store_get_ne _ _ (by decide : ("data" == "_revocationsOffchain") = false),
    store_get_ne _ _ (by decide : ("time" == "revoker") = false),
    store_get_ne _ _ (by decide : ("time" == "data") = false),
    store_get_ne _ _ (by decide : ("time" == "$EAS.freeMemory") = false),
    store_get_ne _ _ (by decide : ("time" == "_revocationsOffchain") = false),
    store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "revoker") = false),
    store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "data") = false),
    store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "time") = false),
    store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "_revocationsOffchain") = false),
    store_get_self,
    store_get_empty,
    and_self]

theorem offchain_lookup : lookupCallable? contract "_revokeOffchain" = some offchainFunction.toCallable := by rfl

theorem offchain_bind (revoker : AccountAddress) (word time : UInt256) (heap : Nat) :
    bindParams? offchainFunction.params [.address revoker, wordBytes32Value word, .int (Int.ofNat time.toNat), .int (Int.ofNat heap)] =
      some (offchainArgs revoker word time heap) := by rfl

theorem offchainCall_ok {locals imms : Store} {evm : EVM.State}
    {args : List Expr} {revoker : AccountAddress} {word time : UInt256} {heap : Nat} {retVar : Ident}
    (hargs : evalExprs? config {contract := contract, locals := locals, immutables := imms} evm args =
      .ok [.address revoker, wordBytes32Value word, .int (Int.ofNat time.toNat), .int (Int.ofNat heap)])
    (hz : offchainWord evm revoker word = ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm
      (.internalCall "_revokeOffchain" args retVar)
      (.ok {contract := contract, locals := locals.insert retVar (.tuple [.tuple [], .int (Int.ofNat heap)]), immutables := imms}
        (offchainStore evm revoker word time)) := by
  have hf := offchainArgs_facts revoker word time heap
  exact internalCallFunctionReturn hargs offchain_lookup (offchain_bind revoker word time heap)
    (offchainSource_ok (fork := fork) (hperm := by assumption) hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2 hz)

theorem offchainCall_revert {locals imms : Store} {evm : EVM.State}
    {args : List Expr} {revoker : AccountAddress} {word time : UInt256} {heap : Nat} {retVar : Ident}
    (hargs : evalExprs? config {contract := contract, locals := locals, immutables := imms} evm args =
      .ok [.address revoker, wordBytes32Value word, .int (Int.ofNat time.toNat), .int (Int.ofNat heap)])
    (hz : offchainWord evm revoker word ≠ ⟨0⟩) :
    ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm
      (.internalCall "_revokeOffchain" args retVar) .reverted := by
  have hf := offchainArgs_facts revoker word time heap
  exact internalCallFunctionRevert hargs offchain_lookup (offchain_bind revoker word time heap)
    (offchainSource_revert hf.1 hf.2.1 hf.2.2.1 hz)

theorem offchainCall_static {locals imms : Store} {evm : EVM.State}
    {args : List Expr} {revoker : AccountAddress} {word time : UInt256} {heap : Nat} {retVar : Ident}
    (hargs : evalExprs? config {contract := contract, locals := locals, immutables := imms} evm args =
      .ok [.address revoker, wordBytes32Value word, .int (Int.ofNat time.toNat), .int (Int.ofNat heap)])
    (hz : offchainWord evm revoker word = ⟨0⟩) (hp : evm.executionEnv.perm = false) :
    ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm
      (.internalCall "_revokeOffchain" args retVar) .staticViolation := by
  have hf := offchainArgs_facts revoker word time heap
  exact internalCallFunctionStatic hargs offchain_lookup (offchain_bind revoker word time heap)
    (offchainSource_static hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hz hp)

end Benchmarks.EAS.EAS
