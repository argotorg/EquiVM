import Benchmarks.UniswapV3.Pool.Slot0Storage
import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def poolAmountsFrame (locals imms : Store) : Frame :=
  {contract := contract, locals := (locals.insert "amount0" (.int 0)).insert "amount1" (.int 0),
    immutables := imms}

def poolAmountsInitBody : List Stmt :=
  [.require (.binary .eq (.env .callvalue) (.intLit 0)),
    .letDecl "amount0" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0),
    .letDecl "amount1" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0)]

def poolLockPrefixBody : List Stmt :=
  poolAmountsInitBody ++ [.require (.storage ⟨"slot0", [.field "unlocked"]⟩),
    .assign .storage ⟨"slot0", [.field "unlocked"]⟩ (.boolLit false)]

theorem poolAmountsInitSource (locals imms : Store) (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      poolAmountsInitBody (.ok (poolAmountsFrame locals imms) evm) := by
  apply (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
  refine ExecBlock.consNormal (ExecStmt.letDecl (name := "amount0")
    (ty := some (.elem (.int (.uint ⟨256, by decide⟩)))) (value := .int 0)
    (by simp only [evalExpr?, pure])) ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl (name := "amount1")
    (ty := some (.elem (.int (.uint ⟨256, by decide⟩)))) (value := .int 0)
    (by simp only [evalExpr?, pure])) ExecBlock.nil

theorem evalPoolAmountsUnlocked (locals imms : Store) (evm : EVM.State)
    (hslot : (poolAmountsFrame locals imms).locals.get? "slot0" = none) :
    evalExpr? config (poolAmountsFrame locals imms) evm (.storage ⟨"slot0", [.field "unlocked"]⟩) =
      .ok (.bool (!decide (slot0FieldWord 30 1 evm.accountMap evm.executionEnv = ⟨0⟩))) := by
  rw [← wordToElemBool]
  exact evalSlot0Unlocked _ _ _ hslot

theorem poolAmountsAssignLock (locals imms : Store) (evm : EVM.State)
    (hslot : (poolAmountsFrame locals imms).locals.get? "slot0" = none) :
    ExecStmt config (poolAmountsFrame locals imms) evm
      (.assign .storage ⟨"slot0", [.field "unlocked"]⟩ (.boolLit false))
      (.ok (poolAmountsFrame locals imms) (storeSlot0Unlocked evm false)) :=
  ExecStmt.assign (by simp only [evalExpr?, pure]) (assignSlot0Unlocked evm _ imms false hslot)

theorem poolLockPrefixSource (locals imms : Store) (evm : EVM.State)
    (hslot : (poolAmountsFrame locals imms).locals.get? "slot0" = none)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      poolLockPrefixBody (.ok (poolAmountsFrame locals imms) (storeSlot0Unlocked evm false)) := by
  apply execBlock_append_ok (poolAmountsInitSource locals imms evm hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hunlocked, decide_false, Bool.not_false] using evalPoolAmountsUnlocked locals imms evm hslot
  · exact ExecBlock.consNormal (poolAmountsAssignLock locals imms evm hslot) ExecBlock.nil

theorem poolEntryRevertsLocked (locals imms : Store) (evm : EVM.State) (rest : List Stmt)
    (hslot : (poolAmountsFrame locals imms).locals.get? "slot0" = none)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv = ⟨0⟩) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      (poolLockPrefixBody ++ rest) .reverted := by
  change ExecBlock config _ _ (poolAmountsInitBody ++
    .require (.storage ⟨"slot0", [.field "unlocked"]⟩) ::
    .assign .storage ⟨"slot0", [.field "unlocked"]⟩ (.boolLit false) :: rest) _
  apply execBlock_append_ok (poolAmountsInitSource locals imms evm hwv)
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  simpa only [hlocked, decide_true, Bool.not_true] using evalPoolAmountsUnlocked locals imms evm hslot

theorem poolEntryStatic (locals imms : Store) (evm : EVM.State) (rest : List Stmt)
    (hslot : (poolAmountsFrame locals imms).locals.get? "slot0" = none)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      (poolLockPrefixBody ++ rest) .staticViolation := by
  change ExecBlock config _ _ (poolAmountsInitBody ++
    .require (.storage ⟨"slot0", [.field "unlocked"]⟩) ::
    .assign .storage ⟨"slot0", [.field "unlocked"]⟩ (.boolLit false) :: rest) _
  apply execBlock_append_ok (poolAmountsInitSource locals imms evm hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hunlocked, decide_false, Bool.not_false] using evalPoolAmountsUnlocked locals imms evm hslot
  · exact ExecBlock.consStatic
      (execStmt_assign_static (poolAmountsAssignLock locals imms evm hslot) hperm)

end Benchmarks.UniswapV3.Pool
