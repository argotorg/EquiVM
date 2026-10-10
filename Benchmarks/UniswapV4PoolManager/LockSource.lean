import Benchmarks.UniswapV4PoolManager.TransientSource
import Benchmarks.UniswapV4PoolManager.CallComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def lockSetFunction (unlocked : Bool) : FunctionDecl := if unlocked then contract.functions[5]! else contract.functions[7]!
abbrev deltaCountReadFunction : FunctionDecl := contract.functions[6]!

def lockSetPost (evm : EVM.State) (unlocked : Bool) : EVM.State :=
  Solm.EVM.transientStore evm evm.executionEnv.codeOwner lockSlot unlocked.toUInt256

theorem lockSetFunction_lookup (unlocked : Bool) :
    lookupCallable? contract (lockSetFunction unlocked).name = some (lockSetFunction unlocked).toCallable := by
  cases unlocked <;> rfl

theorem lockSetFunction_body (unlocked : Bool) :
    (lockSetFunction unlocked).body = [.assign .transient
      {base := "rawTransient", steps := [.aindex (.const "LOCK_SLOT")]}
      (.intLit (if unlocked then 1 else 0))] := by cases unlocked <;> rfl

theorem lockSetBody {f : Frame} {evm : EVM.State} (hf : f.contract = contract) (unlocked : Bool) :
    ExecFuncBody config f evm (lockSetFunction unlocked).body
      (if evm.executionEnv.perm = false then .staticViolation else .returned f (lockSetPost evm unlocked) none) := by
  rw [lockSetFunction_body]
  have he : evalExpr? config f evm (.intLit (if unlocked then 1 else 0)) =
      .ok (.int (Int.ofNat unlocked.toUInt256.toNat)) := by
    cases unlocked <;> simp only [evalExpr?, pure] <;> rfl
  have hw := rawTransient_write (evm := evm) unlocked.toUInt256 hf (evalLockSlot hf)
  by_cases hp : evm.executionEnv.perm = false
  · rw [if_pos hp]
    exact .execBlockStatic (ExecBlock.consStatic (ExecStmt.assignTransientStatic he hw hp))
  · rw [if_neg hp]
    exact .execBlockOK (ExecBlock.consNormal (ExecStmt.assign he hw) ExecBlock.nil)

theorem lockSetCall {f : Frame} {evm : EVM.State} (hf : f.contract = contract) (unlocked : Bool) (retVar : Ident) :
    ExecStmt config f evm (.internalCall (lockSetFunction unlocked).name [] retVar)
      (if evm.executionEnv.perm = false then .staticViolation
       else .ok {f with locals := f.locals.insert retVar .unit} (lockSetPost evm unlocked)) := by
  have hb := lockSetBody (f := {f with locals := ∅}) (evm := evm) hf unlocked
  have hh := internalCallFunctionExec (caller := f) (retVar := retVar) (args := []) (argVals := [])
    rfl (by rw [hf]; exact lockSetFunction_lookup unlocked) (by cases unlocked <;> rfl) hb
  simpa only [resumeCallResult_ite, resumeCallResult_static, resumeCallResult_returned] using hh

theorem deltaCountRead_lookup : lookupCallable? contract "NonzeroDeltaCount_read" = some deltaCountReadFunction.toCallable := rfl

theorem deltaCountReadBody {f : Frame} {evm : EVM.State} (hf : f.contract = contract) :
    ExecFuncBody config f evm deltaCountReadFunction.body
      (.returned f evm (some [.int (Int.ofNat (transientWord evm deltaCountSlot).toNat)])) :=
  .execBlockRet (ABlock.start.returns (rawTransient_read hf (evalDeltaCountSlot hf)))

theorem deltaCountReadCall {f : Frame} {evm : EVM.State} (hf : f.contract = contract) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "NonzeroDeltaCount_read" [] retVar)
      (.ok {f with locals := f.locals.insert retVar (.int (Int.ofNat (transientWord evm deltaCountSlot).toNat))} evm) :=
  internalCallFunctionReturn rfl (by rw [hf]; exact deltaCountRead_lookup) rfl
    (deltaCountReadBody (f := {f with locals := ∅}) hf)

end Benchmarks.UniswapV4PoolManager
