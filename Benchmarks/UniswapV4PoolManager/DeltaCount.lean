import Benchmarks.UniswapV4PoolManager.TransientSource
import Benchmarks.UniswapV4PoolManager.SignedWords

/-! The nonzero transient delta counter, including wrapping updates. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 2000000

-- LIBRARY CANDIDATE: FunctionDecl form of the internal-call static-halt rule.
theorem internalCallFunctionStatic {cfg : Config} {caller : Frame} {evm : EVM.State}
    {name retVar : Ident} {args : List Expr} {argVals : List Value}
    {callee : FunctionDecl} {locals : Store}
    (hargs : evalExprs? cfg caller evm args = .ok argVals)
    (hlookup : lookupCallable? caller.contract name = some callee.toCallable)
    (hbind : bindParams? callee.params argVals = some locals)
    (hbody : ExecFuncBody cfg {caller with locals := locals} evm callee.body .staticViolation) :
    ExecStmt cfg caller evm (.internalCall name args retVar) .staticViolation :=
  ExecStmt.internalCallStatic hargs hlookup hbind hbody

def deltaCountFunction (increment : Bool) : FunctionDecl :=
  if increment then incrementDeltaCountFunction else decrementDeltaCountFunction

def deltaCountNext (evm : EVM.State) (increment : Bool) : UInt256 :=
  if increment then transientWord evm deltaCountSlot + ⟨1⟩
  else UInt256.sub (transientWord evm deltaCountSlot) ⟨1⟩

def deltaCountPost (evm : EVM.State) (increment : Bool) : EVM.State :=
  Solm.EVM.transientStore evm evm.executionEnv.codeOwner deltaCountSlot (deltaCountNext evm increment)

def deltaCountRhs (increment : Bool) : Expr :=
  .cast (.binary (if increment then .add else .sub)
    (.transient {base := "rawTransient", steps := [.aindex (.const "COUNT_SLOT")]}) (.intLit 1))
    (.elem (.int (.uint ⟨256, by decide⟩)))

theorem deltaCountFunction_body (increment : Bool) :
    (deltaCountFunction increment).body =
      [.assign .transient {base := "rawTransient", steps := [.aindex (.const "COUNT_SLOT")]}
        (deltaCountRhs increment)] := by
  cases increment <;> rfl

theorem deltaCountFunction_lookup (increment : Bool) :
    lookupCallable? contract (deltaCountFunction increment).name = some (deltaCountFunction increment).toCallable := by
  cases increment <;> rfl

theorem deltaCountBodyExec {f : Frame} {evm : EVM.State}
    (hf : f.contract = contract) (increment : Bool) :
    ExecFuncBody config f evm (deltaCountFunction increment).body
      (if evm.executionEnv.perm = false then .staticViolation
       else .returned f (deltaCountPost evm increment) none) := by
  let old := transientWord evm deltaCountSlot
  let value : Int := if increment then Int.ofNat old.toNat + 1 else Int.ofNat old.toNat - 1
  have hr := rawTransient_read (evm := evm) hf (evalDeltaCountSlot hf)
  have hv : EVM.wordOfInt value = deltaCountNext evm increment := by
    cases increment
    · exact wordOfInt_sub_toUInt256 old ⟨1⟩
    · exact wordOfInt_natCast_succ old
  have he : evalExpr? config f evm (deltaCountRhs increment) =
      .ok (.int (normalizeInt (.uint ⟨256, by decide⟩) value)) := by
    apply evalExpr_cast_int
    rw [evalExpr_binary_nonshort (by cases increment <;> decide) (by cases increment <;> decide), hr]
    cases increment <;> simp only [evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?] <;> rfl
  have hs := rawTransient_writeInt (evm := evm) (normalizeInt (.uint ⟨256, by decide⟩) value)
    hf (evalDeltaCountSlot hf)
  rw [wordOfInt_normalizeUint256, hv] at hs
  rw [deltaCountFunction_body]
  by_cases hp : evm.executionEnv.perm = false
  · rw [if_pos hp]
    exact ExecFuncBody.execBlockStatic (ExecBlock.consStatic (ExecStmt.assignTransientStatic he hs hp))
  · rw [if_neg hp]
    exact ExecFuncBody.execBlockOK (ExecBlock.consNormal (ExecStmt.assign he hs) ExecBlock.nil)

theorem deltaCountCall {f : Frame} {evm : EVM.State}
    (hf : f.contract = contract) (increment : Bool) (retVar : Ident) :
    ExecStmt config f evm (.internalCall (deltaCountFunction increment).name [] retVar)
      (if evm.executionEnv.perm = false then .staticViolation
       else .ok {f with locals := f.locals.insert retVar .unit} (deltaCountPost evm increment)) := by
  have hbody := deltaCountBodyExec (f := {f with locals := ∅}) (evm := evm) hf increment
  have hl : lookupCallable? f.contract (deltaCountFunction increment).name = some (deltaCountFunction increment).toCallable := by
    rw [hf]; exact deltaCountFunction_lookup increment
  have hb : bindParams? (deltaCountFunction increment).params [] = some ∅ := by
    cases increment <;> rfl
  by_cases hp : evm.executionEnv.perm = false
  · rw [if_pos hp] at hbody ⊢
    exact internalCallFunctionStatic rfl hl hb hbody
  · rw [if_neg hp] at hbody ⊢
    exact internalCallFunctionReturn rfl hl hb hbody

end Benchmarks.UniswapV4PoolManager
