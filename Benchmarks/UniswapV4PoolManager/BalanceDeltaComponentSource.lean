import Benchmarks.UniswapV4PoolManager.BalanceDeltaComponents
import Benchmarks.UniswapV4PoolManager.CallComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def balanceDeltaComponent (one : Bool) (word : UInt256) : Int :=
  if one then balanceDeltaAmount1 word else balanceDeltaAmount0 word
def balanceDeltaComponentExpr (one : Bool) (e : Expr) : Expr :=
  .cast (if one then e else .binary (.shr (.sint ⟨256, by decide⟩)) e (.intLit 128))
    (.elem (.int (.sint ⟨128, by decide⟩)))
def balanceDeltaComponentName (one : Bool) : Ident :=
  if one then "BalanceDeltaLibrary_amount1" else "BalanceDeltaLibrary_amount0"
def balanceDeltaComponentFunction (one : Bool) : FunctionDecl :=
  if one then contract.functions[75]! else contract.functions[74]!

theorem balanceDeltaComponent_fits (one : Bool) (word : UInt256) :
    signedFits ⟨128, by decide⟩ (balanceDeltaComponent one word) := by
  cases one with
  | false => exact balanceDeltaAmount0_fits word
  | true => exact balanceDeltaAmount1_fits word

theorem balanceDeltaComponent_eval {cfg : Config} {f : Frame} {evm : State} {e : Expr} {word : UInt256}
    (he : evalExpr? cfg f evm e = .ok (.int (EVM.signed word))) (one : Bool) :
    evalExpr? cfg f evm (balanceDeltaComponentExpr one e) = .ok (.int (balanceDeltaComponent one word)) := by
  cases one with
  | false => exact balanceDeltaAmount0_eval he
  | true => exact balanceDeltaAmount1_eval he

theorem balanceDeltaComponent_lookup (one : Bool) : lookupCallable? contract (balanceDeltaComponentName one) =
    some (balanceDeltaComponentFunction one).toCallable := by cases one <;> rfl

theorem balanceDeltaComponentBody {f : Frame} {evm : State} {word : UInt256}
    (hw : f.locals.get? "balanceDelta" = some (.int (EVM.signed word))) (one : Bool) :
    ExecFuncBody config f evm (balanceDeltaComponentFunction one).body
      (.returned f evm (some [.int (balanceDeltaComponent one word)])) := by
  have hb : (balanceDeltaComponentFunction one).body = [.return [balanceDeltaComponentExpr one (.var "balanceDelta")]] := by
    cases one <;> rfl
  rw [hb]
  exact .execBlockRet (ABlock.start.returns (balanceDeltaComponent_eval (evalLocalValue hw) one))

theorem balanceDeltaComponentCall {f : Frame} {evm : State} {e : Expr} {word : UInt256}
    (hf : f.contract = contract) (he : evalExpr? config f evm e = .ok (.int (EVM.signed word)))
    (one : Bool) (ret : Ident) :
    ExecStmt config f evm (.internalCall (balanceDeltaComponentName one) [e] ret)
      (.ok {f with locals := f.locals.insert ret (.int (balanceDeltaComponent one word))} evm) := by
  apply internalCallFunctionReturn (argVals := [.int (EVM.signed word)])
    (value := some [.int (balanceDeltaComponent one word)]) (evalExprs?_singleton he)
    (by rw [hf]; exact balanceDeltaComponent_lookup one) (by cases one <;> rfl)
  exact balanceDeltaComponentBody (store_get_self _ _ _) one

end Benchmarks.UniswapV4PoolManager
