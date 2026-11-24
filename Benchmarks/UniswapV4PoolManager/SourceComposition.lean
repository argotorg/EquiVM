import Benchmarks.UniswapV4PoolManager.EntrySource

variable {fork : Ethereum.Fork}

/-! Composing source bodies across normal prefixes and state changes. -/
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: prefix composition also preserves function fallthrough.
theorem execFuncBody_prepend {cfg : Config} {f f' : Frame} {evm evm' : EVM.State}
    {pre body : List Stmt} {result : ExecResult}
    (hp : ExecBlock fork cfg f evm pre (.ok f' evm'))
    (hb : ExecFuncBody fork cfg f' evm' body result) :
    ExecFuncBody fork cfg f evm (pre ++ body) result := by
  cases hb with
  | execBlockOK h => exact .execBlockOK (execBlock_append hp h)
  | execBlockRet h => exact .execBlockRet (execBlock_append hp h)
  | execBlockRevert h => exact .execBlockRevert (execBlock_append hp h)
  | execBlockBreak h => exact .execBlockBreak (execBlock_append hp h)
  | execBlockContinue h => exact .execBlockContinue (execBlock_append hp h)
  | execBlockStatic h => exact .execBlockStatic (execBlock_append hp h)

theorem nonpayableCalldataBody {cfg : Config} {C : ContractDecl} {locals imms : Store}
    {evm : EVM.State} {body : List Stmt} {result : ExecResult}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hb : ExecFuncBody fork cfg (calldataFrame C locals imms evm) evm body result) :
    ExecTransitionBody fork cfg C evm locals (nonpayableCalldataPrefix ++ body) result imms := by
  apply execFuncBody_prepend (pre := nonpayableCalldataPrefix) ?_ hb
  simpa only [List.append_nil] using nonpayableCalldataBlock hwv hhi (ExecBlock.nil (cfg := cfg))

def calldataPrefix : List Stmt :=
  [.letDecl "__calldata" (some .bytes) (.env .msgData), .require calldataSizeGuard]

theorem calldataBlock {cfg : Config} {C : ContractDecl} {locals imms : Store}
    {evm : EVM.State} {rest : List Stmt} {result : ExecResult}
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hrest : ExecBlock fork cfg (calldataFrame C locals imms evm) evm rest result) :
    ExecBlock fork cfg {contract := C, locals := locals, immutables := imms} evm
      (calldataPrefix ++ rest) result := by
  apply (ABlock.start.letStep (value := .bytes evm.executionEnv.calldata)
    (by simp only [evalExpr?, envValue, pure]) |>.requireStep ?_).run hrest
  exact (calldataSizeGuard_eval cfg C locals imms evm).trans
    (congrArg (fun b => EvalResult.ok (Value.bool b)) (decide_eq_true hhi))

theorem calldataBody {cfg : Config} {C : ContractDecl} {locals imms : Store}
    {evm : EVM.State} {body : List Stmt} {result : ExecResult}
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hb : ExecFuncBody fork cfg (calldataFrame C locals imms evm) evm body result) :
    ExecTransitionBody fork cfg C evm locals (calldataPrefix ++ body) result imms := by
  apply execFuncBody_prepend (pre := calldataPrefix) ?_ hb
  simpa only [List.append_nil] using calldataBlock hhi (ExecBlock.nil (cfg := cfg))

theorem calldataBodyReverts {cfg : Config} {C : ContractDecl} {locals imms : Store}
    {evm : EVM.State} {rest : List Stmt} (hhi : ¬ evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody fork cfg C evm locals (calldataPrefix ++ rest) .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  refine (ABlock.start.letStep (value := .bytes evm.executionEnv.calldata)
    (by simp only [evalExpr?, envValue, pure])).requireRevert ?_
  exact (calldataSizeGuard_eval cfg C locals imms evm).trans
    (congrArg (fun b => EvalResult.ok (Value.bool b)) (decide_eq_false hhi))

end Benchmarks.UniswapV4PoolManager
