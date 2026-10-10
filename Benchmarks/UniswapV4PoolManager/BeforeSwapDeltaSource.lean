import Benchmarks.UniswapV4PoolManager.BeforeSwapAmountSource
import Benchmarks.UniswapV4PoolManager.BalanceDeltaComponentSource
import Benchmarks.UniswapV4PoolManager.SignedBytesDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def beforeSwapSpecified (out : ByteArray) : UInt256 := UInt256.sar ⟨128⟩ (calldataWord out 32)
def beforeSwapDeltaFrame (f : Frame) (out : ByteArray) : Frame :=
  valueLocal (valueLocal f "hookReturn" (.int (EVM.signed (calldataWord out 32))))
    "hookDeltaSpecified" (.int (EVM.signed (beforeSwapSpecified out)))
def beforeSwapDeltaResult (f : Frame) (evm : State) (amount : UInt256) (out : ByteArray) : ExecResult :=
  if beforeSwapSpecified out = ⟨0⟩ then .ok (beforeSwapDeltaFrame f out) evm
  else beforeSwapAmountResult (beforeSwapDeltaFrame f out) evm amount (beforeSwapSpecified out)
def beforeSwapDeltaStmts : List Stmt :=
  [.assign .localVar {base := "hookReturn"}
     (.abiDecode abiInt256 (.bytesSlice (.var "result") (.intLit 32) (.intLit 64))),
   .letDecl "hookDeltaSpecified" (some (.elem (.int (.sint ⟨128, by decide⟩))))
     (balanceDeltaComponentExpr false (.var "hookReturn")),
   .ite (.binary .ne (.var "hookDeltaSpecified") (.intLit 0)) beforeSwapAmountStmts []]

theorem beforeSwapDeltaSource {f : Frame} {evm : State} {amount : UInt256} {out : ByteArray} {old : Value}
    (ha : f.locals.get? "amountToSwap" = some (.int (EVM.signed amount)))
    (hh : f.locals.get? "hookReturn" = some old)
    (hr : f.locals.get? "result" = some (.bytes out)) (hsize : 64 ≤ out.size) :
    ExecBlock config f evm beforeSwapDeltaStmts (beforeSwapDeltaResult f evm amount out) := by
  let f1 := valueLocal f "hookReturn" (.int (EVM.signed (calldataWord out 32)))
  have hdecode := evalDecodeSigned256Slice (start := 32) rfl (evalLocalValue (cfg := config) (evm := evm) hr) hsize
  have hcomponent := balanceDeltaComponent_eval
    (evalLocalValue (cfg := config) (evm := evm) (f := f1) (store_get_self _ _ _)) false
  have hcomponent' : evalExpr? config f1 evm (balanceDeltaComponentExpr false (.var "hookReturn")) =
      .ok (.int (EVM.signed (beforeSwapSpecified out))) := by
    simpa only [balanceDeltaComponent, Bool.false_eq_true, if_false, balanceDeltaAmount0,
      beforeSwapSpecified] using hcomponent
  have hspecified : (beforeSwapDeltaFrame f out).locals.get? "hookDeltaSpecified" =
      some (.int (EVM.signed (beforeSwapSpecified out))) := store_get_self _ _ _
  have hamount : (beforeSwapDeltaFrame f out).locals.get? "amountToSwap" = some (.int (EVM.signed amount)) :=
    (store_get_ne2 _ _ _ (by decide : ("hookReturn" == "amountToSwap") = false)
      (by decide : ("hookDeltaSpecified" == "amountToSwap") = false)).trans ha
  have hcondition : evalExpr? config (beforeSwapDeltaFrame f out) evm
      (.binary .ne (.var "hookDeltaSpecified") (.intLit 0)) =
      .ok (.bool (decide (beforeSwapSpecified out ≠ ⟨0⟩))) := by
    simp only [evalExpr?, hspecified, EvalResult.ofOption, bind, EvalResult.bind, pure,
      evalBinaryOp?, BEq.beq, Value.int.injEq, decide_not, ne_eq, signed_eq_zero_iff]
  have hset : ExecStmt config f evm beforeSwapDeltaStmts[0]! (.ok f1 evm) :=
    ExecStmt.assign hdecode (assignLocalValue hh)
  have hlet : ExecStmt config f1 evm beforeSwapDeltaStmts[1]! (.ok (beforeSwapDeltaFrame f out) evm) :=
    ExecStmt.letDecl hcomponent'
  by_cases hz : beforeSwapSpecified out = ⟨0⟩
  · rw [beforeSwapDeltaResult, if_pos hz]
    exact ExecBlock.consNormal hset (ExecBlock.consNormal hlet (execBlock_singleton (ExecStmt.iteFalse
      (hcondition.trans (by rw [decide_eq_false (not_not.mpr hz)])) ExecBlock.nil)))
  · rw [beforeSwapDeltaResult, if_neg hz]
    exact ExecBlock.consNormal hset (ExecBlock.consNormal hlet (execBlock_singleton
      (ExecStmt.iteTrue (hcondition.trans (by rw [decide_eq_true hz])) (beforeSwapAmountSource hamount hspecified))))

theorem beforeSwapDeltaResult_locals {f f' : Frame} {evm post : State} {amount fee : UInt256} {out : ByteArray}
    (ha : f.locals.get? "amountToSwap" = some (.int (EVM.signed amount)))
    (hf : f.locals.get? "lpFeeOverride" = some (.int (Int.ofNat fee.toNat)))
    (hr : beforeSwapDeltaResult f evm amount out = .ok f' post) :
    post = evm ∧
    f'.locals.get? "amountToSwap" = some (.int (EVM.signed (amount+beforeSwapSpecified out))) ∧
    f'.locals.get? "hookReturn" = some (.int (EVM.signed (calldataWord out 32))) ∧
    f'.locals.get? "lpFeeOverride" = some (.int (Int.ofNat fee.toNat)) := by
  rw [beforeSwapDeltaResult] at hr
  split_ifs at hr with hz
  · cases hr
    simp only [hz, u256_add_zero, beforeSwapDeltaFrame, valueLocal_get, beq_iff_eq, String.reduceEq,
      if_true, if_false, ha, hf, and_self]
  · rw [beforeSwapAmountResult] at hr
    split_ifs at hr with hfit hvalid <;> cases hr
    simp only [beforeSwapAmountFrame, beforeSwapDeltaFrame, valueLocal_get, beq_iff_eq, String.reduceEq,
      if_true, if_false, hf, and_self]

end Benchmarks.UniswapV4PoolManager
