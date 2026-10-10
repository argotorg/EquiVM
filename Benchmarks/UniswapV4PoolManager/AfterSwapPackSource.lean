import Benchmarks.UniswapV4PoolManager.AfterSwapBranchSource
import Benchmarks.UniswapV4PoolManager.BalanceDeltaCombineSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def afterSwapSpecifiedFirst (p : SwapParamsWords) : Bool :=
  decide (EVM.signed p.amountSpecified < 0) == p.zeroForOne
def afterSwapPackWord (first : Bool) (specified unspecified : Int) : UInt256 :=
  if first then balanceDeltaWord (EVM.wordOfInt specified) (EVM.wordOfInt unspecified)
  else balanceDeltaWord (EVM.wordOfInt unspecified) (EVM.wordOfInt specified)
def afterSwapPackFrame (f : Frame) (first : Bool) (specified unspecified : Int) : Frame :=
  let packed := Value.int (EVM.signed (afterSwapPackWord first specified unspecified))
  valueLocal (valueLocal f "packed" packed) "hookDelta" packed
def afterSwapPackBranch (first : Bool) : List Stmt :=
  [.internalCall "toBalanceDelta"
     (if first then [.var "specified", .var "unspecified"] else [.var "unspecified", .var "specified"]) "packed",
   .assign .localVar {base := "hookDelta"} (.var "packed")]
def afterSwapPackCondition : Expr :=
  .binary .eq (.binary .lt (.field (.var "params") "amountSpecified") (.intLit 0))
    (.field (.var "params") "zeroForOne")
def afterSwapPackStmt : Stmt := .ite afterSwapPackCondition (afterSwapPackBranch true) (afterSwapPackBranch false)

theorem afterSwapPackPairSource {f : Frame} {evm : State} {e0 e1 : Expr} {a b : UInt256} {old : Value}
    (hf : f.contract = contract)
    (h0 : evalExpr? config f evm e0 = .ok (.int (EVM.signed a)))
    (h1 : evalExpr? config f evm e1 = .ok (.int (EVM.signed b)))
    (hh : f.locals.get? "hookDelta" = some old) :
    ExecBlock config f evm
      [.internalCall "toBalanceDelta" [e0, e1] "packed",
       .assign .localVar {base := "hookDelta"} (.var "packed")]
      (.ok (valueLocal (valueLocal f "packed" (.int (EVM.signed (balanceDeltaWord a b))))
        "hookDelta" (.int (EVM.signed (balanceDeltaWord a b)))) evm) := by
  exact ExecBlock.consNormal (balanceDeltaCall hf h0 h1 "packed") (execBlock_singleton
    (ExecStmt.assign (evalLocalValue (store_get_self _ _ _))
      (assignLocalValue ((store_get_ne _ _ (by decide : ("packed" == "hookDelta") = false)).trans hh))))

theorem afterSwapPackBranchSource {f : Frame} {evm : State} {specified unspecified : Int} {old : Value}
    (first : Bool) (hf : f.contract = contract)
    (hs : f.locals.get? "specified" = some (.int specified))
    (hu : f.locals.get? "unspecified" = some (.int unspecified))
    (hh : f.locals.get? "hookDelta" = some old)
    (hsc : signedFits ⟨128, by decide⟩ specified) (huc : signedFits ⟨128, by decide⟩ unspecified) :
    ExecBlock config f evm (afterSwapPackBranch first) (.ok (afterSwapPackFrame f first specified unspecified) evm) := by
  have hs' : evalExpr? config f evm (.var "specified") = .ok (.int (EVM.signed (EVM.wordOfInt specified))) := by
    rw [signed_wordOfInt (signedFits128_int256 hsc)]
    exact evalLocalValue hs
  have hu' : evalExpr? config f evm (.var "unspecified") = .ok (.int (EVM.signed (EVM.wordOfInt unspecified))) := by
    rw [signed_wordOfInt (signedFits128_int256 huc)]
    exact evalLocalValue hu
  cases first with
  | false => exact afterSwapPackPairSource hf hu' hs' hh
  | true => exact afterSwapPackPairSource hf hs' hu' hh

theorem afterSwapPackCondition_eval {f : Frame} {evm : State} {p : SwapParamsWords}
    (hp : f.locals.get? "params" = some (swapParamsValue p)) :
    evalExpr? config f evm afterSwapPackCondition = .ok (.bool (afterSwapSpecifiedFirst p)) := by
  have hlt : evalExpr? config f evm (.binary .lt (.field (.var "params") "amountSpecified") (.intLit 0)) =
      .ok (.bool (decide (EVM.signed p.amountSpecified < 0))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalStructField (evalLocalValue hp) rfl]
    simp only [evalExpr?, pure, bind, EvalResult.bind, evalBinaryOp?]
  rw [afterSwapPackCondition, evalExpr_binary_nonshort (by decide) (by decide), hlt,
    evalStructField (evalLocalValue hp) rfl]
  simp only [bind, EvalResult.bind, evalBinaryOp?, afterSwapSpecifiedFirst, BEq.beq, Value.bool.injEq]

theorem afterSwapPackSource {f : Frame} {evm : State} {p : SwapParamsWords} {specified unspecified : Int} {old : Value}
    (hf : f.contract = contract) (hp : f.locals.get? "params" = some (swapParamsValue p))
    (hs : f.locals.get? "specified" = some (.int specified))
    (hu : f.locals.get? "unspecified" = some (.int unspecified))
    (hh : f.locals.get? "hookDelta" = some old)
    (hsc : signedFits ⟨128, by decide⟩ specified) (huc : signedFits ⟨128, by decide⟩ unspecified) :
    ExecStmt config f evm afterSwapPackStmt
      (.ok (afterSwapPackFrame f (afterSwapSpecifiedFirst p) specified unspecified) evm) := by
  have hcond := afterSwapPackCondition_eval (evm := evm) hp
  have hbranch := afterSwapPackBranchSource (evm := evm) (afterSwapSpecifiedFirst p) hf hs hu hh hsc huc
  cases he : afterSwapSpecifiedFirst p with
  | false => rw [he] at hcond hbranch; exact ExecStmt.iteFalse hcond hbranch
  | true => rw [he] at hcond hbranch; exact ExecStmt.iteTrue hcond hbranch

end Benchmarks.UniswapV4PoolManager
