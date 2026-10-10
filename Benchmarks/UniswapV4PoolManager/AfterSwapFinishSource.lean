import Benchmarks.UniswapV4PoolManager.AfterSwapPackSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000
attribute [local irreducible] afterSwapPackWord balanceDeltaCombineWord balanceDeltaCombineFits

def afterSwapFinishFrame (f : Frame) (first : Bool) (delta : UInt256) (specified unspecified : Int) : Frame :=
  let packed := afterSwapPackWord first specified unspecified
  let remain := Value.int (EVM.signed (balanceDeltaCombineWord true delta packed))
  valueLocal (valueLocal (afterSwapPackFrame (valueLocal f "hookDelta" (.int 0)) first specified unspecified)
    "remaining" remain) "swapDelta" remain
def afterSwapFinishResult (f : Frame) (evm : State) (p : SwapParamsWords) (delta : UInt256)
    (specified unspecified : Int) : ExecResult :=
  if unspecified ≠ 0 ∨ specified ≠ 0 then
    if balanceDeltaCombineFits true delta (afterSwapPackWord (afterSwapSpecifiedFirst p) specified unspecified) then
      .returned (afterSwapFinishFrame f (afterSwapSpecifiedFirst p) delta specified unspecified) evm
        (some [.int (EVM.signed (balanceDeltaCombineWord true delta
          (afterSwapPackWord (afterSwapSpecifiedFirst p) specified unspecified))),
          .int (EVM.signed (afterSwapPackWord (afterSwapSpecifiedFirst p) specified unspecified))])
    else .reverted
  else .returned (valueLocal f "hookDelta" (.int 0)) evm (some [.int (EVM.signed delta), .int 0])
def afterSwapFinishBranch : List Stmt :=
  [afterSwapPackStmt,
   .internalCall "BalanceDelta_sub" [.var "swapDelta", .var "hookDelta"] "remaining",
   .assign .localVar {base := "swapDelta"} (.var "remaining")]
def afterSwapFinishStmts : List Stmt :=
  [.letDecl "hookDelta" (some (.elem (.int (.sint ⟨256, by decide⟩)))) (.intLit 0),
   .ite (.binary .or (.binary .ne (.var "unspecified") (.intLit 0))
     (.binary .ne (.var "specified") (.intLit 0))) afterSwapFinishBranch [],
   .return [.var "swapDelta", .var "hookDelta"]]

theorem afterSwapFinishSource {f : Frame} {evm : State} {p : SwapParamsWords} {delta : UInt256}
    {specified unspecified : Int}
    (hf : f.contract = contract) (hp : f.locals.get? "params" = some (swapParamsValue p))
    (hd : f.locals.get? "swapDelta" = some (.int (EVM.signed delta)))
    (hs : f.locals.get? "specified" = some (.int specified))
    (hu : f.locals.get? "unspecified" = some (.int unspecified))
    (hsc : signedFits ⟨128, by decide⟩ specified) (huc : signedFits ⟨128, by decide⟩ unspecified) :
    ExecBlock config f evm afterSwapFinishStmts (afterSwapFinishResult f evm p delta specified unspecified) := by
  let f0 := valueLocal f "hookDelta" (.int 0)
  have h0 : ExecStmt config f evm afterSwapFinishStmts[0]! (.ok f0 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure])
  have hget (name : Ident) (hn : ("hookDelta" == name) = false) : f0.locals.get? name = f.locals.get? name :=
    store_get_ne _ _ hn
  have hp0 := (hget "params" (by decide)).trans hp
  have hd0 := (hget "swapDelta" (by decide)).trans hd
  have hs0 := (hget "specified" (by decide)).trans hs
  have hu0 := (hget "unspecified" (by decide)).trans hu
  have hcond : evalExpr? config f0 evm (.binary .or (.binary .ne (.var "unspecified") (.intLit 0))
      (.binary .ne (.var "specified") (.intLit 0))) = .ok (.bool (decide (unspecified ≠ 0 ∨ specified ≠ 0))) := by
    have hne (name : Ident) (n : Int) (hn : f0.locals.get? name = some (.int n)) :
        evalExpr? config f0 evm (.binary .ne (.var name) (.intLit 0)) = .ok (.bool (decide (n ≠ 0))) := by
      simp only [evalExpr?, hn, EvalResult.ofOption, bind, EvalResult.bind, pure,
        evalBinaryOp?, BEq.beq, Value.int.injEq, decide_not, ne_eq]
    simpa only [Bool.decide_or] using evalOrBool (hne "unspecified" unspecified hu0) (hne "specified" specified hs0)
  by_cases hn : unspecified ≠ 0 ∨ specified ≠ 0
  · rw [afterSwapFinishResult, if_pos hn]
    let first := afterSwapSpecifiedFirst p
    let packed := afterSwapPackWord first specified unspecified
    let f1 := afterSwapPackFrame f0 first specified unspecified
    have hpack := afterSwapPackSource (f := f0) (evm := evm) hf hp0 hs0 hu0 (store_get_self _ _ _) hsc huc
    have hd1 : f1.locals.get? "swapDelta" = some (.int (EVM.signed delta)) :=
      (store_get_ne2 _ _ _ (by decide : ("packed" == "swapDelta") = false)
        (by decide : ("hookDelta" == "swapDelta") = false)).trans hd0
    have hsub := balanceDeltaCombineCall (f := f1) (evm := evm) (a := delta) (b := packed) hf
      (evalLocalValue hd1) (evalLocalValue (store_get_self _ _ _)) true "remaining"
    by_cases hfit : balanceDeltaCombineFits true delta packed
    · rw [if_pos hfit] at hsub ⊢
      have hset : ExecStmt config (valueLocal f1 "remaining" (.int (EVM.signed (balanceDeltaCombineWord true delta packed))))
          evm (.assign .localVar {base := "swapDelta"} (.var "remaining"))
          (.ok (afterSwapFinishFrame f first delta specified unspecified) evm) :=
        ExecStmt.assign (evalLocalValue (store_get_self _ _ _))
          (assignLocalValue ((store_get_ne _ _ (by decide : ("remaining" == "swapDelta") = false)).trans hd1))
      have hbranch : ExecBlock config f0 evm afterSwapFinishBranch
          (.ok (afterSwapFinishFrame f first delta specified unspecified) evm) :=
        ExecBlock.consNormal hpack (ExecBlock.consNormal hsub (execBlock_singleton hset))
      have hdelta : (afterSwapFinishFrame f first delta specified unspecified).locals.get? "swapDelta" =
          some (.int (EVM.signed (balanceDeltaCombineWord true delta packed))) := store_get_self _ _ _
      have hhook : (afterSwapFinishFrame f first delta specified unspecified).locals.get? "hookDelta" =
          some (.int (EVM.signed packed)) :=
        (store_get_ne2 _ _ _ (by decide : ("remaining" == "hookDelta") = false)
          (by decide : ("swapDelta" == "hookDelta") = false)).trans (store_get_self _ _ _)
      exact ExecBlock.consNormal h0 (ExecBlock.consNormal
        (ExecStmt.iteTrue (hcond.trans (by rw [decide_eq_true hn])) hbranch)
        (ExecBlock.consReturn (ExecStmt.return (by
          simp only [evalExprs?, evalLocalValue hdelta, evalLocalValue hhook, bind, EvalResult.bind, pure, packed, first]))))
    · rw [if_neg hfit] at hsub ⊢
      exact ExecBlock.consNormal h0 (ExecBlock.consRevert
        (ExecStmt.iteTrue (hcond.trans (by rw [decide_eq_true hn]))
          (ExecBlock.consNormal hpack (ExecBlock.consRevert hsub))))
  · rw [afterSwapFinishResult, if_neg hn]
    exact ExecBlock.consNormal h0 (ExecBlock.consNormal
      (ExecStmt.iteFalse (hcond.trans (by rw [decide_eq_false hn])) ExecBlock.nil)
      (ExecBlock.consReturn (ExecStmt.return (by
        simp only [evalExprs?, evalLocalValue hd0,
          evalLocalValue (show f0.locals.get? "hookDelta" = some (.int 0) from store_get_self _ _ _),
          bind, EvalResult.bind, pure]))))

end Benchmarks.UniswapV4PoolManager
