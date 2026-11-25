import Benchmarks.Midnight.MulDiv

variable {fork : Ethereum.Fork}

/-! Source return and revert paths for the multiplication and division helpers. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem evalMulDivUp_revert {cfg : Config} {frame : Frame} {evm : EVM.State} {x y d : UInt256}
    (hx : frame.locals.get? "x" = some (.int x.toNat))
    (hy : frame.locals.get? "y" = some (.int y.toNat))
    (hd : frame.locals.get? "d" = some (.int d.toNat)) (hbad : ¬ MulDivUpSafe x y d) :
    evalExpr? cfg frame evm mulDivUpExpr = .revert := by
  have hsum : evalExpr? cfg frame evm mulDivSumExpr = .revert := by
    by_cases hmul : x.toNat * y.toNat < UInt256.size
    · have hp := evalMulDivProduct (cfg := cfg) (evm := evm) hx hy hmul
      by_cases hpos : 0 < d.toNat
      · exact checkedAddSourceOverflow hp (evalMulDivPred hd hpos) (by
          have hs : ¬ (UInt256.mul x y).toNat + (UInt256.sub d ⟨1⟩).toNat < UInt256.size :=
            fun hs ↦ hbad ⟨hmul, hpos, hs⟩
          omega)
      · have hz : d.toNat = 0 := by omega
        have hpred : evalExpr? cfg frame evm mulDivPredExpr = .revert := by
          simp only [mulDivPredExpr, evalExpr?, hd, hz, EvalResult.ofOption,
            bind, pure, EvalResult.bind, evalBinaryOp?]
          rfl
        rw [mulDivSumExpr, evalExpr?,
          evalExpr_binary_nonshort (by decide) (by decide), hp]
        simp only [bind, EvalResult.bind, hpred]
    · have hp := evalMulDivProduct_overflow (cfg := cfg) (evm := evm) hx hy (by omega)
      rw [mulDivSumExpr, evalExpr?,
        evalExpr_binary_nonshort (by decide) (by decide), hp]
      rfl
  rw [mulDivUpExpr, evalExpr_binary_nonshort (by decide) (by decide), hsum]
  rfl

theorem evalMulDivDown_revert {cfg : Config} {frame : Frame} {evm : EVM.State} {x y d : UInt256}
    (hx : frame.locals.get? "x" = some (.int x.toNat))
    (hy : frame.locals.get? "y" = some (.int y.toNat))
    (hd : frame.locals.get? "d" = some (.int d.toNat))
    (hbad : ¬ (x.toNat * y.toNat < UInt256.size ∧ d ≠ ⟨0⟩)) :
    evalExpr? cfg frame evm mulDivDownExpr = .revert := by
  rw [mulDivDownExpr, evalExpr_binary_nonshort (by decide) (by decide)]
  by_cases hmul : x.toNat * y.toNat < UInt256.size
  · have hz : d = ⟨0⟩ := by by_contra hn; exact hbad ⟨hmul, hn⟩
    rw [evalMulDivProduct hx hy hmul]
    have hd' : evalExpr? cfg frame evm (.var "d") = .ok (.int 0) := by
      simp only [evalExpr?, hd, hz, EvalResult.ofOption]
      rfl
    simp only [bind, EvalResult.bind, hd', evalBinaryOp?]
    rfl
  · rw [evalMulDivProduct_overflow hx hy (by omega)]
    rfl

-- LIBRARY CANDIDATE: a single returned expression propagates evaluation failure.
theorem singleReturnRevert {cfg : Config} {frame : Frame} {evm : EVM.State} {expr : Expr}
    (he : evalExpr? cfg frame evm expr = .revert) :
    ExecFuncBody fork cfg frame evm [.return [expr]] .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  apply ExecStmt.returnRevert
  simp only [evalExprs?, he, bind, EvalResult.bind]

theorem mulDivDownBodyReturns {cfg : Config} {frame : Frame} {evm : EVM.State} {x y d : UInt256}
    (hx : frame.locals.get? "x" = some (.int x.toNat))
    (hy : frame.locals.get? "y" = some (.int y.toNat))
    (hd : frame.locals.get? "d" = some (.int d.toNat))
    (hfit : x.toNat * y.toNat < UInt256.size) (hnz : d ≠ ⟨0⟩) :
    ExecFuncBody fork cfg frame evm mulDivDownFunction.body
      (.returned frame evm (some [.int (mulDivDown x y d).toNat])) :=
  ExecFuncBody.execBlockRet (ABlock.start.returns (evalMulDivDown hx hy hd hfit hnz))

theorem mulDivDownBodyReverts {cfg : Config} {frame : Frame} {evm : EVM.State} {x y d : UInt256}
    (hx : frame.locals.get? "x" = some (.int x.toNat))
    (hy : frame.locals.get? "y" = some (.int y.toNat))
    (hd : frame.locals.get? "d" = some (.int d.toNat))
    (hbad : ¬ (x.toNat * y.toNat < UInt256.size ∧ d ≠ ⟨0⟩)) :
    ExecFuncBody fork cfg frame evm mulDivDownFunction.body .reverted :=
  singleReturnRevert (evalMulDivDown_revert hx hy hd hbad)

theorem mulDivUpBodyReturns {cfg : Config} {frame : Frame} {evm : EVM.State} {x y d : UInt256}
    (hx : frame.locals.get? "x" = some (.int x.toNat))
    (hy : frame.locals.get? "y" = some (.int y.toNat))
    (hd : frame.locals.get? "d" = some (.int d.toNat)) (hsafe : MulDivUpSafe x y d) :
    ExecFuncBody fork cfg frame evm mulDivUpFunction.body
      (.returned frame evm (some [.int (mulDivUp x y d).toNat])) :=
  ExecFuncBody.execBlockRet (ABlock.start.returns (evalMulDivUp hx hy hd hsafe))

theorem mulDivUpBodyReverts {cfg : Config} {frame : Frame} {evm : EVM.State} {x y d : UInt256}
    (hx : frame.locals.get? "x" = some (.int x.toNat))
    (hy : frame.locals.get? "y" = some (.int y.toNat))
    (hd : frame.locals.get? "d" = some (.int d.toNat)) (hbad : ¬ MulDivUpSafe x y d) :
    ExecFuncBody fork cfg frame evm mulDivUpFunction.body .reverted :=
  singleReturnRevert (evalMulDivUp_revert hx hy hd hbad)

end Benchmarks.Midnight
