import Benchmarks.UniswapV3.Pool.SourceWordBits

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def tickLogFunction : FunctionDecl := contract.functions[7]!

theorem tickLogLookup :
    lookupCallable? contract "TickMath_getTickAtSqrtRatio" = some tickLogFunction.toCallable := rfl

def tickLogLocals (price : UInt256) : Store :=
  (∅ : Store).insert "sqrtPriceX96" (.int (Int.ofNat price.toNat))

def tickLogFrame (imms : Store) (price : UInt256) : Frame :=
  {contract := contract, locals := tickLogLocals price, immutables := imms}

theorem tickLogBind (price : UInt256) :
    bindParams? tickLogFunction.params [.int (Int.ofNat price.toNat)] = some (tickLogLocals price) := rfl

def tickLogValid (price : UInt256) : Prop :=
  4295128739 ≤ price.toNat ∧ price.toNat < 1461446703485210103287273052203988822378723970342

instance (price : UInt256) : Decidable (tickLogValid price) := inferInstanceAs (Decidable (_ ∧ _))

def tickLogGuardExpr : Expr :=
  .binary .and (.binary .ge (.var "sqrtPriceX96") (.intLit 4295128739))
    (.binary .lt (.var "sqrtPriceX96")
      (.intLit 1461446703485210103287273052203988822378723970342))

def tickLogZeroFrame (imms : Store) (price : UInt256) : Frame :=
  {tickLogFrame imms price with locals := (tickLogLocals price).insert "tick" (.int 0)}

theorem evalTickLogGuard {frame : Frame} {evm : EVM.State} (price : UInt256)
    (hp : frame.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat))) :
    evalExpr? config frame evm tickLogGuardExpr = .ok (.bool (decide (tickLogValid price))) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm) hp
  have hlo : evalExpr? config frame evm (.binary .ge (.var "sqrtPriceX96") (.intLit 4295128739)) =
      .ok (.bool (decide (4295128739 ≤ price.toNat))) := by
    simp only [evalExpr?, he, bind, EvalResult.bind, evalBinaryOp?, pure]
    change EvalResult.ok (Value.bool (decide
      ((Int.ofNat 4295128739) ≤ Int.ofNat price.toNat))) = _
    apply congrArg (fun b => EvalResult.ok (Value.bool b))
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact Int.ofNat_le
  have hhi : evalExpr? config frame evm (.binary .lt (.var "sqrtPriceX96")
      (.intLit 1461446703485210103287273052203988822378723970342)) =
      .ok (.bool (decide (price.toNat < 1461446703485210103287273052203988822378723970342))) := by
    simp only [evalExpr?, he, bind, EvalResult.bind, evalBinaryOp?, pure]
    change EvalResult.ok (Value.bool (decide
      (Int.ofNat price.toNat < Int.ofNat 1461446703485210103287273052203988822378723970342))) = _
    apply congrArg (fun b => EvalResult.ok (Value.bool b))
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact Int.ofNat_lt
  simpa only [tickLogGuardExpr, tickLogValid, Bool.decide_and] using evalExpr_bool_and hlo hhi

theorem tickLogGuardSource (imms : Store) (evm : EVM.State) (price : UInt256)
    (hv : tickLogValid price) :
    ExecBlock config (tickLogFrame imms price) evm (tickLogFunction.body.take 2)
      (.ok (tickLogZeroFrame imms price) evm) := by
  refine ExecBlock.consNormal (solm' := tickLogZeroFrame imms price)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil
  simpa only [hv, decide_true] using evalTickLogGuard (evm := evm) price
    (frame := tickLogZeroFrame imms price)
    (by simp [tickLogZeroFrame, tickLogFrame, tickLogLocals, Std.HashMap.getElem_insert])

theorem tickLogReverts (imms : Store) (evm : EVM.State) (price : UInt256)
    (hv : ¬ tickLogValid price) :
    ExecFuncBody config (tickLogFrame imms price) evm tickLogFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  refine ExecBlock.consNormal (solm' := tickLogZeroFrame imms price)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [hv, decide_false] using evalTickLogGuard (evm := evm) price
    (frame := tickLogZeroFrame imms price)
    (by simp [tickLogZeroFrame, tickLogFrame, tickLogLocals, Std.HashMap.getElem_insert])

def tickLogRatio (price : UInt256) : UInt256 := UInt256.shiftLeft price ⟨32⟩

theorem tickLogRatio_toNat (price : UInt256) (hp : price.toNat < 2 ^ 160) :
    (tickLogRatio price).toNat = price.toNat * 2 ^ 32 :=
  shiftLeft_toNat_of_noOverflow _ _ (by decide) (by change price.toNat * 2 ^ 32 < 2 ^ 256; omega)

def tickLogRatioFrame (imms : Store) (price : UInt256) : Frame :=
  {tickLogZeroFrame imms price with
    locals := (tickLogZeroFrame imms price).locals.insert "ratio"
      (.int (Int.ofNat (tickLogRatio price).toNat))}

def tickLogReadyFrame (imms : Store) (price : UInt256) : Frame :=
  {tickLogRatioFrame imms price with
    locals := ((tickLogRatioFrame imms price).locals.insert "r"
      (.int (Int.ofNat (tickLogRatio price).toNat))).insert "msb" (.int 0)}

theorem tickLogReadySource (imms : Store) (evm : EVM.State) (price : UInt256)
    (hp : price.toNat < 2 ^ 160) (hv : tickLogValid price) :
    ExecBlock config (tickLogFrame imms price) evm (tickLogFunction.body.take 5)
      (.ok (tickLogReadyFrame imms price) evm) := by
  change ExecBlock _ _ _ (tickLogFunction.body.take 2 ++ (tickLogFunction.body.drop 2).take 3) _
  apply execBlock_append_ok (tickLogGuardSource imms evm price hv)
  refine ExecBlock.consNormal (solm' := tickLogRatioFrame imms price) (ExecStmt.letDecl ?_) ?_
  · have he : evalExpr? config (tickLogZeroFrame imms price) evm
        (.cast (.var "sqrtPriceX96") (.elem (.int (.uint ⟨256, by decide⟩)))) =
        .ok (.int (Int.ofNat price.toNat)) := by
      have he := evalExpr_var_get (cfg := config) (evm := evm)
        (frame := tickLogZeroFrame imms price) (name := "sqrtPriceX96")
        (value := .int (Int.ofNat price.toNat))
        (by simp [tickLogZeroFrame, tickLogFrame, tickLogLocals, Std.HashMap.getElem_insert])
      simp only [evalExpr?, he, castValue?, normalizeInt_uint256_word,
        EvalResult.ofOption, bind, EvalResult.bind]
    rw [tickLogRatio_toNat price hp]
    exact evalExpr_uintShiftLeft ⟨256, by decide⟩ price.toNat 32 he (by decide)
      (by change price.toNat * 2 ^ 32 < 2 ^ 256; omega)
  refine ExecBlock.consNormal
    (solm' := {tickLogRatioFrame imms price with
      locals := (tickLogRatioFrame imms price).locals.insert "r"
        (.int (Int.ofNat (tickLogRatio price).toNat))})
    (ExecStmt.letDecl (value := .int (Int.ofNat (tickLogRatio price).toNat)) ?_) ?_
  · exact evalExpr_var_get (cfg := config) (evm := evm)
      (frame := tickLogRatioFrame imms price) (name := "ratio")
      (value := .int (Int.ofNat (tickLogRatio price).toNat))
      (by
        change ((tickLogZeroFrame imms price).locals.insert "ratio"
          (.int (Int.ofNat (tickLogRatio price).toNat)))["ratio"]? = _
        simp only [Std.HashMap.getElem?_insert, beq_self_eq_true, ↓reduceIte])
  exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil

end Benchmarks.UniswapV3.Pool
