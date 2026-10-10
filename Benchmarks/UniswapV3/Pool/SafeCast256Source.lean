import Benchmarks.UniswapV3.Pool.SafeCast128Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000
attribute [local instance] Classical.propDecidable

def safeCast256Function : FunctionDecl := contract.functions[19]!

theorem safeCast256Lookup :
    lookupCallable? contract "SafeCast_toInt256" = some safeCast256Function.toCallable := rfl

def safeCast256Locals (y : UInt256) : Store := (∅ : Store).insert "y" (.int (Int.ofNat y.toNat))

def safeCast256Frame (imms : Store) (y : UInt256) : Frame :=
  {contract := contract, locals := safeCast256Locals y, immutables := imms}

def safeCast256ZeroFrame (imms : Store) (y : UInt256) : Frame :=
  {safeCast256Frame imms y with locals := (safeCast256Locals y).insert "z" (.int 0)}

def safeCast256ReadyFrame (imms : Store) (y : UInt256) : Frame :=
  let locals := (safeCast256ZeroFrame imms y).locals.insert "z" (.int (Int.ofNat y.toNat))
  {safeCast256ZeroFrame imms y with locals := locals}

def safeCast256Valid (y : UInt256) : Prop := y.toNat < 2 ^ 255

theorem safeCast256Bind (y : UInt256) :
    bindParams? safeCast256Function.params [.int (Int.ofNat y.toNat)] =
      some (safeCast256Locals y) := rfl

macro "safe_cast_256_get" : tactic =>
  `(tactic| (simp only [safeCast256ReadyFrame, safeCast256ZeroFrame, safeCast256Frame,
    safeCast256Locals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl))

theorem evalSafeCast256Guard (imms : Store) (evm : EVM.State) (y : UInt256) :
    evalExpr? config (safeCast256ZeroFrame imms y) evm
      (.binary .lt (.var "y") (.cast (.binary .exp (.intLit 2) (.intLit 255))
        (.elem (.int (.uint ⟨256, by decide⟩))))) =
      .ok (.bool (decide (safeCast256Valid y))) := by
  have hy : evalExpr? config (safeCast256ZeroFrame imms y) evm (.var "y") =
      .ok (.int (Int.ofNat y.toNat)) := evalExpr_var_get (by safe_cast_256_get)
  have hp : evalExpr? config (safeCast256ZeroFrame imms y) evm
      (.cast (.binary .exp (.intLit 2) (.intLit 255)) (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat (2 ^ 255))) := by
    simp only [evalExpr?, evalBinaryOp?, castValue?, EvalResult.ofOption, bind, EvalResult.bind, pure]
    norm_num [normalizeInt, EVM.twoPow]
    decide
  simp only [evalExpr?, hy, hp, evalBinaryOp?, bind, EvalResult.bind, pure, safeCast256Valid,
    Int.ofNat_eq_natCast, Nat.cast_lt]
  apply congrArg EvalResult.ok
  apply congrArg Value.bool
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]

theorem safeCast256Assign (imms : Store) (evm : EVM.State) (y : UInt256)
    (hy : safeCast256Valid y) :
    ExecStmt config (safeCast256ZeroFrame imms y) evm (safeCast256Function.body[2]!)
      (.ok (safeCast256ReadyFrame imms y) evm) := by
  have hn : normalizeInt (.sint ⟨256, by decide⟩) (Int.ofNat y.toNat) = Int.ofNat y.toNat := by
    apply normalizeSint_eq_self
    · change -(2 ^ 255 : Int) ≤ (y.toNat : Int)
      omega
    · change (y.toNat : Int) < (2 ^ 255 : Nat)
      exact_mod_cast hy
  apply ExecStmt.assign (value := .int (Int.ofNat y.toNat))
  · have he : evalExpr? config (safeCast256ZeroFrame imms y) evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := evalExpr_var_get (by safe_cast_256_get)
    simp only [evalExpr?, he, castValue?, EvalResult.ofOption, bind, EvalResult.bind, hn]
  · exact assignLocalVarBase_frame (by safe_cast_256_get)

theorem safeCast256Returns (imms : Store) (evm : EVM.State) (y : UInt256)
    (hy : safeCast256Valid y) :
    ExecFuncBody config (safeCast256Frame imms y) evm safeCast256Function.body
      (.returned (safeCast256ReadyFrame imms y) evm (some [.int (Int.ofNat y.toNat)])) := by
  apply ExecFuncBody.execBlockRet
  refine ExecBlock.consNormal (solm' := safeCast256ZeroFrame imms y) (evm' := evm)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hy] using evalSafeCast256Guard imms evm y
  refine ExecBlock.consNormal (safeCast256Assign imms evm y hy) ?_
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  have he : evalExpr? config (safeCast256ReadyFrame imms y) evm (.var "z") =
      .ok (.int (Int.ofNat y.toNat)) := evalExpr_var_get (by safe_cast_256_get)
  simp only [evalExprs?, he, bind, EvalResult.bind, pure]

theorem safeCast256Reverts (imms : Store) (evm : EVM.State) (y : UInt256)
    (hy : ¬ safeCast256Valid y) :
    ExecFuncBody config (safeCast256Frame imms y) evm safeCast256Function.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  refine ExecBlock.consNormal (solm' := safeCast256ZeroFrame imms y) (evm' := evm)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  simpa only [decide_eq_false hy] using evalSafeCast256Guard imms evm y

end Benchmarks.UniswapV3.Pool
