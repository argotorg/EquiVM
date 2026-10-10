import Benchmarks.UniswapV3.Pool.TickLogNormalizeSource
import Benchmarks.UniswapV3.Pool.SourceSignedBits

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def tickLogInitial (msb : Nat) : UInt256 :=
  UInt256.shiftLeft (UInt256.sub (UInt256.ofNat msb) ⟨128⟩) ⟨64⟩

def tickLogInitialExpr : Expr :=
  .binary (.shl (.sint ⟨256, by decide⟩))
    (.cast (.binary .sub
      (.cast (.var "msb") (.elem (.int (.sint ⟨256, by decide⟩)))) (.intLit 128))
      (.elem (.int (.sint ⟨256, by decide⟩)))) (.intLit 64)

theorem evalTickLogInitial {frame : Frame} {evm : EVM.State} (msb : Nat)
    (hm : frame.locals.get? "msb" = some (.int (Int.ofNat msb))) :
    evalExpr? config frame evm tickLogInitialExpr =
      .ok (.int (signedWordInt (tickLogInitial msb))) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm) hm
  have hc : evalExpr? config frame evm
      (.cast (.binary .sub
        (.cast (.var "msb") (.elem (.int (.sint ⟨256, by decide⟩)))) (.intLit 128))
        (.elem (.int (.sint ⟨256, by decide⟩)))) =
      .ok (.int (normalizeInt (.sint ⟨256, by decide⟩)
        (normalizeInt (.sint ⟨256, by decide⟩) (Int.ofNat msb) - 128))) := by
    simp only [evalExpr?, he, evalBinaryOp?, castValue?, EvalResult.ofOption,
      bind, EvalResult.bind, pure]
  simpa only [tickLogInitialExpr, tickLogInitial, wordOfInt_normalize256, wordOfInt_sub,
    wordOfInt_ofNat_eq, show EVM.wordOfInt 128 = ⟨128⟩ from rfl] using
    evalExpr_sint_shl 64 (by decide) hc

theorem tickLogLogReadySource (imms : Store) (evm : EVM.State) (price : UInt256)
    (hp : price.toNat < 2 ^ 160) (hv : tickLogValid price) :
    ∃ frame, ExecBlock config (tickLogFrame imms price) evm (tickLogFunction.body.take 15)
        (.ok frame evm) ∧
      frame.locals.get? "r" = some (.int (Int.ofNat
        (tickLogNormalized (tickLogRatio price) (tickLogMsb price).1).toNat)) ∧
      frame.locals.get? "log_2" = some (.int (signedWordInt (tickLogInitial (tickLogMsb price).1))) ∧
      frame.locals.get? "ratio" = some (.int (Int.ofNat (tickLogRatio price).toNat)) ∧
      frame.locals.get? "msb" = some (.int (Int.ofNat (tickLogMsb price).1)) ∧
      frame.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)) ∧
      frame.locals.get? "tick" = some (.int 0) := by
  obtain ⟨base, hs, hm, hr, hq, hp', ht⟩ := tickLogMsbSource imms evm price hp hv
  let mid := tickLogNormalizedFrame base (tickLogRatio price) (tickLogMsb price).1
  let out : Frame :=
    {mid with
      locals := mid.locals.insert "log_2" (.int (signedWordInt (tickLogInitial (tickLogMsb price).1)))}
  have hkeep (name : String) (hn : name ≠ "r") :
      mid.locals.get? name = base.locals.get? name := by
    change (base.locals.insert "r" (.int (Int.ofNat
      (tickLogNormalized (tickLogRatio price) (tickLogMsb price).1).toNat)))[name]? = base.locals[name]?
    simp only [Std.HashMap.getElem?_insert, beq_iff_eq, Ne.symm hn, if_false]
  have hkeep' (name : String) (hn : name ≠ "log_2") :
      out.locals.get? name = mid.locals.get? name := by
    change (mid.locals.insert "log_2"
      (.int (signedWordInt (tickLogInitial (tickLogMsb price).1))))[name]? = mid.locals[name]?
    simp only [Std.HashMap.getElem?_insert, beq_iff_eq, Ne.symm hn, if_false]
  refine ⟨out, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ExecBlock _ _ _ (tickLogFunction.body.take 13 ++
      [tickLogFunction.body[13]!, .letDecl "log_2"
        (some (.elem (.int (.sint ⟨256, by decide⟩)))) tickLogInitialExpr]) _
    apply execBlock_append_ok hs
    refine ExecBlock.consNormal (solm' := mid) (evm' := evm)
      (tickLogNormalizeSource _ _ _ hm hq hr (tickLogMsb_lt price)) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil
    exact evalTickLogInitial _ (by rw [hkeep "msb" (by decide)]; exact hm)
  · rw [hkeep' "r" (by decide)]
    change mid.locals["r"]? = _
    exact Std.HashMap.getElem?_insert_self
  · change out.locals["log_2"]? = _
    exact Std.HashMap.getElem?_insert_self
  · rw [hkeep' "ratio" (by decide), hkeep "ratio" (by decide)]
    exact hq
  · rw [hkeep' "msb" (by decide), hkeep "msb" (by decide)]
    exact hm
  · rw [hkeep' "sqrtPriceX96" (by decide), hkeep "sqrtPriceX96" (by decide)]
    exact hp'
  · rw [hkeep' "tick" (by decide), hkeep "tick" (by decide)]
    exact ht

end Benchmarks.UniswapV3.Pool
