import Benchmarks.UniswapV3.Pool.TickLogMsbWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def tickLogNormalizedFrame (frame : Frame) (ratio : UInt256) (msb : Nat) : Frame :=
  {frame with
    locals := frame.locals.insert "r" (.int (Int.ofNat (tickLogNormalized ratio msb).toNat))}

theorem tickLogNormalizeSource {frame : Frame} {evm : EVM.State}
    (ratio : UInt256) (msb : Nat) (old : Value)
    (hm : frame.locals.get? "msb" = some (.int (Int.ofNat msb)))
    (hq : frame.locals.get? "ratio" = some (.int (Int.ofNat ratio.toNat)))
    (hr : frame.locals.get? "r" = some old) (hmsb : msb < 256) :
    ExecStmt config frame evm (tickLogFunction.body[13]!)
      (.ok (tickLogNormalizedFrame frame ratio msb) evm) := by
  have hfit : msb < UInt256.size := lt_trans hmsb (by decide)
  have hmword : (UInt256.ofNat msb).toNat = msb := UInt256.toNat_ofNat_of_lt hfit
  have he := evalExpr_var_get (cfg := config) (evm := evm) hm
  have hq' := evalExpr_var_get (cfg := config) (evm := evm) hq
  have hm' : evalExpr? config frame evm (.var "msb") =
      .ok (.int (Int.ofNat (UInt256.ofNat msb).toNat)) := by
    simpa only [hmword] using he
  have h127 : evalExpr? config frame evm (.intLit 127) =
      .ok (.int (Int.ofNat (⟨127⟩ : UInt256).toNat)) := by
    norm_num [evalExpr?, pure, UInt256.toNat, UInt256.size]
  have hg : evalExpr? config frame evm (.binary .ge (.var "msb") (.intLit 128)) =
      .ok (.bool (decide (128 ≤ msb))) := by
    simp only [evalExpr?, he, evalBinaryOp?, bind, EvalResult.bind, pure]
    apply congrArg (fun b ↦ EvalResult.ok (Value.bool b))
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact Int.ofNat_le
  by_cases h : 128 ≤ msb
  · have hb : (UInt256.sub (UInt256.ofNat msb) ⟨127⟩).toNat < 256 := by
      have hs : (UInt256.sub (UInt256.ofNat msb) ⟨127⟩).toNat = msb - 127 :=
        usub_ofNat_lit_toNat (n := msb) (c := 127) (by omega) hfit
      rw [hs]
      omega
    refine ExecStmt.iteTrue (by simpa only [h, decide_true] using hg) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign (value := .int (Int.ofNat (tickLogNormalized ratio msb).toNat)) ?_
        (assignLocalVarBase_frame hr)) ExecBlock.nil
    simpa only [tickLogNormalized, if_pos h] using
      evalExpr_word_shr_by hq' (evalExpr_word_sub hm' h127) hb
  · have hb : (UInt256.sub ⟨127⟩ (UInt256.ofNat msb)).toNat < 256 := by
      have hs : (UInt256.sub ⟨127⟩ (UInt256.ofNat msb)).toNat = 127 - msb := by
        rw [usub_toNat (by rw [hmword]; change msb ≤ 127; omega), hmword]
        rfl
      rw [hs]
      omega
    refine ExecStmt.iteFalse (by simpa only [h, decide_false] using hg) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign (value := .int (Int.ofNat (tickLogNormalized ratio msb).toNat)) ?_
        (assignLocalVarBase_frame hr)) ExecBlock.nil
    simpa only [tickLogNormalized, if_neg h] using
      evalExpr_word_shl_by hq' (evalExpr_word_sub h127 hm') hb

end Benchmarks.UniswapV3.Pool
