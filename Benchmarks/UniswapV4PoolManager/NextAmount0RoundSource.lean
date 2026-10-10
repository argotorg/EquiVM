import Benchmarks.UniswapV4PoolManager.NextAmount0Words
import Benchmarks.UniswapV4PoolManager.FullMathRoundSource
import Benchmarks.UniswapV4PoolManager.SafeCast160Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def nextAmount0RoundName (checked : Bool) : Ident := if checked then "__c2" else "__c0"
def nextAmount0RoundStmts (checked : Bool) : List Stmt :=
  [.internalCall "FullMath_mulDivRoundingUp" [.var "numerator1", .var "sqrtPX96", .var "denominator"]
    (nextAmount0RoundName checked)] ++
  if checked then [.internalCall "SafeCast_toUint160" [.var "__c2"] "__c3", .return [.var "__c3"]]
  else [.return [.cast (.var "__c0") (.elem (.int (.uint ⟨160, by decide⟩)))]]

theorem nextAmount0RoundSource {f : Frame} {evm : EVM.State} {n price d : UInt256}
    (checked : Bool) (hf : f.contract = contract)
    (hn : f.locals.get? "numerator1" = some (.int (Int.ofNat n.toNat)))
    (hp : f.locals.get? "sqrtPX96" = some (.int (Int.ofNat price.toNat)))
    (hd : f.locals.get? "denominator" = some (.int (Int.ofNat d.toNat))) :
    ∃ f', ExecBlock config f evm (nextAmount0RoundStmts checked)
      (if nextAmount0RoundFits n price d checked then
        .returned f' evm (some [.int (Int.ofNat (nextAmount0RoundWord n price d checked).toNat)])
       else .reverted) := by
  have hc := fullMathRoundCall (f := f) (evm := evm) hf (evalLocalValue hn) (evalLocalValue hp)
    (evalLocalValue hd) (nextAmount0RoundName checked)
  by_cases hfit : fullMathRoundFits n price d
  · rw [if_pos hfit] at hc
    cases checked with
    | false =>
      simp only [nextAmount0RoundFits, hfit, Bool.false_eq_true, if_false, and_self, if_true, nextAmount0RoundWord]
      let f1 := wordLocal f "__c0" (fullMathRoundWord n price d)
      have he := evalExpr_cast_int (intType := .uint ⟨160, by decide⟩)
        (wordLocal_eval (cfg := config) (f := f) (evm := evm) (name := "__c0") (w := fullMathRoundWord n price d))
      rw [normalizeUintWord ⟨160, by decide⟩ _ solcAddrMask rfl] at he
      exact ⟨f1, ExecBlock.consNormal hc (ABlock.start.returns he)⟩
    | true =>
      let f1 := wordLocal f "__c2" (fullMathRoundWord n price d)
      have hs := uintToUint160Call (f := f1) (evm := evm) hf wordLocal_eval "__c3"
      simp only [nextAmount0RoundFits, hfit, if_true, true_and, nextAmount0RoundWord]
      by_cases h160 : (fullMathRoundWord n price d).toNat < 2^160
      · rw [if_pos h160] at hs
        simp only [if_pos h160]
        exact ⟨wordLocal f1 "__c3" (fullMathRoundWord n price d), ExecBlock.consNormal hc
          (ExecBlock.consNormal hs (ABlock.start.returns wordLocal_eval))⟩
      · rw [if_neg h160] at hs
        simp only [if_neg h160]
        exact ⟨f1, ExecBlock.consNormal hc (ExecBlock.consRevert hs)⟩
  · rw [if_neg hfit] at hc
    simp only [nextAmount0RoundFits, hfit, false_and, if_false]
    exact ⟨f, ExecBlock.consRevert hc⟩

end Benchmarks.UniswapV4PoolManager
