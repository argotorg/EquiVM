import Benchmarks.UniswapV4PoolManager.SwapStepRemainingWords
import Benchmarks.UniswapV4PoolManager.SwapStepFeeSource
import Benchmarks.UniswapV4PoolManager.WordSignedSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def swapStepRemainingExpr : Expr :=
  .cast (.cast (.binary .sub (.intLit 0) (.var "amountRemaining"))
    (.elem (.int (.sint ⟨256, by decide⟩)))) (.elem (.int (.uint ⟨256, by decide⟩)))

theorem swapStepRemainingSource {f : Frame} {evm : EVM.State} {remaining : UInt256}
    (hr : f.locals.get? "amountRemaining" = some (.int (EVM.signed remaining))) :
    evalExpr? config f evm swapStepRemainingExpr =
      .ok (.int (Int.ofNat (swapStepRemainingWord remaining).toNat)) := by
  have hn := evalSignedWordSub (x := ⟨0⟩)
    (show evalExpr? config f evm (.intLit 0) = .ok (.int (EVM.signed ⟨0⟩)) by
      simp only [evalExpr?, pure]
      rfl)
    (evalLocalValue hr)
  have hc := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩) hn
  simpa only [normalizeUnsignedSigned] using hc

def swapStepRemainingFeeExpr : Expr :=
  .cast (.binary .sub swapStepRemainingExpr (.var "amountIn")) (.elem (.int (.uint ⟨256, by decide⟩)))

theorem swapStepRemainingFeeSource {f : Frame} {evm : EVM.State} {remaining amount : UInt256}
    (hr : f.locals.get? "amountRemaining" = some (.int (EVM.signed remaining)))
    (ha : f.locals.get? "amountIn" = some (.int (Int.ofNat amount.toNat))) :
    evalExpr? config f evm swapStepRemainingFeeExpr =
      .ok (.int (Int.ofNat (swapStepRemainingFeeWord remaining amount).toNat)) :=
  evalWordSub (swapStepRemainingSource hr) (evalLocalValue ha)

def swapStepAvailableStmt : Stmt :=
  .internalCall "FullMath_mulDiv"
    [swapStepRemainingExpr, swapStepFeeComplementExpr, .intLit 1000000] "amountRemainingLessFee"

theorem swapStepAvailableSource {f : Frame} {evm : EVM.State} {remaining fee : UInt256}
    (hf : f.contract = contract)
    (hr : f.locals.get? "amountRemaining" = some (.int (EVM.signed remaining)))
    (hp : f.locals.get? "_feePips" = some (.int (Int.ofNat fee.toNat))) :
    ExecStmt config f evm swapStepAvailableStmt
      (if swapStepAvailableFits remaining fee then
        .ok (wordLocal f "amountRemainingLessFee" (swapStepAvailableWord remaining fee)) evm else .reverted) :=
  fullMathCall (a := swapStepRemainingWord remaining) (b := swapStepFeeComplement fee) (d := fullMathPPM)
    hf (swapStepRemainingSource hr) (swapStepFeeComplementSource hp)
    (by simp only [evalExpr?, pure]; rfl) "amountRemainingLessFee"

end Benchmarks.UniswapV4PoolManager
