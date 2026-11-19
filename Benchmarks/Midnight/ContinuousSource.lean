import Benchmarks.Midnight.RoleSource
import Benchmarks.Midnight.PackedWrites

/-! Shared bound and cast evaluation for continuous-fee updates. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def continuousFeeCapExpr : Expr :=
  .cast (.binary .div
    (.cast (.intLit 10000000000000000) (.elem (.int (.uint ⟨256, by decide⟩))))
    (.cast (.intLit 31536000) (.elem (.int (.uint ⟨256, by decide⟩)))))
    (.elem (.int packedUInt32Int))

def continuousFeeBoundExpr : Expr :=
  .binary .le (.var "newContinuousFee") continuousFeeCapExpr

theorem evalContinuousFeeCap {cfg : Config} {frame : Frame} {evm : EVM.State} :
    evalExpr? cfg frame evm continuousFeeCapExpr = .ok (.int 317097919) := by
  simp only [continuousFeeCapExpr, evalExpr?, castValue_int, EvalResult.ofOption,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  rfl

theorem evalContinuousFeeBound {frame : Frame} {evm : EVM.State} {value : UInt256}
    (hget : frame.locals.get? "newContinuousFee" = some (.int value.toNat)) :
    evalExpr? config frame evm continuousFeeBoundExpr =
      .ok (.bool (decide (value.toNat ≤ 317097919))) := by
  rw [continuousFeeBoundExpr,
    evalExpr_binary_nonshort (by decide : BinaryOp.le ≠ .and) (by decide : BinaryOp.le ≠ .or)]
  simp only [evalExpr?, hget, EvalResult.ofOption, EvalResult.bind, bind, evalContinuousFeeCap,
    evalBinaryOp?]
  norm_cast

theorem evalContinuousFeeCast {frame : Frame} {evm : EVM.State} {value : UInt256}
    (hget : frame.locals.get? "newContinuousFee" = some (.int value.toNat)) :
    evalExpr? config frame evm (.cast (.var "newContinuousFee") (.elem (.int packedUInt32Int))) =
      .ok (.int (Int.ofNat value.toNat % packedUInt32Modulus)) := by
  exact evalExpr_cast_int (by simp only [evalExpr?, hget, EvalResult.ofOption]; rfl)

end Benchmarks.Midnight
