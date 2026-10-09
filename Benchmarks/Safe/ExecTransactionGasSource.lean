import Benchmarks.Safe.ExecTransactionContext
import Benchmarks.Safe.WordExpressionSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def execGasScaled (safeGas : UInt256) : UInt256 :=
  UInt256.div (UInt256.shiftLeft safeGas ⟨6⟩) ⟨63⟩

def execGasMaximum (safeGas : UInt256) : UInt256 :=
  maximumWord (execGasScaled safeGas) (safeGas + ⟨2500⟩)

def execRequiredGas (safeGas : UInt256) : UInt256 := execGasMaximum safeGas + ⟨500⟩

def ExecGasFits (safeGas : UInt256) : Prop :=
  safeGas.toNat + 2500 < UInt256.size ∧ (execGasMaximum safeGas).toNat + 500 < UInt256.size

instance (safeGas : UInt256) : Decidable (ExecGasFits safeGas) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem safeEvalExecGasScaled {cfg : Config} {frame : Frame} {evm : EVM.State}
    {safeGas : UInt256}
    (he : evalExpr? cfg frame evm (.var "safeTxGas") = .ok (uint256Value safeGas)) :
    evalExpr? cfg frame evm (divE (shlE (.var "safeTxGas") (.intLit 6)) (.intLit 63)) =
      .ok (uint256Value (execGasScaled safeGas)) := by
  exact divSourceOk (shiftLeftSourceOk he (n := ⟨6⟩)
    (by simp [evalExpr?, uint256Value, pure]; decide +kernel) (by decide)) (b := ⟨63⟩)
    (by simp [evalExpr?, uint256Value, pure]; decide +kernel) (by decide)

theorem safeEvalExecGasMaximum {cfg : Config} {frame : Frame} {evm : EVM.State}
    {safeGas : UInt256}
    (he : evalExpr? cfg frame evm (.var "safeTxGas") = .ok (uint256Value safeGas))
    (hf : safeGas.toNat + 2500 < UInt256.size) :
    evalExpr? cfg frame evm
      (maxE (divE (shlE (.var "safeTxGas") (.intLit 6)) (.intLit 63))
        (add256 (.var "safeTxGas") (.intLit 2500))) =
      .ok (uint256Value (execGasMaximum safeGas)) := by
  exact maximumSourceOk (safeEvalExecGasScaled he)
    (checkedAddSourceOk he (b := ⟨2500⟩) (by simp [evalExpr?, uint256Value, pure]; decide +kernel)
      hf)

theorem safeEvalExecRequiredGas {cfg : Config} {frame : Frame} {evm : EVM.State}
    {safeGas : UInt256}
    (he : evalExpr? cfg frame evm (.var "safeTxGas") = .ok (uint256Value safeGas))
    (hf : ExecGasFits safeGas) :
    evalExpr? cfg frame evm requiredTransactionGasExpr =
      .ok (uint256Value (execRequiredGas safeGas)) :=
  checkedAddSourceOk (safeEvalExecGasMaximum he hf.1) (b := ⟨500⟩)
    (by simp [evalExpr?, uint256Value, pure]; decide +kernel) hf.2

theorem safeEvalExecRequiredGasRevert {cfg : Config} {frame : Frame} {evm : EVM.State}
    {safeGas : UInt256}
    (he : evalExpr? cfg frame evm (.var "safeTxGas") = .ok (uint256Value safeGas))
    (hf : ¬ ExecGasFits safeGas) :
    evalExpr? cfg frame evm requiredTransactionGasExpr = .revert := by
  by_cases hfirst : safeGas.toNat + 2500 < UInt256.size
  · have hsecond : UInt256.size ≤ (execGasMaximum safeGas).toNat + 500 := by
      simp only [ExecGasFits, hfirst, true_and] at hf
      omega
    exact checkedAddSourceOverflow (safeEvalExecGasMaximum he hfirst) (b := ⟨500⟩)
      (by simp [evalExpr?, uint256Value, pure]; decide +kernel) hsecond
  · have hd := safeEvalExecGasScaled he
    have ha : evalExpr? cfg frame evm (add256 (.var "safeTxGas") (.intLit 2500)) =
        .revert := checkedAddSourceOverflow he (b := ⟨2500⟩)
      (by simp [evalExpr?, uint256Value, pure]; decide +kernel) (by
        change UInt256.size ≤ safeGas.toNat + 2500
        omega)
    have hmax : evalExpr? cfg frame evm
        (maxE (divE (shlE (.var "safeTxGas") (.intLit 6)) (.intLit 63))
          (add256 (.var "safeTxGas") (.intLit 2500))) = .revert := by
      rw [maxE, evalExpr?, gtE, evalExpr_binary_nonshort (by decide) (by decide), hd]
      simp only [bind, EvalResult.bind, ha]
    rw [requiredTransactionGasExpr, add256, u256, evalExpr?, addE,
      evalExpr_binary_nonshort (by decide) (by decide), hmax]
    rfl

end Benchmarks.Safe
