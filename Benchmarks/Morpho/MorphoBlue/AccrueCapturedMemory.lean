import Benchmarks.Morpho.MorphoBlue.WordComparisons
import Benchmarks.Morpho.MorphoBlue.AfterAccrueMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def accrueActive (p : MarketParamsWords) (evm : EVM.State) : Bool :=
  decide (p.irm ≠ ⟨0⟩ ∧ accrueElapsed evm.accountMap evm.executionEnv p ≠ ⟨0⟩)

def accrueActiveExpr : Expr := .binary .and
  (.binary .ne (.tupleGet (.var "marketParams") 3) (.cast (.intLit 0) (.elem .address)))
  (.binary .ne (.env .timestamp) (.storage ⟨"market", [.mindex (.var "id"), .field "lastUpdate"]⟩))

theorem evalAccrueActive (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (hc : p.Canonical) (hl : MarketLocals p locals) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm accrueActiveExpr =
      .ok (.bool (accrueActive p evm)) := by
  have ht : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.binary .ne (.env .timestamp) (.storage ⟨"market", [.mindex (.var "id"), .field "lastUpdate"]⟩)) =
      .ok (.bool (decide (accrueElapsed evm.accountMap evm.executionEnv p ≠ ⟨0⟩))) := by
    simpa only [accrueElapsed, ne_eq, u256_sub_eq_zero_iff_eq, marketFieldName] using
      (evalWordNeWord (show evalExpr? config { contract := contract, locals := locals, immutables := imms }
        evm (.env .timestamp) = .ok (.int (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)) from by simp only [evalExpr?, envValue, pure])
        (hl.evalField imms evm ⟨4, by decide⟩))
  rw [accrueActiveExpr, evalExpr?, hl.evalIrmNonzero hc imms evm]
  by_cases hi : p.irm ≠ ⟨0⟩
  · simp only [decide_eq_true hi, bind, EvalResult.bind, ht, pure]
    simp [accrueActive, hi]
  · simp only [decide_eq_false hi, bind, EvalResult.bind, pure]
    simp [accrueActive, hi]

theorem afterAccrueMemoryCost_active (p : MarketParamsWords) (before after : EVM.State) :
    afterAccrueMemoryCost (accrueActive p before) (marketFieldWord after.accountMap after.executionEnv p.id 5) =
      accrueMemoryCost p before after := by
  by_cases hi : p.irm = ⟨0⟩ <;> by_cases hz : accrueElapsed before.accountMap before.executionEnv p = ⟨0⟩ <;>
    simp only [afterAccrueMemoryCost, accrueActive, accrueMemoryCost, hi, hz, ne_eq,
      not_true_eq_false, not_false_eq_true, false_and, true_and, true_or, false_or, or_true, or_false,
      decide_false, decide_true, Bool.false_eq_true, ↓reduceIte]

theorem morphoAfterAccrueCapturedCall (p : MarketParamsWords) (base : Nat)
    (before evm : EVM.State) (locals imms : Store) (hl : MarketLocals p locals)
    (ha : locals.get? "__accrued" = some (.bool (accrueActive p before))) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "Solc_afterAccrueMemory" [.intLit (Int.ofNat base), .var "__accrued",
        .storage ⟨"market", [.mindex (.var "id"), .field "fee"]⟩] "__memory")
      (.ok { contract := contract, locals := locals.insert "__memory" (.int (Int.ofNat (base + accrueMemoryCost p before evm))), immutables := imms } evm) := by
  have hefee : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"market", [.mindex (.var "id"), .field "fee"]⟩) =
      .ok (.int (Int.ofNat (marketFieldWord evm.accountMap evm.executionEnv p.id 5).toNat)) := by
    simpa only [marketFieldName] using hl.evalField imms evm ⟨5, by decide⟩
  have hf := morphoAfterAccrueMemoryCall base (accrueActive p before)
    (marketFieldWord evm.accountMap evm.executionEnv p.id 5) evm locals imms
    [.intLit (Int.ofNat base), .var "__accrued", .storage ⟨"market", [.mindex (.var "id"), .field "fee"]⟩] "__memory"
    (by simp only [evalExprs?, hefee,
      evalExpr?, ha, EvalResult.ofOption, pure, bind, EvalResult.bind])
  simpa only [afterAccrueMemoryCost_active] using hf

end Benchmarks.Morpho.MorphoBlue
