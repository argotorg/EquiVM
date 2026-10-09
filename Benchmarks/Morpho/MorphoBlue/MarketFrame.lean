import Benchmarks.Morpho.MorphoBlue.MarketParamsCommon
import Benchmarks.Morpho.MorphoBlue.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

structure MarketLocals (p : MarketParamsWords) (locals : Store) : Prop where
  params : locals.get? "marketParams" = some p.value
  id : locals.get? "id" = some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id))
  market : locals.get? "market" = none
  position : locals.get? "position" = none
  feeRecipient : locals.get? "feeRecipient" = none

theorem MarketLocals.insert {p : MarketParamsWords} {locals : Store}
    (h : MarketLocals p locals) (name : Ident) (value : Value)
    (hn : name ≠ "marketParams" ∧ name ≠ "id" ∧ name ≠ "market" ∧ name ≠ "position" ∧ name ≠ "feeRecipient") :
    MarketLocals p (locals.insert name value) := by
  rcases hn with ⟨h0, h1, h2, h3, h4⟩
  constructor
  · rw [store_get_ne _ _ (by simpa only [beq_eq_false_iff_ne] using h0)]; exact h.params
  · rw [store_get_ne _ _ (by simpa only [beq_eq_false_iff_ne] using h1)]; exact h.id
  · rw [store_get_ne _ _ (by simpa only [beq_eq_false_iff_ne] using h2)]; exact h.market
  · rw [store_get_ne _ _ (by simpa only [beq_eq_false_iff_ne] using h3)]; exact h.position
  · rw [store_get_ne _ _ (by simpa only [beq_eq_false_iff_ne] using h4)]; exact h.feeRecipient

theorem MarketLocals.evalParams {p : MarketParamsWords} {locals : Store}
    (h : MarketLocals p locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "marketParams") = .ok p.value := by
  simp only [evalExpr?, h.params, EvalResult.ofOption]

theorem MarketLocals.evalId {p : MarketParamsWords} {locals : Store}
    (h : MarketLocals p locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "id") = .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id)) := by
  simp only [evalExpr?, h.id, EvalResult.ofOption]

theorem MarketLocals.evalField {p : MarketParamsWords} {locals : Store}
    (h : MarketLocals p locals) (imms : Store) (evm : EVM.State) (i : Fin 6) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"market", [.mindex (.var "id"), .field (marketFieldName i)]⟩) =
      .ok (.int (Int.ofNat (marketFieldWord evm.accountMap evm.executionEnv p.id i).toNat)) :=
  evalMorphoMarketField evm locals imms (.var "id") p.id i h.market (h.evalId imms evm)

theorem MarketLocals.evalIrm {p : MarketParamsWords} {locals : Store}
    (h : MarketLocals p locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.tupleGet (.var "marketParams") 3) = .ok (.address (AccountAddress.ofNat p.irm.toNat)) := by
  simp only [evalExpr?, h.evalParams, MarketParamsWords.value, tupleGetValue?,
    EvalResult.bind, EvalResult.ofOption, bind]
  rfl

theorem MarketLocals.evalIrmNonzero {p : MarketParamsWords} {locals : Store}
    (h : MarketLocals p locals) (hc : p.Canonical) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.binary .ne (.tupleGet (.var "marketParams") 3) (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (decide (p.irm ≠ ⟨0⟩))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), h.evalIrm]
  simp only [evalExpr?, pure, bind, EvalResult.bind, castValue?, EvalResult.ofOption,
    show ¬ (0 : Int) < 0 from by decide, ↓reduceIte, evalBinaryOp?]
  change EvalResult.ok (Value.bool (!(Value.address (AccountAddress.ofNat p.irm.toNat) ==
    Value.address (AccountAddress.ofNat (⟨0⟩ : UInt256).toNat)))) = _
  rw [canonicalAddress_beq _ _ hc.2.2.2 (by decide)]
  simp only [decide_not]

end Benchmarks.Morpho.MorphoBlue
