import Benchmarks.Morpho.MorphoBlue.LiquidateLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

structure LiquidateEventLocals (p : MarketParamsWords) (account seized shares : UInt256) (data : ByteArray)
    (assets badAssets badShares : UInt256) (locals : Store) : Prop extends LiquidateLocals p account seized shares data locals where
  assets_eq : locals.get? "repaidAssets" = some (.int (Int.ofNat assets.toNat))
  badAssets_eq : locals.get? "badDebtAssets" = some (.int (Int.ofNat badAssets.toNat))
  badShares_eq : locals.get? "badDebtShares" = some (.int (Int.ofNat badShares.toNat))

theorem LiquidateEventLocals.insert {p account seized shares data assets badAssets badShares locals}
    (hl : LiquidateEventLocals p account seized shares data assets badAssets badShares locals) (name : Ident) (value : Value)
    (hn : name ≠ "marketParams" ∧ name ≠ "id" ∧ name ≠ "market" ∧ name ≠ "position" ∧ name ≠ "feeRecipient")
    (hv : name ≠ "borrower" ∧ name ≠ "seizedAssets" ∧ name ≠ "repaidShares" ∧ name ≠ "data")
    (hx : name ≠ "repaidAssets" ∧ name ≠ "badDebtAssets" ∧ name ≠ "badDebtShares") :
    LiquidateEventLocals p account seized shares data assets badAssets badShares (locals.insert name value) := by
  refine ⟨hl.toLiquidateLocals.insert name value hn hv, ?_, ?_, ?_⟩
  · rw [store_get_ne _ _ (by simp [hx.1])]; exact hl.assets_eq
  · rw [store_get_ne _ _ (by simp [hx.2.1])]; exact hl.badAssets_eq
  · rw [store_get_ne _ _ (by simp [hx.2.2])]; exact hl.badShares_eq

theorem LiquidateEventLocals.evalAssets {p account seized shares data assets badAssets badShares locals}
    (hl : LiquidateEventLocals p account seized shares data assets badAssets badShares locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "repaidAssets") =
      .ok (.int (Int.ofNat assets.toNat)) := by simp only [evalExpr?, hl.assets_eq, EvalResult.ofOption]

theorem LiquidateEventLocals.evalBadAssets {p account seized shares data assets badAssets badShares locals}
    (hl : LiquidateEventLocals p account seized shares data assets badAssets badShares locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "badDebtAssets") =
      .ok (.int (Int.ofNat badAssets.toNat)) := by simp only [evalExpr?, hl.badAssets_eq, EvalResult.ofOption]

theorem LiquidateEventLocals.evalBadShares {p account seized shares data assets badAssets badShares locals}
    (hl : LiquidateEventLocals p account seized shares data assets badAssets badShares locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "badDebtShares") =
      .ok (.int (Int.ofNat badShares.toNat)) := by simp only [evalExpr?, hl.badShares_eq, EvalResult.ofOption]

theorem LiquidateEventLocals.setBadShares {p account seized shares data assets badAssets badShares locals}
    (hl : LiquidateEventLocals p account seized shares data assets badAssets badShares locals) (value : UInt256) :
    LiquidateEventLocals p account seized shares data assets badAssets value
      (locals.insert "badDebtShares" (.int (Int.ofNat value.toNat))) := by
  refine ⟨hl.toLiquidateLocals.insert _ _ (by decide) (by decide), ?_, ?_, store_get_self _ _ _⟩
  · rw [store_get_ne _ _ (by decide)]; exact hl.assets_eq
  · rw [store_get_ne _ _ (by decide)]; exact hl.badAssets_eq

theorem LiquidateEventLocals.setBadAssets {p account seized shares data assets badAssets badShares locals}
    (hl : LiquidateEventLocals p account seized shares data assets badAssets badShares locals) (value : UInt256) :
    LiquidateEventLocals p account seized shares data assets value badShares
      (locals.insert "badDebtAssets" (.int (Int.ofNat value.toNat))) := by
  refine ⟨hl.toLiquidateLocals.insert _ _ (by decide) (by decide), ?_, store_get_self _ _ _, ?_⟩
  · rw [store_get_ne _ _ (by decide)]; exact hl.assets_eq
  · rw [store_get_ne _ _ (by decide)]; exact hl.badShares_eq

def liquidateBadBody : List Stmt := match liquidateTransition.body[30]! with | .ite _ yes _ => yes | _ => []

end Benchmarks.Morpho.MorphoBlue
