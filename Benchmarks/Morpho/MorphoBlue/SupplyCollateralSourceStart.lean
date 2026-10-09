import Benchmarks.Morpho.MorphoBlue.WordComparisons
import Benchmarks.Morpho.MorphoBlue.SupplyCollateralGuards

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def supplyCollateralArgs (p : MarketParamsWords) (assets account : UInt256) (data : ByteArray) : Store :=
  ((((∅ : Store).insert "marketParams" p.value).insert "assets" (.int (Int.ofNat assets.toNat))).insert
    "onBehalf" (.address (AccountAddress.ofNat account.toNat))).insert "data" (.bytes data)

def supplyCollateralFrame (p : MarketParamsWords) (assets account : UInt256) (data cd : ByteArray) (imms : Store) : Frame :=
  { contract := contract, immutables := imms,
    locals := ((supplyCollateralArgs p assets account data).insert "__calldata" (.bytes cd)).insert "id"
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id)) }

structure SupplyCollateralLocals (p : MarketParamsWords) (assets account : UInt256) (data : ByteArray)
    (locals : Store) : Prop extends MarketLocals p locals where
  assets_eq : locals.get? "assets" = some (.int (Int.ofNat assets.toNat))
  account_eq : locals.get? "onBehalf" = some (.address (AccountAddress.ofNat account.toNat))
  data_eq : locals.get? "data" = some (.bytes data)

theorem supplyCollateralFrame_locals (p : MarketParamsWords) (assets account : UInt256)
    (data cd : ByteArray) (imms : Store) :
    SupplyCollateralLocals p assets account data (supplyCollateralFrame p assets account data cd imms).locals := by
  constructor
  · constructor <;> simp [supplyCollateralFrame, supplyCollateralArgs,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  all_goals simp [supplyCollateralFrame, supplyCollateralArgs,
    Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]

theorem SupplyCollateralLocals.insert {p assets account data locals}
    (hl : SupplyCollateralLocals p assets account data locals) (name : Ident) (value : Value)
    (hn : name ≠ "marketParams" ∧ name ≠ "id" ∧ name ≠ "market" ∧ name ≠ "position" ∧ name ≠ "feeRecipient")
    (hv : name ≠ "assets" ∧ name ≠ "onBehalf" ∧ name ≠ "data") :
    SupplyCollateralLocals p assets account data (locals.insert name value) := by
  refine ⟨hl.toMarketLocals.insert name value hn, ?_, ?_, ?_⟩
  · rw [store_get_ne _ _ (by simp [hv.1])]; exact hl.assets_eq
  · rw [store_get_ne _ _ (by simp [hv.2.1])]; exact hl.account_eq
  · rw [store_get_ne _ _ (by simp [hv.2.2])]; exact hl.data_eq

theorem SupplyCollateralLocals.evalAssets {p assets account data locals}
    (hl : SupplyCollateralLocals p assets account data locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "assets") =
      .ok (.int (Int.ofNat assets.toNat)) := by simp only [evalExpr?, hl.assets_eq, EvalResult.ofOption]

theorem SupplyCollateralLocals.evalAccount {p assets account data locals}
    (hl : SupplyCollateralLocals p assets account data locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "onBehalf") =
      .ok (.address (AccountAddress.ofNat account.toNat)) := by simp only [evalExpr?, hl.account_eq, EvalResult.ofOption]

theorem morphoSupplyCollateralPrelude (p : MarketParamsWords) (assets account : UInt256) (data : ByteArray)
    (hc : p.Canonical) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm { contract := contract, locals := supplyCollateralArgs p assets account data, immutables := imms }
      supplyCollateralTransition.body (supplyCollateralFrame p assets account data evm.executionEnv.calldata imms)
      (supplyCollateralTransition.body.drop 4) := by
  refine ⟨fun h => (calldataPrelude_ok hcv hsize).run (ExecBlock.consNormal ?_ h)⟩
  exact morphoMarketParamsIdCall p hc evm _ imms (.var "marketParams") "id"
    (by simp [evalExpr?, supplyCollateralArgs, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert,
      EvalResult.ofOption])

theorem morphoSupplyCollateralSourceGuards (p : MarketParamsWords) (assets account : UInt256) (data : ByteArray)
    (hc : p.Canonical) (ha : account.toNat < EVM.addressModulus) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hg : SupplyCollateralGuards evm.accountMap evm.executionEnv p assets account) :
    ABlock config evm { contract := contract, locals := supplyCollateralArgs p assets account data, immutables := imms }
      supplyCollateralTransition.body (supplyCollateralFrame p assets account data evm.executionEnv.calldata imms)
      (supplyCollateralTransition.body.drop 7) := by
  have hl := supplyCollateralFrame_locals p assets account data evm.executionEnv.calldata imms
  exact (((morphoSupplyCollateralPrelude p assets account data hc evm imms hcv hsize).requireStep
    (by simpa only [decide_eq_true hg.1] using evalWordNeZero (hl.evalField imms evm ⟨4, by decide⟩))).requireStep
    (by simpa only [decide_eq_true hg.2.1] using evalWordNeZero (hl.evalAssets imms evm))).requireStep
    (by simpa only [decide_eq_true hg.2.2] using evalCanonicalAddressNeZero ha (hl.evalAccount imms evm))

theorem morphoSupplyCollateralSourceReject (p : MarketParamsWords) (assets account : UInt256) (data : ByteArray)
    (hc : p.Canonical) (ha : account.toNat < EVM.addressModulus) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hg : ¬ SupplyCollateralGuards evm.accountMap evm.executionEnv p assets account) :
    ExecTransitionBody config contract evm (supplyCollateralArgs p assets account data)
      supplyCollateralTransition.body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  have hl := supplyCollateralFrame_locals p assets account data evm.executionEnv.calldata imms
  have pref := morphoSupplyCollateralPrelude p assets account data hc evm imms hcv hsize
  by_cases hcreated : marketFieldWord evm.accountMap evm.executionEnv p.id 4 ≠ ⟨0⟩
  swap
  · exact pref.requireRevert (by simpa only [decide_eq_false hcreated] using
        (evalWordNeZero (hl.evalField imms evm ⟨4, by decide⟩)))
  have pref1 := pref.requireStep (by simpa only [decide_eq_true hcreated] using
      (evalWordNeZero (hl.evalField imms evm ⟨4, by decide⟩)))
  by_cases hz : assets ≠ ⟨0⟩
  swap
  · exact pref1.requireRevert (by simpa only [decide_eq_false hz] using evalWordNeZero (hl.evalAssets imms evm))
  exact (pref1.requireStep (by simpa only [decide_eq_true hz] using evalWordNeZero (hl.evalAssets imms evm))).requireRevert
    (by simpa only [decide_eq_false (fun hn => hg ⟨hcreated, hz, hn⟩)] using
      (evalCanonicalAddressNeZero ha (hl.evalAccount imms evm)))

end Benchmarks.Morpho.MorphoBlue
