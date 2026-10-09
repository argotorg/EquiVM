import Benchmarks.Morpho.MorphoBlue.SupplyCollateralSourceStart
import Benchmarks.Morpho.MorphoBlue.SupplyGuards
import Benchmarks.Morpho.MorphoBlue.AccrueCapturedMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def supplyArgs (p : MarketParamsWords) (assets shares account : UInt256) (data : ByteArray) : Store :=
  (((((∅ : Store).insert "marketParams" p.value).insert "assets" (.int (Int.ofNat assets.toNat))).insert
    "shares" (.int (Int.ofNat shares.toNat))).insert
    "onBehalf" (.address (AccountAddress.ofNat account.toNat))).insert "data" (.bytes data)

def supplyFrame (p : MarketParamsWords) (assets shares account : UInt256) (data cd : ByteArray) (imms : Store) : Frame :=
  { contract := contract, immutables := imms,
    locals := ((supplyArgs p assets shares account data).insert "__calldata" (.bytes cd)).insert "id"
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id)) }

structure SupplyLocals (p : MarketParamsWords) (assets shares account : UInt256) (data : ByteArray)
    (locals : Store) : Prop extends SupplyCollateralLocals p assets account data locals where
  shares_eq : locals.get? "shares" = some (.int (Int.ofNat shares.toNat))

theorem supplyFrame_locals (p : MarketParamsWords) (assets shares account : UInt256)
    (data cd : ByteArray) (imms : Store) :
    SupplyLocals p assets shares account data (supplyFrame p assets shares account data cd imms).locals := by
  constructor
  · constructor
    · constructor <;> simp [supplyFrame, supplyArgs, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
    all_goals simp [supplyFrame, supplyArgs, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  · simp [supplyFrame, supplyArgs, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]

theorem SupplyLocals.insert {p assets shares account data locals}
    (hl : SupplyLocals p assets shares account data locals) (name : Ident) (value : Value)
    (hn : name ≠ "marketParams" ∧ name ≠ "id" ∧ name ≠ "market" ∧ name ≠ "position" ∧ name ≠ "feeRecipient")
    (hv : name ≠ "assets" ∧ name ≠ "onBehalf" ∧ name ≠ "data" ∧ name ≠ "shares") :
    SupplyLocals p assets shares account data (locals.insert name value) := by
  refine ⟨hl.toSupplyCollateralLocals.insert name value hn ⟨hv.1, hv.2.1, hv.2.2.1⟩, ?_⟩
  rw [store_get_ne _ _ (by simp [hv.2.2.2])]; exact hl.shares_eq

theorem SupplyLocals.evalShares {p assets shares account data locals}
    (hl : SupplyLocals p assets shares account data locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "shares") =
      .ok (.int (Int.ofNat shares.toNat)) := by simp only [evalExpr?, hl.shares_eq, EvalResult.ofOption]

def supplyInputFrame (p : MarketParamsWords) (assets shares account : UInt256) (data cd : ByteArray) (imms : Store) : Frame :=
  let frame := supplyFrame p assets shares account data cd imms
  { frame with locals := frame.locals.insert "__c1" (.bool (exactlyOneZero assets shares)) }

def supplyBeforeAccrue (p : MarketParamsWords) (assets shares account : UInt256) (data : ByteArray)
    (evm : EVM.State) (imms : Store) : Frame :=
  let frame := supplyInputFrame p assets shares account data evm.executionEnv.calldata imms
  { frame with locals := frame.locals.insert "__accrued" (.bool (accrueActive p evm)) }

theorem supplyInputFrame_locals (p : MarketParamsWords) (assets shares account : UInt256)
    (data cd : ByteArray) (imms : Store) :
    SupplyLocals p assets shares account data (supplyInputFrame p assets shares account data cd imms).locals :=
  (supplyFrame_locals p assets shares account data cd imms).insert _ _ (by decide) (by decide)

theorem supplyBeforeAccrue_locals (p : MarketParamsWords) (assets shares account : UInt256)
    (data : ByteArray) (evm : EVM.State) (imms : Store) :
    SupplyLocals p assets shares account data (supplyBeforeAccrue p assets shares account data evm imms).locals :=
  (supplyInputFrame_locals p assets shares account data evm.executionEnv.calldata imms).insert _ _ (by decide) (by decide)

theorem morphoSupplyPrelude (p : MarketParamsWords) (assets shares account : UInt256) (data : ByteArray)
    (hc : p.Canonical) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm { contract := contract, locals := supplyArgs p assets shares account data, immutables := imms }
      supplyTransition.body (supplyFrame p assets shares account data evm.executionEnv.calldata imms)
      (supplyTransition.body.drop 4) := by
  refine ⟨fun h ↦ (calldataPrelude_ok hcv hsize).run (ExecBlock.consNormal ?_ h)⟩
  exact morphoMarketParamsIdCall p hc evm _ imms (.var "marketParams") "id"
    (by simp [evalExpr?, supplyArgs, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, EvalResult.ofOption])

theorem morphoSupplyExactlyOneZero (p : MarketParamsWords) (assets shares account : UInt256)
    (data : ByteArray) (evm : EVM.State) (imms : Store) :
    ExecStmt config (supplyFrame p assets shares account data evm.executionEnv.calldata imms) evm
      supplyTransition.body[5]!
      (.ok (supplyInputFrame p assets shares account data evm.executionEnv.calldata imms) evm) := by
  have hl := supplyFrame_locals p assets shares account data evm.executionEnv.calldata imms
  apply morphoExactlyOneZeroCall
  have ha := hl.evalAssets imms evm
  have hs := hl.evalShares imms evm
  dsimp only [supplyFrame] at ha hs
  simp only [evalExprs?, ha, hs, pure, bind, EvalResult.bind]

theorem morphoSupplySourceInput (p : MarketParamsWords) (assets shares account : UInt256) (data : ByteArray)
    (hc : p.Canonical) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hg : marketFieldWord evm.accountMap evm.executionEnv p.id 4 ≠ ⟨0⟩) :
    ABlock config evm { contract := contract, locals := supplyArgs p assets shares account data, immutables := imms }
      supplyTransition.body (supplyInputFrame p assets shares account data evm.executionEnv.calldata imms)
      (supplyTransition.body.drop 6) := by
  have hl := supplyFrame_locals p assets shares account data evm.executionEnv.calldata imms
  have pref := (morphoSupplyPrelude p assets shares account data hc evm imms hcv hsize).requireStep
    (by simpa only [decide_eq_true hg] using evalWordNeZero (hl.evalField imms evm ⟨4, by decide⟩))
  exact ⟨fun h ↦ pref.run (ExecBlock.consNormal (morphoSupplyExactlyOneZero p assets shares account data evm imms) h)⟩

theorem supplyInputFrame_eval_c1 (p : MarketParamsWords) (assets shares account : UInt256)
    (data cd : ByteArray) (evm : EVM.State) (imms : Store) :
    evalExpr? config (supplyInputFrame p assets shares account data cd imms) evm (.var "__c1") =
      .ok (.bool (exactlyOneZero assets shares)) := by
  simp only [evalExpr?, supplyInputFrame, store_get_self, EvalResult.ofOption]

theorem morphoSupplySourceGuards (p : MarketParamsWords) (assets shares account : UInt256) (data : ByteArray)
    (hc : p.Canonical) (ha : account.toNat < EVM.addressModulus) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hg : SupplyGuards evm.accountMap evm.executionEnv p assets shares account) :
    ABlock config evm { contract := contract, locals := supplyArgs p assets shares account data, immutables := imms }
      supplyTransition.body (supplyBeforeAccrue p assets shares account data evm imms)
      (supplyTransition.body.drop 9) := by
  have hl := supplyInputFrame_locals p assets shares account data evm.executionEnv.calldata imms
  exact (((morphoSupplySourceInput p assets shares account data hc evm imms hcv hsize hg.1).requireStep
    (by rw [supplyInputFrame_eval_c1, hg.2.1])).requireStep
    (by simpa only [decide_eq_true hg.2.2] using evalCanonicalAddressNeZero ha (hl.evalAccount imms evm))).letStep
    (evalAccrueActive p _ imms evm hc hl.toMarketLocals)

theorem morphoSupplySourceReject (p : MarketParamsWords) (assets shares account : UInt256) (data : ByteArray)
    (hc : p.Canonical) (ha : account.toNat < EVM.addressModulus) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hg : ¬ SupplyGuards evm.accountMap evm.executionEnv p assets shares account) :
    ExecTransitionBody config contract evm (supplyArgs p assets shares account data)
      supplyTransition.body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  by_cases hcreated : marketFieldWord evm.accountMap evm.executionEnv p.id 4 ≠ ⟨0⟩
  swap
  · have hl := supplyFrame_locals p assets shares account data evm.executionEnv.calldata imms
    exact (morphoSupplyPrelude p assets shares account data hc evm imms hcv hsize).requireRevert
      (by simpa only [decide_eq_false hcreated] using evalWordNeZero (hl.evalField imms evm ⟨4, by decide⟩))
  have pref := morphoSupplySourceInput p assets shares account data hc evm imms hcv hsize hcreated
  by_cases hz : exactlyOneZero assets shares = true
  swap
  · exact pref.requireRevert (by rw [supplyInputFrame_eval_c1, Bool.eq_false_iff.mpr hz])
  have hl := supplyInputFrame_locals p assets shares account data evm.executionEnv.calldata imms
  exact (pref.requireStep (by rw [supplyInputFrame_eval_c1, hz])).requireRevert
    (by simpa only [decide_eq_false (fun hn ↦ hg ⟨hcreated, hz, hn⟩)] using
      evalCanonicalAddressNeZero ha (hl.evalAccount imms evm))

end Benchmarks.Morpho.MorphoBlue
