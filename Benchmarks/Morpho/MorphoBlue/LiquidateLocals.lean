import Benchmarks.Morpho.MorphoBlue.HealthyLocals
import Benchmarks.Morpho.MorphoBlue.SupplySourceStart

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def liquidateArgs (p : MarketParamsWords) (account seized shares : UInt256) (data : ByteArray) : Store :=
  (((((∅ : Store).insert "marketParams" p.value).insert "borrower"
    (.address (AccountAddress.ofNat account.toNat))).insert "seizedAssets"
    (.int (Int.ofNat seized.toNat))).insert "repaidShares" (.int (Int.ofNat shares.toNat))).insert "data" (.bytes data)

def liquidateFrame (p : MarketParamsWords) (account seized shares : UInt256)
    (data cd : ByteArray) (imms : Store) : Frame :=
  { contract := contract, immutables := imms,
    locals := ((liquidateArgs p account seized shares data).insert "__calldata" (.bytes cd)).insert "id"
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id)) }

structure LiquidateLocals (p : MarketParamsWords) (account seized shares : UInt256) (data : ByteArray)
    (locals : Store) : Prop extends HealthyLocals p account locals where
  seized_eq : locals.get? "seizedAssets" = some (.int (Int.ofNat seized.toNat))
  shares_eq : locals.get? "repaidShares" = some (.int (Int.ofNat shares.toNat))
  data_eq : locals.get? "data" = some (.bytes data)

theorem liquidateFrame_locals (p : MarketParamsWords) (account seized shares : UInt256)
    (data cd : ByteArray) (imms : Store) :
    LiquidateLocals p account seized shares data (liquidateFrame p account seized shares data cd imms).locals := by
  constructor
  · constructor
    · constructor <;> simp [liquidateFrame, liquidateArgs, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
    · simp [liquidateFrame, liquidateArgs, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  all_goals simp [liquidateFrame, liquidateArgs, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]

theorem LiquidateLocals.insert {p account seized shares data locals}
    (hl : LiquidateLocals p account seized shares data locals) (name : Ident) (value : Value)
    (hn : name ≠ "marketParams" ∧ name ≠ "id" ∧ name ≠ "market" ∧ name ≠ "position" ∧ name ≠ "feeRecipient")
    (hv : name ≠ "borrower" ∧ name ≠ "seizedAssets" ∧ name ≠ "repaidShares" ∧ name ≠ "data") :
    LiquidateLocals p account seized shares data (locals.insert name value) := by
  refine ⟨hl.toHealthyLocals.insert name value hn hv.1, ?_, ?_, ?_⟩
  · rw [store_get_ne _ _ (by simp [hv.2.1])]; exact hl.seized_eq
  · rw [store_get_ne _ _ (by simp [hv.2.2.1])]; exact hl.shares_eq
  · rw [store_get_ne _ _ (by simp [hv.2.2.2])]; exact hl.data_eq

theorem LiquidateLocals.evalSeized {p account seized shares data locals}
    (hl : LiquidateLocals p account seized shares data locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "seizedAssets") =
      .ok (.int (Int.ofNat seized.toNat)) := by simp only [evalExpr?, hl.seized_eq, EvalResult.ofOption]

theorem LiquidateLocals.evalShares {p account seized shares data locals}
    (hl : LiquidateLocals p account seized shares data locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "repaidShares") =
      .ok (.int (Int.ofNat shares.toNat)) := by simp only [evalExpr?, hl.shares_eq, EvalResult.ofOption]

def liquidateInputFrame (p : MarketParamsWords) (account seized shares : UInt256)
    (data cd : ByteArray) (imms : Store) : Frame :=
  let frame := liquidateFrame p account seized shares data cd imms
  { frame with locals := frame.locals.insert "__c1" (.bool (exactlyOneZero seized shares)) }

def liquidateBeforeAccrue (p : MarketParamsWords) (account seized shares : UInt256) (data : ByteArray)
    (evm : EVM.State) (imms : Store) : Frame :=
  let frame := liquidateInputFrame p account seized shares data evm.executionEnv.calldata imms
  { frame with locals := frame.locals.insert "__accrued" (.bool (accrueActive p evm)) }

theorem liquidateInputFrame_locals (p : MarketParamsWords) (account seized shares : UInt256)
    (data cd : ByteArray) (imms : Store) :
    LiquidateLocals p account seized shares data (liquidateInputFrame p account seized shares data cd imms).locals :=
  (liquidateFrame_locals p account seized shares data cd imms).insert _ _ (by decide) (by decide)

theorem liquidateBeforeAccrue_locals (p : MarketParamsWords) (account seized shares : UInt256)
    (data : ByteArray) (evm : EVM.State) (imms : Store) :
    LiquidateLocals p account seized shares data (liquidateBeforeAccrue p account seized shares data evm imms).locals :=
  (liquidateInputFrame_locals p account seized shares data evm.executionEnv.calldata imms).insert _ _ (by decide) (by decide)

theorem LiquidateLocals.setShares {p account seized shares data locals}
    (hl : LiquidateLocals p account seized shares data locals) (newShares : UInt256) :
    LiquidateLocals p account seized newShares data (locals.insert "repaidShares" (.int (Int.ofNat newShares.toNat))) := by
  refine ⟨hl.toHealthyLocals.insert _ _ (by decide) (by decide), ?_, store_get_self _ _ _, ?_⟩
  · rw [store_get_ne _ _ (by decide)]; exact hl.seized_eq
  · rw [store_get_ne _ _ (by decide)]; exact hl.data_eq

theorem LiquidateLocals.setSeized {p account seized shares data locals}
    (hl : LiquidateLocals p account seized shares data locals) (newSeized : UInt256) :
    LiquidateLocals p account newSeized shares data (locals.insert "seizedAssets" (.int (Int.ofNat newSeized.toNat))) := by
  refine ⟨hl.toHealthyLocals.insert _ _ (by decide) (by decide), store_get_self _ _ _, ?_, ?_⟩
  · rw [store_get_ne _ _ (by decide)]; exact hl.shares_eq
  · rw [store_get_ne _ _ (by decide)]; exact hl.data_eq

end Benchmarks.Morpho.MorphoBlue
