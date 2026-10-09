import Benchmarks.Morpho.MorphoBlue.MarketFrame
import Benchmarks.Morpho.MorphoBlue.AssetsUpSource
import Benchmarks.Morpho.MorphoBlue.WadSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: widening a canonical word to uint256 preserves its source value.
theorem evalCastUint256Word {cfg : Config} {frame : Frame} {evm : EVM.State}
    {e : Expr} {w : UInt256}
    (he : evalExpr? cfg frame evm e = .ok (.int (Int.ofNat w.toNat))) :
    evalExpr? cfg frame evm (.cast e (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat w.toNat)) := by
  rw [evalExpr_cast_int he]
  change EvalResult.ok (Value.int (Int.ofNat (w.toNat % UInt256.size))) = _
  have hw : w.toNat < UInt256.size := w.val.isLt
  rw [Nat.mod_eq_of_lt hw]

structure HealthyLocals (p : MarketParamsWords) (account : UInt256) (locals : Store) : Prop extends MarketLocals p locals where
  borrower : locals.get? "borrower" = some (.address (AccountAddress.ofNat account.toNat))

theorem HealthyLocals.insert {p account locals} (hl : HealthyLocals p account locals)
    (name : Ident) (value : Value)
    (hn : name ≠ "marketParams" ∧ name ≠ "id" ∧ name ≠ "market" ∧ name ≠ "position" ∧ name ≠ "feeRecipient")
    (ha : name ≠ "borrower") : HealthyLocals p account (locals.insert name value) := by
  refine ⟨hl.toMarketLocals.insert name value hn, ?_⟩
  rw [store_get_ne _ _ (by simp [ha])]
  exact hl.borrower

theorem HealthyLocals.evalBorrower {p account locals} (hl : HealthyLocals p account locals)
    (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "borrower") =
      .ok (.address (AccountAddress.ofNat account.toNat)) := by
  simp only [evalExpr?, hl.borrower, EvalResult.ofOption]

theorem HealthyLocals.evalPosition {p account locals} (hl : HealthyLocals p account locals)
    (imms : Store) (evm : EVM.State) (i : Fin 3) (hc : account.toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"position", [.mindex (.var "id"), .mindex (.var "borrower"), .field (positionFieldName i)]⟩) =
      .ok (.int (Int.ofNat (positionFieldWord evm.accountMap evm.executionEnv p.id account i).toNat)) :=
  evalMorphoPositionField evm locals imms _ _ p.id account i hl.position (hl.evalId imms evm) (hl.evalBorrower imms evm) hc

theorem MarketLocals.evalLltv {p locals} (hl : MarketLocals p locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.tupleGet (.var "marketParams") 4) = .ok (.int (Int.ofNat p.lltv.toNat)) := by
  simp only [evalExpr?, hl.evalParams, MarketParamsWords.value, tupleGetValue?,
    EvalResult.bind, EvalResult.ofOption, bind]
  rfl

def healthyFrame (p : MarketParamsWords) (account : UInt256) (imms : Store) : Frame :=
  { contract := contract, immutables := imms,
    locals := (((∅ : Store).insert "borrower" (.address (AccountAddress.ofNat account.toNat))).insert
      "id" (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id))).insert "marketParams" p.value }

def healthyPriceFrame (p : MarketParamsWords) (account price : UInt256) (imms : Store) : Frame :=
  { contract := contract, immutables := imms,
    locals := ((((∅ : Store).insert "collateralPrice" (.int (Int.ofNat price.toNat))).insert
      "borrower" (.address (AccountAddress.ofNat account.toNat))).insert
      "id" (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id))).insert "marketParams" p.value }

theorem healthyFrame_locals (p : MarketParamsWords) (account : UInt256) (imms : Store) :
    HealthyLocals p account (healthyFrame p account imms).locals := by
  constructor
  · constructor <;> simp [healthyFrame, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  · simp [healthyFrame, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]

theorem healthyPriceFrame_locals (p : MarketParamsWords) (account price : UInt256) (imms : Store) :
    HealthyLocals p account (healthyPriceFrame p account price imms).locals := by
  constructor
  · constructor <;> simp [healthyPriceFrame, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  · simp [healthyPriceFrame, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]

def oraclePriceScale : UInt256 := UInt256.ofNat 1000000000000000000000000000000000000

def healthyBorrowed (σ : AccountMap) (ee : ExecutionEnv) (p : MarketParamsWords) (account : UInt256) : UInt256 :=
  assetsUpWord (positionFieldWord σ ee p.id account 1) (marketFieldWord σ ee p.id 2) (marketFieldWord σ ee p.id 3)

def healthyCollateralValue (σ : AccountMap) (ee : ExecutionEnv) (p : MarketParamsWords) (account price : UInt256) : UInt256 :=
  UInt256.div (UInt256.mul (positionFieldWord σ ee p.id account 2) price) oraclePriceScale

def healthyMaxBorrow (σ : AccountMap) (ee : ExecutionEnv) (p : MarketParamsWords) (account price : UInt256) : UInt256 :=
  wMulDownResult (healthyCollateralValue σ ee p account price) p.lltv

def HealthyPriceFits (σ : AccountMap) (ee : ExecutionEnv) (p : MarketParamsWords) (account price : UInt256) : Prop :=
  AssetsUpFits (positionFieldWord σ ee p.id account 1) (marketFieldWord σ ee p.id 2) (marketFieldWord σ ee p.id 3) ∧
  (positionFieldWord σ ee p.id account 2).toNat * price.toNat < UInt256.size ∧
  (healthyCollateralValue σ ee p account price).toNat * p.lltv.toNat < UInt256.size

def healthyPriceResult (σ : AccountMap) (ee : ExecutionEnv) (p : MarketParamsWords) (account price : UInt256) : Bool :=
  decide ((healthyBorrowed σ ee p account).toNat ≤ (healthyMaxBorrow σ ee p account price).toNat)

end Benchmarks.Morpho.MorphoBlue
