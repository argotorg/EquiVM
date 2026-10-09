import Benchmarks.Morpho.MorphoBlue.SenderAuthorizedSource
import Benchmarks.Morpho.MorphoBlue.SupplySourceStart

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- Parameters shared by the collateral withdrawal source helpers.
def collateralTransferArgs (p : MarketParamsWords) (assets account receiver : UInt256) : Store :=
  ((((∅ : Store).insert "marketParams" p.value).insert "assets" (.int (Int.ofNat assets.toNat))).insert
    "onBehalf" (.address (AccountAddress.ofNat account.toNat))).insert
    "receiver" (.address (AccountAddress.ofNat receiver.toNat))

def collateralTransferFrame (p : MarketParamsWords) (assets account receiver : UInt256)
    (cd : ByteArray) (imms : Store) : Frame :=
  { contract := contract, immutables := imms,
    locals := ((collateralTransferArgs p assets account receiver).insert "__calldata" (.bytes cd)).insert "id"
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id)) }

structure CollateralTransferLocals (p : MarketParamsWords) (assets account receiver : UInt256)
    (locals : Store) : Prop extends MarketLocals p locals where
  assets_eq : locals.get? "assets" = some (.int (Int.ofNat assets.toNat))
  account_eq : locals.get? "onBehalf" = some (.address (AccountAddress.ofNat account.toNat))
  receiver_eq : locals.get? "receiver" = some (.address (AccountAddress.ofNat receiver.toNat))

theorem collateralTransferFrame_locals (p : MarketParamsWords) (assets account receiver : UInt256)
    (cd : ByteArray) (imms : Store) :
    CollateralTransferLocals p assets account receiver (collateralTransferFrame p assets account receiver cd imms).locals := by
  constructor
  · constructor <;> simp [collateralTransferFrame, collateralTransferArgs, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  all_goals simp [collateralTransferFrame, collateralTransferArgs, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]

theorem CollateralTransferLocals.insert {p assets account receiver locals}
    (hl : CollateralTransferLocals p assets account receiver locals) (name : Ident) (value : Value)
    (hn : name ≠ "marketParams" ∧ name ≠ "id" ∧ name ≠ "market" ∧ name ≠ "position" ∧ name ≠ "feeRecipient")
    (hv : name ≠ "assets" ∧ name ≠ "onBehalf" ∧ name ≠ "receiver") :
    CollateralTransferLocals p assets account receiver (locals.insert name value) := by
  refine ⟨hl.toMarketLocals.insert name value hn, ?_, ?_, ?_⟩
  · rw [store_get_ne _ _ (by simp [hv.1])]; exact hl.assets_eq
  · rw [store_get_ne _ _ (by simp [hv.2.1])]; exact hl.account_eq
  · rw [store_get_ne _ _ (by simp [hv.2.2])]; exact hl.receiver_eq

theorem CollateralTransferLocals.evalAssets {p assets account receiver locals}
    (hl : CollateralTransferLocals p assets account receiver locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "assets") =
      .ok (.int (Int.ofNat assets.toNat)) := by simp only [evalExpr?, hl.assets_eq, EvalResult.ofOption]

theorem CollateralTransferLocals.evalAccount {p assets account receiver locals}
    (hl : CollateralTransferLocals p assets account receiver locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "onBehalf") =
      .ok (.address (AccountAddress.ofNat account.toNat)) := by simp only [evalExpr?, hl.account_eq, EvalResult.ofOption]

theorem CollateralTransferLocals.evalReceiver {p assets account receiver locals}
    (hl : CollateralTransferLocals p assets account receiver locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "receiver") =
      .ok (.address (AccountAddress.ofNat receiver.toNat)) := by simp only [evalExpr?, hl.receiver_eq, EvalResult.ofOption]

def collateralTransferAuthorizedFrame (p : MarketParamsWords) (assets account receiver : UInt256)
    (evm : EVM.State) (imms : Store) : Frame :=
  let frame := collateralTransferFrame p assets account receiver evm.executionEnv.calldata imms
  { frame with locals := frame.locals.insert "__c1" (wordToElem .bool
      (senderAuthorizedWord evm.accountMap evm.executionEnv account)) }

def collateralTransferBeforeAccrue (p : MarketParamsWords) (assets account receiver : UInt256)
    (evm : EVM.State) (imms : Store) : Frame :=
  let frame := collateralTransferAuthorizedFrame p assets account receiver evm imms
  { frame with locals := frame.locals.insert "__accrued" (.bool (accrueActive p evm)) }

theorem collateralTransferAuthorizedFrame_locals (p : MarketParamsWords) (assets account receiver : UInt256)
    (evm : EVM.State) (imms : Store) :
    CollateralTransferLocals p assets account receiver (collateralTransferAuthorizedFrame p assets account receiver evm imms).locals :=
  (collateralTransferFrame_locals p assets account receiver evm.executionEnv.calldata imms).insert _ _ (by decide) (by decide)

theorem collateralTransferBeforeAccrue_locals (p : MarketParamsWords) (assets account receiver : UInt256)
    (evm : EVM.State) (imms : Store) :
    CollateralTransferLocals p assets account receiver (collateralTransferBeforeAccrue p assets account receiver evm imms).locals :=
  (collateralTransferAuthorizedFrame_locals p assets account receiver evm imms).insert _ _ (by decide) (by decide)

end Benchmarks.Morpho.MorphoBlue
