import Benchmarks.Morpho.MorphoBlue.SenderAuthorizedSource
import Benchmarks.Morpho.MorphoBlue.SupplySourceStart

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- Shared source parameters for borrow and withdraw.
def marketTransferArgs (p : MarketParamsWords) (assets shares account receiver : UInt256) : Store :=
  (((((∅ : Store).insert "marketParams" p.value).insert "assets" (.int (Int.ofNat assets.toNat))).insert
    "shares" (.int (Int.ofNat shares.toNat))).insert
    "onBehalf" (.address (AccountAddress.ofNat account.toNat))).insert
    "receiver" (.address (AccountAddress.ofNat receiver.toNat))

def marketTransferFrame (p : MarketParamsWords) (assets shares account receiver : UInt256)
    (cd : ByteArray) (imms : Store) : Frame :=
  { contract := contract, immutables := imms,
    locals := ((marketTransferArgs p assets shares account receiver).insert "__calldata" (.bytes cd)).insert "id"
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id)) }

structure MarketTransferLocals (p : MarketParamsWords) (assets shares account receiver : UInt256)
    (locals : Store) : Prop extends MarketLocals p locals where
  assets_eq : locals.get? "assets" = some (.int (Int.ofNat assets.toNat))
  shares_eq : locals.get? "shares" = some (.int (Int.ofNat shares.toNat))
  account_eq : locals.get? "onBehalf" = some (.address (AccountAddress.ofNat account.toNat))
  receiver_eq : locals.get? "receiver" = some (.address (AccountAddress.ofNat receiver.toNat))

theorem marketTransferFrame_locals (p : MarketParamsWords) (assets shares account receiver : UInt256)
    (cd : ByteArray) (imms : Store) :
    MarketTransferLocals p assets shares account receiver (marketTransferFrame p assets shares account receiver cd imms).locals := by
  constructor
  · constructor <;> simp [marketTransferFrame, marketTransferArgs, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  all_goals simp [marketTransferFrame, marketTransferArgs, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]

theorem MarketTransferLocals.insert {p assets shares account receiver locals}
    (hl : MarketTransferLocals p assets shares account receiver locals) (name : Ident) (value : Value)
    (hn : name ≠ "marketParams" ∧ name ≠ "id" ∧ name ≠ "market" ∧ name ≠ "position" ∧ name ≠ "feeRecipient")
    (hv : name ≠ "assets" ∧ name ≠ "shares" ∧ name ≠ "onBehalf" ∧ name ≠ "receiver") :
    MarketTransferLocals p assets shares account receiver (locals.insert name value) := by
  refine ⟨hl.toMarketLocals.insert name value hn, ?_, ?_, ?_, ?_⟩
  · rw [store_get_ne _ _ (by simp [hv.1])]; exact hl.assets_eq
  · rw [store_get_ne _ _ (by simp [hv.2.1])]; exact hl.shares_eq
  · rw [store_get_ne _ _ (by simp [hv.2.2.1])]; exact hl.account_eq
  · rw [store_get_ne _ _ (by simp [hv.2.2.2])]; exact hl.receiver_eq

theorem MarketTransferLocals.evalAssets {p assets shares account receiver locals}
    (hl : MarketTransferLocals p assets shares account receiver locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "assets") =
      .ok (.int (Int.ofNat assets.toNat)) := by simp only [evalExpr?, hl.assets_eq, EvalResult.ofOption]

theorem MarketTransferLocals.evalShares {p assets shares account receiver locals}
    (hl : MarketTransferLocals p assets shares account receiver locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "shares") =
      .ok (.int (Int.ofNat shares.toNat)) := by simp only [evalExpr?, hl.shares_eq, EvalResult.ofOption]

theorem MarketTransferLocals.evalAccount {p assets shares account receiver locals}
    (hl : MarketTransferLocals p assets shares account receiver locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "onBehalf") =
      .ok (.address (AccountAddress.ofNat account.toNat)) := by simp only [evalExpr?, hl.account_eq, EvalResult.ofOption]

theorem MarketTransferLocals.evalReceiver {p assets shares account receiver locals}
    (hl : MarketTransferLocals p assets shares account receiver locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "receiver") =
      .ok (.address (AccountAddress.ofNat receiver.toNat)) := by simp only [evalExpr?, hl.receiver_eq, EvalResult.ofOption]

def marketTransferInputFrame (p : MarketParamsWords) (assets shares account receiver : UInt256)
    (cd : ByteArray) (imms : Store) : Frame :=
  let frame := marketTransferFrame p assets shares account receiver cd imms
  { frame with locals := frame.locals.insert "__c1" (.bool (exactlyOneZero assets shares)) }

def marketTransferAuthorizedFrame (p : MarketParamsWords) (assets shares account receiver : UInt256)
    (evm : EVM.State) (imms : Store) : Frame :=
  let frame := marketTransferInputFrame p assets shares account receiver evm.executionEnv.calldata imms
  { frame with locals := frame.locals.insert "__c2" (wordToElem .bool
      (senderAuthorizedWord evm.accountMap evm.executionEnv account)) }

def marketTransferBeforeAccrue (p : MarketParamsWords) (assets shares account receiver : UInt256)
    (evm : EVM.State) (imms : Store) : Frame :=
  let frame := marketTransferAuthorizedFrame p assets shares account receiver evm imms
  { frame with locals := frame.locals.insert "__accrued" (.bool (accrueActive p evm)) }

theorem marketTransferInputFrame_locals (p : MarketParamsWords) (assets shares account receiver : UInt256)
    (cd : ByteArray) (imms : Store) :
    MarketTransferLocals p assets shares account receiver (marketTransferInputFrame p assets shares account receiver cd imms).locals :=
  (marketTransferFrame_locals p assets shares account receiver cd imms).insert _ _ (by decide) (by decide)

theorem marketTransferAuthorizedFrame_locals (p : MarketParamsWords) (assets shares account receiver : UInt256)
    (evm : EVM.State) (imms : Store) :
    MarketTransferLocals p assets shares account receiver (marketTransferAuthorizedFrame p assets shares account receiver evm imms).locals :=
  (marketTransferInputFrame_locals p assets shares account receiver evm.executionEnv.calldata imms).insert _ _ (by decide) (by decide)

theorem marketTransferBeforeAccrue_locals (p : MarketParamsWords) (assets shares account receiver : UInt256)
    (evm : EVM.State) (imms : Store) :
    MarketTransferLocals p assets shares account receiver (marketTransferBeforeAccrue p assets shares account receiver evm imms).locals :=
  (marketTransferAuthorizedFrame_locals p assets shares account receiver evm imms).insert _ _ (by decide) (by decide)


theorem MarketTransferLocals.setShares {p assets shares account receiver locals}
    (hl : MarketTransferLocals p assets shares account receiver locals) (newShares : UInt256) :
    MarketTransferLocals p assets newShares account receiver (locals.insert "shares" (.int (Int.ofNat newShares.toNat))) := by
  refine ⟨hl.toMarketLocals.insert _ _ (by decide), ?_, store_get_self _ _ _, ?_, ?_⟩
  · rw [store_get_ne _ _ (by decide)]; exact hl.assets_eq
  · rw [store_get_ne _ _ (by decide)]; exact hl.account_eq
  · rw [store_get_ne _ _ (by decide)]; exact hl.receiver_eq

theorem MarketTransferLocals.setAssets {p assets shares account receiver locals}
    (hl : MarketTransferLocals p assets shares account receiver locals) (newAssets : UInt256) :
    MarketTransferLocals p newAssets shares account receiver (locals.insert "assets" (.int (Int.ofNat newAssets.toNat))) := by
  refine ⟨hl.toMarketLocals.insert _ _ (by decide), store_get_self _ _ _, ?_, ?_, ?_⟩
  · rw [store_get_ne _ _ (by decide)]; exact hl.shares_eq
  · rw [store_get_ne _ _ (by decide)]; exact hl.account_eq
  · rw [store_get_ne _ _ (by decide)]; exact hl.receiver_eq

end Benchmarks.Morpho.MorphoBlue
