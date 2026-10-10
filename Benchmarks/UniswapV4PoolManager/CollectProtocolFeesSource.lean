import Benchmarks.UniswapV4PoolManager.CurrencyReservesRead

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def collectCurrencyFrame (f : Frame) (evm : EVM.State) (currency : AccountAddress) : Frame :=
  let f1 := {f with locals := f.locals.insert "__c0" (.bool (decide (currency = AccountAddress.ofNat 0)))}
  if currency = AccountAddress.ofNat 0 then f1 else
    {f1 with locals := f1.locals.insert "syncedCurrency" (.address (syncedCurrency evm))}

theorem collectCurrencyFrame_contract (f : Frame) (evm : EVM.State) (currency : AccountAddress) :
    (collectCurrencyFrame f evm currency).contract = f.contract := by
  unfold collectCurrencyFrame
  split <;> rfl

theorem collectCurrencyFrame_get {f : Frame} {evm : EVM.State} {currency : AccountAddress}
    {name : Ident} {value : Option Value} (hzero : ("__c0" == name) = false)
    (hsync : ("syncedCurrency" == name) = false) (h : f.locals.get? name = value) :
    (collectCurrencyFrame f evm currency).locals.get? name = value := by
  unfold collectCurrencyFrame
  split
  · exact (store_get_ne _ _ hzero).trans h
  · exact (store_get_ne _ _ hsync).trans ((store_get_ne _ _ hzero).trans h)

theorem collectCurrencyGuard {f : Frame} {evm : EVM.State} {currency : AccountAddress}
    (hf : f.contract = contract) (hc : f.locals.get? "currency" = some (.address currency)) :
    ExecBlock config f evm ((collectProtocolFeesTransition.body.drop 5).take 2)
      (if currency = AccountAddress.ofNat 0 ∨ syncedCurrency evm ≠ currency then
        .ok (collectCurrencyFrame f evm currency) evm else .reverted) := by
  have hzero := currencyZeroCall (evm := evm) hf (evalLocalValue hc) "__c0"
  by_cases hz : currency = AccountAddress.ofNat 0
  · rw [if_pos (Or.inl hz), collectCurrencyFrame, if_pos hz, decide_eq_true hz] at ⊢
    rw [decide_eq_true hz] at hzero
    exact ExecBlock.consNormal hzero (ExecBlock.consNormal
      (ExecStmt.iteFalse (evalNotBool (va := true) (evalLocalValue (store_get_self _ _ _))) ExecBlock.nil) ExecBlock.nil)
  · rw [decide_eq_false hz] at hzero
    let f1 : Frame := {f with locals := f.locals.insert "__c0" (.bool false)}
    have hsync := syncedCurrencyCall (f := f1) (evm := evm) hf "syncedCurrency"
    have hc1 : ({f1 with locals := f1.locals.insert "syncedCurrency" (.address (syncedCurrency evm))} : Frame).locals.get?
        "currency" = some (.address currency) :=
      (store_get_ne _ _ (by decide : ("syncedCurrency" == "currency") = false)).trans
        ((store_get_ne _ _ (by decide : ("__c0" == "currency") = false)).trans hc)
    have hne := evalNeAddress (cfg := config) (evm := evm) (evalLocalValue (store_get_self _ _ _)) (evalLocalValue hc1)
    by_cases hn : syncedCurrency evm ≠ currency
    · rw [if_pos (Or.inr hn), collectCurrencyFrame, if_neg hz, decide_eq_false hz]
      rw [decide_eq_true hn] at hne
      exact ExecBlock.consNormal hzero (ExecBlock.consNormal
        (ExecStmt.iteTrue (evalNotBool (va := false) (evalLocalValue (store_get_self _ _ _)))
          (ExecBlock.consNormal hsync (ExecBlock.consNormal (ExecStmt.requireTrue hne) ExecBlock.nil))) ExecBlock.nil)
    · rw [if_neg (by tauto)]
      rw [decide_eq_false hn] at hne
      exact ExecBlock.consNormal hzero (ExecBlock.consRevert
        (ExecStmt.iteTrue (evalNotBool (va := false) (evalLocalValue (store_get_self _ _ _)))
          (ExecBlock.consNormal hsync (ExecBlock.consRevert (ExecStmt.requireFalse hne)))))

end Benchmarks.UniswapV4PoolManager
