import Benchmarks.UniswapV4PoolManager.CurrencyId
import Benchmarks.UniswapV4PoolManager.SafeCast
import Benchmarks.UniswapV4PoolManager.AccountDeltaSource
import Benchmarks.UniswapV4PoolManager.BalanceMint
import Benchmarks.UniswapV4PoolManager.SourceComposition

/-! Source execution of mint, preserving accounting before the balance credit. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def mintTailFrame (f : Frame) (currency : AccountAddress) : Frame :=
  {f with locals := (f.locals.insert "__c4" (.int (Int.ofNat (accountWord currency).toNat))).insert "__c5" .unit}

theorem mintTailExec {f : Frame} {evm : EVM.State} {receiver amount : UInt256} {currency : AccountAddress}
    (hf : f.contract = contract) (hcr : receiver.toNat < EVM.addressModulus)
    (hc : f.locals.get? "currency" = some (.address currency))
    (hr : f.locals.get? "to" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat))) :
    ExecFuncBody config f evm (mintTransition.body.drop 8)
      (balanceMintResult (mintTailFrame f currency) evm receiver (accountWord currency) amount) := by
  have hconvert := currencyToIdCall (evm := evm) hf (evalLocalValue hc) "__c4"
  let f1 := {f with locals := f.locals.insert "__c4" (.int (Int.ofNat (accountWord currency).toNat))}
  have hr1 : f1.locals.get? "to" = some (.address (AccountAddress.ofNat receiver.toNat)) :=
    (store_get_ne _ _ (by decide : ("__c4" == "to") = false)).trans hr
  have ha1 : f1.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)) :=
    (store_get_ne _ _ (by decide : ("__c4" == "amount") = false)).trans ha
  have hcall := balanceMintCall (f := f1) (evm := evm) hf hcr (evalLocalValue hr1)
    (evalLocalValue (f := f1) (store_get_self _ _ _)) (evalLocalValue ha1) "__c5"
  rw [balanceMintResult]
  rw [balanceMintCallResult] at hcall
  by_cases hfit : (balanceWord evm receiver (accountWord currency)).toNat + amount.toNat < UInt256.size
  · rw [if_pos hfit] at hcall ⊢
    by_cases hp : evm.executionEnv.perm = false
    · rw [if_pos hp] at hcall ⊢
      exact .execBlockStatic (ExecBlock.consNormal hconvert (ExecBlock.consStatic hcall))
    · rw [if_neg hp] at hcall ⊢
      exact .execBlockOK (ExecBlock.consNormal hconvert (ExecBlock.consNormal hcall ExecBlock.nil))
  · rw [if_neg hfit] at hcall ⊢
    exact .execBlockRevert (ExecBlock.consNormal hconvert (ExecBlock.consRevert hcall))

def mintAccountResult (f : Frame) (evm : EVM.State) (receiver : UInt256) (currency : AccountAddress)
    (amount : UInt256) : ExecResult :=
  let f' := mintTailFrame {f with locals := f.locals.insert "__c3" .unit} currency
  if amount.toNat = 0 then balanceMintResult f' evm receiver (accountWord currency) amount else
  if int256Fits (currencyDeltaValue evm evm.executionEnv.source currency + -(Int.ofNat amount.toNat)) then
    if evm.executionEnv.perm = false then .staticViolation else
    balanceMintResult f' (accountDeltaPost evm evm.executionEnv.source currency (-(Int.ofNat amount.toNat)))
      receiver (accountWord currency) amount
  else .reverted

theorem mintAccountExec {f : Frame} {evm : EVM.State} {receiver amount : UInt256} {currency : AccountAddress}
    (hf : f.contract = contract) (hcr : receiver.toNat < EVM.addressModulus) (hfit : amount.toNat < 2^127)
    (hc : f.locals.get? "currency" = some (.address currency))
    (hr : f.locals.get? "to" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hd : f.locals.get? "__c2" = some (.int (Int.ofNat amount.toNat))) :
    ExecFuncBody config f evm (mintTransition.body.drop 7) (mintAccountResult f evm receiver currency amount) := by
  have hdelta := evalNegateInt128Word (cfg := config) (evm := evm) (evalLocalValue hd) hfit
  have hcall := accountDeltaCall (evm := evm) (et := .env .caller) hf (evalLocalValue hc) hdelta
    (by simp only [evalExpr?, envValue, pure]; rfl) "__c3"
  let f1 := {f with locals := f.locals.insert "__c3" .unit}
  have hc1 : f1.locals.get? "currency" = some (.address currency) :=
    (store_get_ne _ _ (by decide : ("__c3" == "currency") = false)).trans hc
  have hr1 : f1.locals.get? "to" = some (.address (AccountAddress.ofNat receiver.toNat)) :=
    (store_get_ne _ _ (by decide : ("__c3" == "to") = false)).trans hr
  have ha1 : f1.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)) :=
    (store_get_ne _ _ (by decide : ("__c3" == "amount") = false)).trans ha
  rw [mintAccountResult]
  rw [accountDeltaCallResult] at hcall
  by_cases hz : amount.toNat = 0
  · rw [if_pos hz]
    have hzInt : -(Int.ofNat amount.toNat) = 0 := by rw [hz]; rfl
    rw [if_pos hzInt] at hcall
    exact execFuncBody_prepend (execBlock_singleton hcall) (mintTailExec (f := f1) hf hcr hc1 hr1 ha1)
  · rw [if_neg hz]
    have hzInt : -(Int.ofNat amount.toNat) ≠ 0 := by simp only [Int.ofNat_eq_natCast]; omega
    rw [if_neg hzInt] at hcall
    by_cases hsum : int256Fits (currencyDeltaValue evm evm.executionEnv.source currency + -(Int.ofNat amount.toNat))
    · rw [if_pos hsum] at hcall ⊢
      by_cases hp : evm.executionEnv.perm = false
      · rw [if_pos hp] at hcall ⊢
        exact .execBlockStatic (ExecBlock.consStatic hcall)
      · rw [if_neg hp] at hcall ⊢
        exact execFuncBody_prepend (execBlock_singleton hcall) (mintTailExec (f := f1) hf hcr hc1 hr1 ha1)
    · rw [if_neg hsum] at hcall ⊢
      exact .execBlockRevert (ExecBlock.consRevert hcall)

def mintInputFrame (f : Frame) (id amount : UInt256) : Frame :=
  {f with locals := ((f.locals.insert "__c0" (.bool true)).insert "currency"
    (.address (AccountAddress.ofNat id.toNat))).insert "__c2" (.int (Int.ofNat amount.toNat))}

def mintBodyResult (f : Frame) (evm : EVM.State) (receiver id amount : UInt256) : ExecResult :=
  if transientWord evm lockSlot = ⟨0⟩ then .reverted else
  if amount.toNat < 2^127 then
    mintAccountResult (mintInputFrame f id amount) evm receiver (AccountAddress.ofNat id.toNat) amount
  else .reverted

theorem mintBodyExec {evm : EVM.State} {locals imms : Store} {receiver id amount : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hcr : receiver.toNat < EVM.addressModulus)
    (hr : locals.get? "to" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (hi : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (ha : locals.get? "amount" = some (.int (Int.ofNat amount.toNat))) :
    ExecTransitionBody config contract evm locals mintTransition.body
      (mintBodyResult (calldataFrame contract locals imms evm) evm receiver id amount) imms := by
  let f := calldataFrame contract locals imms evm
  have hlock := lockCall (f := f) (evm := evm) rfl "__c0"
  rw [mintBodyResult]
  apply nonpayableCalldataBody hwv hhi
  by_cases hl : transientWord evm lockSlot = ⟨0⟩
  · rw [if_pos hl]
    rw [decide_eq_false (not_not.mpr hl)] at hlock
    exact .execBlockRevert (ExecBlock.consNormal hlock (ExecBlock.consRevert (ExecStmt.iteTrue
      (evalNotBool (va := false) (evalLocalValue (store_get_self _ _ _)))
      (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?]; rfl))))))
  · rw [if_neg hl]
    rw [decide_eq_true hl] at hlock
    let f1 := {f with locals := f.locals.insert "__c0" (.bool true)}
    have hguard : ExecStmt config f1 evm mintTransition.body[4]! (.ok f1 evm) :=
      ExecStmt.iteFalse (evalNotBool (va := true) (evalLocalValue (store_get_self _ _ _))) ExecBlock.nil
    have hi1 : f1.locals.get? "id" = some (.int (Int.ofNat id.toNat)) :=
      (store_get_ne _ _ (by decide : ("__c0" == "id") = false)).trans
        ((store_get_ne _ _ (by decide : ("__calldata" == "id") = false)).trans hi)
    have hcurrency := currencyFromIdCall (evm := evm) rfl (evalLocalValue hi1) "currency"
    let f2 := {f1 with locals := f1.locals.insert "currency" (.address (AccountAddress.ofNat id.toNat))}
    have ha2 : f2.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)) :=
      (store_get_ne _ _ (by decide : ("currency" == "amount") = false)).trans
        ((store_get_ne _ _ (by decide : ("__c0" == "amount") = false)).trans
          ((store_get_ne _ _ (by decide : ("__calldata" == "amount") = false)).trans ha))
    by_cases hfit : amount.toNat < 2^127
    · rw [if_pos hfit]
      have hcast := uintToInt128Call rfl (evalLocalValue (cfg := config) (evm := evm) ha2) hfit "__c2"
      let f3 := {f2 with locals := f2.locals.insert "__c2" (.int (Int.ofNat amount.toNat))}
      have hr3 : f3.locals.get? "to" = some (.address (AccountAddress.ofNat receiver.toNat)) :=
        (store_get_ne _ _ (by decide : ("__c2" == "to") = false)).trans
          ((store_get_ne _ _ (by decide : ("currency" == "to") = false)).trans
            ((store_get_ne _ _ (by decide : ("__c0" == "to") = false)).trans
              ((store_get_ne _ _ (by decide : ("__calldata" == "to") = false)).trans hr)))
      have ha3 : f3.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)) :=
        (store_get_ne _ _ (by decide : ("__c2" == "amount") = false)).trans ha2
      have hc3 : f3.locals.get? "currency" = some (.address (AccountAddress.ofNat id.toNat)) :=
        (store_get_ne _ _ (by decide : ("__c2" == "currency") = false)).trans (store_get_self _ _ _)
      exact execFuncBody_prepend
        (ExecBlock.consNormal hlock (ExecBlock.consNormal hguard (ExecBlock.consNormal hcurrency
          (ExecBlock.consNormal hcast ExecBlock.nil))))
        (mintAccountExec rfl hcr hfit hc3 hr3 ha3 (store_get_self _ _ _))
    · rw [if_neg hfit]
      have hcast := uintToInt128CallReverts rfl (evalLocalValue (cfg := config) (evm := evm) ha2) hfit "__c2"
      exact .execBlockRevert (ExecBlock.consNormal hlock (ExecBlock.consNormal hguard
        (ExecBlock.consNormal hcurrency (ExecBlock.consRevert hcast))))

end Benchmarks.UniswapV4PoolManager
