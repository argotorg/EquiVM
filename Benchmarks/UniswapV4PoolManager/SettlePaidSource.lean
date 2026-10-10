import Benchmarks.UniswapV4PoolManager.CurrencyReservesRead
import Benchmarks.UniswapV4PoolManager.SafeCast
import Benchmarks.UniswapV4PoolManager.AccountDeltaSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev settleFunction : FunctionDecl := contract.functions[42]!
theorem settleFunction_lookup : lookupCallable? contract "_settle" = some settleFunction.toCallable := rfl

def settlePaidFrame (f : Frame) (paid : UInt256) : Frame :=
  {f with locals := (f.locals.insert "__c5" (.int (Int.ofNat paid.toNat))).insert "__c6" .unit}

@[irreducible] def settlePaidResult (f : Frame) (evm : EVM.State) (recipient currency : AccountAddress) (paid : UInt256) : ExecResult :=
  if paid.toNat < 2^127 then
    if Int.ofNat paid.toNat = 0 then .returned (settlePaidFrame f paid) evm (some [.int (Int.ofNat paid.toNat)]) else
    if int256Fits (currencyDeltaValue evm recipient currency + Int.ofNat paid.toNat) then
      if evm.executionEnv.perm = false then .staticViolation else
      .returned (settlePaidFrame f paid) (accountDeltaPost evm recipient currency (Int.ofNat paid.toNat))
        (some [.int (Int.ofNat paid.toNat)])
    else .reverted
  else .reverted

theorem settlePaidBody {f : Frame} {evm : EVM.State} {recipient currency : AccountAddress} {paid : UInt256}
    (hf : f.contract = contract)
    (hr : f.locals.get? "recipient" = some (.address recipient))
    (hc : f.locals.get? "currency" = some (.address currency))
    (hp : f.locals.get? "paid" = some (.int (Int.ofNat paid.toNat))) :
    ExecFuncBody config f evm (settleFunction.body.drop 4) (settlePaidResult f evm recipient currency paid) := by
  rw [settlePaidResult]
  by_cases hfit : paid.toNat < 2^127
  · rw [if_pos hfit]
    have hcast := uintToInt128Call (evm := evm) hf (evalLocalValue hp) hfit "__c5"
    let f1 : Frame := {f with locals := f.locals.insert "__c5" (.int (Int.ofNat paid.toNat))}
    have haccount := accountDeltaCall (f := f1) (evm := evm) hf
      (evalLocalValue ((store_get_ne _ _ (by decide : ("__c5" == "currency") = false)).trans hc))
      (evalLocalValue (store_get_self _ _ _))
      (evalLocalValue ((store_get_ne _ _ (by decide : ("__c5" == "recipient") = false)).trans hr)) "__c6"
    have hpaid : (settlePaidFrame f paid).locals.get? "paid" = some (.int (Int.ofNat paid.toNat)) :=
      (store_get_ne _ _ (by decide : ("__c6" == "paid") = false)).trans
        ((store_get_ne _ _ (by decide : ("__c5" == "paid") = false)).trans hp)
    rw [accountDeltaCallResult] at haccount
    by_cases hz : Int.ofNat paid.toNat = 0
    · rw [if_pos hz] at haccount ⊢
      exact .execBlockRet (ExecBlock.consNormal hcast (ExecBlock.consNormal haccount
        (ABlock.start.returns (evalLocalValue hpaid))))
    · rw [if_neg hz] at haccount ⊢
      by_cases hs : int256Fits (currencyDeltaValue evm recipient currency + Int.ofNat paid.toNat)
      · rw [if_pos hs] at haccount ⊢
        by_cases hperm : evm.executionEnv.perm = false
        · rw [if_pos hperm] at haccount ⊢
          exact .execBlockStatic (ExecBlock.consNormal hcast (ExecBlock.consStatic haccount))
        · rw [if_neg hperm] at haccount ⊢
          exact .execBlockRet (ExecBlock.consNormal hcast (ExecBlock.consNormal haccount
            (ABlock.start.returns (evalLocalValue hpaid))))
      · rw [if_neg hs] at haccount ⊢
        exact .execBlockRevert (ExecBlock.consNormal hcast (ExecBlock.consRevert haccount))
  · rw [if_neg hfit]
    exact .execBlockRevert (ExecBlock.consRevert (uintToInt128CallReverts hf (evalLocalValue hp) hfit "__c5"))

end Benchmarks.UniswapV4PoolManager
