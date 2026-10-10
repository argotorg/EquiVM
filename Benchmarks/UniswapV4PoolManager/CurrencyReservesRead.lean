import Benchmarks.UniswapV4PoolManager.CurrencyReservesSource
import Benchmarks.UniswapV4PoolManager.CurrencyId

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev syncedCurrencyFunction : FunctionDecl := contract.functions[54]!
abbrev syncedReservesFunction : FunctionDecl := contract.functions[83]!

def syncedCurrency (evm : EVM.State) : AccountAddress :=
  AccountAddress.ofNat (transientWord evm currencySlot).toNat

theorem syncedCurrency_word (evm : EVM.State) :
    accountWord (syncedCurrency evm) = UInt256.land (transientWord evm currencySlot) solcAddrMask :=
  accountWord_fromId _

theorem syncedCurrency_lookup : lookupCallable? contract "CurrencyReserves_getSyncedCurrency" =
    some syncedCurrencyFunction.toCallable := rfl
theorem syncedReserves_lookup : lookupCallable? contract "CurrencyReserves_getSyncedReserves" =
    some syncedReservesFunction.toCallable := rfl

theorem syncedCurrencyBody {f : Frame} {evm : EVM.State} (hf : f.contract = contract) :
    ExecFuncBody config f evm syncedCurrencyFunction.body (.returned f evm (some [.address (syncedCurrency evm)])) := by
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  apply evalCastValue (rawTransient_read hf (evalCurrencySlot hf))
  simp only [castValue?, Int.ofNat_eq_natCast, Int.not_lt.mpr (Int.natCast_nonneg _), if_false, Int.toNat_natCast]
  rfl

theorem syncedReservesBody {f : Frame} {evm : EVM.State} (hf : f.contract = contract) :
    ExecFuncBody config f evm syncedReservesFunction.body
      (.returned f evm (some [.int (Int.ofNat (transientWord evm reservesSlot).toNat)])) :=
  .execBlockRet (ABlock.start.returns (rawTransient_read hf (evalReservesSlot hf)))

theorem syncedCurrencyCall {f : Frame} {evm : EVM.State} (hf : f.contract = contract) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "CurrencyReserves_getSyncedCurrency" [] retVar)
      (.ok {f with locals := f.locals.insert retVar (.address (syncedCurrency evm))} evm) :=
  internalCallFunctionReturn rfl (by rw [hf]; exact syncedCurrency_lookup) rfl
    (syncedCurrencyBody (f := {f with locals := ∅}) hf)

theorem syncedReservesCall {f : Frame} {evm : EVM.State} (hf : f.contract = contract) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "CurrencyReserves_getSyncedReserves" [] retVar)
      (.ok {f with locals := f.locals.insert retVar (.int (Int.ofNat (transientWord evm reservesSlot).toNat))} evm) :=
  internalCallFunctionReturn rfl (by rw [hf]; exact syncedReserves_lookup) rfl
    (syncedReservesBody (f := {f with locals := ∅}) hf)

end Benchmarks.UniswapV4PoolManager
