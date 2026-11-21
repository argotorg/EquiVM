import Benchmarks.Midnight.ToMarketSource
import Benchmarks.Midnight.MarketValueDecode

/-! Source execution stated using the typed result of stored-market decoding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def toMarketDataFits (len : Nat) (market : MarketData) : Prop :=
  (len + 31) / 32 * 32 + 160 * market.collaterals.length + 1408 < 2^64

theorem toMarketDataReturns (evm : State) (id : UInt256) (market : MarketData)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hinit : 0 < (marketTickSpacing (marketFeeWord evm id)).toNat)
    (hcode : (extCodeSizeWord evm.accountMap id).toNat ≤ 18446744073709550464)
    (hdecode : decodeStoredMarketData (externalCodePrefix evm.accountMap id) = some market)
    (hfit : toMarketDataFits (extCodeSizeWord evm.accountMap id).toNat market) :
    ExecTransitionBody config contract evm (toMarketArguments id) toMarketTransition.body
      (.returned (toMarketResultFrame evm id market.value (market.collaterals.map CollateralData.value))
        evm (some [market.value])) := by
  apply toMarketReturns evm id hwv hhi hinit hcode
  · rw [decodeStoredMarketData_eq (by rw [externalCodePrefix_size]; omega), hdecode]
    rfl
  · exact market.collaterals_get
  · simpa only [List.length_map] using hfit

theorem toMarketDataReverts (evm : State) (id : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hinit : 0 < (marketTickSpacing (marketFeeWord evm id)).toNat)
    (hcode : (extCodeSizeWord evm.accountMap id).toNat ≤ 18446744073709550464)
    (hbad : ∀ market, decodeStoredMarketData (externalCodePrefix evm.accountMap id) = some market →
      ¬ toMarketDataFits (extCodeSizeWord evm.accountMap id).toNat market) :
    ExecTransitionBody config contract evm (toMarketArguments id) toMarketTransition.body .reverted := by
  cases hd : decodeStoredMarketData (externalCodePrefix evm.accountMap id) with
  | none =>
    apply toMarketDecodeReverts evm id hwv hhi hinit hcode
    rw [decodeStoredMarketData_eq (by rw [externalCodePrefix_size]; omega), hd]
    rfl
  | some market =>
    apply toMarketCapacityReverts evm id hwv hhi hinit hcode
      (decoded := market.value) (collaterals := market.collaterals.map CollateralData.value)
    · rw [decodeStoredMarketData_eq (by rw [externalCodePrefix_size]; omega), hd]
      rfl
    · exact market.collaterals_get
    · simpa only [List.length_map] using hbad market hd

end Benchmarks.Midnight
