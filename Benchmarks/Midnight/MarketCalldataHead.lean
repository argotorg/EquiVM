import Benchmarks.Midnight.MarketCalldataValue
import Benchmarks.Midnight.MarketCalldataHuge

/-! A typed dynamic market head in external calldata. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

def decodeCalldataMarket (bytes : ByteArray) (head : Nat) : Option MarketData :=
  let relative := (calldataWord bytes head).toNat
  if solcMaxU64 < relative ∨ 2^255 ≤ bytes.size then none
  else decodeMarketData bytes (4 + relative)

theorem solcDecodeFields_market {types : List ABIType} {bytes : ByteArray}
    {cursor : Nat} {plans : List CalldataPlan}
    (hplan : plans.headD {} = {}) (hbound : 4 + cursor + 32 ≤ bytes.size)
    (hsize : bytes.size < UInt256.size) :
    decodeFields? (Model.marketABI :: types) bytes.toList 4 cursor plans true = (do
      let market ← decodeCalldataMarket bytes (4 + cursor)
      let rest ← decodeFields? types bytes.toList 4 (cursor + 32) plans.tail true
      pure (market.value :: rest)) := by
  rw [solcDecodeFields_dynamic Model.marketABI (by decide +kernel) hplan hbound hsize
    (by decide +kernel)]
  unfold decodeCalldataMarket
  by_cases ho : solcMaxU64 < (calldataWord bytes (4 + cursor)).toNat
  · simp only [ho, true_or, if_true, bind, Option.bind]
  · have hs : 4 + (calldataWord bytes (4 + cursor)).toNat < 2^127 := by
      change ¬ (2^64 - 1 < _) at ho
      omega
    simp only [ho, false_or, if_false]
    by_cases hh : 2^255 ≤ bytes.size
    · rw [solcMarketValue_huge hh hsize hs]
      simp only [hh, if_true, bind, Option.bind]
    · rw [solcMarketValue_eq (by omega) hs]
      simp only [hh, if_false]
      cases decodeMarketData bytes (4 + (calldataWord bytes (4 + cursor)).toNat) <;> rfl

end Benchmarks.Midnight
