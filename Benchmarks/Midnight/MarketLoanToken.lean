import Benchmarks.Midnight.CollateralDecodeIndex
import Benchmarks.Midnight.AddressDecode

/-! The canonical loan-token address in a successfully decoded market. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem decodeCalldataMarket_loanToken {bytes : ByteArray} {m : MarketData}
    (hd : decodeCalldataMarket bytes 4 = some m) :
    calldataWord bytes (calldataWord bytes 4 + UInt256.ofNat 68).toNat =
      UInt256.ofNat m.loanToken.val := by
  obtain ⟨hr, _, hdata⟩ := decodeCalldataMarket_data hd
  obtain ⟨_, hc, _, _, _, cs, _, he⟩ := decodeMarketData_success hdata
  rw [he, uadd_word_ofNat_toNat _ 68 (by change _ < 2^256; omega)]
  have hoff : (calldataWord bytes 4).toNat + 68 = 4 + (calldataWord bytes 4).toNat + 64 :=
    by omega
  rw [hoff]
  exact (addressWord_eq_ofNat_address hc.2.1).symm

end Benchmarks.Midnight
