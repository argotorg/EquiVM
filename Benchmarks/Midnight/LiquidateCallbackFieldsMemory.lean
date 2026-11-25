import Benchmarks.Midnight.LiquidateCallbackHeadMemory
import Benchmarks.Midnight.LiquidateThresholdTrace
import Benchmarks.Midnight.LiquidatorGateHead

/-! The remaining market fields and scalar arguments of the liquidation callback. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def liquidateCallbackFieldsMemory (mem : ByteArray) (root : Nat) (m : MarketData)
    (index seized repaid borrower receiver : UInt256) : ByteArray :=
  writeWordArray (writeWordArray mem (root + 452)
    [m.maturity, m.rcfThreshold, UInt256.ofNat m.enterGate.val, UInt256.ofNat m.liquidatorGate.val])
    (root + 100) [index, seized, repaid, borrower, receiver,
      UInt256.ofNat (608 + 128 * m.collaterals.length)]

theorem liquidateCallbackFieldsMemory_prefix (mem : ByteArray) (root : Nat) (m : MarketData)
    (index seized repaid borrower receiver : UInt256) :
    MemoryPrefix mem (liquidateCallbackFieldsMemory mem root m index seized repaid borrower receiver)
      root := (memoryPrefix_writeWordArray _ _ _ _ (by omega)).trans
    (memoryPrefix_writeWordArray _ _ _ _ (by omega))

theorem decodeCalldataMarket_enterGate {bytes : ByteArray} {m : MarketData}
    (hd : decodeCalldataMarket bytes 4 = some m) :
    calldataWord bytes (calldataWord bytes 4 + UInt256.ofNat 196).toNat =
      UInt256.ofNat m.enterGate.val := by
  obtain ⟨hr, _, hdata⟩ := decodeCalldataMarket_data hd
  obtain ⟨_, hc, _, _, _, cs, _, he⟩ := decodeMarketData_success hdata
  rw [he, uadd_word_ofNat_toNat _ 196 (by change _ < 2^256; omega)]
  have hoff : (calldataWord bytes 4).toNat + 196 = 4 + (calldataWord bytes 4).toNat + 192 := by omega
  rw [hoff]
  exact (addressWord_eq_ofNat_address hc.2.2.1).symm

end Benchmarks.Midnight
