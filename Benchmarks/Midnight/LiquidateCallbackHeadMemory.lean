import Benchmarks.Midnight.MarketLoanToken
import Benchmarks.Midnight.MemoryWords
import Benchmarks.Midnight.MemoryPrefix

/-! Initial callback fields, before the collateral array and remaining scalar fields. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def liquidateCallbackSelector : UInt256 := UInt256.ofNat (2162466306 * 2^224)

def liquidateCallbackPrefixMemory (mem : ByteArray) (root : Nat) (sender : AccountAddress)
    (id : UInt256) : ByteArray :=
  writeWordArray (writeWord mem root liquidateCallbackSelector) (root + 4)
    [UInt256.ofNat sender.val, id, UInt256.ofNat 320]

def liquidateCallbackHeadMemory (mem : ByteArray) (root : Nat) (sender : AccountAddress)
    (id : UInt256) (m : MarketData) : ByteArray :=
  writeWordArray (liquidateCallbackPrefixMemory mem root sender id) (root + 324)
    [m.chainId, UInt256.ofNat m.midnight.val]

def liquidateCallbackArrayHeadMemory (mem : ByteArray) (root : Nat) (sender : AccountAddress)
    (id : UInt256) (m : MarketData) : ByteArray :=
  writeWord (writeWordArray (liquidateCallbackHeadMemory mem root sender id m) (root + 388)
    [UInt256.ofNat m.loanToken.val, UInt256.ofNat 256]) (root + 580)
      (UInt256.ofNat m.collaterals.length)

theorem liquidateCallbackHeadMemory_prefix (mem : ByteArray) (root : Nat)
    (sender : AccountAddress) (id : UInt256) (m : MarketData) :
    MemoryPrefix mem (liquidateCallbackHeadMemory mem root sender id m) root :=
  ((memoryPrefix_writeWord _ _ _ _ (Or.inl le_rfl)).trans
    (memoryPrefix_writeWordArray _ _ _ _ (by omega))).trans
    (memoryPrefix_writeWordArray _ _ _ _ (by omega))

theorem liquidateCallbackArrayHeadMemory_prefix (mem : ByteArray) (root : Nat)
    (sender : AccountAddress) (id : UInt256) (m : MarketData) :
    MemoryPrefix mem (liquidateCallbackArrayHeadMemory mem root sender id m) root :=
  ((liquidateCallbackHeadMemory_prefix _ _ _ _ _).trans
    (memoryPrefix_writeWordArray _ _ _ _ (by omega))).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega)))

theorem decodeCalldataMarket_chainId {bytes : ByteArray} {m : MarketData}
    (hd : decodeCalldataMarket bytes 4 = some m) :
    calldataWord bytes (UInt256.ofNat 4 + calldataWord bytes 4).toNat = m.chainId := by
  obtain ⟨hr, _, hdata⟩ := decodeCalldataMarket_data hd
  obtain ⟨_, _, _, _, _, cs, _, he⟩ := decodeMarketData_success hdata
  rw [he, u256_add_comm, uadd_word_ofNat_toNat _ 4 (by change _ < 2^256; omega)]
  change calldataWord bytes ((calldataWord bytes 4).toNat + 4) =
    calldataWord bytes (4 + (calldataWord bytes 4).toNat)
  rw [Nat.add_comm]

theorem decodeCalldataMarket_midnight {bytes : ByteArray} {m : MarketData}
    (hd : decodeCalldataMarket bytes 4 = some m) :
    calldataWord bytes (calldataWord bytes 4 + UInt256.ofNat 36).toNat =
      UInt256.ofNat m.midnight.val := by
  obtain ⟨hr, _, hdata⟩ := decodeCalldataMarket_data hd
  obtain ⟨_, hc, _, _, _, cs, _, he⟩ := decodeMarketData_success hdata
  rw [he, uadd_word_ofNat_toNat _ 36 (by change _ < 2^256; omega)]
  have hoff : (calldataWord bytes 4).toNat + 36 = 4 + (calldataWord bytes 4).toNat + 32 := by omega
  rw [hoff]
  exact (addressWord_eq_ofNat_address hc.1).symm

end Benchmarks.Midnight
