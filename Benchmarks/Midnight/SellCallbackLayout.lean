import Benchmarks.Midnight.SellCallbackABI
import Benchmarks.Midnight.MemoryBytesRead

/-! Memory layout of the seller callback's selector, static fields, market, and bytes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def sellCallbackSize (m : MarketData) (len : Nat) : Nat :=
  548 + 128 * m.collaterals.length + returnDataAllocation len

def sellCallbackHeaderMemory (mem : ByteArray) (root : Nat) (id : UInt256) : ByteArray :=
  writeWord (writeWord (writeWord mem root (UInt256.ofNat (1827805250 * 2^224)))
    (root + 4) id) (root + 36) (UInt256.ofNat 256)

def sellCallbackFieldsMemory (mem : ByteArray) (root : Nat) (m : MarketData)
    (id assets units fee user receiver : UInt256) : ByteArray :=
  let encoded := marketEncodeMemory (sellCallbackHeaderMemory mem root id) (root + 260) m
  writeWordArray encoded (root + 68)
    [assets, units, fee, user, receiver, UInt256.ofNat (544 + 128 * m.collaterals.length)]

def sellCallbackMemory (mem : ByteArray) (root : Nat) (m : MarketData)
    (id assets units fee user receiver : UInt256) (ptr len : Nat) : ByteArray :=
  memoryBytesEncodeMemory (sellCallbackFieldsMemory mem root m id assets units fee user receiver)
    ptr (root + 548 + 128 * m.collaterals.length) len

theorem sellCallbackHeaderMemory_prefix (mem : ByteArray) (root limit : Nat) (id : UInt256)
    (h : limit ≤ root) : MemoryPrefix mem (sellCallbackHeaderMemory mem root id) limit :=
  ((memoryPrefix_writeWord _ _ _ _ (Or.inl h)).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega)))).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega)))

theorem sellCallbackFieldsMemory_prefix (mem : ByteArray) (root limit : Nat) (m : MarketData)
    (id assets units fee user receiver : UInt256) (h : limit ≤ root) :
    MemoryPrefix mem (sellCallbackFieldsMemory mem root m id assets units fee user receiver) limit :=
  ((sellCallbackHeaderMemory_prefix _ _ _ _ h).trans
    (marketEncodeMemory_prefix _ _ _ _ (by omega))).trans
    (memoryPrefix_writeWordArray _ _ _ _ (by omega))

theorem sellCallbackMemory_prefix (mem : ByteArray) (root limit : Nat) (m : MarketData)
    (id assets units fee user receiver : UInt256) (ptr len : Nat)
    (h : limit ≤ root) (hs : ptr + 32 + len ≤ mem.size) :
    MemoryPrefix mem (sellCallbackMemory mem root m id assets units fee user receiver ptr len) limit := by
  have hp := sellCallbackFieldsMemory_prefix mem root limit m id assets units fee user receiver h
  exact hp.trans (memoryBytesEncodeMemory_prefix _ _ _ _ _ (hs.trans hp.size) (by omega))

theorem sellCallbackMemory_size_lower (mem : ByteArray) (root : Nat) (m : MarketData)
    (id assets units fee user receiver : UInt256) (ptr len : Nat) (hs : ptr + 32 + len ≤ mem.size) :
    root + 612 + 128 * m.collaterals.length + len ≤
      (sellCallbackMemory mem root m id assets units fee user receiver ptr len).size := by
  have hp := sellCallbackFieldsMemory_prefix mem root root m id assets units fee user receiver le_rfl
  rw [sellCallbackMemory, memoryBytesEncodeMemory_size _ _ _ _ (hs.trans hp.size)]
  omega

end Benchmarks.Midnight
