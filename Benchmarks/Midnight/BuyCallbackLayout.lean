import Benchmarks.Midnight.BuyCallbackABI
import Benchmarks.Midnight.MemoryBytesRead

/-! Memory layout of the buyer callback's selector, static fields, market, and bytes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def buyCallbackSize (m : MarketData) (len : Nat) : Nat :=
  516 + 128 * m.collaterals.length + returnDataAllocation len

def buyCallbackHeaderMemory (mem : ByteArray) (root : Nat) (id : UInt256) : ByteArray :=
  writeWord (writeWord (writeWord mem root (UInt256.ofNat (470529357 * 2^224)))
    (root + 4) id) (root + 36) (UInt256.ofNat 224)

def buyCallbackFieldsMemory (mem : ByteArray) (root : Nat) (m : MarketData)
    (id assets units fee user : UInt256) : ByteArray :=
  let encoded := marketEncodeMemory (buyCallbackHeaderMemory mem root id) (root + 228) m
  writeWordArray encoded (root + 68)
    [assets, units, fee, user, UInt256.ofNat (512 + 128 * m.collaterals.length)]

def buyCallbackMemory (mem : ByteArray) (root : Nat) (m : MarketData)
    (id assets units fee user : UInt256) (ptr len : Nat) : ByteArray :=
  memoryBytesEncodeMemory (buyCallbackFieldsMemory mem root m id assets units fee user)
    ptr (root + 516 + 128 * m.collaterals.length) len

theorem buyCallbackHeaderMemory_prefix (mem : ByteArray) (root limit : Nat) (id : UInt256)
    (h : limit ≤ root) : MemoryPrefix mem (buyCallbackHeaderMemory mem root id) limit :=
  ((memoryPrefix_writeWord _ _ _ _ (Or.inl h)).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega)))).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega)))

theorem buyCallbackFieldsMemory_prefix (mem : ByteArray) (root limit : Nat) (m : MarketData)
    (id assets units fee user : UInt256) (h : limit ≤ root) :
    MemoryPrefix mem (buyCallbackFieldsMemory mem root m id assets units fee user) limit :=
  ((buyCallbackHeaderMemory_prefix _ _ _ _ h).trans
    (marketEncodeMemory_prefix _ _ _ _ (by omega))).trans
    (memoryPrefix_writeWordArray _ _ _ _ (by omega))

theorem buyCallbackMemory_prefix (mem : ByteArray) (root limit : Nat) (m : MarketData)
    (id assets units fee user : UInt256) (ptr len : Nat)
    (h : limit ≤ root) (hs : ptr + 32 + len ≤ mem.size) :
    MemoryPrefix mem (buyCallbackMemory mem root m id assets units fee user ptr len) limit := by
  have hp := buyCallbackFieldsMemory_prefix mem root limit m id assets units fee user h
  exact hp.trans (memoryBytesEncodeMemory_prefix _ _ _ _ _ (hs.trans hp.size) (by omega))

theorem buyCallbackMemory_size_lower (mem : ByteArray) (root : Nat) (m : MarketData)
    (id assets units fee user : UInt256) (ptr len : Nat) (hs : ptr + 32 + len ≤ mem.size) :
    root + 580 + 128 * m.collaterals.length + len ≤
      (buyCallbackMemory mem root m id assets units fee user ptr len).size := by
  have hp := buyCallbackFieldsMemory_prefix mem root root m id assets units fee user le_rfl
  rw [buyCallbackMemory, memoryBytesEncodeMemory_size _ _ _ _ (hs.trans hp.size)]
  omega

end Benchmarks.Midnight
