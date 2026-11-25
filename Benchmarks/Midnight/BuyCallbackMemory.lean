import Benchmarks.Midnight.BuyCallbackWords
import Benchmarks.Midnight.RepayCallbackMemory

/-! Reading the complete onBuy calldata from its encoded memory buffer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem buyCallbackMemory_selector (mem : ByteArray) (root : Nat) (m : MarketData)
    (id assets units fee user : UInt256) (ptr len : Nat) (hs : ptr + 32 + len ≤ mem.size) :
    (buyCallbackMemory mem root m id assets units fee user ptr len).readWithPadding root 4 =
      (⟨#[0x1c, 0x0b, 0xb5, 0x4d]⟩ : ByteArray) := by
  let head := buyCallbackHeaderMemory mem root id
  let encoded := marketEncodeMemory head (root + 228) m
  let fields := buyCallbackFieldsMemory mem root m id assets units fee user
  have hh : root + 4 ≤ head.size := by
    simp only [head, buyCallbackHeaderMemory, writeWord_sparse_size]
    omega
  have he : head.size ≤ encoded.size :=
    (marketEncodeMemory_prefix head (root + 228) (root + 228) m le_rfl).size
  have hf : encoded.size ≤ fields.size := writeWordArray_size_ge ..
  have hp := buyCallbackFieldsMemory_prefix mem root root m id assets units fee user le_rfl
  have hr := writeWord_sparse_read_window mem root 0 4
    (UInt256.ofNat (470529357 * 2^224)) (by decide) (by decide) (by decide)
  have hsel : (UInt256.ofNat (470529357 * 2^224)).toByteArray.extract 0 4 =
      (⟨#[0x1c, 0x0b, 0xb5, 0x4d]⟩ : ByteArray) := by decide +kernel
  simp only [Nat.add_zero, Nat.zero_add, hsel] at hr
  unfold buyCallbackMemory
  rw [memoryBytesEncodeMemory_read_before _ _ _ _ _ _ (hs.trans hp.size)
    (by decide) (by decide) (hh.trans (he.trans hf)) (by omega)]
  unfold buyCallbackFieldsMemory
  rw [writeWordArray_read_below_len _ _ _ _ _ (hh.trans he) (by omega) (by decide) (by decide),
    marketEncodeMemory_read_before _ _ _ _ _ hh (by omega) (by decide) (by decide)]
  unfold head buyCallbackHeaderMemory
  rw [writeWord_sparse_read_preserved_len _ _ _ _ _
      (by rw [writeWord_sparse_size]; omega) (Or.inl (by omega)) (by decide) (by decide),
    writeWord_sparse_read_preserved_len _ _ _ _ _
      (by rw [writeWord_sparse_size]; omega) (Or.inl (by omega)) (by decide) (by decide), hr]

theorem buyCallbackMemory_read {mem data : ByteArray} (root : Nat) (m : MarketData)
    (id assets units fee : UInt256) (user : AccountAddress) {ptr : UInt256}
    (hdata : MemoryByteString mem ptr data) (hroot : 96 ≤ root)
    (hbelow : ptr.toNat + 32 + paddedSize data.size ≤ root)
    (hb : root + 548 + 128 * m.collaterals.length + paddedSize data.size < UInt256.size) :
    (buyCallbackMemory mem root m id assets units fee (UInt256.ofNat user.val)
      ptr.toNat data.size).readWithPadding root (buyCallbackSize m data.size) =
      buyCallbackCalldata m id assets units fee user data := by
  have hpad := nat_le_paddedSize data.size
  have hpadhi := paddedSize_le_add31 data.size
  have hsrc : ptr.toNat + 32 + data.size ≤ mem.size := by have hh := hdata.size; omega
  have hs := buyCallbackMemory_size_lower mem root m id assets units fee
    (UInt256.ofNat user.val) ptr.toNat data.size hsrc
  have hw := buyCallbackMemory_words mem root m id assets units fee
    (UInt256.ofNat user.val) ptr.toNat data.size hroot hsrc (by omega)
  have hr := hw.read
  rw [buyCallbackWords_length] at hr
  let fields := buyCallbackFieldsMemory mem root m id assets units fee (UInt256.ofNat user.val)
  have hp := buyCallbackFieldsMemory_prefix mem root root m id assets units fee
    (UInt256.ofNat user.val) le_rfl
  have hdata' : MemoryByteString fields ptr data := hdata.preserve hp hbelow
  have hout : (UInt256.ofNat (root + 516 + 128 * m.collaterals.length)).toNat =
      root + 516 + 128 * m.collaterals.length := UInt256.toNat_ofNat_of_lt (by omega)
  have hbstr := memoryBytesEncodeMemory_stored
    (output := UInt256.ofNat (root + 516 + 128 * m.collaterals.length)) hdata'
    (by rw [hout]; omega) (by rw [hout]; omega) (by rw [hout]; omega)
  have ht := hbstr.payload
  simp only [hout] at ht
  change (buyCallbackMemory mem root m id assets units fee (UInt256.ofNat user.val)
    ptr.toNat data.size).readWithPadding
    (root + 516 + 128 * m.collaterals.length + 32) (paddedSize data.size) = _ at ht
  have he : buyCallbackSize m data.size =
      4 + (32 * (17 + 4 * m.collaterals.length) + paddedSize data.size) := by
    unfold buyCallbackSize returnDataAllocation paddedSize
    omega
  rw [he, readWithPadding_split_inbounds _ _ _ _ (by omega),
    buyCallbackMemory_selector _ _ _ _ _ _ _ _ _ _ hsrc,
    readWithPadding_split_inbounds _ _ _ _ (by omega), hr]
  have hoff : root + 4 + 32 * (17 + 4 * m.collaterals.length) =
      root + 516 + 128 * m.collaterals.length + 32 := by omega
  rw [hoff, ht]
  simp only [buyCallbackCalldata, buyCallbackWords, wordArrayBytes_append,
    wordArrayBytes, ByteArray.append_empty, ByteArray.append_assoc]

end Benchmarks.Midnight
