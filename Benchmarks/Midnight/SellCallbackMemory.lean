import Benchmarks.Midnight.SellCallbackWords
import Benchmarks.Midnight.RepayCallbackMemory

/-! Reading the complete onSell calldata from its encoded memory buffer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem sellCallbackMemory_selector (mem : ByteArray) (root : Nat) (m : MarketData)
    (id assets units fee user receiver : UInt256) (ptr len : Nat) (hs : ptr + 32 + len ≤ mem.size) :
    (sellCallbackMemory mem root m id assets units fee user receiver ptr len).readWithPadding root 4 =
      (⟨#[0x6c, 0xf2, 0x18, 0x42]⟩ : ByteArray) := by
  let head := sellCallbackHeaderMemory mem root id
  let encoded := marketEncodeMemory head (root + 260) m
  let fields := sellCallbackFieldsMemory mem root m id assets units fee user receiver
  have hh : root + 4 ≤ head.size := by
    simp only [head, sellCallbackHeaderMemory, writeWord_sparse_size]
    omega
  have he : head.size ≤ encoded.size :=
    (marketEncodeMemory_prefix head (root + 260) (root + 260) m le_rfl).size
  have hf : encoded.size ≤ fields.size := writeWordArray_size_ge ..
  have hp := sellCallbackFieldsMemory_prefix mem root root m id assets units fee user receiver le_rfl
  have hr := writeWord_sparse_read_window mem root 0 4
    (UInt256.ofNat (1827805250 * 2^224)) (by decide) (by decide) (by decide)
  have hsel : (UInt256.ofNat (1827805250 * 2^224)).toByteArray.extract 0 4 =
      (⟨#[0x6c, 0xf2, 0x18, 0x42]⟩ : ByteArray) := by decide +kernel
  simp only [Nat.add_zero, Nat.zero_add, hsel] at hr
  unfold sellCallbackMemory
  rw [memoryBytesEncodeMemory_read_before _ _ _ _ _ _ (hs.trans hp.size)
    (by decide) (by decide) (hh.trans (he.trans hf)) (by omega)]
  unfold sellCallbackFieldsMemory
  rw [writeWordArray_read_below_len _ _ _ _ _ (hh.trans he) (by omega) (by decide) (by decide),
    marketEncodeMemory_read_before _ _ _ _ _ hh (by omega) (by decide) (by decide)]
  unfold head sellCallbackHeaderMemory
  rw [writeWord_sparse_read_preserved_len _ _ _ _ _
      (by rw [writeWord_sparse_size]; omega) (Or.inl (by omega)) (by decide) (by decide),
    writeWord_sparse_read_preserved_len _ _ _ _ _
      (by rw [writeWord_sparse_size]; omega) (Or.inl (by omega)) (by decide) (by decide), hr]

theorem sellCallbackMemory_read {mem data : ByteArray} (root : Nat) (m : MarketData)
    (id assets units fee : UInt256) (user receiver : AccountAddress) {ptr : UInt256}
    (hdata : MemoryByteString mem ptr data) (hroot : 96 ≤ root)
    (hbelow : ptr.toNat + 32 + paddedSize data.size ≤ root)
    (hb : root + 580 + 128 * m.collaterals.length + paddedSize data.size < UInt256.size) :
    (sellCallbackMemory mem root m id assets units fee (UInt256.ofNat user.val) (UInt256.ofNat receiver.val)
      ptr.toNat data.size).readWithPadding root (sellCallbackSize m data.size) =
      sellCallbackCalldata m id assets units fee user receiver data := by
  have hpad := nat_le_paddedSize data.size
  have hpadhi := paddedSize_le_add31 data.size
  have hsrc : ptr.toNat + 32 + data.size ≤ mem.size := by have hh := hdata.size; omega
  have hs := sellCallbackMemory_size_lower mem root m id assets units fee
    (UInt256.ofNat user.val) (UInt256.ofNat receiver.val) ptr.toNat data.size hsrc
  have hw := sellCallbackMemory_words mem root m id assets units fee
    (UInt256.ofNat user.val) (UInt256.ofNat receiver.val) ptr.toNat data.size hroot hsrc (by omega)
  have hr := hw.read
  rw [sellCallbackWords_length] at hr
  let fields := sellCallbackFieldsMemory mem root m id assets units fee (UInt256.ofNat user.val) (UInt256.ofNat receiver.val)
  have hp := sellCallbackFieldsMemory_prefix mem root root m id assets units fee
    (UInt256.ofNat user.val) (UInt256.ofNat receiver.val) le_rfl
  have hdata' : MemoryByteString fields ptr data := hdata.preserve hp hbelow
  have hout : (UInt256.ofNat (root + 548 + 128 * m.collaterals.length)).toNat =
      root + 548 + 128 * m.collaterals.length := UInt256.toNat_ofNat_of_lt (by omega)
  have hbstr := memoryBytesEncodeMemory_stored
    (output := UInt256.ofNat (root + 548 + 128 * m.collaterals.length)) hdata'
    (by rw [hout]; omega) (by rw [hout]; omega) (by rw [hout]; omega)
  have ht := hbstr.payload
  simp only [hout] at ht
  change (sellCallbackMemory mem root m id assets units fee (UInt256.ofNat user.val) (UInt256.ofNat receiver.val)
    ptr.toNat data.size).readWithPadding
    (root + 548 + 128 * m.collaterals.length + 32) (paddedSize data.size) = _ at ht
  have he : sellCallbackSize m data.size =
      4 + (32 * (18 + 4 * m.collaterals.length) + paddedSize data.size) := by
    unfold sellCallbackSize returnDataAllocation paddedSize
    omega
  rw [he, readWithPadding_split_inbounds _ _ _ _ (by omega),
    sellCallbackMemory_selector _ _ _ _ _ _ _ _ _ _ _ hsrc,
    readWithPadding_split_inbounds _ _ _ _ (by omega), hr]
  have hoff : root + 4 + 32 * (18 + 4 * m.collaterals.length) =
      root + 548 + 128 * m.collaterals.length + 32 := by omega
  rw [hoff, ht]
  simp only [sellCallbackCalldata, sellCallbackWords, wordArrayBytes_append,
    wordArrayBytes, ByteArray.append_empty, ByteArray.append_assoc]

end Benchmarks.Midnight
