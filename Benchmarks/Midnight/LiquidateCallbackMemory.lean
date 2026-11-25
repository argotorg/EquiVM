import Benchmarks.Midnight.LiquidateCallbackWords
import Benchmarks.Midnight.LiquidateCallbackABI
import Benchmarks.Midnight.RepayCallbackMemory
import Benchmarks.Midnight.MemoryReadAbove

/-! Exact selector, word prefix, and padded data of the liquidation callback input. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem liquidateCallbackMemory_size_lower (mem bytes : ByteArray) (root : Nat)
    (sender : AccountAddress) (m : MarketData)
    (id index seized repaid borrower receiver badDebt : UInt256) (dp dl : Nat)
    (hd : dp + dl ≤ bytes.size) :
    root + 676 + 128 * m.collaterals.length + dl ≤
      (liquidateCallbackMemory mem bytes root sender m id index seized repaid borrower receiver
        dp dl badDebt).size := by
  rw [liquidateCallbackMemory, writeWord_sparse_size, calldataBytesEncodeMemory_size _ _ _ _ _ hd]
  omega

theorem liquidateCallbackMemory_selector (mem bytes : ByteArray) (root : Nat)
    (sender : AccountAddress) (m : MarketData)
    (id index seized repaid borrower receiver badDebt : UInt256) (dp dl : Nat)
    (hd : dp + dl ≤ bytes.size) :
    (liquidateCallbackMemory mem bytes root sender m id index seized repaid borrower receiver
      dp dl badDebt).readWithPadding root 4 = (⟨#[0x80, 0xe4, 0x9e, 0x02]⟩ : ByteArray) := by
  let head := liquidateCallbackPrefixMemory mem root sender id
  have hh : root + 4 ≤ head.size := by
    simp only [head, liquidateCallbackPrefixMemory, writeWordArray, writeWord_sparse_size]
    omega
  have he := (marketEncodeMemory_prefix head (root + 324) (root + 324) m le_rfl).size
  have hf := (memoryPrefix_writeWordArray (marketEncodeMemory head (root + 324) m)
    (root + 100) (root + 100) [index, seized, repaid, borrower, receiver,
      UInt256.ofNat (608 + 128 * m.collaterals.length)] le_rfl).size
  dsimp only [head] at hh he hf
  have hr := writeWord_sparse_read_window mem root 0 4 liquidateCallbackSelector
    (by decide) (by decide) (by decide)
  have hsel : liquidateCallbackSelector.toByteArray.extract 0 4 =
      (⟨#[0x80, 0xe4, 0x9e, 0x02]⟩ : ByteArray) := by decide +kernel
  simp only [Nat.add_zero, Nat.zero_add, hsel] at hr
  unfold liquidateCallbackMemory
  rw [liquidateCallbackFieldsMemory_eq,
    writeWord_sparse_read_preserved_len _ _ _ _ _
      (by rw [calldataBytesEncodeMemory_size _ _ _ _ _ hd]; omega)
      (Or.inl (by omega)) (by decide) (by decide),
    calldataBytesEncodeMemory_read_before _ _ _ _ _ _ _ hd (by decide) (by decide)
      ((hh.trans he).trans hf) (by omega),
    writeWordArray_read_below_len _ _ _ _ _ (hh.trans he) (by omega) (by decide) (by decide),
    marketEncodeMemory_read_before _ _ _ _ _ hh (by omega) (by decide) (by decide)]
  unfold liquidateCallbackPrefixMemory
  rw [writeWordArray_read_below_len _ _ _ _ _
    (by rw [writeWord_sparse_size]; omega) (by omega) (by decide) (by decide), hr]

theorem liquidateCallbackMemory_read (mem bytes : ByteArray) (root : Nat)
    (sender : AccountAddress) (m : MarketData) (id index seized repaid : UInt256)
    (borrower receiver : AccountAddress) (badDebt : UInt256) (dp dl : Nat) (hroot : 96 ≤ root)
    (hd : dp + dl ≤ bytes.size) (hdl : dl < 2^64)
    (hb : root + 644 + 128 * m.collaterals.length < UInt256.size) :
    (liquidateCallbackMemory mem bytes root sender m id index seized repaid
      (UInt256.ofNat borrower.val) (UInt256.ofNat receiver.val) dp dl badDebt).readWithPadding
      root (liquidateCallbackSize m dl) =
      liquidateCallbackCalldata sender m id index seized repaid borrower receiver
        (bytes.extract dp (dp + dl)) badDebt := by
  have hs := liquidateCallbackMemory_size_lower mem bytes root sender m id index seized repaid
    (UInt256.ofNat borrower.val) (UInt256.ofNat receiver.val) badDebt dp dl hd
  have hw := liquidateCallbackMemory_words mem bytes root sender m id index seized repaid
    (UInt256.ofNat borrower.val) (UInt256.ofNat receiver.val) badDebt dp dl hroot hd hb
  have hr := hw.read
  rw [liquidateCallbackWords_length] at hr
  have hpad := paddedSize_le_add31 dl
  have ht : (liquidateCallbackMemory mem bytes root sender m id index seized repaid
      (UInt256.ofNat borrower.val) (UInt256.ofNat receiver.val) dp dl badDebt).readWithPadding
      (root + 644 + 128 * m.collaterals.length) (paddedSize dl) =
      bytes.extract dp (dp + dl) ++ ByteArray.zeroes (paddedSize dl - dl) := by
    rw [liquidateCallbackMemory, writeWord_read_above _ _ _ _ _ (by omega)
      (by rw [calldataBytesEncodeMemory_size _ _ _ _ _ hd]; omega)]
    have ho : root + 644 + 128 * m.collaterals.length =
        root + 612 + 128 * m.collaterals.length + 32 := by omega
    rw [ho]
    exact copyZeroMemory_read_padded _ _ _ _ _ hd hdl
  have he : liquidateCallbackSize m dl =
      4 + (32 * (20 + 4 * m.collaterals.length) + paddedSize dl) := by
    unfold liquidateCallbackSize returnDataAllocation paddedSize
    omega
  have hdsize : (bytes.extract dp (dp + dl)).size = dl := by rw [ByteArray.size_extract]; omega
  rw [he, readWithPadding_split_inbounds _ _ _ _ (by omega),
    liquidateCallbackMemory_selector _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd,
    readWithPadding_split_inbounds _ _ _ _ (by omega), hr,
    show root + 4 + 32 * (20 + 4 * m.collaterals.length) =
      root + 644 + 128 * m.collaterals.length by omega, ht]
  simp only [liquidateCallbackCalldata, liquidateCallbackWords, wordArrayBytes_append,
    wordArrayBytes, ByteArray.append_empty, ByteArray.append_assoc, hdsize]

end Benchmarks.Midnight
