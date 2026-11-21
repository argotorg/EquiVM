import Benchmarks.Midnight.RepayCallbackWords
import Benchmarks.Midnight.RepayCallbackABI
import Benchmarks.Midnight.FlashLoanCallbackRead

/-! Reading onRepay's full input buffer, including its selector and padded bytes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem marketEncodeMemory_read_before (mem : ByteArray) (output : Nat) (m : MarketData)
    (read count : Nat) (hin : read + count ≤ mem.size) (hl : read + count ≤ output)
    (hp : 0 < count) (hc : count < 2^64) :
    (marketEncodeMemory mem output m).readWithPadding read count =
      mem.readWithPadding read count := by
  have hs1 := (memoryPrefix_writeWordArray mem output output m.headWords le_rfl).size
  have hs2 := (memoryPrefix_writeWord (writeWordArray mem output m.headWords)
    (output + 256) output (UInt256.ofNat m.collaterals.length) (Or.inl (by omega))).size
  have hs3 := (memoryPrefix_writeWordArray (marketEncodeHeadMemory mem output m)
    (output + 288) output (m.collaterals.flatMap CollateralData.words) (by omega)).size
  unfold marketEncodeMemory marketEncodeHeadMemory
  rw [writeWordArray_read_below_len _ _ _ _ _ (by exact hin.trans (hs1.trans (hs2.trans hs3)))
      (by omega) hp hc,
    writeWordArray_read_below_len _ _ _ _ _ (hin.trans (hs1.trans hs2)) (by omega) hp hc,
    writeWord_sparse_read_preserved_len _ _ _ _ _ (hin.trans hs1) (Or.inl (by omega)) hp hc,
    writeWordArray_read_below_len _ _ _ _ _ hin hl hp hc]

theorem repayCallbackMemory_size_lower (mem bytes : ByteArray) (root : Nat) (m : MarketData)
    (id units user : UInt256) (dp dl : Nat) (hd : dp + dl ≤ bytes.size) :
    root + 516 + 128 * m.collaterals.length + dl ≤
      (repayCallbackMemory mem bytes root m id units user dp dl).size := by
  rw [repayCallbackMemory, calldataBytesEncodeMemory_size _ _ _ _ _ hd]
  omega

theorem repayCallbackMemory_selector (mem bytes : ByteArray) (root : Nat) (m : MarketData)
    (id units user : UInt256) (dp dl : Nat) (hd : dp + dl ≤ bytes.size) :
    (repayCallbackMemory mem bytes root m id units user dp dl).readWithPadding root 4 =
      (⟨#[0x29, 0x0e, 0xf4, 0xa4]⟩ : ByteArray) := by
  let head := repayCallbackHeaderMemory mem root id
  have hh : root + 4 ≤ head.size := by
    simp only [head, repayCallbackHeaderMemory, writeWord_sparse_size]
    omega
  have he := (marketEncodeMemory_prefix head (root + 164) (root + 164) m le_rfl).size
  dsimp only [head] at hh he
  have hr := writeWord_sparse_read_window mem root 0 4
    (UInt256.ofNat (688845988 * 2^224)) (by decide) (by decide) (by decide)
  have hsel : (UInt256.ofNat (688845988 * 2^224)).toByteArray.extract 0 4 =
      (⟨#[0x29, 0x0e, 0xf4, 0xa4]⟩ : ByteArray) := by decide +kernel
  simp only [Nat.add_zero, Nat.zero_add, hsel] at hr
  unfold repayCallbackMemory repayCallbackFieldsMemory
  rw [calldataBytesEncodeMemory_read_before _ _ _ _ _ _ _ hd (by decide) (by decide)
      (by simp only [writeWord_sparse_size]; change root + 4 ≤ max _ _; omega) (by omega),
    writeWord_sparse_read_preserved_len _ _ _ _ _
      (by simp only [writeWord_sparse_size]; exact (hh.trans he).trans (by omega))
      (Or.inl (by omega)) (by decide) (by decide),
    writeWord_sparse_read_preserved_len _ _ _ _ _
      (by rw [writeWord_sparse_size]; omega) (Or.inl (by omega)) (by decide) (by decide),
    writeWord_sparse_read_preserved_len _ _ _ _ _ (hh.trans he)
      (Or.inl (by omega)) (by decide) (by decide),
    marketEncodeMemory_read_before _ _ _ _ _ hh (by omega) (by decide) (by decide)]
  unfold repayCallbackHeaderMemory
  rw [writeWord_sparse_read_preserved_len _ _ _ _ _
      (by rw [writeWord_sparse_size]; omega) (Or.inl (by omega)) (by decide) (by decide),
    writeWord_sparse_read_preserved_len _ _ _ _ _
      (by rw [writeWord_sparse_size]; omega) (Or.inl (by omega)) (by decide) (by decide), hr]

theorem repayCallbackMemory_read (mem bytes : ByteArray) (root : Nat) (m : MarketData)
    (id units : UInt256) (user : AccountAddress) (dp dl : Nat) (hroot : 96 ≤ root)
    (hd : dp + dl ≤ bytes.size) (hdl : dl < 2^64)
    (hb : root + 484 + 128 * m.collaterals.length < UInt256.size) :
    (repayCallbackMemory mem bytes root m id units (UInt256.ofNat user.val) dp dl).readWithPadding
      root (repayCallbackSize m dl) =
      repayCallbackCalldata m id units user (bytes.extract dp (dp + dl)) := by
  have hs := repayCallbackMemory_size_lower mem bytes root m id units
    (UInt256.ofNat user.val) dp dl hd
  have hw := repayCallbackMemory_words mem bytes root m id units
    (UInt256.ofNat user.val) dp dl hroot hd hb
  have hr := hw.read
  rw [repayCallbackWords_length] at hr
  have ht : (repayCallbackMemory mem bytes root m id units
      (UInt256.ofNat user.val) dp dl).readWithPadding
      (root + 484 + 128 * m.collaterals.length) (paddedSize dl) =
      bytes.extract dp (dp + dl) ++ ByteArray.zeroes (paddedSize dl - dl) := by
    have ho : root + 484 + 128 * m.collaterals.length =
        root + 452 + 128 * m.collaterals.length + 32 := by omega
    rw [ho]
    exact copyZeroMemory_read_padded _ _ _ _ _ hd hdl
  have he : repayCallbackSize m dl = 4 + (32 * (15 + 4 * m.collaterals.length) + paddedSize dl) := by
    unfold repayCallbackSize returnDataAllocation paddedSize
    omega
  have hpad := paddedSize_le_add31 dl
  have hdsize : (bytes.extract dp (dp + dl)).size = dl := by rw [ByteArray.size_extract]; omega
  rw [he, readWithPadding_split_inbounds _ _ _ _ (by omega),
    repayCallbackMemory_selector _ _ _ _ _ _ _ _ _ hd,
    readWithPadding_split_inbounds _ _ _ _ (by omega), hr,
    show root + 4 + 32 * (15 + 4 * m.collaterals.length) =
      root + 484 + 128 * m.collaterals.length by omega, ht]
  simp only [repayCallbackCalldata, repayCallbackWords, wordArrayBytes_append,
    wordArrayBytes, ByteArray.append_empty, ByteArray.append_assoc, hdsize]

end Benchmarks.Midnight
