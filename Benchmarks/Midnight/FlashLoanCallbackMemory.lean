import Benchmarks.Midnight.FlashLoanCallbackWords
import Benchmarks.Midnight.FlashLoanCallbackABI

/-! The size, preserved memory, and selector of the callback input buffer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem calldataArrayEncodeMemory_size (mem bytes : ByteArray) (output ptr n : Nat) :
    (calldataArrayEncodeMemory mem output bytes ptr n).size =
      max mem.size (output + 32 + 32 * n) := by
  rw [calldataArrayEncodeMemory, writeWordArray_size_nonempty _ _ _ (by simp)]
  simp only [List.length_cons, calldataArrayWords_length]
  congr 1
  omega

theorem flashLoanCallbackMemory_size (mem bytes : ByteArray) (sender : AccountAddress)
    (root tp tn ap an dp dl : Nat) (ha : ap + 32 * an ≤ bytes.size)
    (hd : dp + dl ≤ bytes.size) :
    (flashLoanCallbackMemory mem bytes sender root tp tn ap an dp dl).size =
      max mem.size (root + 260 + 32 * tn + 32 * an + dl) := by
  rw [flashLoanCallbackMemory, calldataBytesEncodeMemory_size _ _ _ _ _ hd,
    writeWord_sparse_size, calldataArrayCopyMemory_size _ _ _ _ _ ha,
    writeWord_sparse_size, calldataArrayEncodeMemory_size,
    writeWord_sparse_size, writeWord_sparse_size, writeWord_sparse_size]
  omega

theorem flashLoanCallbackMemory_load_before (mem bytes : ByteArray) (sender : AccountAddress)
    (root tp tn ap an dp dl : Nat) (read : UInt256) (ha : ap + 32 * an ≤ bytes.size)
    (hd : dp + dl ≤ bytes.size) (hin : read.toNat + 32 ≤ mem.size)
    (hbelow : read.toNat + 32 ≤ root) :
    memLoad read (flashLoanCallbackMemory mem bytes sender root tp tn ap an dp dl) =
      memLoad read mem := by
  have hac (m : ByteArray) (off : Nat) :
      (calldataArrayCopyMemory m off bytes ap an).size = max m.size (off + 32 + 32 * an) :=
    calldataArrayCopyMemory_size _ _ _ _ _ ha
  have hat (m : ByteArray) (off : Nat) :
      (writeWordArray m off (UInt256.ofNat tn :: calldataArrayWords bytes tn tp)).size =
        max m.size (off + 32 + 32 * tn) := calldataArrayEncodeMemory_size m bytes off tp tn
  unfold flashLoanCallbackMemory
  rw [calldataBytesEncodeMemory_load_before _ _ _ _ _ _ hd,
    memLoad_writeWord_preserved,
    calldataArrayCopyMemory_load_preserved _ _ _ _ _ _ ha,
    memLoad_writeWord_preserved, calldataArrayEncodeMemory,
    memLoad_writeWordArray_below, memLoad_writeWord_preserved,
    memLoad_writeWord_preserved, memLoad_writeWord_preserved]
  all_goals
    try simp only [hac, hat, calldataArrayEncodeMemory_size, writeWord_sparse_size]
    first | omega | exact Or.inl (by omega)

theorem flashLoanCallbackMemory_selector (mem bytes : ByteArray) (sender : AccountAddress)
    (root tp tn ap an dp dl : Nat) (ha : ap + 32 * an ≤ bytes.size)
    (hd : dp + dl ≤ bytes.size) :
    (flashLoanCallbackMemory mem bytes sender root tp tn ap an dp dl).readWithPadding root 4 =
      (⟨#[0xd1, 0xf2, 0x60, 0xc3]⟩ : ByteArray) := by
  have hac (m : ByteArray) (off : Nat) :
      (calldataArrayCopyMemory m off bytes ap an).size = max m.size (off + 32 + 32 * an) :=
    calldataArrayCopyMemory_size _ _ _ _ _ ha
  have hat (m : ByteArray) (off : Nat) :
      (writeWordArray m off (UInt256.ofNat tn :: calldataArrayWords bytes tn tp)).size =
        max m.size (off + 32 + 32 * tn) := calldataArrayEncodeMemory_size m bytes off tp tn
  have hr := writeWord_sparse_read_window mem root 0 4
    (UInt256.ofNat (3522322627 * 2^224)) (by decide) (by decide) (by decide)
  have hsel : (UInt256.ofNat (3522322627 * 2^224)).toByteArray.extract 0 4 =
      (⟨#[0xd1, 0xf2, 0x60, 0xc3]⟩ : ByteArray) := by decide +kernel
  simp only [Nat.add_zero, Nat.zero_add, hsel] at hr
  unfold flashLoanCallbackMemory
  rw [calldataBytesEncodeMemory_read_before _ _ _ _ _ _ _ hd (by decide) (by decide),
    writeWord_sparse_read_preserved_len _ _ _ _ _,
    calldataArrayCopyMemory_read_before _ _ _ _ _ _ _ ha (by decide) (by decide),
    writeWord_sparse_read_preserved_len _ _ _ _ _, calldataArrayEncodeMemory,
    writeWordArray_read_below_len, writeWord_sparse_read_preserved_len _ _ _ _ _,
    writeWord_sparse_read_preserved_len _ _ _ _ _, hr]
  all_goals
    try simp only [hac, hat, calldataArrayEncodeMemory_size, writeWord_sparse_size]
    first | omega | exact Or.inl (by omega)

end Benchmarks.Midnight
