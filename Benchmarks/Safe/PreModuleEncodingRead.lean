import Benchmarks.Safe.PreModuleEncodingMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe

theorem preModuleHeadMemory_array (mem : ByteArray) (base : Nat) (target value : UInt256) :
    WordArrayMemory (preModuleHeadMemory mem base target value) base
      [UInt256.land target solcAddrMask, value, UInt256.ofNat 160] := by
  intro i hi
  have hi' : i < 3 := by simpa using hi
  interval_cases i
  · simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero]
    rw [preModuleHeadMemory,
      writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by omega, by
        simp only [writeWord_sparse_size]; omega⟩),
      writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by omega, by
        rw [writeWord_sparse_size]; omega⟩), writeWord_sparse_read_back]
  · simp only [Nat.mul_one, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [preModuleHeadMemory,
      writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by omega, by
        rw [writeWord_sparse_size]; omega⟩), writeWord_sparse_read_back]
  · simp only [show 32 * 2 = 64 from rfl, List.getElem_cons_succ, List.getElem_cons_zero]
    exact writeWord_sparse_read_back _ _ _

theorem preModuleArgsMemory_array (mem : ByteArray) (base len : Nat)
    (target value operation sender : UInt256) (words : List UInt256)
    (hm : mem.size ≤ base + 160) (hn : words.length = (len + 31) / 32) :
    WordArrayMemory (preModuleArgsMemory mem base len target value operation sender words)
      base [UInt256.land target solcAddrMask, value, UInt256.ofNat 160,
        operation, UInt256.land solcAddrMask sender] := by
  let m := memoryBytesEncodedMemory (preModuleHeadMemory mem base target value)
    (base + 160) len words
  have hs : m.size = base + 224 + len := by
    dsimp [m]
    rw [memoryBytesEncodedMemory_size _ _ _ _ (by rw [preModuleHeadMemory_size]; omega) hn]
  have hh : WordArrayMemory m base
      [UInt256.land target solcAddrMask, value, UInt256.ofNat 160] := by
    intro i hi
    have hi' : i < 3 := by simpa using hi
    rw [show m = memoryBytesEncodedMemory _ _ _ _ from rfl,
      memoryBytesEncodedMemory_preserved _ _ _ _ _ _ (by
        rw [preModuleHeadMemory_size]; omega) (by omega)]
    exact preModuleHeadMemory_array mem base target value i hi
  have hh' := hh.writeAfter m base _ (by simp; omega) (base + 96) operation (by simp)
  have hh'' := hh'.writeAfter _ base _ (by simp; rw [writeWord_sparse_size]; omega)
    (base + 128) (UInt256.land solcAddrMask sender) (by simp)
  intro i hi
  have hi' : i < 5 := by simpa using hi
  by_cases hlo : i < 3
  · have hr := hh'' i (by simpa using hlo)
    interval_cases i <;> exact hr
  · have hi2 : i = 3 ∨ i = 4 := by omega
    rcases hi2 with rfl | rfl
    · simp only [show 32 * 3 = 96 from rfl, List.getElem_cons_succ, List.getElem_cons_zero]
      rw [preModuleArgsMemory,
        writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by omega, by
          rw [writeWord_sparse_size]; omega⟩), writeWord_sparse_read_back]
    · simp only [show 32 * 4 = 128 from rfl, List.getElem_cons_succ, List.getElem_cons_zero]
      exact writeWord_sparse_read_back _ _ _

theorem preModuleArgsMemory_read (mem : ByteArray) (base len : Nat)
    (target value operation sender : UInt256) (words : List UInt256)
    (hm : mem.size ≤ base + 160) (hn : words.length = (len + 31) / 32) :
    (preModuleArgsMemory mem base len target value operation sender words).readWithPadding
      base (192 + 32 * words.length) =
      wordBytes [UInt256.land target solcAddrMask, value, UInt256.ofNat 160,
        operation, UInt256.land solcAddrMask sender, UInt256.ofNat len] ++
        (wordBytes words).extract 0 len ++ ByteArray.zeroes (32 * words.length - len) := by
  have hs := preModuleArgsMemory_size mem base len target value operation sender words hm hn
  have hh := (preModuleArgsMemory_array mem base len target value operation sender words
    hm hn).read _ _ _ (by simp; omega)
  simp only [List.length_cons, List.length_nil] at hh
  have ht :
      (preModuleArgsMemory mem base len target value operation sender words).readWithPadding
        (base + 160) (32 + 32 * words.length) =
        (UInt256.ofNat len).toByteArray ++ (wordBytes words).extract 0 len ++
          ByteArray.zeroes (32 * words.length - len) := by
    have hb : (preModuleHeadMemory mem base target value).size ≤ base + 160 := by
      rw [preModuleHeadMemory_size]; omega
    have hm' := memoryBytesEncodedMemory_size (preModuleHeadMemory mem base target value)
      (base + 160) len words hb hn
    rw [preModuleArgsMemory,
      writeWordReadAbove _ _ _ _ _ (by rw [writeWord_sparse_size, hn]; omega)
        (by omega),
      writeWordReadAbove _ _ _ _ _ (by rw [hn]; omega) (by omega),
      memoryBytesEncodedMemory_read _ _ _ _ hb hn]
  rw [show 192 + 32 * words.length = 160 + (32 + 32 * words.length) by omega,
    byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by omega)
      (by rw [hn]; omega), hh, ht]
  simp only [wordBytes, ByteArray.append_empty, ByteArray.append_assoc]

end Benchmarks.Safe
