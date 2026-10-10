import Benchmarks.UniswapV3.Pool.ObserveCalldata
import Benchmarks.UniswapV3.Pool.DynamicWordArray
import Benchmarks.UniswapV3.Pool.MemoryGasBound

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def observeInputFree (n : Nat) : UInt256 := UInt256.ofNat (160 + 32 * n)
def observeInputAw (n : Nat) : UInt256 := UInt256.ofNat (n + 6)
def observeInputHead (n : Nat) : ByteArray :=
  writeWord (writeWord solcFreePtrMem 64 (observeInputFree n)) 128 (UInt256.ofNat n)
def observeInputCopy (cd : ByteArray) (start n : Nat) : ByteArray :=
  cd.write start (observeInputHead n) 160 (32 * n)
def observeInputMem (cd : ByteArray) (start n : Nat) : ByteArray :=
  writeWord (observeInputCopy cd start n) (160 + 32 * n) ⟨0⟩

theorem observeInputHead_size (n : Nat) : (observeInputHead n).size = 160 := by
  simp only [observeInputHead, writeWord_sparse_size, solcFreePtrMem_size]
  rfl

theorem observeInputCopy_size (cd : ByteArray) (start n : Nat)
    (hb : start + 32 * n ≤ cd.size) : (observeInputCopy cd start n).size = 160 + 32 * n := by
  unfold observeInputCopy
  by_cases hn : n = 0
  · subst n
    rw [Nat.mul_zero, byteArray_write_len_zero, observeInputHead_size]
  · rw [copyWindow_size _ _ _ _ _ (by omega) hb (by rw [observeInputHead_size]),
      observeInputHead_size]
    omega

theorem observeInputMem_size (cd : ByteArray) (start n : Nat)
    (hb : start + 32 * n ≤ cd.size) : (observeInputMem cd start n).size = 192 + 32 * n := by
  rw [observeInputMem, writeWord_sparse_size, observeInputCopy_size _ _ _ hb]
  omega

theorem observeInputCopy_preserve (cd : ByteArray) (start n read : Nat)
    (hb : start + 32 * n ≤ cd.size) (hr : read + 32 ≤ 160) :
    (observeInputCopy cd start n).readWithPadding read 32 =
      (observeInputHead n).readWithPadding read 32 := by
  unfold observeInputCopy
  by_cases hn : n = 0
  · subst n; rw [Nat.mul_zero, byteArray_write_len_zero]
  · exact copyWindow_read_preserved _ _ _ _ _ _ (by omega) hb
      (by rw [observeInputHead_size]) (by rw [observeInputHead_size]; exact hr) (Or.inl hr)

theorem observeInputMemory (cd : ByteArray) (start n : Nat) (hn : n ≤ 2 ^ 32)
    (hb : start + 32 * n ≤ cd.size) :
    HeapMemory (observeInputMem cd start n) (observeInputAw n) (observeInputFree n) ∧
    DynamicWordArrayMemory (observeInputMem cd start n) ⟨128⟩ (calldataWordList cd start n) ∧
    (observeInputFree n).toNat ≤ (observeInputAw n).toNat * 32 + 32 ∧
    MemoryGasBound (observeInputAw n) 0 (2 ^ 200) := by
  have hf : (observeInputFree n).toNat = 160 + 32 * n :=
    ulit_toNat' _ (by change _ < 2 ^ 256; omega)
  have ha : (observeInputAw n).toNat = n + 6 :=
    ulit_toNat' _ (by change _ < 2 ^ 256; omega)
  have hp : ∀ read, read + 32 ≤ 160 →
      (observeInputMem cd start n).readWithPadding read 32 =
        (observeInputHead n).readWithPadding read 32 := by
    intro read hr
    rw [observeInputMem, writeWord_sparse_read_preserved _ _ _ _
      (Or.inl ⟨by omega, by rw [observeInputCopy_size _ _ _ hb]; omega⟩),
      observeInputCopy_preserve _ _ _ _ hb hr]
  refine ⟨⟨by rw [observeInputMem_size _ _ _ hb]; omega, ?_, by rw [hf]; omega,
    by rw [hf, observeInputMem_size _ _ _ hb]; omega, by rw [ActiveWords, ha]; omega⟩,
    ⟨?_, ?_⟩, by rw [hf, ha]; omega, ?_⟩
  · rw [hp 64 (by decide), observeInputHead,
      writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨by decide, by
        rw [writeWord_sparse_size, solcFreePtrMem_size]; decide⟩), writeWord_sparse_read_back]
  · simp only [dynamicWordArrayWords, List.length_cons, calldataWordList_length]
    rw [observeInputMem_size _ _ _ hb]
    change 128 + 32 * (n + 1) ≤ 192 + 32 * n
    omega
  · intro i hi
    simp only [dynamicWordArrayWords, List.length_cons, calldataWordList_length] at hi
    cases i with
    | zero =>
        simp only [dynamicWordArrayWords, List.getElem_cons_zero, calldataWordList_length,
          Nat.mul_zero, Nat.add_zero]
        change (observeInputMem cd start n).readWithPadding 128 32 = _
        rw [hp 128 (by decide), observeInputHead, writeWord_sparse_read_back]
    | succ i =>
        simp only [dynamicWordArrayWords, List.getElem_cons_succ,
          calldataWordList_getElem cd start n i (by omega)]
        change (observeInputMem cd start n).readWithPadding (128 + 32 * (i + 1)) 32 = _
        rw [observeInputMem, writeWord_sparse_read_preserved _ _ _ _
          (Or.inl ⟨by omega, by rw [observeInputCopy_size _ _ _ hb]; omega⟩)]
        rw [show 128 + 32 * (i + 1) = 160 + 32 * i by omega, observeInputCopy,
          copyWindow_read_word _ _ _ _ _ _ (by omega) hb
            (by rw [observeInputHead_size]) (by omega),
          readWithPadding_eq_extract _ _ (by omega), calldataWord_bytes_at (by omega)]
  · have hm := Cₘ_monotone_of_lt (show n + 6 ≤ 2 ^ 32 + 6 by omega)
      (by decide : 2 ^ 32 + 6 < UInt256.size)
    have hc : Cₘ (UInt256.ofNat (2 ^ 32 + 6)) ≤ 2 ^ 200 := by native_decide
    exact le_trans hm hc

end Benchmarks.UniswapV3.Pool
