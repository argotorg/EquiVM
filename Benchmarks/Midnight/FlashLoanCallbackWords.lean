import Benchmarks.Midnight.FlashLoanCallbackPrepare
import Benchmarks.Midnight.CalldataBytesEncodeMemory

/-! The contiguous ABI word prefix of the flash-loan callback input. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def flashLoanCallbackWords (bytes : ByteArray) (sender : AccountAddress)
    (tp tn ap an dl : Nat) : List UInt256 :=
  [UInt256.ofNat sender.val, UInt256.ofNat 128, UInt256.ofNat (160 + 32 * tn),
    UInt256.ofNat (192 + 32 * tn + 32 * an)] ++
    (UInt256.ofNat tn :: calldataArrayWords bytes tn tp) ++
    (UInt256.ofNat an :: calldataArrayWords bytes an ap) ++ [UInt256.ofNat dl]

theorem flashLoanCallbackWords_length (bytes : ByteArray) (sender : AccountAddress)
    (tp tn ap an dl : Nat) :
    (flashLoanCallbackWords bytes sender tp tn ap an dl).length = 7 + tn + an := by
  simp only [flashLoanCallbackWords, List.length_append, List.length_cons, List.length_nil,
    calldataArrayWords_length]
  omega

theorem flashLoanCallbackMemory_words (mem bytes : ByteArray) (sender : AccountAddress)
    (root tp tn ap an dp dl : Nat) (ha : ap + 32 * an ≤ bytes.size)
    (hd : dp + dl ≤ bytes.size) (hb : root + 228 + 32 * tn + 32 * an < UInt256.size) :
    MemoryWords (flashLoanCallbackMemory mem bytes sender root tp tn ap an dp dl) (root + 4)
      (flashLoanCallbackWords bytes sender tp tn ap an dl) := by
  let m0 := writeWord mem root (UInt256.ofNat (3522322627 * 2^224))
  let m1 := writeWord m0 (root + 4) (UInt256.ofNat sender.val)
  let m2 := writeWord m1 (root + 36) (UInt256.ofNat 128)
  let ts := UInt256.ofNat tn :: calldataArrayWords bytes tn tp
  let ass := UInt256.ofNat an :: calldataArrayWords bytes an ap
  let m3 := writeWordArray m2 (root + 132) ts
  let m4 := writeWord m3 (root + 68) (UInt256.ofNat (160 + 32 * tn))
  let m5 := calldataArrayCopyMemory m4 (root + 164 + 32 * tn) bytes ap an
  let m6 := writeWord m5 (root + 100) (UInt256.ofNat (192 + 32 * tn + 32 * an))
  have htlen : ts.length = tn + 1 := by simp [ts, calldataArrayWords_length]
  have halen : ass.length = an + 1 := by simp [ass, calldataArrayWords_length]
  have h1 : MemoryWords m1 (root + 4) [UInt256.ofNat sender.val] :=
    MemoryWords.of_writeWord m0 (root + 4) _ (by omega)
  have h2 := (h1.writeWord (off := root + 36) (UInt256.ofNat 128)
      (Or.inl (by simp <;> omega))).append
    (show MemoryWords m2 (root + 4 + 32 * [UInt256.ofNat sender.val].length)
      [UInt256.ofNat 128] from by
        convert MemoryWords.of_writeWord m1 (root + 36) (UInt256.ofNat 128) (by omega) using 1
        )
  have h3 : MemoryWords m3 (root + 4) [UInt256.ofNat sender.val, UInt256.ofNat 128] :=
    h2.writeWords ts (Or.inl (by simp <;> omega))
  have ht3 : MemoryWords m3 (root + 132) ts :=
    MemoryWords.of_writeWordArray m2 _ ts (by rw [htlen]; omega) (by simp [ts])
  have h4 := h3.writeWord (off := root + 68) (UInt256.ofNat (160 + 32 * tn))
    (Or.inl (by simp <;> omega))
  have ht4 := ht3.writeWord (off := root + 68) (UInt256.ofNat (160 + 32 * tn))
    (Or.inr (by omega))
  have hs4 : MemoryWords m4 (root + 68) [UInt256.ofNat (160 + 32 * tn)] :=
    MemoryWords.of_writeWord m3 _ _ (by omega)
  have h5 := h4.calldataArrayCopy (output := root + 164 + 32 * tn) ha
    (Or.inl (by simp <;> omega))
  have hs5 := hs4.calldataArrayCopy (output := root + 164 + 32 * tn) ha
    (Or.inl (by simp <;> omega))
  have ht5 := ht4.calldataArrayCopy (output := root + 164 + 32 * tn) ha
    (Or.inl (by rw [htlen]; omega))
  have ha5 : MemoryWords m5 (root + 164 + 32 * tn) ass :=
    calldataArrayCopyMemory_words m4 bytes _ ap an ha (by omega)
  have h6 := h5.writeWord (off := root + 100)
    (UInt256.ofNat (192 + 32 * tn + 32 * an)) (Or.inl (by simp <;> omega))
  have hs6 := hs5.writeWord (off := root + 100)
    (UInt256.ofNat (192 + 32 * tn + 32 * an)) (Or.inl (by simp <;> omega))
  have ht6 := ht5.writeWord (off := root + 100)
    (UInt256.ofNat (192 + 32 * tn + 32 * an)) (Or.inr (by omega))
  have ha6 := ha5.writeWord (off := root + 100)
    (UInt256.ofNat (192 + 32 * tn + 32 * an)) (Or.inr (by omega))
  have hs6' : MemoryWords m6 (root + 100) [UInt256.ofNat (192 + 32 * tn + 32 * an)] :=
    MemoryWords.of_writeWord m5 _ _ (by omega)
  have hhead := h6.append (last := [UInt256.ofNat (160 + 32 * tn)]) (by simpa using hs6)
  have hhead' := hhead.append (last := [UInt256.ofNat (192 + 32 * tn + 32 * an)])
    (by simpa using hs6')
  have htokens := hhead'.append (last := ts) (by simpa using ht6)
  have harrays := htokens.append (last := ass) (by
    convert ha6 using 1
    simp only [List.length_append, List.length_cons, List.length_nil, htlen,
      Nat.mul_add, Nat.mul_one, Nat.mul_zero, Nat.add_zero, Nat.add_assoc]
    omega)
  have hwords := harrays.calldataBytesEncode (output := root + 196 + 32 * tn + 32 * an) hd
    (by simp only [List.length_append, List.length_cons, List.length_nil, htlen, halen]; omega)
  have hlength := calldataBytesEncodeMemory_header m6 bytes
    (root + 196 + 32 * tn + 32 * an) dp dl hd (by omega)
  have hall := hwords.append (last := [UInt256.ofNat dl]) (by
    convert hlength using 1
    simp only [List.length_append, List.length_cons, List.length_nil, htlen, halen,
      Nat.mul_add, Nat.mul_one, Nat.mul_zero, Nat.add_zero, Nat.add_assoc]
    omega)
  simpa only [flashLoanCallbackMemory, flashLoanCallbackWords, calldataArrayEncodeMemory,
    List.cons_append, List.nil_append, m0, m1, m2, m3, m4, m5, m6, ts, ass] using hall

end Benchmarks.Midnight
