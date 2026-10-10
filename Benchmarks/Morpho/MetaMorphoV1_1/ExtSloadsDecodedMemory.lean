import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsCopyLoop
import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsReturnBuffer

/-! Memory invariants for the array produced by the return decoder. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def extSloadsReturnWords (out : ByteArray) : List UInt256 :=
  wordArrayWords (fun i => calldataWord out (extSloadsReturnOffset out + 32 + 32 * i))
    0 (extSloadsReturnCount out)

theorem extSloadsReturnWords_length (out : ByteArray) :
    (extSloadsReturnWords out).length = extSloadsReturnCount out :=
  wordArrayWords_length _ _ _

theorem extSloadsReturnWords_get (out : ByteArray) (i : Nat)
    (hi : i < (extSloadsReturnWords out).length) :
    (extSloadsReturnWords out)[i] = calldataWord out (extSloadsReturnOffset out + 32 + 32 * i) := by
  have h := wordArrayWords_getElem
    (fun i => calldataWord out (extSloadsReturnOffset out + 32 + 32 * i))
    0 (extSloadsReturnCount out) i (by rwa [extSloadsReturnWords_length] at hi)
  change (extSloadsReturnWords out)[i]? = some _ at h
  simpa only [List.getElem?_eq_getElem hi, Option.some.injEq, Nat.zero_add] using h

theorem extSloadsArraySize_rounded {out : ByteArray}
    (hcount : extSloadsReturnCount out ≤ solcMaxU64) :
    (roundedSize (extSloadsArraySize out)).toNat = 32 + 32 * extSloadsReturnCount out := by
  change extSloadsReturnCount out ≤ 18446744073709551615 at hcount
  have hs : 32 + 32 * extSloadsReturnCount out < UInt256.size := by change _ < 2 ^ 256; omega
  have hb : 32 + 32 * extSloadsReturnCount out + 31 < UInt256.size := by change _ < 2 ^ 256; omega
  rw [roundedSize_toNat, extSloadsArraySize, UInt256.toNat_ofNat_of_lt hs,
    Nat.mod_eq_of_lt hb]
  omega

theorem extSloadsArrayBound {out : ByteArray} {ptr : UInt256}
    (hcount : extSloadsReturnCount out ≤ solcMaxU64)
    (hfit : allocationFits ptr (extSloadsArraySize out)) :
    ptr.toNat + 32 + 32 * extSloadsReturnCount out < 2 ^ 64 := by
  rw [allocationFits_iff_sum_lt, extSloadsArraySize_rounded hcount] at hfit
  omega

theorem extSloadsArrayHeaderMem_load {mem out : ByteArray} {base off : Nat} {ptr : UInt256}
    (hlo : 96 ≤ base) (hmem : base + out.size ≤ mem.size)
    (hsep : base + out.size ≤ ptr.toNat)
    (hin : off + 32 ≤ out.size)
    (hread : memLoad (UInt256.ofNat (base + off)) mem = calldataWord out off) :
    memLoad (UInt256.ofNat (base + off)) (extSloadsArrayHeaderMem mem ptr out) =
      calldataWord out off := by
  have hp : ptr.toNat < UInt256.size := ptr.val.isLt
  have hf : base + off < UInt256.size := by omega
  rw [extSloadsArrayHeaderMem, memLoad_write_above _ _ ptr.toNat _
    (by rw [UInt256.toNat_ofNat_of_lt hf, writeWord_sparse_size]; omega)
    (by rw [UInt256.toNat_ofNat_of_lt hf]; omega)]
  rw [Reasoning.Theory.writeWord, memLoad_write_disjoint _ _ _ _
    (by rw [UInt256.toNat_ofNat_of_lt hf]; omega)
    (.inr (by rw [UInt256.toNat_ofNat_of_lt hf]; omega))]
  exact hread

def extSloadsDecodedMem (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  wordSequenceMemory (extSloadsArrayHeaderMem mem ptr out) (ptr.toNat + 32)
    (extSloadsReturnWords out)

theorem extSloadsDecodedMem_size (mem : ByteArray) (ptr : UInt256) (out : ByteArray) :
    (extSloadsDecodedMem mem ptr out).size =
      max (max mem.size 96) (ptr.toNat + 32 + 32 * extSloadsReturnCount out) := by
  rw [extSloadsDecodedMem, wordSequenceMemory_size _ (by
    simp only [extSloadsArrayHeaderMem, writeWord_sparse_size]; omega)]
  simp only [extSloadsArrayHeaderMem, writeWord_sparse_size, extSloadsReturnWords_length]
  omega

theorem extSloadsDecodedMem_length (mem : ByteArray) (ptr : UInt256) (out : ByteArray) :
    memLoad ptr (extSloadsDecodedMem mem ptr out) = UInt256.ofNat (extSloadsReturnCount out) := by
  apply mloadWordValue_of_readWithPadding
  · rw [extSloadsDecodedMem_size]; omega
  · rw [extSloadsDecodedMem, wordSequenceMemory_read_below _ _ _ _
      (by simp only [extSloadsArrayHeaderMem, writeWord_sparse_size]; omega) (by omega)]
    exact writeWord_sparse_read_back _ _ _

theorem extSloadsDecodedMem_cursor (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hptr : 96 ≤ ptr.toNat) :
    memLoad ⟨64⟩ (extSloadsDecodedMem mem ptr out) = nextCursor ptr (extSloadsArraySize out) := by
  apply mloadWordValue_of_readWithPadding
  · rw [extSloadsDecodedMem_size]; change 64 < _; omega
  · change (extSloadsDecodedMem mem ptr out).readWithPadding 64 32 = _
    rw [extSloadsDecodedMem, wordSequenceMemory_read_below _ _ _ _
      (by simp only [extSloadsArrayHeaderMem, writeWord_sparse_size]; omega) (by omega)]
    rw [extSloadsArrayHeaderMem, writeWord_sparse_read_preserved _ _ _ _
      (.inl ⟨hptr, by rw [writeWord_sparse_size]; omega⟩)]
    exact writeWord_sparse_read_back _ _ _

theorem extSloadsDecodedMem_first (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hn : 0 < extSloadsReturnCount out) (hp : ptr.toNat + 32 < UInt256.size) :
    memLoad (ptr + ⟨32⟩) (extSloadsDecodedMem mem ptr out) =
      calldataWord out (extSloadsReturnOffset out + 32) := by
  have hadd : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := addWord_toNat ptr ⟨32⟩ hp
  apply mloadWordValue_of_readWithPadding
  · rw [hadd, extSloadsDecodedMem_size]; omega
  · rw [hadd]
    cases hcount : extSloadsReturnCount out with
    | zero => omega
    | succ n =>
        simp only [extSloadsDecodedMem, extSloadsReturnWords, hcount, wordArrayWords,
          wordSequenceMemory, Nat.mul_zero, Nat.add_zero]
        rw [wordSequenceMemory_read_below _ _ _ _
          (by rw [writeWord_sparse_size]; omega) (by omega)]
        exact writeWord_sparse_read_back _ _ _

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
