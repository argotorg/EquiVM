import Benchmarks.Morpho.MetaMorphoV1_1.Eip712ABI

/-! Final header stores and the empty extensions tail of the domain return buffer. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Theory

-- GENERALIZES wordSequenceMemory_read_below_unbounded to a window after the whole sequence.
theorem wordSequenceMemory_read_above (mem : ByteArray) (off : Nat)
    (words : List UInt256) (read len : Nat) (hin : read + len ≤ mem.size)
    (habove : off + 32 * words.length ≤ read) :
    (wordSequenceMemory mem off words).readWithPadding read len = mem.readWithPadding read len := by
  induction words generalizing mem off with
  | nil => rfl
  | cons word words ih =>
      rw [wordSequenceMemory, ih _ _ (by rw [writeWord_sparse_size]; omega)
        (by simp only [List.length_cons] at habove; omega)]
      exact writeWord_sparse_read_preserved_unbounded mem off read len word hin
        (.inr (by simp only [List.length_cons] at habove; omega))

end Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def eip712HeadPrefixWords (name : ByteArray) : List UInt256 :=
  [eip712FieldsWord, ⟨224⟩, UInt256.ofNat (256 + paddedSize name.size)]

def eip712HeadSuffixWords (I : ExecutionEnv) (name version : ByteArray) : List UInt256 :=
  [UInt256.ofNat Ethereum.chainId, UInt256.ofNat I.codeOwner.val, ⟨0⟩,
   UInt256.ofNat (288 + paddedSize name.size + paddedSize version.size)]

def eip712FinishMemory (I : ExecutionEnv) (mem : ByteArray) (out : Nat)
    (name version : ByteArray) : ByteArray :=
  writeWord (wordSequenceMemory mem (out + 96) (eip712HeadSuffixWords I name version))
    (out + 288 + paddedSize name.size + paddedSize version.size) ⟨0⟩

theorem eip712FinishMemory_read (I : ExecutionEnv) (mem name version : ByteArray) (out : Nat)
    (hmem : out + 288 + paddedSize name.size + paddedSize version.size ≤ mem.size)
    (hhead : mem.readWithPadding out 96 = wordBytes (eip712HeadPrefixWords name))
    (htail : mem.readWithPadding (out + 224)
      (64 + paddedSize name.size + paddedSize version.size) =
        stringPayloadBytes name ++ stringPayloadBytes version) :
    (eip712FinishMemory I mem out name version).readWithPadding out
      (320 + paddedSize name.size + paddedSize version.size) =
      eip712ReturnBytes I name version := by
  let mid := wordSequenceMemory mem (out + 96) (eip712HeadSuffixWords I name version)
  have hmid : mid.size = max mem.size (out + 224) :=
    wordSequenceMemory_size _ (by omega)
  have hfinal : out + 320 + paddedSize name.size + paddedSize version.size ≤
      (eip712FinishMemory I mem out name version).size := by
    rw [eip712FinishMemory, writeWord_sparse_size]
    omega
  have hfirst : (eip712FinishMemory I mem out name version).readWithPadding out 96 =
      wordBytes (eip712HeadPrefixWords name) := by
    rw [eip712FinishMemory, writeWord_sparse_read_preserved_unbounded _ _ _ _ _
      (by change out + 96 ≤ mid.size; rw [hmid]; omega) (.inl (by omega)),
      wordSequenceMemory_read_below_unbounded _ _ _ _ _ (by omega) (by omega), hhead]
  have hlast : (eip712FinishMemory I mem out name version).readWithPadding (out + 96) 128 =
      wordBytes (eip712HeadSuffixWords I name version) := by
    rw [eip712FinishMemory, writeWord_sparse_read_preserved_unbounded _ _ _ _ _
      (by change out + 96 + 128 ≤ mid.size; rw [hmid]; omega) (.inl (by omega))]
    exact wordSequenceMemory_read _ _ _
  have hstrings : (eip712FinishMemory I mem out name version).readWithPadding (out + 224)
      (64 + paddedSize name.size + paddedSize version.size) =
        stringPayloadBytes name ++ stringPayloadBytes version := by
    rw [eip712FinishMemory, writeWord_sparse_read_preserved_unbounded _ _ _ _ _
      (by change _ ≤ mid.size; rw [hmid]; omega) (.inl (by omega)),
      wordSequenceMemory_read_above _ _ _ _ _ (by omega)
        (by simp only [eip712HeadSuffixWords, List.length_cons, List.length_nil]; omega), htail]
  have hext : (eip712FinishMemory I mem out name version).readWithPadding
      (out + 288 + paddedSize name.size + paddedSize version.size) 32 =
      (⟨0⟩ : UInt256).toByteArray := writeWord_sparse_read_back _ _ _
  rw [show 320 + paddedSize name.size + paddedSize version.size =
      96 + (128 + (64 + paddedSize name.size + paddedSize version.size + 32)) by omega,
    readWithPadding_split _ _ _ _ (by omega), hfirst,
    readWithPadding_split _ _ _ _ (by omega), hlast,
    show out + 96 + 128 = out + 224 by omega,
    readWithPadding_split _ _ _ _ (by omega), hstrings,
    show out + 224 + (64 + paddedSize name.size + paddedSize version.size) =
      out + 288 + paddedSize name.size + paddedSize version.size by omega, hext]
  simp only [eip712ReturnBytes, eip712HeadWords, eip712HeadPrefixWords, eip712HeadSuffixWords,
    wordBytes, ByteArray.append_empty, ByteArray.append_assoc]

end Benchmarks.Morpho.MetaMorphoV1_1
