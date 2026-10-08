import Benchmarks.EAS.Attester.AttestCellEncodeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

def attestCellWords (input : UInt256) : List UInt256 :=
  [⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨192⟩, ⟨0⟩, ⟨32⟩, input]

set_option maxRecDepth 1000 in
theorem attestCellEncodedMemory_read (mem : ByteArray) (dst : Nat) (input : UInt256) :
    (attestCellEncodedMemory mem dst input).readWithPadding dst 256 = wordBytes (attestCellWords
        input) := by
  have heq : attestCellEncodedMemory mem dst input = writeCascade mem
      [(dst, ⟨0⟩), (dst + 32, ⟨0⟩), (dst + 64, ⟨1⟩), (dst + 96, ⟨0⟩),
        (dst + 128, ⟨192⟩), (dst + 192, ⟨32⟩), (dst + 224, input),
        (dst + 256, ⟨0⟩), (dst + 160, ⟨0⟩)] := by
    simp only [attestCellEncodedMemory, attestCellEncodedPayload, attestCellEncodedHead,
      writeCascade, Reasoning.Theory.writeWord]
  apply readWithPadding_words _ dst (attestCellWords input)
  · change dst + 256 ≤ _
    rw [attestCellEncodedMemory_size]; omega
  · intro i
    rw [heq]
    fin_cases i
    · apply writeCascade_read_word_at (i := 0)
      · rfl
      · simp only [List.drop_succ_cons, List.drop_zero, List.forall_mem_cons,
          List.not_mem_nil, false_implies, forall_const, and_true] <;>
        dsimp <;> omega
    · apply writeCascade_read_word_at (i := 1)
      · rfl
      · simp only [List.drop_succ_cons, List.drop_zero, List.forall_mem_cons,
          List.not_mem_nil, false_implies, forall_const, and_true] <;>
        dsimp <;> omega
    · apply writeCascade_read_word_at (i := 2)
      · rfl
      · simp only [List.drop_succ_cons, List.drop_zero, List.forall_mem_cons,
          List.not_mem_nil, false_implies, forall_const, and_true] <;>
        dsimp <;> omega
    · apply writeCascade_read_word_at (i := 3)
      · rfl
      · simp only [List.drop_succ_cons, List.drop_zero, List.forall_mem_cons,
          List.not_mem_nil, false_implies, forall_const, and_true] <;>
        dsimp <;> omega
    · apply writeCascade_read_word_at (i := 4)
      · rfl
      · simp only [List.drop_succ_cons, List.drop_zero, List.forall_mem_cons,
          List.not_mem_nil, false_implies, forall_const, and_true] <;>
        dsimp <;> omega
    · apply writeCascade_read_word_at (i := 8)
      · rfl
      · simp only [List.drop_succ_cons, List.drop_zero, List.forall_mem_cons,
          List.not_mem_nil, false_implies, forall_const, and_true] <;>
        dsimp <;> omega
    · apply writeCascade_read_word_at (i := 5)
      · rfl
      · simp only [List.drop_succ_cons, List.drop_zero, List.forall_mem_cons,
          List.not_mem_nil, false_implies, forall_const, and_true] <;>
        dsimp <;> omega
    · apply writeCascade_read_word_at (i := 6)
      · rfl
      · simp only [List.drop_succ_cons, List.drop_zero, List.forall_mem_cons,
          List.not_mem_nil, false_implies, forall_const, and_true] <;>
        dsimp <;> omega

theorem attestCellEncodedMemory_read_below {mem : ByteArray} {dst read len : Nat}
    {input : UInt256} (hin : read + len ≤ mem.size) (hbelow : read + len ≤ dst) :
    (attestCellEncodedMemory mem dst input).readWithPadding read len = mem.readWithPadding read len
        := by
  unfold attestCellEncodedMemory attestCellEncodedPayload attestCellEncodedHead
  rw [writeCascade_read_preserved_unbounded _ _ _ _
    (by simp only [writeCascade, writeWord_sparse_size]; omega) (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> exact .inl (by omega))]
  rw [writeWord_sparse_read_preserved_unbounded _ _ _ _ _
    (by simp only [writeCascade, writeWord_sparse_size]; omega) (.inl (by omega))]
  apply writeCascade_read_preserved_unbounded _ _ _ _ hin
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> exact .inl (by omega)

end Benchmarks.EAS.Attester
