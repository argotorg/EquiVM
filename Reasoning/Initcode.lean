import Ethereum.Semantics

/-!
# Initcode — decoding stable prefixes with appended constructor arguments

Creation bytecode is often executed as `initcode ++ args`, where the instruction stream lives
entirely in the fixed `initcode` prefix and `args` is ABI data.  These lemmas let per-PC decode
facts be proved once on the prefix and reused for every appended argument tail.
-/

open Ethereum Ethereum.EVM

namespace Reasoning.Theory

/-- Reading an index inside the left component of an append is unchanged by the suffix. -/
theorem byteArray_get?_append_left (A B : ByteArray) {i : Nat} (h : i < A.size) :
    (A ++ B).get? i = A.get? i := by
  unfold ByteArray.get?
  have hAB : i < (A ++ B).size := by
    rw [ByteArray.size_append]
    omega
  simp only [dif_pos hAB, dif_pos h]
  simp [ByteArray.get, ByteArray.data_append, Array.getElem_append_left h]

/-- Extracting a window from a prefix is unchanged after appending a suffix. -/
theorem byteArray_extract_append_left (A B : ByteArray) (i j : Nat) (h : j ≤ A.size) :
    (A ++ B).extract i j = A.extract i j := by
  apply ByteArray.ext
  rw [ByteArray.data_extract, ByteArray.data_append, ByteArray.data_extract,
      Array.extract_append_of_stop_le_size_left (by rwa [← ByteArray.size_data] at h)]

/-- `extract'` agrees with the prefix when its window stays within that prefix. -/
theorem byteArray_extract'_append_left (A B : ByteArray) {i j : Nat}
    (hi : i < 2 ^ 64) (hj64 : j < 2 ^ 64) (hj : j ≤ A.size) :
    (A ++ B).extract' i j = A.extract' i j := by
  have hdi : decide (i < 2 ^ 64) = true := decide_eq_true hi
  have hdj : decide (j < 2 ^ 64) = true := decide_eq_true hj64
  have hguard : (decide (i < 2 ^ 64) && decide (j < 2 ^ 64)) = true := by
    rw [hdi, hdj]
    rfl
  unfold ByteArray.extract'
  rw [if_pos hguard, if_pos hguard]
  exact byteArray_extract_append_left A B i j hj

/-- Decoding at a PC in a fixed bytecode prefix is unchanged by appending arbitrary bytes, provided
    the whole instruction window also lies in that prefix. -/
theorem decode_append_left (A B : ByteArray) (pc : UInt256)
    (hpc : pc.toNat < A.size)
    (hwin : ∀ b instr, A.get? pc.toNat = some b → parseInstr b = some instr →
      pc.toNat + 1 + argOnNBytesOfInstr instr ≤ A.size)
    (hwin64 : ∀ b instr, A.get? pc.toNat = some b → parseInstr b = some instr →
      pc.toNat + 1 + argOnNBytesOfInstr instr < 2 ^ 64) :
    decode (A ++ B) pc = decode A pc := by
  unfold decode
  rw [byteArray_get?_append_left A B hpc]
  cases hget : A.get? pc.toNat with
  | none => simp
  | some b =>
      cases hinstr : parseInstr b with
      | none => simp [hinstr]
      | some instr =>
          simp [hinstr]
          by_cases harg : argOnNBytesOfInstr instr = 0
          · simp [harg]
          · simp [harg]
            rw [byteArray_extract'_append_left A B]
            · have hargpos : 0 < argOnNBytesOfInstr instr := Nat.pos_of_ne_zero harg
              have := hwin64 b instr hget hinstr
              omega
            · exact hwin64 b instr hget hinstr
            · exact hwin b instr hget hinstr

end Reasoning.Theory
