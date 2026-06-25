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

/-- Every EVM instruction carries at most 32 immediate argument bytes (`PUSH32`). -/
theorem argOnNBytesOfInstr_le_32 (i : Operation) : argOnNBytesOfInstr i ≤ 32 := by
  cases i <;> first | decide | (rename_i p; cases p <;> decide)

/-- A ready-to-apply form of `decode_append_left`: appending arbitrary bytes to a fixed prefix `A`
    leaves the decode at `pc` unchanged whenever the *whole* maximal instruction window
    (`pc + 1 + 32`, the `PUSH32` worst case) still lies inside `A`.  The window/`2^64` side
    conditions are discharged from `argOnNBytesOfInstr_le_32`, so callers supply only the single
    arithmetic fact `pc + 33 ≤ A.size` (plus `A.size < 2^64`, trivial for any real bytecode). -/
theorem decode_append_left_window (A B : ByteArray) (pc : UInt256)
    (hwin : pc.toNat + 33 ≤ A.size) (hsize : A.size < 2 ^ 64) :
    decode (A ++ B) pc = decode A pc := by
  apply decode_append_left A B pc
  · omega
  · intro b instr _ _; have := argOnNBytesOfInstr_le_32 instr; omega
  · intro b instr _ _; have := argOnNBytesOfInstr_le_32 instr; omega

/-! ## Jump-destination set under an appended argument tail

`D_J_aux` (the `JUMPDEST`-set scanner) threads its accumulator linearly — scanning from `i` only ever
*appends* discovered destinations.  Hence appending bytes to a fixed prefix can only *add* later
destinations, never remove the prefix's own.  So a `(D_J A 0).contains pc` fact survives `A ↦ A ++ B`,
which is what every `jump`/`jumpiT` in a creation-code trace needs (the instruction stream is in the
fixed prefix, the symbolic ABI argument tail follows). -/

/-- One scan step when the current byte does not decode (or the stream ended). -/
theorem D_J_aux_eq_none (c : ByteArray) (i : ℕ) (result : Array UInt256)
    (h : c.get? i >>= parseInstr = none) : D_J_aux c i result = result := by
  rw [D_J_aux]; split
  · rfl
  · rename_i cᵢ hc; rw [hc] at h; simp at h

/-- One scan step when the current byte decodes to `cᵢ`: recurse past its immediates, recording the
    position iff it is a `JUMPDEST`. -/
theorem D_J_aux_eq_some (c : ByteArray) (i : ℕ) (result : Array UInt256) (cᵢ : Operation)
    (h : c.get? i >>= parseInstr = some cᵢ) :
    D_J_aux c i result = D_J_aux c (N i cᵢ)
      (if cᵢ = Operation.JUMPDEST then result.push (UInt256.ofNat i) else result) := by
  rw [D_J_aux]; split
  · rename_i hc; rw [hc] at h; simp at h
  · rename_i cᵢ' hc; rw [hc] at h; simp only [Option.some.injEq] at h; subst h; rfl

/-- The scan position reaching the end of the bytecode returns the accumulator. -/
theorem D_J_aux_ge_size (c : ByteArray) (i : ℕ) (result : Array UInt256) (h : c.size ≤ i) :
    D_J_aux c i result = result :=
  D_J_aux_eq_none c i result (by
    have : c.get? i = none := by rw [ByteArray.get?, dif_neg (by omega)]
    simp [this])

/-- `c.get? i = some _` exactly when `i` is in range. -/
private theorem lt_size_of_get?_isSome {c : ByteArray} {i : ℕ} {cᵢ : Operation}
    (h : c.get? i >>= parseInstr = some cᵢ) : i < c.size := by
  rcases hb : c.get? i with _ | b
  · rw [hb] at h; simp at h
  · rw [ByteArray.get?] at hb; split at hb
    · assumption
    · simp at hb

/-- `D_J_aux` appends to its accumulator: scanning from `i` adds the same destinations regardless of
    what is already accumulated. -/
theorem D_J_aux_acc (c : ByteArray) (i : ℕ) (result : Array UInt256) :
    D_J_aux c i result = result ++ D_J_aux c i #[] := by
  cases h : c.get? i >>= parseInstr with
  | none => rw [D_J_aux_eq_none c i result h, D_J_aux_eq_none c i #[] h]; exact Array.append_empty.symm
  | some cᵢ =>
      rw [D_J_aux_eq_some c i result cᵢ h, D_J_aux_eq_some c i #[] cᵢ h,
          D_J_aux_acc c (N i cᵢ)
            (if cᵢ = Operation.JUMPDEST then result.push (UInt256.ofNat i) else result),
          D_J_aux_acc c (N i cᵢ)
            (if cᵢ = Operation.JUMPDEST then (#[] : Array UInt256).push (UInt256.ofNat i) else #[])]
      by_cases hjd : cᵢ = Operation.JUMPDEST
      · simp only [if_pos hjd, Array.push_eq_append, Array.empty_append, Array.append_assoc]
      · simp only [if_neg hjd, Array.empty_append]
termination_by c.size - i
decreasing_by all_goals (have := lt_size_of_get?_isSome h; simp only [N]; omega)

/-- Appending bytes to a fixed prefix `A` only extends the scanned `JUMPDEST` set: from any position
    `i ≤ A.size`, `D_J_aux (A ++ B) i #[]` is `D_J_aux A i #[]` followed by some suffix. -/
theorem D_J_aux_append_left_suffix (A B : ByteArray) (i : ℕ) (hi : i ≤ A.size) :
    ∃ suf : Array UInt256, D_J_aux (A ++ B) i #[] = D_J_aux A i #[] ++ suf := by
  by_cases hib : i < A.size
  · have hget : (A ++ B).get? i >>= parseInstr = A.get? i >>= parseInstr := by
      rw [byteArray_get?_append_left A B hib]
    cases h : A.get? i >>= parseInstr with
    | none =>
        rw [D_J_aux_eq_none (A ++ B) i #[] (hget.trans h), D_J_aux_eq_none A i #[] h]
        exact ⟨#[], Array.append_empty.symm⟩
    | some cᵢ =>
        rw [D_J_aux_eq_some (A ++ B) i #[] cᵢ (hget.trans h), D_J_aux_eq_some A i #[] cᵢ h,
            D_J_aux_acc (A ++ B) (N i cᵢ)
              (if cᵢ = Operation.JUMPDEST then (#[] : Array UInt256).push (UInt256.ofNat i) else #[]),
            D_J_aux_acc A (N i cᵢ)
              (if cᵢ = Operation.JUMPDEST then (#[] : Array UInt256).push (UInt256.ofNat i) else #[])]
        by_cases hN : N i cᵢ ≤ A.size
        · obtain ⟨suf, hsuf⟩ := D_J_aux_append_left_suffix A B (N i cᵢ) hN
          exact ⟨suf, by rw [hsuf]; simp [Array.append_assoc]⟩
        · refine ⟨D_J_aux (A ++ B) (N i cᵢ) #[], ?_⟩
          rw [D_J_aux_ge_size A (N i cᵢ) #[] (by omega)]
          simp [Array.append_empty]
  · rw [D_J_aux_ge_size A i #[] (by omega)]
    exact ⟨D_J_aux (A ++ B) i #[], by simp⟩
termination_by A.size - i
decreasing_by simp only [N]; omega

/-- A `JUMPDEST`-membership fact for a fixed prefix `A` survives appending an arbitrary tail `B`. -/
theorem D_J_contains_append_left (A B : ByteArray) (pc : UInt256)
    (h : (D_J A 0).contains pc = true) : (D_J (A ++ B) 0).contains pc = true := by
  obtain ⟨suf, hsuf⟩ := D_J_aux_append_left_suffix A B 0 (Nat.zero_le _)
  rw [Array.contains_iff_mem] at h ⊢
  simp only [D_J] at h hsuf ⊢
  rw [hsuf, Array.mem_append]
  exact Or.inl h

end Reasoning.Theory
