import Init.Data.ByteArray.Lemmas
import Act.Equiv
import Ethereum.Theory.ProgressLemmas
import Ethereum.Theory.OpcodeLemmas

/-!
# Theory — reusable, compositional lemmas for runtime-equivalence proofs

General, **contract-agnostic** infrastructure for proving
`runtimeEquivalence!?! cfg bytecode contract`.

Lemmas in this file (and any further `TruthCodex.*` theory files) must not mention any
specific contract — they are about `runtimeEquivalenceFor`, `actExec`, `execResultsEquiv`,
`returnEquiv`, `ExecStmt`/`ExecBlock`/`ExecFuncBody`, `Ethereum.EVM.Ξ`, etc.
`TruthCorrect.lean` assembles them with the Truth-specific facts.
-/

open Act ABI

/-! ## Small data facts -/

instance : ReflBEq ByteArray where
  rfl := by
    intro a
    cases a with
    | mk data =>
      change (data == data) = true
      exact BEq.rfl

instance : LawfulBEq ByteArray where
  eq_of_beq := by
    intro a b h
    cases a with
    | mk dataA =>
      cases b with
      | mk dataB =>
        change (dataA == dataB) = true at h
        have hData : dataA = dataB := LawfulBEq.eq_of_beq h
        cases hData
        rfl

lemma ByteArray.beq_false_of_ne {a b : ByteArray} (h : a ≠ b) :
    (a == b) = false := by
  cases hbeq : (a == b)
  · rfl
  · exact False.elim (h (LawfulBEq.eq_of_beq hbeq))

namespace USize

lemma toNat_ofNat_sub_ofNat_of_le {a b : Nat}
    (ha : a < USize.size) (hb : b ≤ a) :
    (((OfNat.ofNat a : USize) - (OfNat.ofNat b : USize))).toNat = a - b := by
  have hbSize : b < USize.size := Nat.lt_of_le_of_lt hb ha
  have hle : (OfNat.ofNat b : USize) ≤ (OfNat.ofNat a : USize) := by
    rw [USize.le_iff_toNat_le, USize.toNat_ofNat_of_lt hbSize,
      USize.toNat_ofNat_of_lt ha]
    exact hb
  rw [USize.toNat_sub_of_le _ _ hle, USize.toNat_ofNat_of_lt ha,
    USize.toNat_ofNat_of_lt hbSize]

end USize

namespace ByteArray

lemma toList_loop_length (bs : ByteArray) (i : Nat) (r : List UInt8) :
    (ByteArray.toList.loop bs i r).length = (bs.size - i) + r.length := by
  rw [ByteArray.toList.loop.eq_def]
  by_cases h : i < bs.size
  · simp [h, toList_loop_length bs (i + 1) (bs.get! i :: r)]
    omega
  · simp [h]
    have : bs.size - i = 0 := by omega
    simp [this]
termination_by bs.size - i

lemma length_toList (bs : ByteArray) :
    bs.toList.length = bs.size := by
  rw [ByteArray.toList.eq_1]
  simpa using toList_loop_length bs 0 []

lemma not_toList_length_lt_of_extract_eq_size {bytes selector : ByteArray} {n : Nat}
    (hSelectorSize : selector.size = n)
    (hExtract : bytes.extract 0 n = selector) :
    ¬ bytes.toList.length < n := by
  have hExtractSize : (bytes.extract 0 n).size = n := by
    rw [hExtract, hSelectorSize]
  rw [ByteArray.size_extract] at hExtractSize
  have hBytesSize : n ≤ bytes.size := by
    omega
  rw [length_toList]
  omega

lemma extract_ne_of_size_lt {bytes selector : ByteArray} {n : Nat}
    (hBytesSize : bytes.size < n)
    (hSelectorSize : selector.size = n) :
    bytes.extract 0 n ≠ selector := by
  intro hExtract
  have hExtractSize : (bytes.extract 0 n).size = n := by
    rw [hExtract, hSelectorSize]
  rw [ByteArray.size_extract] at hExtractSize
  omega

lemma extract_zero_four_eq_toByteArray_getElem {bytes : ByteArray}
    (hSize : 4 ≤ bytes.size) :
    bytes.extract 0 4 =
      [bytes[0], bytes[1], bytes[2], bytes[3]].toByteArray := by
  simpa using ByteArray.extract_add_four (a := bytes) (i := 0) (by simpa using hSize)

lemma extract_append_of_stop_le_size_left {a b : ByteArray} {i j : Nat}
    (h : j ≤ a.size) :
    (a ++ b).extract i j = a.extract i j := by
  apply ByteArray.ext
  rw [ByteArray.data_extract, ByteArray.data_extract, ByteArray.data_append]
  exact Array.extract_append_of_stop_le_size_left
    (a := a.data) (b := b.data) (i := i) (j := j)
    (by simpa [ByteArray.size_data] using h)

lemma copySlice_zero_empty_eq_extract (source : ByteArray) (size : Nat) :
    source.copySlice 0 ByteArray.empty 0 size = source.extract 0 size := by
  rw [ByteArray.copySlice_eq_append]
  simp [ByteArray.extract_same, ByteArray.size_data]
  have hEmpty : ByteArray.empty.extract (min size source.size) 0 = ByteArray.empty := by
    rw [ByteArray.extract_eq_empty_iff]
    simp
  rw [hEmpty, ByteArray.append_empty]

lemma readBytes_zero_extract_eq_extract {source : ByteArray} {readSize len : Nat}
    (hReadSize : readSize < 2^64)
    (hLenRead : len ≤ readSize)
    (hLenSource : len ≤ source.size) :
    (source.readBytes 0 readSize).extract 0 len = source.extract 0 len := by
  have hReadSizeDecimal : readSize < 18446744073709551616 := by
    norm_num at hReadSize ⊢
    exact hReadSize
  unfold ByteArray.readBytes
  simp [hReadSizeDecimal]
  rw [ByteArray.copySlice_zero_empty_eq_extract]
  rw [ByteArray.extract_append_of_stop_le_size_left]
  · rw [ByteArray.extract_extract]
    simp [Nat.min_eq_left hLenRead]
  · rw [ByteArray.size_extract]
    omega

lemma readBytes_zero_extract_zero_four {source : ByteArray}
    (hSize : 4 ≤ source.size) :
    (source.readBytes 0 32).extract 0 4 = source.extract 0 4 :=
  readBytes_zero_extract_eq_extract (source := source)
    (readSize := 32) (len := 4) (by norm_num) (by norm_num) hSize

lemma readBytes_size_of_lt (source : ByteArray) (start size : Nat)
    (hSize : size < USize.size) :
    (source.readBytes start size).size = size := by
  unfold ByteArray.readBytes
  let read : ByteArray :=
    if start < 2^64 && size < 2^64 then
      source.copySlice start ByteArray.empty 0 size
    else
      ⟨⟨source.toList.drop start |>.take size⟩⟩
  have hReadSizeLe : read.size ≤ size := by
    dsimp [read]
    by_cases hCond : start < 18446744073709551616 ∧ size < 18446744073709551616
    · simp [hCond]
      rw [ByteArray.copySlice_eq_append, ByteArray.size_append, ByteArray.size_append,
        ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract]
      simp [ByteArray.size_data]
      omega
    · simp [hCond]
      change (List.take size (List.drop start source.toList)).toArray.size ≤ size
      simp
  change (read ++ ffi.ByteArray.zeroes ((OfNat.ofNat size : USize) - OfNat.ofNat read.size)).size =
    size
  rw [ByteArray.size_append, ByteArray_zeroes_size]
  rw [USize.toNat_ofNat_sub_ofNat_of_le]
  · omega
  · exact hSize
  · exact hReadSizeLe

lemma readBytes_size_32 (source : ByteArray) (start : Nat) :
    (source.readBytes start 32).size = 32 :=
  readBytes_size_of_lt source start 32 (by cases USize.size_eq <;> omega)

end ByteArray

namespace Ethereum.UInt256

lemma eq_zero_of_val_val_eq_zero {x : Ethereum.UInt256} (h : x.val.val = 0) :
    x = (⟨0⟩ : Ethereum.UInt256) := by
  cases x with
  | mk val =>
      cases val with
      | mk n hn =>
          simp at h
          subst n
          rfl

lemma val_val_ne_zero_of_ne_zero {x : Ethereum.UInt256}
    (h : x ≠ (⟨0⟩ : Ethereum.UInt256)) :
    x.val.val ≠ 0 :=
  fun hZero => h (eq_zero_of_val_val_eq_zero hZero)

lemma ofNat_toNat_of_lt {n : Nat} (hn : n < Ethereum.UInt256.size) :
    (Ethereum.UInt256.ofNat n).toNat = n := by
  unfold Ethereum.UInt256.ofNat Ethereum.UInt256.toNat
  simp [Id.run, Nat.mod_eq_of_lt hn]

@[simp] lemma toNat_zero :
    (⟨0⟩ : Ethereum.UInt256).toNat = 0 := by
  rfl

lemma toNat_shiftRight_of_lt {a b : Ethereum.UInt256}
    (hb : b.toNat < 256) :
    (Ethereum.UInt256.shiftRight a b).toNat = a.toNat >>> b.toNat := by
  cases a with
  | mk av =>
      cases b with
      | mk bv =>
          unfold Ethereum.UInt256.toNat at hb
          unfold Ethereum.UInt256.shiftRight Ethereum.UInt256.toNat
          simp at hb ⊢
          have hBranch : ¬ (256 : Fin Ethereum.UInt256.size) ≤ bv := by
            rw [Fin.le_iff_val_le_val]
            simp [Ethereum.UInt256.size, Nat.mod_eq_of_lt]
            omega
          rw [if_neg hBranch]
          simp

lemma toNat_shiftRight_eq_div_pow_of_lt {a b : Ethereum.UInt256}
    (hb : b.toNat < 256) :
    (Ethereum.UInt256.shiftRight a b).toNat = a.toNat / 2 ^ b.toNat := by
  rw [toNat_shiftRight_of_lt hb, Nat.shiftRight_eq_div_pow]

lemma toNat_fin_ofNat_of_lt {n : Nat} (hn : n < Ethereum.UInt256.size) :
    (⟨(OfNat.ofNat n : Fin Ethereum.UInt256.size)⟩ : Ethereum.UInt256).toNat = n := by
  unfold Ethereum.UInt256.toNat
  simp
  change n % Ethereum.UInt256.size = n
  rw [Nat.mod_eq_of_lt hn]

lemma ofNat_eq_fin (n : Nat) :
    Ethereum.UInt256.ofNat n =
      (⟨(OfNat.ofNat n : Fin Ethereum.UInt256.size)⟩ : Ethereum.UInt256) := by
  unfold Ethereum.UInt256.ofNat
  simp [Id.run]
  apply Fin.ext
  simp
  rfl

lemma eq_of_toNat_eq {x : Ethereum.UInt256} {n : Nat}
    (hn : n < Ethereum.UInt256.size)
    (h : x.toNat = n) :
    x = Ethereum.UInt256.ofNat n := by
  cases x with
  | mk xv =>
      unfold Ethereum.UInt256.toNat at h
      cases xv with
      | mk v hv =>
          simp at h
          subst v
          apply congrArg Ethereum.UInt256.mk
          apply Fin.ext
          simp [Nat.mod_eq_of_lt hn]

lemma eq_fin_of_toNat_eq {x : Ethereum.UInt256} {n : Nat}
    (hn : n < Ethereum.UInt256.size)
    (h : x.toNat = n) :
    x = (⟨(OfNat.ofNat n : Fin Ethereum.UInt256.size)⟩ : Ethereum.UInt256) := by
  rw [Ethereum.UInt256.eq_of_toNat_eq hn h]
  exact ofNat_eq_fin n

lemma toNat_sub_ofNat_of_le {x : Ethereum.UInt256} {n : Nat}
    (hn : n < Ethereum.UInt256.size)
    (h : n ≤ x.toNat) :
    (x - Ethereum.UInt256.ofNat n).toNat = x.toNat - n := by
  cases x with
  | mk xv =>
      unfold Ethereum.UInt256.toNat at h
      have hVal : (Fin.ofNat Ethereum.UInt256.size n).val = n := by
        simp [Nat.mod_eq_of_lt hn]
      have hLe : Fin.ofNat Ethereum.UInt256.size n ≤ xv := by
        rw [Fin.le_iff_val_le_val]
        rw [hVal]
        exact h
      change (xv - Fin.ofNat Ethereum.UInt256.size n).val = xv.val - n
      rw [Fin.sub_val_of_le hLe]
      rw [hVal]

lemma toNat_sub_ofNat_sub_ofNat_of_le {x : Ethereum.UInt256} {a b : Nat}
    (ha : a < Ethereum.UInt256.size)
    (hb : b < Ethereum.UInt256.size)
    (h : a + b ≤ x.toNat) :
    ((x - Ethereum.UInt256.ofNat a) - Ethereum.UInt256.ofNat b).toNat =
      x.toNat - a - b := by
  have hFirst : (x - Ethereum.UInt256.ofNat a).toNat = x.toNat - a :=
    toNat_sub_ofNat_of_le ha (by omega)
  have hSecond :
      b ≤ (x - Ethereum.UInt256.ofNat a).toNat := by
    rw [hFirst]
    omega
  have hSub :=
    toNat_sub_ofNat_of_le (x := x - Ethereum.UInt256.ofNat a) (n := b) hb hSecond
  rw [hSub, hFirst]

lemma add_le_toNat_of_not_sub_ofNat_lt {x : Ethereum.UInt256} {cost remaining : Nat}
    (hCostSize : cost < Ethereum.UInt256.size)
    (hCost : cost ≤ x.toNat)
    (hRemaining :
      ¬ (x - Ethereum.UInt256.ofNat cost).toNat < remaining) :
    cost + remaining ≤ x.toNat := by
  have hSub := toNat_sub_ofNat_of_le (x := x) (n := cost) hCostSize hCost
  rw [hSub] at hRemaining
  omega

lemma add_add_le_toNat_of_not_sub_ofNat_sub_ofNat_lt
    {x : Ethereum.UInt256} {cost₁ cost₂ remaining : Nat}
    (hCost₁Size : cost₁ < Ethereum.UInt256.size)
    (hCost₂Size : cost₂ < Ethereum.UInt256.size)
    (hCost₁ : cost₁ ≤ x.toNat)
    (hCost₂ : cost₂ ≤ (x - Ethereum.UInt256.ofNat cost₁).toNat)
    (hRemaining :
      ¬ ((x - Ethereum.UInt256.ofNat cost₁) -
          Ethereum.UInt256.ofNat cost₂).toNat < remaining) :
    cost₁ + cost₂ + remaining ≤ x.toNat := by
  have hTail :=
    add_le_toNat_of_not_sub_ofNat_lt
      (x := x - Ethereum.UInt256.ofNat cost₁)
      (cost := cost₂)
      (remaining := remaining)
      hCost₂Size
      hCost₂
      hRemaining
  have hSub := toNat_sub_ofNat_of_le (x := x) (n := cost₁) hCost₁Size hCost₁
  rw [hSub] at hTail
  omega

lemma add_add_add_le_toNat_of_not_sub_ofNat_sub_ofNat_sub_ofNat_lt
    {x : Ethereum.UInt256} {cost₁ cost₂ cost₃ remaining : Nat}
    (hCost₁Size : cost₁ < Ethereum.UInt256.size)
    (hCost₂Size : cost₂ < Ethereum.UInt256.size)
    (hCost₃Size : cost₃ < Ethereum.UInt256.size)
    (hCost₁ : cost₁ ≤ x.toNat)
    (hCost₂ : cost₂ ≤ (x - Ethereum.UInt256.ofNat cost₁).toNat)
    (hCost₃ :
      cost₃ ≤
        ((x - Ethereum.UInt256.ofNat cost₁) -
          Ethereum.UInt256.ofNat cost₂).toNat)
    (hRemaining :
      ¬ (((x - Ethereum.UInt256.ofNat cost₁) -
            Ethereum.UInt256.ofNat cost₂) -
          Ethereum.UInt256.ofNat cost₃).toNat < remaining) :
    cost₁ + cost₂ + cost₃ + remaining ≤ x.toNat := by
  have hTail :=
    add_le_toNat_of_not_sub_ofNat_lt
      (x := (x - Ethereum.UInt256.ofNat cost₁) - Ethereum.UInt256.ofNat cost₂)
      (cost := cost₃)
      (remaining := remaining)
      hCost₃Size
      hCost₃
      hRemaining
  have hSub₂ :=
    toNat_sub_ofNat_of_le
      (x := x - Ethereum.UInt256.ofNat cost₁)
      (n := cost₂)
      hCost₂Size
      hCost₂
  have hSub₁ := toNat_sub_ofNat_of_le (x := x) (n := cost₁) hCost₁Size hCost₁
  rw [hSub₂, hSub₁] at hTail
  omega

lemma add_add_add_add_le_toNat_of_not_sub_ofNat_sub_ofNat_sub_ofNat_sub_ofNat_lt
    {x : Ethereum.UInt256} {cost₁ cost₂ cost₃ cost₄ remaining : Nat}
    (hCost₁Size : cost₁ < Ethereum.UInt256.size)
    (hCost₂Size : cost₂ < Ethereum.UInt256.size)
    (hCost₃Size : cost₃ < Ethereum.UInt256.size)
    (hCost₄Size : cost₄ < Ethereum.UInt256.size)
    (hCost₁ : cost₁ ≤ x.toNat)
    (hCost₂ : cost₂ ≤ (x - Ethereum.UInt256.ofNat cost₁).toNat)
    (hCost₃ :
      cost₃ ≤
        ((x - Ethereum.UInt256.ofNat cost₁) -
          Ethereum.UInt256.ofNat cost₂).toNat)
    (hCost₄ :
      cost₄ ≤
        (((x - Ethereum.UInt256.ofNat cost₁) -
            Ethereum.UInt256.ofNat cost₂) -
          Ethereum.UInt256.ofNat cost₃).toNat)
    (hRemaining :
      ¬ ((((x - Ethereum.UInt256.ofNat cost₁) -
              Ethereum.UInt256.ofNat cost₂) -
            Ethereum.UInt256.ofNat cost₃) -
          Ethereum.UInt256.ofNat cost₄).toNat < remaining) :
    cost₁ + cost₂ + cost₃ + cost₄ + remaining ≤ x.toNat := by
  have hTail :=
    add_le_toNat_of_not_sub_ofNat_lt
      (x := ((x - Ethereum.UInt256.ofNat cost₁) -
          Ethereum.UInt256.ofNat cost₂) -
        Ethereum.UInt256.ofNat cost₃)
      (cost := cost₄)
      (remaining := remaining)
      hCost₄Size
      hCost₄
      hRemaining
  have hSub₃ :=
    toNat_sub_ofNat_of_le
      (x := (x - Ethereum.UInt256.ofNat cost₁) - Ethereum.UInt256.ofNat cost₂)
      (n := cost₃)
      hCost₃Size
      hCost₃
  have hSub₂ :=
    toNat_sub_ofNat_of_le
      (x := x - Ethereum.UInt256.ofNat cost₁)
      (n := cost₂)
      hCost₂Size
      hCost₂
  have hSub₁ := toNat_sub_ofNat_of_le (x := x) (n := cost₁) hCost₁Size hCost₁
  rw [hSub₃, hSub₂, hSub₁] at hTail
  omega

lemma add_add_add_add_add_le_toNat_of_not_sub_ofNat_sub_ofNat_sub_ofNat_sub_ofNat_sub_ofNat_lt
    {x : Ethereum.UInt256} {cost₁ cost₂ cost₃ cost₄ cost₅ remaining : Nat}
    (hCost₁Size : cost₁ < Ethereum.UInt256.size)
    (hCost₂Size : cost₂ < Ethereum.UInt256.size)
    (hCost₃Size : cost₃ < Ethereum.UInt256.size)
    (hCost₄Size : cost₄ < Ethereum.UInt256.size)
    (hCost₅Size : cost₅ < Ethereum.UInt256.size)
    (hCost₁ : cost₁ ≤ x.toNat)
    (hCost₂ : cost₂ ≤ (x - Ethereum.UInt256.ofNat cost₁).toNat)
    (hCost₃ :
      cost₃ ≤
        ((x - Ethereum.UInt256.ofNat cost₁) -
          Ethereum.UInt256.ofNat cost₂).toNat)
    (hCost₄ :
      cost₄ ≤
        (((x - Ethereum.UInt256.ofNat cost₁) -
            Ethereum.UInt256.ofNat cost₂) -
          Ethereum.UInt256.ofNat cost₃).toNat)
    (hCost₅ :
      cost₅ ≤
        ((((x - Ethereum.UInt256.ofNat cost₁) -
              Ethereum.UInt256.ofNat cost₂) -
            Ethereum.UInt256.ofNat cost₃) -
          Ethereum.UInt256.ofNat cost₄).toNat)
    (hRemaining :
      ¬ (((((x - Ethereum.UInt256.ofNat cost₁) -
                Ethereum.UInt256.ofNat cost₂) -
              Ethereum.UInt256.ofNat cost₃) -
            Ethereum.UInt256.ofNat cost₄) -
          Ethereum.UInt256.ofNat cost₅).toNat < remaining) :
    cost₁ + cost₂ + cost₃ + cost₄ + cost₅ + remaining ≤ x.toNat := by
  have hTail :=
    add_le_toNat_of_not_sub_ofNat_lt
      (x := (((x - Ethereum.UInt256.ofNat cost₁) -
            Ethereum.UInt256.ofNat cost₂) -
          Ethereum.UInt256.ofNat cost₃) -
        Ethereum.UInt256.ofNat cost₄)
      (cost := cost₅)
      (remaining := remaining)
      hCost₅Size
      hCost₅
      hRemaining
  have hSub₄ :=
    toNat_sub_ofNat_of_le
      (x := ((x - Ethereum.UInt256.ofNat cost₁) -
          Ethereum.UInt256.ofNat cost₂) -
        Ethereum.UInt256.ofNat cost₃)
      (n := cost₄)
      hCost₄Size
      hCost₄
  have hSub₃ :=
    toNat_sub_ofNat_of_le
      (x := (x - Ethereum.UInt256.ofNat cost₁) - Ethereum.UInt256.ofNat cost₂)
      (n := cost₃)
      hCost₃Size
      hCost₃
  have hSub₂ :=
    toNat_sub_ofNat_of_le
      (x := x - Ethereum.UInt256.ofNat cost₁)
      (n := cost₂)
      hCost₂Size
      hCost₂
  have hSub₁ := toNat_sub_ofNat_of_le (x := x) (n := cost₁) hCost₁Size hCost₁
  rw [hSub₄, hSub₃, hSub₂, hSub₁] at hTail
  omega

lemma add_add_add_add_add_add_le_toNat_of_not_sub_ofNat_sub_ofNat_sub_ofNat_sub_ofNat_sub_ofNat_sub_ofNat_lt
    {x : Ethereum.UInt256} {cost₁ cost₂ cost₃ cost₄ cost₅ cost₆ remaining : Nat}
    (hCost₁Size : cost₁ < Ethereum.UInt256.size)
    (hCost₂Size : cost₂ < Ethereum.UInt256.size)
    (hCost₃Size : cost₃ < Ethereum.UInt256.size)
    (hCost₄Size : cost₄ < Ethereum.UInt256.size)
    (hCost₅Size : cost₅ < Ethereum.UInt256.size)
    (hCost₆Size : cost₆ < Ethereum.UInt256.size)
    (hCost₁ : cost₁ ≤ x.toNat)
    (hCost₂ : cost₂ ≤ (x - Ethereum.UInt256.ofNat cost₁).toNat)
    (hCost₃ :
      cost₃ ≤
        ((x - Ethereum.UInt256.ofNat cost₁) -
          Ethereum.UInt256.ofNat cost₂).toNat)
    (hCost₄ :
      cost₄ ≤
        (((x - Ethereum.UInt256.ofNat cost₁) -
            Ethereum.UInt256.ofNat cost₂) -
          Ethereum.UInt256.ofNat cost₃).toNat)
    (hCost₅ :
      cost₅ ≤
        ((((x - Ethereum.UInt256.ofNat cost₁) -
              Ethereum.UInt256.ofNat cost₂) -
            Ethereum.UInt256.ofNat cost₃) -
          Ethereum.UInt256.ofNat cost₄).toNat)
    (hCost₆ :
      cost₆ ≤
        (((((x - Ethereum.UInt256.ofNat cost₁) -
                Ethereum.UInt256.ofNat cost₂) -
              Ethereum.UInt256.ofNat cost₃) -
            Ethereum.UInt256.ofNat cost₄) -
          Ethereum.UInt256.ofNat cost₅).toNat)
    (hRemaining :
      ¬ ((((((x - Ethereum.UInt256.ofNat cost₁) -
                  Ethereum.UInt256.ofNat cost₂) -
                Ethereum.UInt256.ofNat cost₃) -
              Ethereum.UInt256.ofNat cost₄) -
            Ethereum.UInt256.ofNat cost₅) -
          Ethereum.UInt256.ofNat cost₆).toNat < remaining) :
    cost₁ + cost₂ + cost₃ + cost₄ + cost₅ + cost₆ + remaining ≤ x.toNat := by
  have hTail :=
    add_le_toNat_of_not_sub_ofNat_lt
      (x := ((((x - Ethereum.UInt256.ofNat cost₁) -
              Ethereum.UInt256.ofNat cost₂) -
            Ethereum.UInt256.ofNat cost₃) -
          Ethereum.UInt256.ofNat cost₄) -
        Ethereum.UInt256.ofNat cost₅)
      (cost := cost₆)
      (remaining := remaining)
      hCost₆Size
      hCost₆
      hRemaining
  have hSub₅ :=
    toNat_sub_ofNat_of_le
      (x := (((x - Ethereum.UInt256.ofNat cost₁) -
            Ethereum.UInt256.ofNat cost₂) -
          Ethereum.UInt256.ofNat cost₃) -
        Ethereum.UInt256.ofNat cost₄)
      (n := cost₅)
      hCost₅Size
      hCost₅
  have hSub₄ :=
    toNat_sub_ofNat_of_le
      (x := ((x - Ethereum.UInt256.ofNat cost₁) -
          Ethereum.UInt256.ofNat cost₂) -
        Ethereum.UInt256.ofNat cost₃)
      (n := cost₄)
      hCost₄Size
      hCost₄
  have hSub₃ :=
    toNat_sub_ofNat_of_le
      (x := (x - Ethereum.UInt256.ofNat cost₁) - Ethereum.UInt256.ofNat cost₂)
      (n := cost₃)
      hCost₃Size
      hCost₃
  have hSub₂ :=
    toNat_sub_ofNat_of_le
      (x := x - Ethereum.UInt256.ofNat cost₁)
      (n := cost₂)
      hCost₂Size
      hCost₂
  have hSub₁ := toNat_sub_ofNat_of_le (x := x) (n := cost₁) hCost₁Size hCost₁
  rw [hSub₅, hSub₄, hSub₃, hSub₂, hSub₁] at hTail
  omega

lemma add_add_add_add_add_add_add_le_toNat_of_not_sub_ofNat_sub_ofNat_sub_ofNat_sub_ofNat_sub_ofNat_sub_ofNat_sub_ofNat_lt
    {x : Ethereum.UInt256} {cost₁ cost₂ cost₃ cost₄ cost₅ cost₆ cost₇ remaining : Nat}
    (hCost₁Size : cost₁ < Ethereum.UInt256.size)
    (hCost₂Size : cost₂ < Ethereum.UInt256.size)
    (hCost₃Size : cost₃ < Ethereum.UInt256.size)
    (hCost₄Size : cost₄ < Ethereum.UInt256.size)
    (hCost₅Size : cost₅ < Ethereum.UInt256.size)
    (hCost₆Size : cost₆ < Ethereum.UInt256.size)
    (hCost₇Size : cost₇ < Ethereum.UInt256.size)
    (hCost₁ : cost₁ ≤ x.toNat)
    (hCost₂ : cost₂ ≤ (x - Ethereum.UInt256.ofNat cost₁).toNat)
    (hCost₃ :
      cost₃ ≤
        ((x - Ethereum.UInt256.ofNat cost₁) -
          Ethereum.UInt256.ofNat cost₂).toNat)
    (hCost₄ :
      cost₄ ≤
        (((x - Ethereum.UInt256.ofNat cost₁) -
            Ethereum.UInt256.ofNat cost₂) -
          Ethereum.UInt256.ofNat cost₃).toNat)
    (hCost₅ :
      cost₅ ≤
        ((((x - Ethereum.UInt256.ofNat cost₁) -
              Ethereum.UInt256.ofNat cost₂) -
            Ethereum.UInt256.ofNat cost₃) -
          Ethereum.UInt256.ofNat cost₄).toNat)
    (hCost₆ :
      cost₆ ≤
        (((((x - Ethereum.UInt256.ofNat cost₁) -
                Ethereum.UInt256.ofNat cost₂) -
              Ethereum.UInt256.ofNat cost₃) -
            Ethereum.UInt256.ofNat cost₄) -
          Ethereum.UInt256.ofNat cost₅).toNat)
    (hCost₇ :
      cost₇ ≤
        ((((((x - Ethereum.UInt256.ofNat cost₁) -
                  Ethereum.UInt256.ofNat cost₂) -
                Ethereum.UInt256.ofNat cost₃) -
              Ethereum.UInt256.ofNat cost₄) -
            Ethereum.UInt256.ofNat cost₅) -
          Ethereum.UInt256.ofNat cost₆).toNat)
    (hRemaining :
      ¬ (((((((x - Ethereum.UInt256.ofNat cost₁) -
                    Ethereum.UInt256.ofNat cost₂) -
                  Ethereum.UInt256.ofNat cost₃) -
                Ethereum.UInt256.ofNat cost₄) -
              Ethereum.UInt256.ofNat cost₅) -
            Ethereum.UInt256.ofNat cost₆) -
          Ethereum.UInt256.ofNat cost₇).toNat < remaining) :
    cost₁ + cost₂ + cost₃ + cost₄ + cost₅ + cost₆ + cost₇ + remaining ≤ x.toNat := by
  let after₆ :=
    (((((x - Ethereum.UInt256.ofNat cost₁) -
            Ethereum.UInt256.ofNat cost₂) -
          Ethereum.UInt256.ofNat cost₃) -
        Ethereum.UInt256.ofNat cost₄) -
      Ethereum.UInt256.ofNat cost₅) -
    Ethereum.UInt256.ofNat cost₆
  have hTail :
      cost₇ + remaining ≤ after₆.toNat :=
    add_le_toNat_of_not_sub_ofNat_lt
      (x := after₆)
      (cost := cost₇)
      (remaining := remaining)
      hCost₇Size
      (by simpa [after₆] using hCost₇)
      (by simpa [after₆] using hRemaining)
  have hSixRemainingShort : ¬ after₆.toNat < cost₇ + remaining :=
    not_lt_of_ge hTail
  have hHead :=
    add_add_add_add_add_add_le_toNat_of_not_sub_ofNat_sub_ofNat_sub_ofNat_sub_ofNat_sub_ofNat_sub_ofNat_lt
      (x := x)
      (cost₁ := cost₁)
      (cost₂ := cost₂)
      (cost₃ := cost₃)
      (cost₄ := cost₄)
      (cost₅ := cost₅)
      (cost₆ := cost₆)
      (remaining := cost₇ + remaining)
      hCost₁Size
      hCost₂Size
      hCost₃Size
      hCost₄Size
      hCost₅Size
      hCost₆Size
      hCost₁
      hCost₂
      hCost₃
      hCost₄
      hCost₅
      hCost₆
      (by simpa [after₆] using hSixRemainingShort)
  omega

lemma isZero_eq_one_of_eq_zero {x : Ethereum.UInt256}
    (h : x = (⟨0⟩ : Ethereum.UInt256)) :
    Ethereum.UInt256.isZero x = (⟨1⟩ : Ethereum.UInt256) := by
  subst h
  decide

lemma isZero_eq_zero_of_ne_zero {x : Ethereum.UInt256}
    (h : x ≠ (⟨0⟩ : Ethereum.UInt256)) :
    Ethereum.UInt256.isZero x = (⟨0⟩ : Ethereum.UInt256) := by
  unfold Ethereum.UInt256.isZero Ethereum.UInt256.eq0 Ethereum.UInt256.fromBool Bool.toUInt256
  cases hbeq : (x == (⟨0⟩ : Ethereum.UInt256))
  · rfl
  · have hbne : (x != (⟨0⟩ : Ethereum.UInt256)) = false := by
      simp [bne, hbeq]
    have hx := Ethereum.EVM.UInt256_bne_zero_eq_false_eq x hbne
    contradiction

lemma isZero_bne_zero_eq_true_of_eq_zero {x : Ethereum.UInt256}
    (h : x = (⟨0⟩ : Ethereum.UInt256)) :
    (Ethereum.UInt256.isZero x != (⟨0⟩ : Ethereum.UInt256)) = true := by
  rw [isZero_eq_one_of_eq_zero h]
  decide

lemma isZero_bne_zero_eq_false_of_ne_zero {x : Ethereum.UInt256}
    (h : x ≠ (⟨0⟩ : Ethereum.UInt256)) :
    (Ethereum.UInt256.isZero x != (⟨0⟩ : Ethereum.UInt256)) = false := by
  rw [isZero_eq_zero_of_ne_zero h]
  decide

lemma ofNat_lt_of_lt {a b : Nat}
    (ha : a < Ethereum.UInt256.size)
    (hb : b < Ethereum.UInt256.size)
    (h : a < b) :
    Ethereum.UInt256.ofNat a < Ethereum.UInt256.ofNat b := by
  unfold Ethereum.UInt256.ofNat
  simp [Id.run]
  change (Fin.ofNat Ethereum.UInt256.size a) < (Fin.ofNat Ethereum.UInt256.size b)
  rw [Fin.lt_def]
  simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact h

lemma not_ofNat_lt_of_not_lt {a b : Nat}
    (ha : a < Ethereum.UInt256.size)
    (hb : b < Ethereum.UInt256.size)
    (h : ¬ a < b) :
    ¬ Ethereum.UInt256.ofNat a < Ethereum.UInt256.ofNat b := by
  unfold Ethereum.UInt256.ofNat
  simp [Id.run]
  change ¬ (Fin.ofNat Ethereum.UInt256.size a) < (Fin.ofNat Ethereum.UInt256.size b)
  rw [Fin.lt_def]
  simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  omega

lemma lt_eq_one_of_lt {a b : Ethereum.UInt256}
    (h : a < b) :
    Ethereum.UInt256.lt a b = (⟨1⟩ : Ethereum.UInt256) := by
  unfold Ethereum.UInt256.lt Ethereum.UInt256.fromBool Bool.toUInt256
  have hdec : decide (a < b) = true := by simp [h]
  rw [hdec]
  decide

lemma lt_eq_zero_of_not_lt {a b : Ethereum.UInt256}
    (h : ¬ a < b) :
    Ethereum.UInt256.lt a b = (⟨0⟩ : Ethereum.UInt256) := by
  unfold Ethereum.UInt256.lt Ethereum.UInt256.fromBool Bool.toUInt256
  have hdec : decide (a < b) = false := by simp [h]
  rw [hdec]
  decide

lemma lt_bne_zero_eq_true_of_lt {a b : Ethereum.UInt256}
    (h : a < b) :
    (Ethereum.UInt256.lt a b != (⟨0⟩ : Ethereum.UInt256)) = true := by
  rw [lt_eq_one_of_lt h]
  decide

lemma lt_bne_zero_eq_false_of_not_lt {a b : Ethereum.UInt256}
    (h : ¬ a < b) :
    (Ethereum.UInt256.lt a b != (⟨0⟩ : Ethereum.UInt256)) = false := by
  rw [lt_eq_zero_of_not_lt h]
  decide

lemma lt_ofNat_bne_zero_eq_true_of_lt {a b : Nat}
    (ha : a < Ethereum.UInt256.size)
    (hb : b < Ethereum.UInt256.size)
    (h : a < b) :
    (Ethereum.UInt256.lt (Ethereum.UInt256.ofNat a) (Ethereum.UInt256.ofNat b) !=
      (⟨0⟩ : Ethereum.UInt256)) = true :=
  lt_bne_zero_eq_true_of_lt (ofNat_lt_of_lt ha hb h)

lemma lt_ofNat_bne_zero_eq_false_of_not_lt {a b : Nat}
    (ha : a < Ethereum.UInt256.size)
    (hb : b < Ethereum.UInt256.size)
    (h : ¬ a < b) :
    (Ethereum.UInt256.lt (Ethereum.UInt256.ofNat a) (Ethereum.UInt256.ofNat b) !=
      (⟨0⟩ : Ethereum.UInt256)) = false :=
  lt_bne_zero_eq_false_of_not_lt (not_ofNat_lt_of_not_lt ha hb h)

lemma eq_eq_one_of_eq {a b : Ethereum.UInt256}
    (h : a = b) :
    Ethereum.UInt256.eq a b = (⟨1⟩ : Ethereum.UInt256) := by
  unfold Ethereum.UInt256.eq Ethereum.UInt256.fromBool Bool.toUInt256
  have hdec : decide (a = b) = true := by simp [h]
  rw [hdec]
  decide

lemma eq_eq_zero_of_ne {a b : Ethereum.UInt256}
    (h : a ≠ b) :
    Ethereum.UInt256.eq a b = (⟨0⟩ : Ethereum.UInt256) := by
  unfold Ethereum.UInt256.eq Ethereum.UInt256.fromBool Bool.toUInt256
  have hdec : decide (a = b) = false := by simp [h]
  rw [hdec]
  decide

lemma eq_bne_zero_eq_true_of_eq {a b : Ethereum.UInt256}
    (h : a = b) :
    (Ethereum.UInt256.eq a b != (⟨0⟩ : Ethereum.UInt256)) = true := by
  rw [eq_eq_one_of_eq h]
  decide

lemma eq_bne_zero_eq_false_of_ne {a b : Ethereum.UInt256}
    (h : a ≠ b) :
    (Ethereum.UInt256.eq a b != (⟨0⟩ : Ethereum.UInt256)) = false := by
  rw [eq_eq_zero_of_ne h]
  decide

end Ethereum.UInt256

namespace Ethereum

lemma fromBytes'_append (xs ys : List UInt8) :
    fromBytes' (xs ++ ys) = fromBytes' xs + 2 ^ (8 * xs.length) * fromBytes' ys := by
  induction xs with
  | nil => simp [fromBytes']
  | cons x xs ih =>
      simp only [List.cons_append, fromBytes', List.length_cons, ih]
      rw [Nat.mul_succ, Nat.pow_add]
      ring

lemma fromBytes'_append_div_pow_length (xs ys : List UInt8) :
    fromBytes' (xs ++ ys) / 2 ^ (8 * xs.length) = fromBytes' ys := by
  rw [fromBytes'_append]
  rw [Nat.add_mul_div_left]
  · rw [Nat.div_eq_of_lt]
    · simp
    · exact fromBytes'_le
  · exact Nat.pow_pos (a := 2) (n := 8 * xs.length) (by decide)

lemma fromBytes'_cons_mod (b : UInt8) (bs : List UInt8) :
    fromBytes' (b :: bs) % 256 = b.toNat := by
  unfold fromBytes'
  rw [show 2 ^ 8 = 256 by norm_num]
  rw [Nat.mul_comm 256 (fromBytes' bs)]
  rw [Nat.add_mul_mod_self_right]
  rw [Nat.mod_eq_of_lt]
  · rfl
  · exact b.toFin.isLt

lemma fromBytes'_cons_div (b : UInt8) (bs : List UInt8) :
    fromBytes' (b :: bs) / 256 = fromBytes' bs := by
  change (b.toFin.val + 2 ^ 8 * fromBytes' bs) / 256 = fromBytes' bs
  rw [show 2 ^ 8 = 256 by norm_num]
  rw [Nat.mul_comm 256 (fromBytes' bs)]
  rw [Nat.add_mul_div_right]
  · rw [Nat.div_eq_of_lt]
    · simp
    · exact b.toFin.isLt
  · norm_num

lemma fromBytes'_inj_of_length_eq : ∀ {xs ys : List UInt8},
    xs.length = ys.length → fromBytes' xs = fromBytes' ys → xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, hLen, _ => by simp at hLen
  | _ :: _, [], hLen, _ => by simp at hLen
  | x :: xs, y :: ys, hLen, hVal => by
      have hHeadVal : x.toNat = y.toNat := by
        have hMod := congrArg (fun n => n % 256) hVal
        simpa [fromBytes'_cons_mod] using hMod
      have hHead : x = y := UInt8.ext hHeadVal
      subst y
      have hTailLen : xs.length = ys.length := by simpa using hLen
      have hTailVal : fromBytes' xs = fromBytes' ys := by
        have hDiv := congrArg (fun n => n / 256) hVal
        simpa [fromBytes'_cons_div] using hDiv
      exact congrArg (List.cons x) (fromBytes'_inj_of_length_eq hTailLen hTailVal)

lemma fromBytes'_reverse_div_pow_224_eq_take_four_reverse {bs : List UInt8}
    (hLen : bs.length = 32) :
    fromBytes' bs.reverse / 2 ^ 224 = fromBytes' (bs.take 4).reverse := by
  have hSplit : bs.reverse = (bs.drop 4).reverse ++ (bs.take 4).reverse := by
    calc
      bs.reverse = (bs.take 4 ++ bs.drop 4).reverse := by rw [List.take_append_drop]
      _ = (bs.drop 4).reverse ++ (bs.take 4).reverse := by rw [List.reverse_append]
  rw [hSplit]
  have hDropLen : (bs.drop 4).reverse.length = 28 := by
    rw [List.length_reverse, List.length_drop, hLen]
  have hPow : 2 ^ 224 = 2 ^ (8 * (bs.drop 4).reverse.length) := by
    rw [hDropLen]
  rw [hPow]
  exact fromBytes'_append_div_pow_length (bs.drop 4).reverse (bs.take 4).reverse

lemma fromBytes'_lt_uint256_size_of_length_le {bs : List UInt8}
    (hLen : bs.length ≤ 32) :
    fromBytes' bs < Ethereum.UInt256.size := by
  have h := @fromBytes'_le bs
  unfold Ethereum.UInt256.size
  refine lt_of_lt_of_le h ?_
  have hPow : 8 * bs.length ≤ 256 := by omega
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hPow

lemma uInt256OfByteArray_toNat_of_size_le {arr : ByteArray}
    (hSize : arr.size ≤ 32) :
    (Ethereum.uInt256OfByteArray arr).toNat =
      Ethereum.fromBytes' arr.data.toList.reverse := by
  have hLen : arr.data.toList.reverse.length ≤ 32 := by
    rw [List.length_reverse, Array.length_toList, ByteArray.size_data]
    exact hSize
  have hLt : Ethereum.fromBytes' arr.data.toList.reverse < Ethereum.UInt256.size :=
    fromBytes'_lt_uint256_size_of_length_le hLen
  unfold Ethereum.uInt256OfByteArray
  exact Ethereum.UInt256.ofNat_toNat_of_lt hLt

lemma uInt256OfByteArray_readBytes_toNat_32 (source : ByteArray) (start : Nat) :
    (Ethereum.uInt256OfByteArray (source.readBytes start 32)).toNat =
      Ethereum.fromBytes' (source.readBytes start 32).data.toList.reverse := by
  apply Ethereum.uInt256OfByteArray_toNat_of_size_le
  rw [ByteArray.readBytes_size_32]

lemma uInt256OfByteArray_shiftRight_224_toNat_eq_extract_zero_four (arr : ByteArray)
    (hSize : arr.size = 32) :
    (Ethereum.UInt256.shiftRight (Ethereum.uInt256OfByteArray arr)
      (⟨0xe0⟩ : Ethereum.UInt256)).toNat =
      Ethereum.fromBytes' (arr.extract 0 4).data.toList.reverse := by
  rw [Ethereum.UInt256.toNat_shiftRight_eq_div_pow_of_lt]
  · rw [Ethereum.UInt256.toNat_fin_ofNat_of_lt (n := 0xe0)
      (by norm_num [Ethereum.UInt256.size])]
    rw [Ethereum.uInt256OfByteArray_toNat_of_size_le]
    · have hLen : arr.data.toList.length = 32 := by
        rw [Array.length_toList, ByteArray.size_data, hSize]
      rw [fromBytes'_reverse_div_pow_224_eq_take_four_reverse hLen]
      congr 1
      rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
      simp
    · omega
  · rw [Ethereum.UInt256.toNat_fin_ofNat_of_lt (n := 0xe0)
      (by norm_num [Ethereum.UInt256.size])]
    norm_num

lemma uInt256OfByteArray_readBytes_zero_shiftRight_224_toNat_eq_extract_zero_four
    {source : ByteArray}
    (hSize : 4 ≤ source.size) :
    (Ethereum.UInt256.shiftRight
      (Ethereum.uInt256OfByteArray (source.readBytes 0 32))
      (⟨0xe0⟩ : Ethereum.UInt256)).toNat =
      Ethereum.fromBytes' (source.extract 0 4).data.toList.reverse := by
  rw [uInt256OfByteArray_shiftRight_224_toNat_eq_extract_zero_four]
  · rw [ByteArray.readBytes_zero_extract_zero_four hSize]
  · rw [ByteArray.readBytes_size_32]

lemma selectorWord_eq_of_extract_eq {source selector : ByteArray} {selectorNat : Nat}
    (hSelectorNat :
      Ethereum.fromBytes' selector.data.toList.reverse = selectorNat)
    (hSelectorNatBound : selectorNat < Ethereum.UInt256.size)
    (hLongCalldata : ¬ source.size < 4)
    (hSelector : source.extract 0 4 = selector) :
    (⟨(OfNat.ofNat selectorNat : Fin Ethereum.UInt256.size)⟩ : Ethereum.UInt256) =
      Ethereum.UInt256.shiftRight
        (Ethereum.uInt256OfByteArray <| source.readBytes 0 32)
        (⟨0xe0⟩ : Ethereum.UInt256) := by
  have hLong : 4 ≤ source.size := by omega
  symm
  apply Ethereum.UInt256.eq_fin_of_toNat_eq hSelectorNatBound
  rw [Ethereum.uInt256OfByteArray_readBytes_zero_shiftRight_224_toNat_eq_extract_zero_four hLong]
  rw [hSelector]
  exact hSelectorNat

lemma extract_eq_of_selectorWord_eq {source selector : ByteArray} {selectorNat : Nat}
    (hSelectorSize : selector.size = 4)
    (hSelectorNat :
      Ethereum.fromBytes' selector.data.toList.reverse = selectorNat)
    (hSelectorNatBound : selectorNat < Ethereum.UInt256.size)
    (hLongCalldata : ¬ source.size < 4)
    (hSelectorWordEq :
      (⟨(OfNat.ofNat selectorNat : Fin Ethereum.UInt256.size)⟩ : Ethereum.UInt256) =
        Ethereum.UInt256.shiftRight
          (Ethereum.uInt256OfByteArray <| source.readBytes 0 32)
          (⟨0xe0⟩ : Ethereum.UInt256)) :
    source.extract 0 4 = selector := by
  have hLong : 4 ≤ source.size := by omega
  have hWordNat :=
    Ethereum.uInt256OfByteArray_readBytes_zero_shiftRight_224_toNat_eq_extract_zero_four
      (source := source) hLong
  have hConstNat :
      (⟨(OfNat.ofNat selectorNat : Fin Ethereum.UInt256.size)⟩ :
        Ethereum.UInt256).toNat = selectorNat :=
    Ethereum.UInt256.toNat_fin_ofNat_of_lt hSelectorNatBound
  have hNat :
      Ethereum.fromBytes' (source.extract 0 4).data.toList.reverse =
        Ethereum.fromBytes' selector.data.toList.reverse := by
    calc
      Ethereum.fromBytes' (source.extract 0 4).data.toList.reverse =
          (Ethereum.UInt256.shiftRight
            (Ethereum.uInt256OfByteArray <| source.readBytes 0 32)
            (⟨0xe0⟩ : Ethereum.UInt256)).toNat := hWordNat.symm
      _ = (⟨(OfNat.ofNat selectorNat : Fin Ethereum.UInt256.size)⟩ :
            Ethereum.UInt256).toNat :=
          (congrArg Ethereum.UInt256.toNat hSelectorWordEq).symm
      _ = selectorNat := hConstNat
      _ = Ethereum.fromBytes' selector.data.toList.reverse := hSelectorNat.symm
  have hExtractSize : (source.extract 0 4).size = 4 := by
    rw [ByteArray.size_extract]
    omega
  have hLen :
      (source.extract 0 4).data.toList.reverse.length =
        selector.data.toList.reverse.length := by
    rw [List.length_reverse, List.length_reverse, Array.length_toList, Array.length_toList,
      ByteArray.size_data, ByteArray.size_data, hExtractSize, hSelectorSize]
  have hRevList :
      (source.extract 0 4).data.toList.reverse =
        selector.data.toList.reverse :=
    Ethereum.fromBytes'_inj_of_length_eq hLen hNat
  apply ByteArray.ext
  apply Array.toList_inj.mp
  exact List.reverse_injective hRevList

lemma selectorWord_ne_of_extract_ne {source selector : ByteArray} {selectorNat : Nat}
    (hSelectorSize : selector.size = 4)
    (hSelectorNat :
      Ethereum.fromBytes' selector.data.toList.reverse = selectorNat)
    (hSelectorNatBound : selectorNat < Ethereum.UInt256.size)
    (hLongCalldata : ¬ source.size < 4)
    (hSelector : source.extract 0 4 ≠ selector) :
    (⟨(OfNat.ofNat selectorNat : Fin Ethereum.UInt256.size)⟩ : Ethereum.UInt256) ≠
      Ethereum.UInt256.shiftRight
        (Ethereum.uInt256OfByteArray <| source.readBytes 0 32)
        (⟨0xe0⟩ : Ethereum.UInt256) := by
  intro hEq
  exact hSelector
    (extract_eq_of_selectorWord_eq hSelectorSize hSelectorNat hSelectorNatBound
      hLongCalldata hEq)

end Ethereum

lemma Ethereum_toBytes'_one : Ethereum.toBytes' 1 = [1] := by
  unfold Ethereum.toBytes'
  simp
  constructor
  · decide
  · unfold Ethereum.toBytes'
    rfl

namespace ABI

lemma decodeCalldata_no_params_of_not_lt {calldata : ByteArray}
    (hSize : ¬ calldata.toList.length < 4) :
    decodeCalldata [] [] calldata = some (∅ : Store) := by
  simp [decodeCalldata, decodeCalldata.decodeArgs, hSize]

lemma decodeCalldata_no_params_of_lt {calldata : ByteArray}
    (hSize : calldata.toList.length < 4) :
    decodeCalldata [] [] calldata = none := by
  simp [decodeCalldata, hSize]

end ABI

/-! ## Dispatch helpers -/

lemma dispatchMsg_singleton_some_of_selector
    {contract : ContractDecl} {transition : TransitionDecl} {selector calldata : ByteArray}
    (hTransitions : contract.transitions = [transition])
    (hHash :
      (ffi.KEC (String.toByteArray (transitionSigStr transition))).extract 0 4 = selector)
    (hSelector : calldata.extract 0 4 = selector) :
    dispatchMsg contract calldata = some transition := by
  simp [dispatchMsg, hTransitions, hHash, hSelector]

lemma dispatchMsg_singleton_none_of_selector_ne
    {contract : ContractDecl} {transition : TransitionDecl} {selector calldata : ByteArray}
    (hTransitions : contract.transitions = [transition])
    (hHash :
      (ffi.KEC (String.toByteArray (transitionSigStr transition))).extract 0 4 = selector)
    (hSelector : calldata.extract 0 4 ≠ selector) :
    dispatchMsg contract calldata = none := by
  have hBeq : (selector == calldata.extract 0 4) = false :=
    ByteArray.beq_false_of_ne (fun h => hSelector h.symm)
  simp [dispatchMsg, hTransitions, hHash, hBeq]

/-! ## Runtime-equivalence constructors as compositional helpers -/

lemma runtimeEquivalence_intro
    {cfg : Config} {bytecode : ByteArray} {contract : ContractDecl}
    (h :
      ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
        (genesisBlockHeader : Ethereum.BlockHeader)
        (blocks : Ethereum.ProcessedBlocks)
        (σ : Ethereum.AccountMap)
        (σ₀ : Ethereum.AccountMap)
        (g : Ethereum.UInt256)
        (A : Ethereum.Substate)
        (I : Ethereum.ExecutionEnv),
        I.code = bytecode →
        I.calldata.size < Ethereum.UInt256.size →
        runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I) :
    runtimeEquivalence!?! cfg bytecode contract :=
  runtimeEquivalence!?!.intro h

lemma runtimeEquivalenceFor_execution
    {cfg : Config} {contract : ContractDecl}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {Ξ_res actRes returnType}
    (hΞ :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = Ξ_res)
    (hAct :
      actExec cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I actRes returnType)
    (hEquiv : execResultsEquiv Ξ_res actRes returnType) :
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I :=
  runtimeEquivalenceFor.execution hΞ hAct hEquiv

lemma runtimeEquivalenceFor_noDispatch
    {cfg : Config} {contract : ContractDecl}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g g' : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {o : ByteArray}
    (hDispatch : dispatchMsg contract I.calldata = none)
    (hΞ :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .ok (.revert g' o)) :
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I :=
  runtimeEquivalenceFor.noDispatch hDispatch hΞ

lemma runtimeEquivalenceFor_noDispatch_singleton_revert
    {cfg : Config} {contract : ContractDecl} {transition : TransitionDecl}
    {selector : ByteArray}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g g' : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {o : ByteArray}
    (hTransitions : contract.transitions = [transition])
    (hHash :
      (ffi.KEC (String.toByteArray (transitionSigStr transition))).extract 0 4 = selector)
    (hSelector : I.calldata.extract 0 4 ≠ selector)
    (hΞ :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .ok (.revert g' o)) :
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I :=
  runtimeEquivalenceFor_noDispatch
    (dispatchMsg_singleton_none_of_selector_ne hTransitions hHash hSelector)
    hΞ

lemma runtimeEquivalenceFor_decodingFailed
    {cfg : Config} {contract : ContractDecl}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g g' : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {transition transitionSig o}
    (hDispatch : dispatchMsg contract I.calldata = some transition)
    (hSig : transitionSig = transitionSignature transition)
    (hDecode :
      decodeCalldata (transition.params.map Param.name) transitionSig.paramTypes I.calldata =
        none)
    (hΞ :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .ok (.revert g' o)) :
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I :=
  runtimeEquivalenceFor.decodingFailed hDispatch hSig hDecode hΞ

lemma runtimeEquivalenceFor_outOfGas
    {cfg : Config} {contract : ContractDecl}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hΞ :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .error .OutOfGass) :
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I :=
  runtimeEquivalenceFor.outOfGas hΞ

/-! ## Initial EVM state used by `Ξ` and `actExec` -/

def initialEVMState
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ : Ethereum.AccountMap)
    (σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) : EVM.State :=
  { (default : EVM.State) with
    accountMap := σ
    σ₀ := σ₀
    executionEnv := I
    substate := A
    createdAccounts := createdAccounts
    machineState.gasAvailable := g
    blocks := blocks
    genesisBlockHeader := genesisBlockHeader }

@[simp] lemma initialEVMState_accountMap
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ : Ethereum.AccountMap}
    {σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).accountMap = σ :=
  rfl

@[simp] lemma initialEVMState_createdAccounts
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ : Ethereum.AccountMap}
    {σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).createdAccounts =
      createdAccounts :=
  rfl

@[simp] lemma initialEVMState_executionEnv
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ : Ethereum.AccountMap}
    {σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
      (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).executionEnv = I :=
  rfl

@[simp] lemma initialEVMState_gasAvailable
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ : Ethereum.AccountMap}
    {σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).machineState.gasAvailable =
      g :=
  rfl

@[simp] lemma initialEVMState_pc
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ : Ethereum.AccountMap}
    {σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).machineState.pc =
      (⟨0⟩ : Ethereum.UInt256) :=
  rfl

@[simp] lemma initialEVMState_stack
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ : Ethereum.AccountMap}
    {σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).machineState.stack =
      ([] : Ethereum.Stack Ethereum.UInt256) :=
  rfl

@[simp] lemma initialEVMState_execLength
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ : Ethereum.AccountMap}
    {σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).machineState.execLength =
      0 :=
  rfl

@[simp] lemma initialEVMState_activeWords
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ : Ethereum.AccountMap}
    {σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).machineState.activeWords =
      (⟨0⟩ : Ethereum.UInt256) :=
  rfl

@[simp] lemma initialEVMState_memory
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ : Ethereum.AccountMap}
    {σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).machineState.memory =
      (default : ByteArray) :=
  rfl

@[simp] lemma initialEVMState_returnData
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ : Ethereum.AccountMap}
    {σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).machineState.returnData =
      (default : ByteArray) :=
  rfl

@[simp] lemma initialEVMState_H_return
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ : Ethereum.AccountMap}
    {σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).machineState.H_return =
      (default : ByteArray) :=
  rfl

/-! ## Return/result equivalence helpers -/

namespace returnEquiv

lemma returned_of_encode {o : ByteArray} {rv : Value} {abit : ABIType}
    (hEncode : encodeReturnValue? abit rv = some o) :
    returnEquiv o (some rv) (some abit) :=
  returnEquiv.returned rfl rfl hEncode

lemma void_of_null {o : ByteArray} (ho : o = null) :
    returnEquiv o none none :=
  returnEquiv.void rfl rfl ho

lemma fallthrough_of_default {o : ByteArray} {abit : ABIType} {dv : Value}
    (hDefault : defaultAbiValue abit = some dv)
    (hEncode : encodeReturnValue? abit dv = some o) :
    returnEquiv o none (some abit) :=
  returnEquiv.fallthrough rfl rfl hDefault hEncode

end returnEquiv

def abiBoolTrueReturn : ByteArray :=
  ByteArray.mk #[
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1
  ]

lemma encodeReturnValue_bool_true :
    encodeReturnValue? (.elem .bool) (.bool true) = some abiBoolTrueReturn := by
  simp [abiBoolTrueReturn, encodeReturnValue?, encodeReturnValues?, encodeABIValues?,
    encodeABIValuesFrom?, encodeABIValue?, encodeABIWord?, EVM.Word.toBytesBE,
    Ethereum.toBytesBigEndian, Ethereum.UInt256.ofNat, Ethereum.UInt256.size, Id.run,
    abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, Ethereum_toBytes'_one]

lemma returnEquiv_bool_true :
    returnEquiv abiBoolTrueReturn (some (.bool true)) (some (.elem .bool)) :=
  returnEquiv.returned_of_encode encodeReturnValue_bool_true

namespace execResultsEquiv

lemma success_of_returnEquiv
    {evmRes :
      Except Ethereum.EVM.ExecutionException
        (Ethereum.ExecutionResult
          (Batteries.RBSet Ethereum.AccountAddress compare × Ethereum.AccountMap ×
            Ethereum.UInt256 × Ethereum.Substate))}
    {actRes : ExecResult}
    {t : Option ABIType}
    {createdAccounts' : Batteries.RBSet Ethereum.AccountAddress compare}
    {σ' : Ethereum.AccountMap}
    {g' : Ethereum.UInt256}
    {A' : Ethereum.Substate}
    {o : ByteArray}
    {frame : Frame}
    {actState : EVM.State}
    {retVal : Option Value}
    (hEvm : evmRes = .ok (.success (createdAccounts', σ', g', A') o))
    (hAct : actRes = .returned frame actState retVal)
    (hCreated : createdAccounts' = actState.createdAccounts)
    (hAccounts : σ' = actState.accountMap)
    (hReturn : returnEquiv o retVal t) :
    execResultsEquiv evmRes actRes t :=
  execResultsEquiv.success hEvm hAct hCreated hAccounts hReturn

lemma success_rfl
    {t : Option ABIType}
    {g' : Ethereum.UInt256}
    {A' : Ethereum.Substate}
    {o : ByteArray}
    {frame : Frame}
    {actState : EVM.State}
    {retVal : Option Value}
    (hReturn : returnEquiv o retVal t) :
    execResultsEquiv
      (.ok (.success (actState.createdAccounts, actState.accountMap, g', A') o))
      (.returned frame actState retVal)
      t :=
  execResultsEquiv.success rfl rfl rfl rfl hReturn

lemma revert_rfl {g : Ethereum.UInt256} {o : ByteArray} {t : Option ABIType} :
    execResultsEquiv (.ok (.revert g o)) .reverted t :=
  execResultsEquiv.revert rfl rfl

lemma error_rfl {e : Ethereum.EVM.ExecutionException} {t : Option ABIType} :
    execResultsEquiv (.error e) .reverted t :=
  execResultsEquiv.error rfl rfl

end execResultsEquiv

/-! ## Act execution helpers -/

lemma actExec_of_dispatch_decode_exec
    {conf : Config}
    {contract : ContractDecl}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {actRes : ExecResult}
    {transition transitionSig callargs evmState}
    (hDispatch : dispatchMsg contract I.calldata = some transition)
    (hSig : transitionSig = transitionSignature transition)
    (hDecode :
      decodeCalldata (transition.params.map Param.name) transitionSig.paramTypes I.calldata =
        some callargs)
    (hState :
      evmState =
        { (default : EVM.State) with
          accountMap := σ
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := createdAccounts
          machineState.gasAvailable := g
          blocks := blocks
          genesisBlockHeader := genesisBlockHeader })
    (hExec : ExecContractBody conf contract evmState callargs transition.body actRes) :
    actExec conf contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I actRes
      transition.returnType :=
  actExec.intro hDispatch hSig hDecode hState hExec

lemma actExec_of_dispatch_decode_initial
    {conf : Config}
    {contract : ContractDecl}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {actRes : ExecResult}
    {transition transitionSig callargs}
    (hDispatch : dispatchMsg contract I.calldata = some transition)
    (hSig : transitionSig = transitionSignature transition)
    (hDecode :
      decodeCalldata (transition.params.map Param.name) transitionSig.paramTypes I.calldata =
        some callargs)
    (hExec :
      ExecContractBody conf contract
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
        callargs transition.body actRes) :
    actExec conf contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I actRes
      transition.returnType :=
  actExec_of_dispatch_decode_exec
    (evmState := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
    hDispatch hSig hDecode rfl hExec

lemma actExec_singleton_no_params_initial
    {conf : Config}
    {contract : ContractDecl}
    {transition : TransitionDecl}
    {selector : ByteArray}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {actRes : ExecResult}
    (hTransitions : contract.transitions = [transition])
    (hHash :
      (ffi.KEC (String.toByteArray (transitionSigStr transition))).extract 0 4 = selector)
    (hSelectorSize : selector.size = 4)
    (hParams : transition.params = [])
    (hSelector : I.calldata.extract 0 4 = selector)
    (hExec :
      ExecContractBody conf contract
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
        (∅ : Store) transition.body actRes) :
    actExec conf contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I actRes
      transition.returnType := by
  have hDispatch : dispatchMsg contract I.calldata = some transition :=
    dispatchMsg_singleton_some_of_selector hTransitions hHash hSelector
  have hEnoughCalldata : ¬ I.calldata.toList.length < 4 :=
    ByteArray.not_toList_length_lt_of_extract_eq_size hSelectorSize hSelector
  have hDecode :
      decodeCalldata (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata =
        some (∅ : Store) := by
    simpa [transitionSignature, hParams] using
      ABI.decodeCalldata_no_params_of_not_lt (calldata := I.calldata) hEnoughCalldata
  exact actExec_of_dispatch_decode_initial
    (transition := transition)
    (transitionSig := transitionSignature transition)
    (callargs := (∅ : Store))
    hDispatch
    rfl
    hDecode
    hExec

lemma runtimeEquivalenceFor_success_initial
    {cfg : Config} {contract : ContractDecl}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g g' : Ethereum.UInt256}
    {A A' : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {frame : Frame}
    {retVal : Option Value}
    {returnType : Option ABIType}
    {o : ByteArray}
    (hΞ :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .ok (.success (createdAccounts, σ, g', A') o))
    (hAct :
      actExec cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I
        (.returned frame
          (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
          retVal)
        returnType)
    (hReturn : returnEquiv o retVal returnType) :
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I :=
  runtimeEquivalenceFor_execution hΞ hAct
    (execResultsEquiv.success rfl rfl rfl rfl hReturn)

lemma runtimeEquivalenceFor_success_initial_of_eq
    {cfg : Config} {contract : ContractDecl}
    {createdAccounts createdAccounts' : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ σ' : Ethereum.AccountMap}
    {g g' : Ethereum.UInt256}
    {A A' : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {frame : Frame}
    {retVal : Option Value}
    {returnType : Option ABIType}
    {o : ByteArray}
    (hΞ :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .ok (.success (createdAccounts', σ', g', A') o))
    (hCreated : createdAccounts' = createdAccounts)
    (hAccounts : σ' = σ)
    (hAct :
      actExec cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I
        (.returned frame
          (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
          retVal)
        returnType)
    (hReturn : returnEquiv o retVal returnType) :
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I :=
  runtimeEquivalenceFor_execution hΞ hAct
    (execResultsEquiv.success rfl rfl
      (by simpa [initialEVMState] using hCreated)
      (by simpa [initialEVMState] using hAccounts)
      hReturn)

lemma runtimeEquivalenceFor_revert_of_act_reverted
    {cfg : Config} {contract : ContractDecl}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g g' : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {returnType : Option ABIType}
    {o : ByteArray}
    (hΞ :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .ok (.revert g' o))
    (hAct :
      actExec cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I
        .reverted returnType) :
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I :=
  runtimeEquivalenceFor_execution hΞ hAct execResultsEquiv.revert_rfl

/-! ## Relating EVM `X` traces to top-level `Ξ` results -/

lemma EVM_Xi_of_X_success
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {evmState : Ethereum.State}
    {o : ByteArray}
    (hX :
      Ethereum.EVM.X (g.toNat + 1) (Ethereum.EVM.D_J I.code ⟨0⟩)
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
        .ok (.success evmState o)) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success
        (evmState.createdAccounts, evmState.accountMap, evmState.machineState.gasAvailable,
          evmState.substate) o) := by
  unfold Ethereum.EVM.Ξ
  change (do
      let result ← Ethereum.EVM.X (g.toNat + 1) (Ethereum.EVM.D_J I.code ⟨0⟩)
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      match result with
      | Ethereum.ExecutionResult.success st out =>
          .ok (Ethereum.ExecutionResult.success
            (st.createdAccounts, st.accountMap, st.machineState.gasAvailable, st.substate) out)
      | Ethereum.ExecutionResult.revert gas out => .ok (Ethereum.ExecutionResult.revert gas out)) =
    .ok (.success
      (evmState.createdAccounts, evmState.accountMap, evmState.machineState.gasAvailable,
        evmState.substate) o)
  simp [hX, bind, Except.bind]

lemma EVM_Xi_of_X_revert
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g g' : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {o : ByteArray}
    (hX :
      Ethereum.EVM.X (g.toNat + 1) (Ethereum.EVM.D_J I.code ⟨0⟩)
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
        .ok (.revert g' o)) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert g' o) := by
  unfold Ethereum.EVM.Ξ
  change (do
      let result ← Ethereum.EVM.X (g.toNat + 1) (Ethereum.EVM.D_J I.code ⟨0⟩)
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      match result with
      | Ethereum.ExecutionResult.success st out =>
          .ok (Ethereum.ExecutionResult.success
            (st.createdAccounts, st.accountMap, st.machineState.gasAvailable, st.substate) out)
      | Ethereum.ExecutionResult.revert gas out => .ok (Ethereum.ExecutionResult.revert gas out)) =
    .ok (.revert g' o)
  simp [hX, bind, Except.bind]

lemma EVM_Xi_of_X_error
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {e : Ethereum.EVM.ExecutionException}
    (hX :
      Ethereum.EVM.X (g.toNat + 1) (Ethereum.EVM.D_J I.code ⟨0⟩)
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
        .error e) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e := by
  unfold Ethereum.EVM.Ξ
  change (do
      let result ← Ethereum.EVM.X (g.toNat + 1) (Ethereum.EVM.D_J I.code ⟨0⟩)
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      match result with
      | Ethereum.ExecutionResult.success st out =>
          .ok (Ethereum.ExecutionResult.success
            (st.createdAccounts, st.accountMap, st.machineState.gasAvailable, st.substate) out)
      | Ethereum.ExecutionResult.revert gas out => .ok (Ethereum.ExecutionResult.revert gas out)) =
    .error e
  simp [hX, bind, Except.bind]

lemma EVM_Xi_of_initial_Xstep_success
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {evmState : Ethereum.State}
    {o : ByteArray}
    (hStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
        .ok (evmState, some (true, o))) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success
        (evmState.createdAccounts, evmState.accountMap, evmState.machineState.gasAvailable,
          evmState.substate) o) :=
  EVM_Xi_of_X_success
    (Ethereum.EVM.Xstep_X_X_halt_success g.toNat
      (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      evmState (Ethereum.EVM.D_J I.code ⟨0⟩) o hStep)

lemma EVM_Xi_of_initial_Xstep_revert
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {evmState : Ethereum.State}
    {o : ByteArray}
    (hStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
        .ok (evmState, some (false, o))) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert evmState.machineState.gasAvailable o) :=
  EVM_Xi_of_X_revert
    (Ethereum.EVM.Xstep_X_X_halt_revert g.toNat
      (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      evmState (Ethereum.EVM.D_J I.code ⟨0⟩) o hStep)

lemma EVM_Xi_of_initial_Xstep_error
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {e : Ethereum.EVM.ExecutionException}
    (hStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
        .error e) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e :=
  EVM_Xi_of_X_error
    (Ethereum.EVM.Xstep_X_X_except g.toNat
      (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (Ethereum.EVM.D_J I.code ⟨0⟩) e hStep)

namespace Ethereum.EVM

/-! ### Small opcode-step wrappers -/

theorem decode_of_code_eq {code : ByteArray} {s : Ethereum.State}
    {decoded : Option (Ethereum.Operation × Option (Ethereum.UInt256 × Nat))}
    (hCode : s.executionEnv.code = code)
    (hDecode : decode code s.machineState.pc = decoded) :
    decode s.executionEnv.code s.machineState.pc = decoded := by
  simpa [hCode] using hDecode

theorem Xstep_of_code_eq {code : ByteArray} {s : Ethereum.State}
    {result : Except ExecutionException (Ethereum.State × Option (Bool × ByteArray))}
    (hCode : s.executionEnv.code = code)
    (hStep : Xstep (D_J s.executionEnv.code ⟨0⟩) s = result) :
    Xstep (D_J code ⟨0⟩) s = result := by
  simpa [hCode] using hStep

theorem Xstep_of_code_eq_of_decode {code : ByteArray} {s : Ethereum.State}
    {decoded : Option (Ethereum.Operation × Option (Ethereum.UInt256 × Nat))}
    {result : Except ExecutionException (Ethereum.State × Option (Bool × ByteArray))}
    (hCode : s.executionEnv.code = code)
    (hDecode : decode code s.machineState.pc = decoded)
    (hStep :
      decode s.executionEnv.code s.machineState.pc = decoded →
        Xstep (D_J s.executionEnv.code ⟨0⟩) s = result) :
    Xstep (D_J code ⟨0⟩) s = result :=
  Xstep_of_code_eq hCode (hStep (decode_of_code_eq hCode hDecode))

theorem D_J_contains_of_code_eq {code code' : ByteArray} {start dest : Ethereum.UInt256}
    (hCode : code = code')
    (hContains : (D_J code' start).contains dest = true) :
    (D_J code start).contains dest = true := by
  simpa [hCode] using hContains

theorem executionEnv_eq_of_Xstep {validJumps : Array Ethereum.UInt256}
    {s t : Ethereum.State} {o : Option (Bool × ByteArray)}
    (hStep : Xstep validJumps s = .ok (t, o)) :
    s.executionEnv = t.executionEnv :=
  Xstep_env_unchanged s t validJumps o hStep

theorem code_eq_of_Xstep {validJumps : Array Ethereum.UInt256}
    {code : ByteArray} {s t : Ethereum.State} {o : Option (Bool × ByteArray)}
    (hStep : Xstep validJumps s = .ok (t, o))
    (hCode : s.executionEnv.code = code) :
    t.executionEnv.code = code := by
  have hEnv := executionEnv_eq_of_Xstep hStep
  exact (congrArg (fun env => env.code) hEnv.symm).trans hCode

def push1NextState (s : Ethereum.State) (arg : Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := arg :: s.machineState.stack
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem push1NextState_stack (s : Ethereum.State) (arg : Ethereum.UInt256) :
    (push1NextState s arg).machineState.stack = arg :: s.machineState.stack :=
  rfl

@[simp] theorem push1NextState_gasAvailable (s : Ethereum.State) (arg : Ethereum.UInt256) :
    (push1NextState s arg).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow :=
  rfl

@[simp] theorem push1NextState_pc (s : Ethereum.State) (arg : Ethereum.UInt256) :
    (push1NextState s arg).machineState.pc =
      s.machineState.pc + Ethereum.UInt256.ofNat 2 :=
  rfl

theorem Xstep_push1_oog_of_decode {s : Ethereum.State} {arg : Ethereum.UInt256}
    (hDecode :
      decode s.executionEnv.code s.machineState.pc = some (.PUSH1, .some (arg, 1)))
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_push1 s arg hDecode
  simpa [hGas] using hStep

theorem Xstep_push1_continue_of_decode {s : Ethereum.State} {arg : Ethereum.UInt256}
    (hDecode :
      decode s.executionEnv.code s.machineState.pc = some (.PUSH1, .some (arg, 1)))
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow)
    (hStack : s.machineState.stack.length < 1024) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (push1NextState s arg, none) := by
  have hStep := step_push1 s arg hDecode
  have hNoOverflow : ¬ s.machineState.stack.length - 0 + 1 > 1024 := by
    omega
  have hNoOverflow' : ¬ 1024 < s.machineState.stack.length + 1 := by
    omega
  simpa [push1NextState, hGas, hNoOverflow, hNoOverflow'] using hStep

def push4NextState (s : Ethereum.State) (arg : Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := arg :: s.machineState.stack
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + Ethereum.UInt256.ofNat 5
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem push4NextState_stack (s : Ethereum.State) (arg : Ethereum.UInt256) :
    (push4NextState s arg).machineState.stack = arg :: s.machineState.stack :=
  rfl

@[simp] theorem push4NextState_gasAvailable (s : Ethereum.State) (arg : Ethereum.UInt256) :
    (push4NextState s arg).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow :=
  rfl

@[simp] theorem push4NextState_pc (s : Ethereum.State) (arg : Ethereum.UInt256) :
    (push4NextState s arg).machineState.pc =
      s.machineState.pc + Ethereum.UInt256.ofNat 5 :=
  rfl

theorem Xstep_push4_oog_of_decode {s : Ethereum.State} {arg : Ethereum.UInt256}
    (hDecode :
      decode s.executionEnv.code s.machineState.pc = some (.PUSH4, .some (arg, 4)))
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_push4 s arg hDecode
  simpa [hGas] using hStep

theorem Xstep_push4_continue_of_decode {s : Ethereum.State} {arg : Ethereum.UInt256}
    (hDecode :
      decode s.executionEnv.code s.machineState.pc = some (.PUSH4, .some (arg, 4)))
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow)
    (hStack : s.machineState.stack.length < 1024) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (push4NextState s arg, none) := by
  have hStep := step_push4 s arg hDecode
  have hNoOverflow : ¬ s.machineState.stack.length - 0 + 1 > 1024 := by
    omega
  have hNoOverflow' : ¬ 1024 < s.machineState.stack.length + 1 := by
    omega
  simpa [push4NextState, hGas, hNoOverflow, hNoOverflow'] using hStep

def mloadValue (s : Ethereum.State) (a : Ethereum.UInt256) : Ethereum.UInt256 :=
  if a.toNat ≥ s.machineState.memory.size ∨
      a ≥ s.machineState.activeWords * (⟨32⟩ : Ethereum.UInt256) then
    (⟨0⟩ : Ethereum.UInt256)
  else
    Ethereum.UInt256.ofNat
      (Ethereum.fromByteArrayBigEndian
        (s.machineState.memory.readWithPadding a.toNat 32))

def mloadNextState (s : Ethereum.State) (a : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  let memoryCost := memoryExpansionCost s .MLOAD
  let gasAvailable' := s.machineState.gasAvailable - Ethereum.UInt256.ofNat memoryCost
  {s with
    machineState.stack := mloadValue s a :: t
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M s.machineState.activeWords.toNat a.toNat 32)
    machineState.gasAvailable := gasAvailable' - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem mloadNextState_stack (s : Ethereum.State) (a : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (mloadNextState s a t).machineState.stack = mloadValue s a :: t :=
  rfl

@[simp] theorem mloadNextState_gasAvailable (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (mloadNextState s a t).machineState.gasAvailable =
      (s.machineState.gasAvailable - Ethereum.UInt256.ofNat (memoryExpansionCost s .MLOAD)) -
        Ethereum.UInt256.ofNat GasConstants.Gverylow :=
  rfl

@[simp] theorem mloadNextState_pc (s : Ethereum.State) (a : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (mloadNextState s a t).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_mload_memory_oog_of_decode {s : Ethereum.State}
    {a : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.MLOAD, .none))
    (hStack : s.machineState.stack = a :: t)
    (hMemGas : s.machineState.gasAvailable.toNat < memoryExpansionCost s .MLOAD) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_mload s hDecode
  simpa [hStack, hMemGas] using hStep

theorem Xstep_mload_verylow_oog_of_decode {s : Ethereum.State}
    {a : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.MLOAD, .none))
    (hStack : s.machineState.stack = a :: t)
    (hMemGas : ¬ s.machineState.gasAvailable.toNat < memoryExpansionCost s .MLOAD)
    (hVerylowGas :
      (s.machineState.gasAvailable - Ethereum.UInt256.ofNat (memoryExpansionCost s .MLOAD)).toNat <
        GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_mload s hDecode
  simpa [hStack, hMemGas, hVerylowGas] using hStep

theorem Xstep_mload_continue_of_decode {s : Ethereum.State}
    {a : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.MLOAD, .none))
    (hStack : s.machineState.stack = a :: t)
    (hMemGas : ¬ s.machineState.gasAvailable.toNat < memoryExpansionCost s .MLOAD)
    (hVerylowGas :
      ¬ (s.machineState.gasAvailable - Ethereum.UInt256.ofNat (memoryExpansionCost s .MLOAD)).toNat <
        GasConstants.Gverylow)
    (hStackBound : ¬ 1024 < t.length + 1) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (mloadNextState s a t, none) := by
  have hStep := step_mload s hDecode
  simpa [mloadNextState, mloadValue, hStack, hMemGas, hVerylowGas, hStackBound] using hStep

def mstoreNextState (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  let memoryCost := memoryExpansionCost s .MSTORE
  let gasAvailable' := s.machineState.gasAvailable - Ethereum.UInt256.ofNat memoryCost
  {s with
    machineState.stack := t
    machineState.memory := b.toByteArray.write 0 s.machineState.memory a.toNat 32
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M s.machineState.activeWords.toNat a.toNat 32)
    machineState.gasAvailable := gasAvailable' - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem mstoreNextState_stack (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (mstoreNextState s a b t).machineState.stack = t :=
  rfl

@[simp] theorem mstoreNextState_memory (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (mstoreNextState s a b t).machineState.memory =
      b.toByteArray.write 0 s.machineState.memory a.toNat 32 :=
  rfl

@[simp] theorem mstoreNextState_gasAvailable (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (mstoreNextState s a b t).machineState.gasAvailable =
      (s.machineState.gasAvailable - Ethereum.UInt256.ofNat (memoryExpansionCost s .MSTORE)) -
        Ethereum.UInt256.ofNat GasConstants.Gverylow :=
  rfl

@[simp] theorem mstoreNextState_pc (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (mstoreNextState s a b t).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_mstore_memory_oog_of_decode {s : Ethereum.State}
    {a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.MSTORE, .none))
    (hStack : s.machineState.stack = a :: b :: t)
    (hMemGas : s.machineState.gasAvailable.toNat < memoryExpansionCost s .MSTORE) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_mstore s hDecode
  simpa [hStack, hMemGas] using hStep

theorem Xstep_mstore_verylow_oog_of_decode {s : Ethereum.State}
    {a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.MSTORE, .none))
    (hStack : s.machineState.stack = a :: b :: t)
    (hMemGas : ¬ s.machineState.gasAvailable.toNat < memoryExpansionCost s .MSTORE)
    (hVerylowGas :
      (s.machineState.gasAvailable - Ethereum.UInt256.ofNat (memoryExpansionCost s .MSTORE)).toNat <
        GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_mstore s hDecode
  simpa [hStack, hMemGas, hVerylowGas] using hStep

theorem Xstep_mstore_continue_of_decode {s : Ethereum.State}
    {a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.MSTORE, .none))
    (hStack : s.machineState.stack = a :: b :: t)
    (hMemGas : ¬ s.machineState.gasAvailable.toNat < memoryExpansionCost s .MSTORE)
    (hVerylowGas :
      ¬ (s.machineState.gasAvailable - Ethereum.UInt256.ofNat (memoryExpansionCost s .MSTORE)).toNat <
        GasConstants.Gverylow)
    (hStackBound : ¬ 1024 < t.length) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (mstoreNextState s a b t, none) := by
  have hStep := step_mstore s hDecode
  simpa [mstoreNextState, hStack, hMemGas, hVerylowGas, hStackBound] using hStep

def callvalueNextState (s : Ethereum.State) : Ethereum.State :=
  {s with
    machineState.stack := s.executionEnv.weiValue :: s.machineState.stack
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

theorem Xstep_callvalue_oog_of_decode {s : Ethereum.State}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.CALLVALUE, .none))
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gbase) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_callvalue s hDecode
  simpa [hGas] using hStep

theorem Xstep_callvalue_continue_of_decode {s : Ethereum.State}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.CALLVALUE, .none))
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase)
    (hStack : s.machineState.stack.length < 1024) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (callvalueNextState s, none) := by
  have hStep := step_callvalue s hDecode
  have hNoOverflow : ¬ s.machineState.stack.length - 0 + 1 > 1024 := by
    omega
  have hNoOverflow' : ¬ 1024 < s.machineState.stack.length + 1 := by
    omega
  simpa [callvalueNextState, hGas, hNoOverflow, hNoOverflow'] using hStep

def calldatasizeNextState (s : Ethereum.State) : Ethereum.State :=
  {s with
    machineState.stack := Ethereum.UInt256.ofNat s.executionEnv.calldata.size :: s.machineState.stack
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem calldatasizeNextState_stack (s : Ethereum.State) :
    (calldatasizeNextState s).machineState.stack =
      Ethereum.UInt256.ofNat s.executionEnv.calldata.size :: s.machineState.stack :=
  rfl

@[simp] theorem calldatasizeNextState_gasAvailable (s : Ethereum.State) :
    (calldatasizeNextState s).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gbase :=
  rfl

@[simp] theorem calldatasizeNextState_pc (s : Ethereum.State) :
    (calldatasizeNextState s).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_calldatasize_oog_of_decode {s : Ethereum.State}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.CALLDATASIZE, .none))
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gbase) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_calldatasize s hDecode
  simpa [hGas] using hStep

theorem Xstep_calldatasize_continue_of_decode {s : Ethereum.State}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.CALLDATASIZE, .none))
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase)
    (hStack : s.machineState.stack.length < 1024) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (calldatasizeNextState s, none) := by
  have hStep := step_calldatasize s hDecode
  have hNoOverflow : ¬ s.machineState.stack.length - 0 + 1 > 1024 := by
    omega
  have hNoOverflow' : ¬ 1024 < s.machineState.stack.length + 1 := by
    omega
  simpa [calldatasizeNextState, hGas, hNoOverflow, hNoOverflow'] using hStep

def calldataloadNextState (s : Ethereum.State) (a : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack :=
      (Ethereum.uInt256OfByteArray <| s.executionEnv.calldata.readBytes a.toNat 32) :: t
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem calldataloadNextState_stack (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (calldataloadNextState s a t).machineState.stack =
      (Ethereum.uInt256OfByteArray <| s.executionEnv.calldata.readBytes a.toNat 32) :: t :=
  rfl

@[simp] theorem calldataloadNextState_gasAvailable (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (calldataloadNextState s a t).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow :=
  rfl

@[simp] theorem calldataloadNextState_pc (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (calldataloadNextState s a t).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_calldataload_oog_of_decode {s : Ethereum.State}
    {a : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.CALLDATALOAD, .none))
    (hStack : s.machineState.stack = a :: t)
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_calldataload s hDecode
  simpa [hStack, hGas] using hStep

theorem Xstep_calldataload_continue_of_decode {s : Ethereum.State}
    {a : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.CALLDATALOAD, .none))
    (hStack : s.machineState.stack = a :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow)
    (hStackBound : ¬ 1024 < t.length + 1) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s =
      .ok (calldataloadNextState s a t, none) := by
  have hStep := step_calldataload s hDecode
  have hNoOverflow : ¬ (a :: t).length - 1 + 1 > 1024 := by
    simpa using hStackBound
  simpa [calldataloadNextState, hStack, hGas, hStackBound, hNoOverflow] using hStep

def dup1NextState (s : Ethereum.State) (a : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := a :: a :: t
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem dup1NextState_stack (s : Ethereum.State) (a : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (dup1NextState s a t).machineState.stack = a :: a :: t :=
  rfl

@[simp] theorem dup1NextState_gasAvailable (s : Ethereum.State) (a : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (dup1NextState s a t).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow :=
  rfl

@[simp] theorem dup1NextState_pc (s : Ethereum.State) (a : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (dup1NextState s a t).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_dup1_oog_of_decode {s : Ethereum.State}
    {a : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.DUP1, .none))
    (hStack : s.machineState.stack = a :: t)
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_dup1 s hDecode
  simpa [hStack, hGas] using hStep

theorem Xstep_dup1_continue_of_decode {s : Ethereum.State}
    {a : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.DUP1, .none))
    (hStack : s.machineState.stack = a :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow)
    (hStackBound : ¬ 1024 < t.length + 2) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (dup1NextState s a t, none) := by
  have hStep := step_dup1 s hDecode
  simpa [dup1NextState, hStack, hGas, hStackBound] using hStep

def dup2NextState (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := b :: a :: b :: t
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem dup2NextState_stack (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (dup2NextState s a b t).machineState.stack = b :: a :: b :: t :=
  rfl

@[simp] theorem dup2NextState_gasAvailable (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup2NextState s a b t).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow :=
  rfl

@[simp] theorem dup2NextState_pc (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (dup2NextState s a b t).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_dup2_oog_of_decode {s : Ethereum.State}
    {a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.DUP2, .none))
    (hStack : s.machineState.stack = a :: b :: t)
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_dup2 s hDecode
  simpa [hStack, hGas] using hStep

theorem Xstep_dup2_continue_of_decode {s : Ethereum.State}
    {a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.DUP2, .none))
    (hStack : s.machineState.stack = a :: b :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow)
    (hStackBound : ¬ 1024 < t.length + 3) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (dup2NextState s a b t, none) := by
  have hStep := step_dup2 s hDecode
  simpa [dup2NextState, hStack, hGas, hStackBound] using hStep

def dup3NextState (s : Ethereum.State) (a b c : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := c :: a :: b :: c :: t
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem dup3NextState_stack (s : Ethereum.State) (a b c : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (dup3NextState s a b c t).machineState.stack = c :: a :: b :: c :: t :=
  rfl

@[simp] theorem dup3NextState_gasAvailable (s : Ethereum.State)
    (a b c : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup3NextState s a b c t).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow :=
  rfl

@[simp] theorem dup3NextState_pc (s : Ethereum.State) (a b c : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (dup3NextState s a b c t).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_dup3_oog_of_decode {s : Ethereum.State}
    {a b c : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.DUP3, .none))
    (hStack : s.machineState.stack = a :: b :: c :: t)
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_dup3 s hDecode
  simpa [hStack, hGas] using hStep

theorem Xstep_dup3_continue_of_decode {s : Ethereum.State}
    {a b c : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.DUP3, .none))
    (hStack : s.machineState.stack = a :: b :: c :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow)
    (hStackBound : ¬ 1024 < t.length + 4) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (dup3NextState s a b c t, none) := by
  have hStep := step_dup3 s hDecode
  simpa [dup3NextState, hStack, hGas, hStackBound] using hStep

def dup4NextState (s : Ethereum.State) (a b c d : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := d :: a :: b :: c :: d :: t
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem dup4NextState_stack (s : Ethereum.State)
    (a b c d : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup4NextState s a b c d t).machineState.stack = d :: a :: b :: c :: d :: t :=
  rfl

@[simp] theorem dup4NextState_gasAvailable (s : Ethereum.State)
    (a b c d : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup4NextState s a b c d t).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow :=
  rfl

@[simp] theorem dup4NextState_pc (s : Ethereum.State) (a b c d : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (dup4NextState s a b c d t).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_dup4_oog_of_decode {s : Ethereum.State}
    {a b c d : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.DUP4, .none))
    (hStack : s.machineState.stack = a :: b :: c :: d :: t)
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_dup4 s hDecode
  simpa [hStack, hGas] using hStep

theorem Xstep_dup4_continue_of_decode {s : Ethereum.State}
    {a b c d : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.DUP4, .none))
    (hStack : s.machineState.stack = a :: b :: c :: d :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow)
    (hStackBound : ¬ 1024 < t.length + 5) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (dup4NextState s a b c d t, none) := by
  have hStep := step_dup4 s hDecode
  simpa [dup4NextState, hStack, hGas, hStackBound] using hStep

def dup5NextState (s : Ethereum.State) (a b c d e : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := e :: a :: b :: c :: d :: e :: t
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem dup5NextState_stack (s : Ethereum.State)
    (a b c d e : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup5NextState s a b c d e t).machineState.stack =
      e :: a :: b :: c :: d :: e :: t :=
  rfl

@[simp] theorem dup5NextState_gasAvailable (s : Ethereum.State)
    (a b c d e : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup5NextState s a b c d e t).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow :=
  rfl

@[simp] theorem dup5NextState_pc (s : Ethereum.State) (a b c d e : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (dup5NextState s a b c d e t).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_dup5_oog_of_decode {s : Ethereum.State}
    {a b c d e : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.DUP5, .none))
    (hStack : s.machineState.stack = a :: b :: c :: d :: e :: t)
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_dup5 s hDecode
  simpa [hStack, hGas] using hStep

theorem Xstep_dup5_continue_of_decode {s : Ethereum.State}
    {a b c d e : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.DUP5, .none))
    (hStack : s.machineState.stack = a :: b :: c :: d :: e :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow)
    (hStackBound : ¬ 1024 < t.length + 6) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s =
      .ok (dup5NextState s a b c d e t, none) := by
  have hStep := step_dup5 s hDecode
  simpa [dup5NextState, hStack, hGas, hStackBound] using hStep

def swap1NextState (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := b :: a :: t
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem swap1NextState_stack (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (swap1NextState s a b t).machineState.stack = b :: a :: t :=
  rfl

@[simp] theorem swap1NextState_gasAvailable (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (swap1NextState s a b t).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow :=
  rfl

@[simp] theorem swap1NextState_pc (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (swap1NextState s a b t).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_swap1_oog_of_decode {s : Ethereum.State}
    {a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.SWAP1, .none))
    (hStack : s.machineState.stack = a :: b :: t)
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_swap1 s hDecode
  simpa [hStack, hGas] using hStep

theorem Xstep_swap1_continue_of_decode {s : Ethereum.State}
    {a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.SWAP1, .none))
    (hStack : s.machineState.stack = a :: b :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow)
    (hStackBound : ¬ 1024 < t.length + 2) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (swap1NextState s a b t, none) := by
  have hStep := step_swap1 s hDecode
  simpa [swap1NextState, hStack, hGas, hStackBound] using hStep

def swap2NextState (s : Ethereum.State) (a b c : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := c :: b :: a :: t
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem swap2NextState_stack (s : Ethereum.State) (a b c : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (swap2NextState s a b c t).machineState.stack = c :: b :: a :: t :=
  rfl

@[simp] theorem swap2NextState_gasAvailable (s : Ethereum.State)
    (a b c : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (swap2NextState s a b c t).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow :=
  rfl

@[simp] theorem swap2NextState_pc (s : Ethereum.State) (a b c : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (swap2NextState s a b c t).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_swap2_oog_of_decode {s : Ethereum.State}
    {a b c : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.SWAP2, .none))
    (hStack : s.machineState.stack = a :: b :: c :: t)
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_swap2 s hDecode
  simpa [hStack, hGas] using hStep

theorem Xstep_swap2_continue_of_decode {s : Ethereum.State}
    {a b c : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.SWAP2, .none))
    (hStack : s.machineState.stack = a :: b :: c :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow)
    (hStackBound : ¬ 1024 < t.length + 3) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (swap2NextState s a b c t, none) := by
  have hStep := step_swap2 s hDecode
  simpa [swap2NextState, hStack, hGas, hStackBound] using hStep

def swap3NextState (s : Ethereum.State) (a b c d : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := d :: b :: c :: a :: t
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem swap3NextState_stack (s : Ethereum.State)
    (a b c d : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (swap3NextState s a b c d t).machineState.stack = d :: b :: c :: a :: t :=
  rfl

@[simp] theorem swap3NextState_gasAvailable (s : Ethereum.State)
    (a b c d : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (swap3NextState s a b c d t).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow :=
  rfl

@[simp] theorem swap3NextState_pc (s : Ethereum.State) (a b c d : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (swap3NextState s a b c d t).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_swap3_oog_of_decode {s : Ethereum.State}
    {a b c d : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.SWAP3, .none))
    (hStack : s.machineState.stack = a :: b :: c :: d :: t)
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_swap3 s hDecode
  simpa [hStack, hGas] using hStep

theorem Xstep_swap3_continue_of_decode {s : Ethereum.State}
    {a b c d : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.SWAP3, .none))
    (hStack : s.machineState.stack = a :: b :: c :: d :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow)
    (hStackBound : ¬ 1024 < t.length + 4) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (swap3NextState s a b c d t, none) := by
  have hStep := step_swap3 s hDecode
  simpa [swap3NextState, hStack, hGas, hStackBound] using hStep

def iszeroNextState (s : Ethereum.State) (a : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := Ethereum.UInt256.isZero a :: t
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem iszeroNextState_stack (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (iszeroNextState s a t).machineState.stack = Ethereum.UInt256.isZero a :: t :=
  rfl

@[simp] theorem iszeroNextState_gasAvailable (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (iszeroNextState s a t).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow :=
  rfl

@[simp] theorem iszeroNextState_pc (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (iszeroNextState s a t).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_iszero_oog_of_decode {s : Ethereum.State}
    {a : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.ISZERO, .none))
    (hStack : s.machineState.stack = a :: t)
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_iszero s hDecode
  simpa [hStack, hGas] using hStep

theorem Xstep_iszero_continue_of_decode {s : Ethereum.State}
    {a : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.ISZERO, .none))
    (hStack : s.machineState.stack = a :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow)
    (hStackBound : ¬ 1024 < t.length + 1) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (iszeroNextState s a t, none) := by
  have hStep := step_iszero s hDecode
  simpa [iszeroNextState, hStack, hGas, hStackBound] using hStep

def addNextState (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := (a + b) :: t
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem addNextState_stack (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (addNextState s a b t).machineState.stack = (a + b) :: t :=
  rfl

@[simp] theorem addNextState_gasAvailable (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (addNextState s a b t).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow :=
  rfl

@[simp] theorem addNextState_pc (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (addNextState s a b t).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_add_oog_of_decode {s : Ethereum.State}
    {a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.ADD, .none))
    (hStack : s.machineState.stack = a :: b :: t)
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_add s hDecode
  simpa [hStack, hGas] using hStep

theorem Xstep_add_continue_of_decode {s : Ethereum.State}
    {a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.ADD, .none))
    (hStack : s.machineState.stack = a :: b :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow)
    (hStackBound : ¬ 1024 < t.length + 1) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (addNextState s a b t, none) := by
  have hStep := step_add s hDecode
  simpa [addNextState, hStack, hGas, hStackBound] using hStep

def subNextState (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := Ethereum.UInt256.sub a b :: t
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem subNextState_stack (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (subNextState s a b t).machineState.stack = Ethereum.UInt256.sub a b :: t :=
  rfl

@[simp] theorem subNextState_gasAvailable (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (subNextState s a b t).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow :=
  rfl

@[simp] theorem subNextState_pc (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (subNextState s a b t).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_sub_oog_of_decode {s : Ethereum.State}
    {a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.SUB, .none))
    (hStack : s.machineState.stack = a :: b :: t)
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_sub s hDecode
  simpa [hStack, hGas] using hStep

theorem Xstep_sub_continue_of_decode {s : Ethereum.State}
    {a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.SUB, .none))
    (hStack : s.machineState.stack = a :: b :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow)
    (hStackBound : ¬ 1024 < t.length + 1) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (subNextState s a b t, none) := by
  have hStep := step_sub s hDecode
  simpa [subNextState, hStack, hGas, hStackBound] using hStep

def ltNextState (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := Ethereum.UInt256.lt a b :: t
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem ltNextState_stack (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (ltNextState s a b t).machineState.stack = Ethereum.UInt256.lt a b :: t :=
  rfl

@[simp] theorem ltNextState_gasAvailable (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (ltNextState s a b t).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow :=
  rfl

@[simp] theorem ltNextState_pc (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (ltNextState s a b t).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_lt_oog_of_decode {s : Ethereum.State}
    {a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.LT, .none))
    (hStack : s.machineState.stack = a :: b :: t)
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_lt s hDecode
  simpa [hStack, hGas] using hStep

theorem Xstep_lt_continue_of_decode {s : Ethereum.State}
    {a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.LT, .none))
    (hStack : s.machineState.stack = a :: b :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow)
    (hStackBound : ¬ 1024 < t.length + 1) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (ltNextState s a b t, none) := by
  have hStep := step_lt s hDecode
  simpa [ltNextState, hStack, hGas, hStackBound] using hStep

def shrNextState (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := Ethereum.UInt256.shiftRight b a :: t
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem shrNextState_stack (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (shrNextState s a b t).machineState.stack = Ethereum.UInt256.shiftRight b a :: t :=
  rfl

@[simp] theorem shrNextState_gasAvailable (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (shrNextState s a b t).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow :=
  rfl

@[simp] theorem shrNextState_pc (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (shrNextState s a b t).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_shr_oog_of_decode {s : Ethereum.State}
    {a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.SHR, .none))
    (hStack : s.machineState.stack = a :: b :: t)
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_shr s hDecode
  simpa [hStack, hGas] using hStep

theorem Xstep_shr_continue_of_decode {s : Ethereum.State}
    {a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.SHR, .none))
    (hStack : s.machineState.stack = a :: b :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow)
    (hStackBound : ¬ 1024 < t.length + 1) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (shrNextState s a b t, none) := by
  have hStep := step_shr s hDecode
  simpa [shrNextState, hStack, hGas, hStackBound] using hStep

def eqNextState (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := Ethereum.UInt256.eq a b :: t
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem eqNextState_stack (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (eqNextState s a b t).machineState.stack = Ethereum.UInt256.eq a b :: t :=
  rfl

@[simp] theorem eqNextState_gasAvailable (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (eqNextState s a b t).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow :=
  rfl

@[simp] theorem eqNextState_pc (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (eqNextState s a b t).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_eq_oog_of_decode {s : Ethereum.State}
    {a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.EQ, .none))
    (hStack : s.machineState.stack = a :: b :: t)
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_eq s hDecode
  simpa [hStack, hGas] using hStep

theorem Xstep_eq_continue_of_decode {s : Ethereum.State}
    {a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.EQ, .none))
    (hStack : s.machineState.stack = a :: b :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow)
    (hStackBound : ¬ 1024 < t.length + 1) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (eqNextState s a b t, none) := by
  have hStep := step_eq s hDecode
  simpa [eqNextState, hStack, hGas, hStackBound] using hStep

def push0NextState (s : Ethereum.State) : Ethereum.State :=
  {s with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: s.machineState.stack
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem push0NextState_stack (s : Ethereum.State) :
    (push0NextState s).machineState.stack =
      (⟨0⟩ : Ethereum.UInt256) :: s.machineState.stack :=
  rfl

@[simp] theorem push0NextState_gasAvailable (s : Ethereum.State) :
    (push0NextState s).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gbase :=
  rfl

@[simp] theorem push0NextState_pc (s : Ethereum.State) :
    (push0NextState s).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_push0_oog_of_decode {s : Ethereum.State}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.PUSH0, .none))
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gbase) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_push0 s hDecode
  simpa [hGas] using hStep

theorem Xstep_push0_continue_of_decode {s : Ethereum.State}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.PUSH0, .none))
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase)
    (hStack : s.machineState.stack.length < 1024) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (push0NextState s, none) := by
  have hStep := step_push0 s hDecode
  have hNoOverflow : ¬ s.machineState.stack.length - 0 + 1 > 1024 := by
    omega
  have hNoOverflow' : ¬ 1024 < s.machineState.stack.length + 1 := by
    omega
  simpa [push0NextState, hGas, hNoOverflow, hNoOverflow'] using hStep

def jumpNextState (s : Ethereum.State) (dest : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := t
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gmid
    machineState.pc := dest
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem jumpNextState_stack (s : Ethereum.State) (dest : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (jumpNextState s dest t).machineState.stack = t :=
  rfl

@[simp] theorem jumpNextState_gasAvailable (s : Ethereum.State)
    (dest : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (jumpNextState s dest t).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gmid :=
  rfl

@[simp] theorem jumpNextState_pc (s : Ethereum.State) (dest : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (jumpNextState s dest t).machineState.pc = dest :=
  rfl

theorem Xstep_jump_oog_of_decode {s : Ethereum.State}
    {dest : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.JUMP, .none))
    (hStack : s.machineState.stack = dest :: t)
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gmid) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_jump s hDecode
  simpa [hStack, hGas] using hStep

theorem Xstep_jump_bad_dest_of_decode {s : Ethereum.State}
    {dest : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.JUMP, .none))
    (hStack : s.machineState.stack = dest :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gmid)
    (hDest : ¬ (D_J s.executionEnv.code ⟨0⟩).contains dest = true) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .BadJumpDestination := by
  have hStep := step_jump s hDecode
  have hContainsFalse : (D_J s.executionEnv.code ⟨0⟩).contains dest = false := by
    cases hContains : (D_J s.executionEnv.code ⟨0⟩).contains dest <;> simp [hContains] at hDest ⊢
  simpa [hStack, hGas, hContainsFalse] using hStep

theorem Xstep_jump_continue_of_decode {s : Ethereum.State}
    {dest : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.JUMP, .none))
    (hStack : s.machineState.stack = dest :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gmid)
    (hDest : (D_J s.executionEnv.code ⟨0⟩).contains dest = true)
    (hStackBound : ¬ 1024 < t.length) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s =
      .ok (jumpNextState s dest t, none) := by
  have hStep := step_jump s hDecode
  have hNoOverflow : ¬ (dest :: t).length - 1 + 0 > 1024 := by
    simpa using hStackBound
  simpa [jumpNextState, hStack, hGas, hDest, hStackBound, hNoOverflow] using hStep

def jumpiNextState (s : Ethereum.State) (dest cond : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := t
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Ghigh
    machineState.pc := if cond != (⟨0⟩ : Ethereum.UInt256) then dest else s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem jumpiNextState_stack (s : Ethereum.State) (dest cond : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (jumpiNextState s dest cond t).machineState.stack = t :=
  rfl

@[simp] theorem jumpiNextState_gasAvailable (s : Ethereum.State)
    (dest cond : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (jumpiNextState s dest cond t).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Ghigh :=
  rfl

theorem jumpiNextState_pc_of_cond_bne_true {s : Ethereum.State}
    {dest cond : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hCond : (cond != (⟨0⟩ : Ethereum.UInt256)) = true) :
    (jumpiNextState s dest cond t).machineState.pc = dest := by
  simp [jumpiNextState, hCond]

theorem jumpiNextState_pc_of_cond_bne_false {s : Ethereum.State}
    {dest cond : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hCond : (cond != (⟨0⟩ : Ethereum.UInt256)) = false) :
    (jumpiNextState s dest cond t).machineState.pc = s.machineState.pc + ⟨1⟩ := by
  simp [jumpiNextState, hCond]

theorem jumpiNextState_pc_of_isZero_eq_zero {s : Ethereum.State}
    {dest x : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hx : x = (⟨0⟩ : Ethereum.UInt256)) :
    (jumpiNextState s dest (Ethereum.UInt256.isZero x) t).machineState.pc = dest :=
  jumpiNextState_pc_of_cond_bne_true
    (Ethereum.UInt256.isZero_bne_zero_eq_true_of_eq_zero hx)

theorem jumpiNextState_pc_of_isZero_ne_zero {s : Ethereum.State}
    {dest x : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hx : x ≠ (⟨0⟩ : Ethereum.UInt256)) :
    (jumpiNextState s dest (Ethereum.UInt256.isZero x) t).machineState.pc =
      s.machineState.pc + ⟨1⟩ :=
  jumpiNextState_pc_of_cond_bne_false
    (Ethereum.UInt256.isZero_bne_zero_eq_false_of_ne_zero hx)

theorem jumpiNextState_pc_of_lt {s : Ethereum.State}
    {dest a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (h : a < b) :
    (jumpiNextState s dest (Ethereum.UInt256.lt a b) t).machineState.pc = dest :=
  jumpiNextState_pc_of_cond_bne_true
    (Ethereum.UInt256.lt_bne_zero_eq_true_of_lt h)

theorem jumpiNextState_pc_of_not_lt {s : Ethereum.State}
    {dest a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (h : ¬ a < b) :
    (jumpiNextState s dest (Ethereum.UInt256.lt a b) t).machineState.pc =
      s.machineState.pc + ⟨1⟩ :=
  jumpiNextState_pc_of_cond_bne_false
    (Ethereum.UInt256.lt_bne_zero_eq_false_of_not_lt h)

theorem jumpiNextState_pc_of_eq {s : Ethereum.State}
    {dest a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (h : a = b) :
    (jumpiNextState s dest (Ethereum.UInt256.eq a b) t).machineState.pc = dest :=
  jumpiNextState_pc_of_cond_bne_true
    (Ethereum.UInt256.eq_bne_zero_eq_true_of_eq h)

theorem jumpiNextState_pc_of_ne {s : Ethereum.State}
    {dest a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (h : a ≠ b) :
    (jumpiNextState s dest (Ethereum.UInt256.eq a b) t).machineState.pc =
      s.machineState.pc + ⟨1⟩ :=
  jumpiNextState_pc_of_cond_bne_false
    (Ethereum.UInt256.eq_bne_zero_eq_false_of_ne h)

theorem Xstep_jumpi_oog_of_decode {s : Ethereum.State}
    {dest cond : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.JUMPI, .none))
    (hStack : s.machineState.stack = dest :: cond :: t)
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Ghigh) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_jumpi s hDecode
  simpa [hStack, hGas] using hStep

theorem Xstep_jumpi_bad_dest_of_decode {s : Ethereum.State}
    {dest cond : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.JUMPI, .none))
    (hStack : s.machineState.stack = dest :: cond :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Ghigh)
    (hCond : (cond != (⟨0⟩ : Ethereum.UInt256)) = true)
    (hDest : ¬ (D_J s.executionEnv.code ⟨0⟩).contains dest = true) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .BadJumpDestination := by
  have hStep := step_jumpi s hDecode
  have hBad :
      (cond != (⟨0⟩ : Ethereum.UInt256)) = true ∧
        ¬ (D_J s.executionEnv.code ⟨0⟩).contains dest = true :=
    ⟨hCond, hDest⟩
  simpa [hStack, hGas, hBad] using hStep

theorem Xstep_jumpi_continue_of_decode {s : Ethereum.State}
    {dest cond : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.JUMPI, .none))
    (hStack : s.machineState.stack = dest :: cond :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Ghigh)
    (hNoBad :
      (cond != (⟨0⟩ : Ethereum.UInt256)) = true →
        (D_J s.executionEnv.code ⟨0⟩).contains dest = true)
    (hStackBound : ¬ 1024 < t.length) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s =
      .ok (jumpiNextState s dest cond t, none) := by
  have hStep := step_jumpi s hDecode
  have hBadFalse :
      ¬ ((cond != (⟨0⟩ : Ethereum.UInt256)) = true ∧
        (D_J s.executionEnv.code ⟨0⟩).contains dest = false) := by
    intro hBad
    have hContains := hNoBad hBad.1
    rw [hContains] at hBad
    simp at hBad
  have hNoOverflow : ¬ (dest :: cond :: t).length - 2 + 0 > 1024 := by
    simpa using hStackBound
  simpa [jumpiNextState, hStack, hGas, hBadFalse, hStackBound, hNoOverflow] using hStep

theorem Xstep_jumpi_taken_continue_of_decode {s : Ethereum.State}
    {dest cond : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.JUMPI, .none))
    (hStack : s.machineState.stack = dest :: cond :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Ghigh)
    (_hCond : (cond != (⟨0⟩ : Ethereum.UInt256)) = true)
    (hDest : (D_J s.executionEnv.code ⟨0⟩).contains dest = true)
    (hStackBound : ¬ 1024 < t.length) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s =
      .ok (jumpiNextState s dest cond t, none) := by
  exact Xstep_jumpi_continue_of_decode hDecode hStack hGas
    (by
      intro _hCond
      exact hDest)
    hStackBound

theorem Xstep_jumpi_fallthrough_continue_of_decode {s : Ethereum.State}
    {dest cond : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.JUMPI, .none))
    (hStack : s.machineState.stack = dest :: cond :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Ghigh)
    (hCond : (cond != (⟨0⟩ : Ethereum.UInt256)) = false)
    (hStackBound : ¬ 1024 < t.length) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s =
      .ok (jumpiNextState s dest cond t, none) := by
  exact Xstep_jumpi_continue_of_decode hDecode hStack hGas
    (by
      intro hCondTrue
      rw [hCond] at hCondTrue
      contradiction)
    hStackBound

def jumpdestNextState (s : Ethereum.State) : Ethereum.State :=
  {s with
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gjumpdest
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem jumpdestNextState_stack (s : Ethereum.State) :
    (jumpdestNextState s).machineState.stack = s.machineState.stack :=
  rfl

@[simp] theorem jumpdestNextState_gasAvailable (s : Ethereum.State) :
    (jumpdestNextState s).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gjumpdest :=
  rfl

@[simp] theorem jumpdestNextState_pc (s : Ethereum.State) :
    (jumpdestNextState s).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_jumpdest_oog_of_decode {s : Ethereum.State}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.JUMPDEST, .none))
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gjumpdest) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_jumpdest s hDecode
  simpa [hGas] using hStep

theorem Xstep_jumpdest_continue_of_decode {s : Ethereum.State}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.JUMPDEST, .none))
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gjumpdest)
    (hStackBound : ¬ 1024 < s.machineState.stack.length) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (jumpdestNextState s, none) := by
  have hStep := step_jumpdest s hDecode
  have hNoOverflow : ¬ s.machineState.stack.length - 0 + 0 > 1024 := by
    simpa using hStackBound
  simpa [jumpdestNextState, hGas, hStackBound, hNoOverflow] using hStep

def popNextState (s : Ethereum.State) (_a : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := t
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem popNextState_stack (s : Ethereum.State) (a : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (popNextState s a t).machineState.stack = t :=
  rfl

@[simp] theorem popNextState_gasAvailable (s : Ethereum.State) (a : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (popNextState s a t).machineState.gasAvailable =
      s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gbase :=
  rfl

@[simp] theorem popNextState_pc (s : Ethereum.State) (a : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) :
    (popNextState s a t).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_pop_oog_of_decode {s : Ethereum.State}
    {a : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.POP, .none))
    (hStack : s.machineState.stack = a :: t)
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gbase) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_pop s hDecode
  simpa [hStack, hGas] using hStep

theorem Xstep_pop_continue_of_decode {s : Ethereum.State}
    {a : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.POP, .none))
    (hStack : s.machineState.stack = a :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase)
    (hStackBound : ¬ 1024 < t.length) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (popNextState s a t, none) := by
  have hStep := step_pop s hDecode
  have hNoOverflow : ¬ (a :: t).length - 1 + 0 > 1024 := by
    simpa using hStackBound
  simpa [popNextState, hStack, hGas, hStackBound, hNoOverflow] using hStep

def revertOutput (s : Ethereum.State) (offset size : Ethereum.UInt256) : ByteArray :=
  s.machineState.memory.readWithPadding offset.toNat size.toNat

def revertNextState (s : Ethereum.State) (offset size : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := t
    machineState.H_return := revertOutput s offset size
    machineState.activeWords :=
      let m := MachineState.M s.machineState.activeWords.toNat offset.toNat size.toNat
      Ethereum.UInt256.ofNat (MachineState.M (Ethereum.UInt256.ofNat m).toNat offset.toNat size.toNat)
    machineState.gasAvailable :=
      (s.machineState.gasAvailable - Ethereum.UInt256.ofNat (memoryExpansionCost s .REVERT)) -
        Ethereum.UInt256.ofNat GasConstants.Gzero
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem revertNextState_stack (s : Ethereum.State)
    (offset size : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (revertNextState s offset size t).machineState.stack = t :=
  rfl

@[simp] theorem revertNextState_H_return (s : Ethereum.State)
    (offset size : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (revertNextState s offset size t).machineState.H_return =
      revertOutput s offset size :=
  rfl

@[simp] theorem revertNextState_createdAccounts (s : Ethereum.State)
    (offset size : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (revertNextState s offset size t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem revertNextState_accountMap (s : Ethereum.State)
    (offset size : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (revertNextState s offset size t).accountMap = s.accountMap :=
  rfl

@[simp] theorem revertNextState_substate (s : Ethereum.State)
    (offset size : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (revertNextState s offset size t).substate = s.substate :=
  rfl

@[simp] theorem revertNextState_gasAvailable (s : Ethereum.State)
    (offset size : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (revertNextState s offset size t).machineState.gasAvailable =
      (s.machineState.gasAvailable - Ethereum.UInt256.ofNat (memoryExpansionCost s .REVERT)) -
        Ethereum.UInt256.ofNat GasConstants.Gzero :=
  rfl

@[simp] theorem revertNextState_pc (s : Ethereum.State)
    (offset size : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (revertNextState s offset size t).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_revert_memory_oog_of_decode {s : Ethereum.State}
    {offset size : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.REVERT, .none))
    (hStack : s.machineState.stack = offset :: size :: t)
    (hMemGas : s.machineState.gasAvailable.toNat < memoryExpansionCost s .REVERT) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_revert s hDecode
  simpa [hStack, hMemGas] using hStep

theorem Xstep_revert_continue_of_decode {s : Ethereum.State}
    {offset size : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.REVERT, .none))
    (hStack : s.machineState.stack = offset :: size :: t)
    (hMemGas : ¬ s.machineState.gasAvailable.toNat < memoryExpansionCost s .REVERT)
    (hStackBound : ¬ 1024 < t.length) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s =
      .ok (revertNextState s offset size t, some (false, revertOutput s offset size)) := by
  have hStep := step_revert s hDecode
  have hNoOverflow : ¬ (offset :: size :: t).length - 2 + 0 > 1024 := by
    simpa using hStackBound
  simpa [revertNextState, revertOutput, hStack, hMemGas, hStackBound, hNoOverflow] using hStep

theorem memoryExpansionCost_revert_zero_stack {s : Ethereum.State}
    {t : Ethereum.Stack Ethereum.UInt256}
    (hStack :
      s.machineState.stack =
        (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) :: t) :
    memoryExpansionCost s .REVERT = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, hStack,
    Ethereum.MachineState.M, Ethereum.UInt256.ofNat, Ethereum.UInt256.toNat, Id.run]

theorem Xstep_revert_zero_continue_of_decode {s : Ethereum.State}
    {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.REVERT, .none))
    (hStack :
      s.machineState.stack =
        (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) :: t)
    (hStackBound : ¬ 1024 < t.length) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s =
      .ok (revertNextState s (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256) t,
        some (false, revertOutput s (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256))) := by
  exact Xstep_revert_continue_of_decode
    hDecode
    hStack
    (by
      rw [memoryExpansionCost_revert_zero_stack hStack]
      simp)
    hStackBound

def returnOutput (s : Ethereum.State) (offset size : Ethereum.UInt256) : ByteArray :=
  s.machineState.memory.readWithPadding offset.toNat size.toNat

def returnNextState (s : Ethereum.State) (offset size : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := t
    machineState.H_return := returnOutput s offset size
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (MachineState.M s.machineState.activeWords.toNat offset.toNat size.toNat)
    machineState.gasAvailable :=
      (s.machineState.gasAvailable - Ethereum.UInt256.ofNat (memoryExpansionCost s .RETURN)) -
        Ethereum.UInt256.ofNat GasConstants.Gzero
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

@[simp] theorem returnNextState_stack (s : Ethereum.State)
    (offset size : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (returnNextState s offset size t).machineState.stack = t :=
  rfl

@[simp] theorem returnNextState_H_return (s : Ethereum.State)
    (offset size : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (returnNextState s offset size t).machineState.H_return =
      returnOutput s offset size :=
  rfl

@[simp] theorem returnNextState_createdAccounts (s : Ethereum.State)
    (offset size : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (returnNextState s offset size t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem returnNextState_accountMap (s : Ethereum.State)
    (offset size : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (returnNextState s offset size t).accountMap = s.accountMap :=
  rfl

@[simp] theorem returnNextState_substate (s : Ethereum.State)
    (offset size : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (returnNextState s offset size t).substate = s.substate :=
  rfl

@[simp] theorem returnNextState_gasAvailable (s : Ethereum.State)
    (offset size : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (returnNextState s offset size t).machineState.gasAvailable =
      (s.machineState.gasAvailable - Ethereum.UInt256.ofNat (memoryExpansionCost s .RETURN)) -
        Ethereum.UInt256.ofNat GasConstants.Gzero :=
  rfl

@[simp] theorem returnNextState_pc (s : Ethereum.State)
    (offset size : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (returnNextState s offset size t).machineState.pc = s.machineState.pc + ⟨1⟩ :=
  rfl

theorem Xstep_return_memory_oog_of_decode {s : Ethereum.State}
    {offset size : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.RETURN, .none))
    (hStack : s.machineState.stack = offset :: size :: t)
    (hMemGas : s.machineState.gasAvailable.toNat < memoryExpansionCost s .RETURN) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_return s hDecode
  simpa [hStack, hMemGas] using hStep

theorem Xstep_return_continue_of_decode {s : Ethereum.State}
    {offset size : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.RETURN, .none))
    (hStack : s.machineState.stack = offset :: size :: t)
    (hMemGas : ¬ s.machineState.gasAvailable.toNat < memoryExpansionCost s .RETURN)
    (hStackBound : ¬ 1024 < t.length) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s =
      .ok (returnNextState s offset size t, some (true, returnOutput s offset size)) := by
  have hStep := step_return s hDecode
  have hNoOverflow : ¬ (offset :: size :: t).length - 2 + 0 > 1024 := by
    simpa using hStackBound
  simpa [returnNextState, returnOutput, hStack, hMemGas, hStackBound, hNoOverflow] using hStep

/-! Execution-environment projections for opcode next-state helpers. -/

@[simp] theorem push1NextState_executionEnv (s : Ethereum.State) (arg : Ethereum.UInt256) :
    (push1NextState s arg).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem push4NextState_executionEnv (s : Ethereum.State) (arg : Ethereum.UInt256) :
    (push4NextState s arg).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem mloadNextState_executionEnv (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (mloadNextState s a t).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem mstoreNextState_executionEnv (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (mstoreNextState s a b t).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem callvalueNextState_executionEnv (s : Ethereum.State) :
    (callvalueNextState s).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem calldatasizeNextState_executionEnv (s : Ethereum.State) :
    (calldatasizeNextState s).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem calldataloadNextState_executionEnv (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (calldataloadNextState s a t).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem dup1NextState_executionEnv (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup1NextState s a t).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem dup2NextState_executionEnv (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup2NextState s a b t).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem dup3NextState_executionEnv (s : Ethereum.State)
    (a b c : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup3NextState s a b c t).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem dup4NextState_executionEnv (s : Ethereum.State)
    (a b c d : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup4NextState s a b c d t).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem dup5NextState_executionEnv (s : Ethereum.State)
    (a b c d e : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup5NextState s a b c d e t).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem swap1NextState_executionEnv (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (swap1NextState s a b t).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem swap2NextState_executionEnv (s : Ethereum.State)
    (a b c : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (swap2NextState s a b c t).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem swap3NextState_executionEnv (s : Ethereum.State)
    (a b c d : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (swap3NextState s a b c d t).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem iszeroNextState_executionEnv (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (iszeroNextState s a t).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem addNextState_executionEnv (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (addNextState s a b t).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem subNextState_executionEnv (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (subNextState s a b t).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem ltNextState_executionEnv (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (ltNextState s a b t).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem shrNextState_executionEnv (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (shrNextState s a b t).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem eqNextState_executionEnv (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (eqNextState s a b t).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem push0NextState_executionEnv (s : Ethereum.State) :
    (push0NextState s).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem jumpNextState_executionEnv (s : Ethereum.State)
    (dest : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (jumpNextState s dest t).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem jumpiNextState_executionEnv (s : Ethereum.State)
    (dest cond : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (jumpiNextState s dest cond t).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem jumpdestNextState_executionEnv (s : Ethereum.State) :
    (jumpdestNextState s).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem popNextState_executionEnv (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (popNextState s a t).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem revertNextState_executionEnv (s : Ethereum.State)
    (offset size : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (revertNextState s offset size t).executionEnv = s.executionEnv :=
  rfl

@[simp] theorem returnNextState_executionEnv (s : Ethereum.State)
    (offset size : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (returnNextState s offset size t).executionEnv = s.executionEnv :=
  rfl

/-! World-state projections for opcode next-state helpers. -/

@[simp] theorem push1NextState_createdAccounts (s : Ethereum.State) (arg : Ethereum.UInt256) :
    (push1NextState s arg).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem push1NextState_accountMap (s : Ethereum.State) (arg : Ethereum.UInt256) :
    (push1NextState s arg).accountMap = s.accountMap :=
  rfl

@[simp] theorem push1NextState_substate (s : Ethereum.State) (arg : Ethereum.UInt256) :
    (push1NextState s arg).substate = s.substate :=
  rfl

@[simp] theorem push4NextState_createdAccounts (s : Ethereum.State) (arg : Ethereum.UInt256) :
    (push4NextState s arg).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem push4NextState_accountMap (s : Ethereum.State) (arg : Ethereum.UInt256) :
    (push4NextState s arg).accountMap = s.accountMap :=
  rfl

@[simp] theorem push4NextState_substate (s : Ethereum.State) (arg : Ethereum.UInt256) :
    (push4NextState s arg).substate = s.substate :=
  rfl

@[simp] theorem mloadNextState_createdAccounts (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (mloadNextState s a t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem mloadNextState_accountMap (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (mloadNextState s a t).accountMap = s.accountMap :=
  rfl

@[simp] theorem mloadNextState_substate (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (mloadNextState s a t).substate = s.substate :=
  rfl

@[simp] theorem mstoreNextState_createdAccounts (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (mstoreNextState s a b t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem mstoreNextState_accountMap (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (mstoreNextState s a b t).accountMap = s.accountMap :=
  rfl

@[simp] theorem mstoreNextState_substate (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (mstoreNextState s a b t).substate = s.substate :=
  rfl

@[simp] theorem callvalueNextState_createdAccounts (s : Ethereum.State) :
    (callvalueNextState s).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem callvalueNextState_accountMap (s : Ethereum.State) :
    (callvalueNextState s).accountMap = s.accountMap :=
  rfl

@[simp] theorem callvalueNextState_substate (s : Ethereum.State) :
    (callvalueNextState s).substate = s.substate :=
  rfl

@[simp] theorem calldatasizeNextState_createdAccounts (s : Ethereum.State) :
    (calldatasizeNextState s).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem calldatasizeNextState_accountMap (s : Ethereum.State) :
    (calldatasizeNextState s).accountMap = s.accountMap :=
  rfl

@[simp] theorem calldatasizeNextState_substate (s : Ethereum.State) :
    (calldatasizeNextState s).substate = s.substate :=
  rfl

@[simp] theorem calldataloadNextState_createdAccounts (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (calldataloadNextState s a t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem calldataloadNextState_accountMap (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (calldataloadNextState s a t).accountMap = s.accountMap :=
  rfl

@[simp] theorem calldataloadNextState_substate (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (calldataloadNextState s a t).substate = s.substate :=
  rfl

@[simp] theorem dup1NextState_createdAccounts (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup1NextState s a t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem dup1NextState_accountMap (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup1NextState s a t).accountMap = s.accountMap :=
  rfl

@[simp] theorem dup1NextState_substate (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup1NextState s a t).substate = s.substate :=
  rfl

@[simp] theorem dup2NextState_createdAccounts (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup2NextState s a b t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem dup2NextState_accountMap (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup2NextState s a b t).accountMap = s.accountMap :=
  rfl

@[simp] theorem dup2NextState_substate (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup2NextState s a b t).substate = s.substate :=
  rfl

@[simp] theorem dup3NextState_createdAccounts (s : Ethereum.State)
    (a b c : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup3NextState s a b c t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem dup3NextState_accountMap (s : Ethereum.State)
    (a b c : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup3NextState s a b c t).accountMap = s.accountMap :=
  rfl

@[simp] theorem dup3NextState_substate (s : Ethereum.State)
    (a b c : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup3NextState s a b c t).substate = s.substate :=
  rfl

@[simp] theorem dup4NextState_createdAccounts (s : Ethereum.State)
    (a b c d : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup4NextState s a b c d t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem dup4NextState_accountMap (s : Ethereum.State)
    (a b c d : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup4NextState s a b c d t).accountMap = s.accountMap :=
  rfl

@[simp] theorem dup4NextState_substate (s : Ethereum.State)
    (a b c d : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup4NextState s a b c d t).substate = s.substate :=
  rfl

@[simp] theorem dup5NextState_createdAccounts (s : Ethereum.State)
    (a b c d e : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup5NextState s a b c d e t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem dup5NextState_accountMap (s : Ethereum.State)
    (a b c d e : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup5NextState s a b c d e t).accountMap = s.accountMap :=
  rfl

@[simp] theorem dup5NextState_substate (s : Ethereum.State)
    (a b c d e : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (dup5NextState s a b c d e t).substate = s.substate :=
  rfl

@[simp] theorem swap1NextState_createdAccounts (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (swap1NextState s a b t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem swap1NextState_accountMap (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (swap1NextState s a b t).accountMap = s.accountMap :=
  rfl

@[simp] theorem swap1NextState_substate (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (swap1NextState s a b t).substate = s.substate :=
  rfl

@[simp] theorem swap2NextState_createdAccounts (s : Ethereum.State)
    (a b c : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (swap2NextState s a b c t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem swap2NextState_accountMap (s : Ethereum.State)
    (a b c : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (swap2NextState s a b c t).accountMap = s.accountMap :=
  rfl

@[simp] theorem swap2NextState_substate (s : Ethereum.State)
    (a b c : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (swap2NextState s a b c t).substate = s.substate :=
  rfl

@[simp] theorem swap3NextState_createdAccounts (s : Ethereum.State)
    (a b c d : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (swap3NextState s a b c d t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem swap3NextState_accountMap (s : Ethereum.State)
    (a b c d : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (swap3NextState s a b c d t).accountMap = s.accountMap :=
  rfl

@[simp] theorem swap3NextState_substate (s : Ethereum.State)
    (a b c d : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (swap3NextState s a b c d t).substate = s.substate :=
  rfl

@[simp] theorem iszeroNextState_createdAccounts (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (iszeroNextState s a t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem iszeroNextState_accountMap (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (iszeroNextState s a t).accountMap = s.accountMap :=
  rfl

@[simp] theorem iszeroNextState_substate (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (iszeroNextState s a t).substate = s.substate :=
  rfl

@[simp] theorem addNextState_createdAccounts (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (addNextState s a b t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem addNextState_accountMap (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (addNextState s a b t).accountMap = s.accountMap :=
  rfl

@[simp] theorem addNextState_substate (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (addNextState s a b t).substate = s.substate :=
  rfl

@[simp] theorem subNextState_createdAccounts (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (subNextState s a b t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem subNextState_accountMap (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (subNextState s a b t).accountMap = s.accountMap :=
  rfl

@[simp] theorem subNextState_substate (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (subNextState s a b t).substate = s.substate :=
  rfl

@[simp] theorem ltNextState_createdAccounts (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (ltNextState s a b t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem ltNextState_accountMap (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (ltNextState s a b t).accountMap = s.accountMap :=
  rfl

@[simp] theorem ltNextState_substate (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (ltNextState s a b t).substate = s.substate :=
  rfl

@[simp] theorem shrNextState_createdAccounts (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (shrNextState s a b t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem shrNextState_accountMap (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (shrNextState s a b t).accountMap = s.accountMap :=
  rfl

@[simp] theorem shrNextState_substate (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (shrNextState s a b t).substate = s.substate :=
  rfl

@[simp] theorem eqNextState_createdAccounts (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (eqNextState s a b t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem eqNextState_accountMap (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (eqNextState s a b t).accountMap = s.accountMap :=
  rfl

@[simp] theorem eqNextState_substate (s : Ethereum.State)
    (a b : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (eqNextState s a b t).substate = s.substate :=
  rfl

@[simp] theorem push0NextState_createdAccounts (s : Ethereum.State) :
    (push0NextState s).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem push0NextState_accountMap (s : Ethereum.State) :
    (push0NextState s).accountMap = s.accountMap :=
  rfl

@[simp] theorem push0NextState_substate (s : Ethereum.State) :
    (push0NextState s).substate = s.substate :=
  rfl

@[simp] theorem jumpNextState_createdAccounts (s : Ethereum.State)
    (dest : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (jumpNextState s dest t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem jumpNextState_accountMap (s : Ethereum.State)
    (dest : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (jumpNextState s dest t).accountMap = s.accountMap :=
  rfl

@[simp] theorem jumpNextState_substate (s : Ethereum.State)
    (dest : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (jumpNextState s dest t).substate = s.substate :=
  rfl

@[simp] theorem jumpiNextState_createdAccounts (s : Ethereum.State)
    (dest cond : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (jumpiNextState s dest cond t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem jumpiNextState_accountMap (s : Ethereum.State)
    (dest cond : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (jumpiNextState s dest cond t).accountMap = s.accountMap :=
  rfl

@[simp] theorem jumpiNextState_substate (s : Ethereum.State)
    (dest cond : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (jumpiNextState s dest cond t).substate = s.substate :=
  rfl

@[simp] theorem jumpdestNextState_createdAccounts (s : Ethereum.State) :
    (jumpdestNextState s).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem jumpdestNextState_accountMap (s : Ethereum.State) :
    (jumpdestNextState s).accountMap = s.accountMap :=
  rfl

@[simp] theorem jumpdestNextState_substate (s : Ethereum.State) :
    (jumpdestNextState s).substate = s.substate :=
  rfl

@[simp] theorem popNextState_createdAccounts (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (popNextState s a t).createdAccounts = s.createdAccounts :=
  rfl

@[simp] theorem popNextState_accountMap (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (popNextState s a t).accountMap = s.accountMap :=
  rfl

@[simp] theorem popNextState_substate (s : Ethereum.State)
    (a : Ethereum.UInt256) (t : Ethereum.Stack Ethereum.UInt256) :
    (popNextState s a t).substate = s.substate :=
  rfl

/-- A finite prefix of non-halting EVM `Xstep`s. `ContinueTrace validJumps n s t`
means `Xstep` runs from `s` to `t` in exactly `n` continuing steps. -/
inductive ContinueTrace (validJumps : Array Ethereum.UInt256) :
    Nat → Ethereum.State → Ethereum.State → Prop where
  | nil {s} : ContinueTrace validJumps 0 s s
  | cons {n s s' t} :
      Xstep validJumps s = .ok (s', none) →
      ContinueTrace validJumps n s' t →
      ContinueTrace validJumps (n + 1) s t

namespace ContinueTrace

theorem one {validJumps : Array Ethereum.UInt256} {s t : Ethereum.State}
    (hStep : Xstep validJumps s = .ok (t, none)) :
    ContinueTrace validJumps 1 s t := by
  simpa using (ContinueTrace.cons hStep ContinueTrace.nil)

theorem two {validJumps : Array Ethereum.UInt256} {s t u : Ethereum.State}
    (hStep₁ : Xstep validJumps s = .ok (t, none))
    (hStep₂ : Xstep validJumps t = .ok (u, none)) :
    ContinueTrace validJumps 2 s u := by
  simpa using
    (ContinueTrace.cons hStep₁ (ContinueTrace.cons hStep₂ ContinueTrace.nil))

theorem three {validJumps : Array Ethereum.UInt256} {s t u v : Ethereum.State}
    (hStep₁ : Xstep validJumps s = .ok (t, none))
    (hStep₂ : Xstep validJumps t = .ok (u, none))
    (hStep₃ : Xstep validJumps u = .ok (v, none)) :
    ContinueTrace validJumps 3 s v := by
  simpa using
    (ContinueTrace.cons hStep₁
      (ContinueTrace.cons hStep₂ (ContinueTrace.cons hStep₃ ContinueTrace.nil)))

theorem four {validJumps : Array Ethereum.UInt256} {s t u v w : Ethereum.State}
    (hStep₁ : Xstep validJumps s = .ok (t, none))
    (hStep₂ : Xstep validJumps t = .ok (u, none))
    (hStep₃ : Xstep validJumps u = .ok (v, none))
    (hStep₄ : Xstep validJumps v = .ok (w, none)) :
    ContinueTrace validJumps 4 s w := by
  simpa using
    (ContinueTrace.cons hStep₁
      (ContinueTrace.cons hStep₂
        (ContinueTrace.cons hStep₃ (ContinueTrace.cons hStep₄ ContinueTrace.nil))))

theorem five {validJumps : Array Ethereum.UInt256}
    {s₀ s₁ s₂ s₃ s₄ s₅ : Ethereum.State}
    (hStep₁ : Xstep validJumps s₀ = .ok (s₁, none))
    (hStep₂ : Xstep validJumps s₁ = .ok (s₂, none))
    (hStep₃ : Xstep validJumps s₂ = .ok (s₃, none))
    (hStep₄ : Xstep validJumps s₃ = .ok (s₄, none))
    (hStep₅ : Xstep validJumps s₄ = .ok (s₅, none)) :
    ContinueTrace validJumps 5 s₀ s₅ := by
  simpa using
    (ContinueTrace.cons hStep₁
      (ContinueTrace.cons hStep₂
        (ContinueTrace.cons hStep₃
          (ContinueTrace.cons hStep₄
            (ContinueTrace.cons hStep₅ ContinueTrace.nil)))))

theorem six {validJumps : Array Ethereum.UInt256}
    {s₀ s₁ s₂ s₃ s₄ s₅ s₆ : Ethereum.State}
    (hStep₁ : Xstep validJumps s₀ = .ok (s₁, none))
    (hStep₂ : Xstep validJumps s₁ = .ok (s₂, none))
    (hStep₃ : Xstep validJumps s₂ = .ok (s₃, none))
    (hStep₄ : Xstep validJumps s₃ = .ok (s₄, none))
    (hStep₅ : Xstep validJumps s₄ = .ok (s₅, none))
    (hStep₆ : Xstep validJumps s₅ = .ok (s₆, none)) :
    ContinueTrace validJumps 6 s₀ s₆ := by
  simpa using
    (ContinueTrace.cons hStep₁
      (ContinueTrace.cons hStep₂
        (ContinueTrace.cons hStep₃
          (ContinueTrace.cons hStep₄
            (ContinueTrace.cons hStep₅
              (ContinueTrace.cons hStep₆ ContinueTrace.nil))))))

theorem seven {validJumps : Array Ethereum.UInt256}
    {s₀ s₁ s₂ s₃ s₄ s₅ s₆ s₇ : Ethereum.State}
    (hStep₁ : Xstep validJumps s₀ = .ok (s₁, none))
    (hStep₂ : Xstep validJumps s₁ = .ok (s₂, none))
    (hStep₃ : Xstep validJumps s₂ = .ok (s₃, none))
    (hStep₄ : Xstep validJumps s₃ = .ok (s₄, none))
    (hStep₅ : Xstep validJumps s₄ = .ok (s₅, none))
    (hStep₆ : Xstep validJumps s₅ = .ok (s₆, none))
    (hStep₇ : Xstep validJumps s₆ = .ok (s₇, none)) :
    ContinueTrace validJumps 7 s₀ s₇ := by
  simpa using
    (ContinueTrace.cons hStep₁
      (ContinueTrace.cons hStep₂
        (ContinueTrace.cons hStep₃
          (ContinueTrace.cons hStep₄
            (ContinueTrace.cons hStep₅
              (ContinueTrace.cons hStep₆
                (ContinueTrace.cons hStep₇ ContinueTrace.nil)))))))

theorem eight {validJumps : Array Ethereum.UInt256}
    {s₀ s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ : Ethereum.State}
    (hStep₁ : Xstep validJumps s₀ = .ok (s₁, none))
    (hStep₂ : Xstep validJumps s₁ = .ok (s₂, none))
    (hStep₃ : Xstep validJumps s₂ = .ok (s₃, none))
    (hStep₄ : Xstep validJumps s₃ = .ok (s₄, none))
    (hStep₅ : Xstep validJumps s₄ = .ok (s₅, none))
    (hStep₆ : Xstep validJumps s₅ = .ok (s₆, none))
    (hStep₇ : Xstep validJumps s₆ = .ok (s₇, none))
    (hStep₈ : Xstep validJumps s₇ = .ok (s₈, none)) :
    ContinueTrace validJumps 8 s₀ s₈ := by
  simpa using
    (ContinueTrace.cons hStep₁
      (ContinueTrace.cons hStep₂
        (ContinueTrace.cons hStep₃
          (ContinueTrace.cons hStep₄
            (ContinueTrace.cons hStep₅
              (ContinueTrace.cons hStep₆
                (ContinueTrace.cons hStep₇
                  (ContinueTrace.cons hStep₈ ContinueTrace.nil))))))))

theorem snoc {validJumps : Array Ethereum.UInt256}
    {n : Nat} {s t u : Ethereum.State}
    (hTrace : ContinueTrace validJumps n s t)
    (hStep : Xstep validJumps t = .ok (u, none)) :
    ContinueTrace validJumps (n + 1) s u := by
  induction hTrace with
  | nil =>
      simpa using (ContinueTrace.cons hStep ContinueTrace.nil)
  | cons hHead _ ih =>
      have hRest := ih hStep
      simpa [Nat.add_assoc] using (ContinueTrace.cons hHead hRest)

theorem append {validJumps : Array Ethereum.UInt256}
    {m n : Nat} {s t u : Ethereum.State}
    (hLeft : ContinueTrace validJumps m s t)
    (hRight : ContinueTrace validJumps n t u) :
    ContinueTrace validJumps (m + n) s u := by
  induction hLeft with
  | nil =>
      simpa using hRight
  | cons hHead _ ih =>
      have hRest := ih hRight
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ContinueTrace.cons hHead hRest)

theorem append_three {validJumps : Array Ethereum.UInt256}
    {m n k : Nat} {s t u v : Ethereum.State}
    (h₁ : ContinueTrace validJumps m s t)
    (h₂ : ContinueTrace validJumps n t u)
    (h₃ : ContinueTrace validJumps k u v) :
    ContinueTrace validJumps (m + n + k) s v := by
  have h₁₂ : ContinueTrace validJumps (m + n) s u :=
    ContinueTrace.append h₁ h₂
  exact ContinueTrace.append h₁₂ h₃

theorem append_four {validJumps : Array Ethereum.UInt256}
    {m n k l : Nat} {s t u v w : Ethereum.State}
    (h₁ : ContinueTrace validJumps m s t)
    (h₂ : ContinueTrace validJumps n t u)
    (h₃ : ContinueTrace validJumps k u v)
    (h₄ : ContinueTrace validJumps l v w) :
    ContinueTrace validJumps (m + n + k + l) s w := by
  have h₁₂₃ : ContinueTrace validJumps (m + n + k) s v :=
    ContinueTrace.append_three h₁ h₂ h₃
  exact ContinueTrace.append h₁₂₃ h₄

theorem append_five {validJumps : Array Ethereum.UInt256}
    {m n k l p : Nat} {s t u v w x : Ethereum.State}
    (h₁ : ContinueTrace validJumps m s t)
    (h₂ : ContinueTrace validJumps n t u)
    (h₃ : ContinueTrace validJumps k u v)
    (h₄ : ContinueTrace validJumps l v w)
    (h₅ : ContinueTrace validJumps p w x) :
    ContinueTrace validJumps (m + n + k + l + p) s x := by
  have h₁₂₃₄ : ContinueTrace validJumps (m + n + k + l) s w :=
    ContinueTrace.append_four h₁ h₂ h₃ h₄
  exact ContinueTrace.append h₁₂₃₄ h₅

theorem append_ten {validJumps : Array Ethereum.UInt256}
    {m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ : Nat}
    {s₀ s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ : Ethereum.State}
    (h₁ : ContinueTrace validJumps m₁ s₀ s₁)
    (h₂ : ContinueTrace validJumps m₂ s₁ s₂)
    (h₃ : ContinueTrace validJumps m₃ s₂ s₃)
    (h₄ : ContinueTrace validJumps m₄ s₃ s₄)
    (h₅ : ContinueTrace validJumps m₅ s₄ s₅)
    (h₆ : ContinueTrace validJumps m₆ s₅ s₆)
    (h₇ : ContinueTrace validJumps m₇ s₆ s₇)
    (h₈ : ContinueTrace validJumps m₈ s₇ s₈)
    (h₉ : ContinueTrace validJumps m₉ s₈ s₉)
    (h₁₀ : ContinueTrace validJumps m₁₀ s₉ s₁₀) :
    ContinueTrace validJumps
      ((m₁ + m₂ + m₃ + m₄ + m₅) + (m₆ + m₇ + m₈ + m₉ + m₁₀)) s₀ s₁₀ := by
  have hLeft : ContinueTrace validJumps (m₁ + m₂ + m₃ + m₄ + m₅) s₀ s₅ :=
    ContinueTrace.append_five h₁ h₂ h₃ h₄ h₅
  have hRight : ContinueTrace validJumps (m₆ + m₇ + m₈ + m₉ + m₁₀) s₅ s₁₀ :=
    ContinueTrace.append_five h₆ h₇ h₈ h₉ h₁₀
  exact ContinueTrace.append hLeft hRight

theorem relation {validJumps : Array Ethereum.UInt256}
    {n : Nat} {s t : Ethereum.State} {R : Ethereum.State → Ethereum.State → Prop}
    (hRefl : ∀ s, R s s)
    (hStep :
      ∀ {s t : Ethereum.State},
        Xstep validJumps s = .ok (t, none) → R s t)
    (hTrans : ∀ {s t u : Ethereum.State}, R s t → R t u → R s u)
    (hTrace : ContinueTrace validJumps n s t) :
    R s t := by
  induction hTrace with
  | nil =>
      exact hRefl _
  | cons hHead hTail ih =>
      exact hTrans (hStep hHead) ih

theorem executionEnv_eq {validJumps : Array Ethereum.UInt256}
    {n : Nat} {s t : Ethereum.State}
    (hTrace : ContinueTrace validJumps n s t) :
    s.executionEnv = t.executionEnv :=
  relation
    (R := fun s t => s.executionEnv = t.executionEnv)
    (fun _ => rfl)
    (fun hStep => Xstep_env_unchanged _ _ _ _ hStep)
    (fun h₁ h₂ => h₁.trans h₂)
    hTrace

theorem code_eq_of_start {validJumps : Array Ethereum.UInt256}
    {n : Nat} {s t : Ethereum.State} {code : ByteArray}
    (hTrace : ContinueTrace validJumps n s t)
    (hCode : s.executionEnv.code = code) :
    t.executionEnv.code = code := by
  have hEnv := executionEnv_eq hTrace
  exact (congrArg (fun env => env.code) hEnv.symm).trans hCode

theorem code_eq_of_initial
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat} {t : Ethereum.State}
    (hTrace :
      ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t) :
    t.executionEnv.code = I.code :=
  code_eq_of_start hTrace (by simp [initialEVMState])

theorem length_le_initial_gas
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat} {t : Ethereum.State}
    (hTrace :
      ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t) :
    n ≤ g.toNat := by
  -- Every non-halting `Xstep` in a `ContinueTrace` consumes positive gas and
  -- refuses to continue when that gas is unavailable. The remaining reusable
  -- kernel work is a generic `Xstep` gas-decrease lemma, then induction here.
  sorry

theorem X_halt_success {validJumps : Array Ethereum.UInt256}
    {n : Nat} {s t u : Ethereum.State} {o : ByteArray}
    (hTrace : ContinueTrace validJumps n s t)
    (hHalt : Xstep validJumps t = .ok (u, some (true, o))) :
    X (n + 1) validJumps s = .ok (.success u o) := by
  induction hTrace with
  | nil =>
      simpa using Xstep_X_X_halt_success 0 _ u validJumps o hHalt
  | cons hStep hRest ih =>
      exact Xstep_X_X_continue _ _ _ _ _ hStep (ih hHalt)

theorem X_halt_success_with_fuel {validJumps : Array Ethereum.UInt256}
    {n fuel : Nat} {s t u : Ethereum.State} {o : ByteArray}
    (hTrace : ContinueTrace validJumps n s t)
    (hHalt : Xstep validJumps t = .ok (u, some (true, o))) :
    X (n + fuel + 1) validJumps s = .ok (.success u o) := by
  induction hTrace with
  | nil =>
      simpa using Xstep_X_X_halt_success fuel _ u validJumps o hHalt
  | cons hStep _ ih =>
      have hX := Xstep_X_X_continue _ _ _ _ _ hStep (ih hHalt)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hX

theorem X_halt_revert {validJumps : Array Ethereum.UInt256}
    {n : Nat} {s t u : Ethereum.State} {o : ByteArray}
    (hTrace : ContinueTrace validJumps n s t)
    (hHalt : Xstep validJumps t = .ok (u, some (false, o))) :
    X (n + 1) validJumps s = .ok (.revert u.machineState.gasAvailable o) := by
  induction hTrace with
  | nil =>
      simpa using Xstep_X_X_halt_revert 0 _ u validJumps o hHalt
  | cons hStep hRest ih =>
      exact Xstep_X_X_continue _ _ _ _ _ hStep (ih hHalt)

theorem X_halt_revert_with_fuel {validJumps : Array Ethereum.UInt256}
    {n fuel : Nat} {s t u : Ethereum.State} {o : ByteArray}
    (hTrace : ContinueTrace validJumps n s t)
    (hHalt : Xstep validJumps t = .ok (u, some (false, o))) :
    X (n + fuel + 1) validJumps s = .ok (.revert u.machineState.gasAvailable o) := by
  induction hTrace with
  | nil =>
      simpa using Xstep_X_X_halt_revert fuel _ u validJumps o hHalt
  | cons hStep _ ih =>
      have hX := Xstep_X_X_continue _ _ _ _ _ hStep (ih hHalt)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hX

theorem X_error {validJumps : Array Ethereum.UInt256}
    {n : Nat} {s t : Ethereum.State} {e : ExecutionException}
    (hTrace : ContinueTrace validJumps n s t)
    (hErr : Xstep validJumps t = .error e) :
    X (n + 1) validJumps s = .error e := by
  induction hTrace with
  | nil =>
      simpa using Xstep_X_X_except 0 _ validJumps e hErr
  | cons hStep hRest ih =>
      exact Xstep_X_X_continue _ _ _ _ _ hStep (ih hErr)

theorem X_error_with_fuel {validJumps : Array Ethereum.UInt256}
    {n fuel : Nat} {s t : Ethereum.State} {e : ExecutionException}
    (hTrace : ContinueTrace validJumps n s t)
    (hErr : Xstep validJumps t = .error e) :
    X (n + fuel + 1) validJumps s = .error e := by
  induction hTrace with
  | nil =>
      simpa using Xstep_X_X_except fuel _ validJumps e hErr
  | cons hStep _ ih =>
      have hX := Xstep_X_X_continue _ _ _ _ _ hStep (ih hErr)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hX

end ContinueTrace

end Ethereum.EVM

lemma EVM_Xi_of_initial_continue_trace_success
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n fuel : Nat}
    {t evmState : Ethereum.State}
    {o : ByteArray}
    (hFuel : g.toNat = n + fuel)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hHalt :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t =
        .ok (evmState, some (true, o))) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success
        (evmState.createdAccounts, evmState.accountMap, evmState.machineState.gasAvailable,
          evmState.substate) o) :=
  EVM_Xi_of_X_success (by
    have hX := Ethereum.EVM.ContinueTrace.X_halt_success_with_fuel
      (fuel := fuel) hTrace hHalt
    simpa [hFuel, Nat.add_assoc] using hX)

lemma EVM_Xi_of_initial_continue_trace_revert
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n fuel : Nat}
    {t evmState : Ethereum.State}
    {o : ByteArray}
    (hFuel : g.toNat = n + fuel)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hHalt :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t =
        .ok (evmState, some (false, o))) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert evmState.machineState.gasAvailable o) :=
  EVM_Xi_of_X_revert (by
    have hX := Ethereum.EVM.ContinueTrace.X_halt_revert_with_fuel
      (fuel := fuel) hTrace hHalt
    simpa [hFuel, Nat.add_assoc] using hX)

lemma EVM_Xi_of_initial_continue_trace_error
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n fuel : Nat}
    {t : Ethereum.State}
    {e : Ethereum.EVM.ExecutionException}
    (hFuel : g.toNat = n + fuel)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hErr :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t = .error e) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e :=
  EVM_Xi_of_X_error (by
    have hX := Ethereum.EVM.ContinueTrace.X_error_with_fuel
      (fuel := fuel) hTrace hErr
    simpa [hFuel, Nat.add_assoc] using hX)

lemma EVM_Xi_of_initial_continue_trace_success_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t evmState : Ethereum.State}
    {o : ByteArray}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hHalt :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t =
        .ok (evmState, some (true, o))) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success
        (evmState.createdAccounts, evmState.accountMap, evmState.machineState.gasAvailable,
          evmState.substate) o) :=
  EVM_Xi_of_initial_continue_trace_success
    (fuel := g.toNat - n)
    (by omega)
    hTrace
    hHalt

lemma EVM_Xi_of_initial_continue_trace_return_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {offset size : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.RETURN, .none))
    (hStack : t.machineState.stack = offset :: size :: tail)
    (hMemGas :
      ¬ t.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost t .RETURN)
    (hStackBound : ¬ 1024 < tail.length) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success
        ((Ethereum.EVM.returnNextState t offset size tail).createdAccounts,
          (Ethereum.EVM.returnNextState t offset size tail).accountMap,
          (Ethereum.EVM.returnNextState t offset size tail).machineState.gasAvailable,
          (Ethereum.EVM.returnNextState t offset size tail).substate)
        (Ethereum.EVM.returnOutput t offset size)) := by
  have hCode := Ethereum.EVM.ContinueTrace.code_eq_of_initial hTrace
  exact EVM_Xi_of_initial_continue_trace_success_of_le
    (n := n)
    hFuel
    hTrace
    (by
      have hStep := Ethereum.EVM.Xstep_return_continue_of_decode
        (Ethereum.EVM.decode_of_code_eq hCode hDecode)
        hStack
        hMemGas
        hStackBound
      exact Ethereum.EVM.Xstep_of_code_eq hCode hStep)

lemma EVM_Xi_of_initial_continue_trace_revert_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t evmState : Ethereum.State}
    {o : ByteArray}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hHalt :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t =
        .ok (evmState, some (false, o))) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert evmState.machineState.gasAvailable o) :=
  EVM_Xi_of_initial_continue_trace_revert
    (fuel := g.toNat - n)
    (by omega)
    hTrace
    hHalt

lemma EVM_Xi_of_initial_continue_trace_revert_of_le_of_endpoint_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {offset size : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hCode : t.executionEnv.code = I.code)
    (hDecode :
      Ethereum.EVM.decode t.executionEnv.code t.machineState.pc = some (.REVERT, .none))
    (hStack : t.machineState.stack = offset :: size :: tail)
    (hMemGas :
      ¬ t.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost t .REVERT)
    (hStackBound : ¬ 1024 < tail.length) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert
        (Ethereum.EVM.revertNextState t offset size tail).machineState.gasAvailable
        (Ethereum.EVM.revertOutput t offset size)) :=
  EVM_Xi_of_initial_continue_trace_revert_of_le
    (n := n)
    hFuel
    hTrace
    (by
      have hStep :=
        Ethereum.EVM.Xstep_revert_continue_of_decode hDecode hStack hMemGas hStackBound
      simpa [hCode] using hStep)

lemma EVM_Xi_of_initial_continue_trace_revert_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {offset size : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.REVERT, .none))
    (hStack : t.machineState.stack = offset :: size :: tail)
    (hMemGas :
      ¬ t.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost t .REVERT)
    (hStackBound : ¬ 1024 < tail.length) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert
        (Ethereum.EVM.revertNextState t offset size tail).machineState.gasAvailable
        (Ethereum.EVM.revertOutput t offset size)) := by
  have hCode := Ethereum.EVM.ContinueTrace.code_eq_of_initial hTrace
  exact EVM_Xi_of_initial_continue_trace_revert_of_le_of_endpoint_decode
    hFuel
    hTrace
    hCode
    (by simpa [hCode] using hDecode)
    hStack
    hMemGas
    hStackBound

lemma EVM_Xi_of_initial_continue_trace_revert_zero_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hCode : t.executionEnv.code = I.code)
    (hDecode :
      Ethereum.EVM.decode t.executionEnv.code t.machineState.pc = some (.REVERT, .none))
    (hStack :
      t.machineState.stack =
        (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) :: tail)
    (hStackBound : ¬ 1024 < tail.length) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert
        (Ethereum.EVM.revertNextState t
          (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256) tail).machineState.gasAvailable
        (Ethereum.EVM.revertOutput t
          (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256))) :=
  EVM_Xi_of_initial_continue_trace_revert_of_le_of_endpoint_decode
    hFuel
    hTrace
    hCode
    hDecode
    hStack
    (by
      have hCost := Ethereum.EVM.memoryExpansionCost_revert_zero_stack hStack
      simp [hCost])
    hStackBound

lemma EVM_Xi_of_initial_continue_trace_revert_zero_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.REVERT, .none))
    (hStack :
      t.machineState.stack =
        (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) :: tail)
    (hStackBound : ¬ 1024 < tail.length) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert
        (Ethereum.EVM.revertNextState t
          (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256) tail).machineState.gasAvailable
        (Ethereum.EVM.revertOutput t
          (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256))) := by
  exact EVM_Xi_of_initial_continue_trace_revert_of_le_of_decode
    hFuel
    hTrace
    hDecode
    hStack
    (by
      have hCost := Ethereum.EVM.memoryExpansionCost_revert_zero_stack hStack
      simp [hCost])
    hStackBound

lemma EVM_Xi_of_initial_continue_trace_error_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {e : Ethereum.EVM.ExecutionException}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hErr :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t = .error e) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e :=
  EVM_Xi_of_initial_continue_trace_error
    (fuel := g.toNat - n)
    (by omega)
    hTrace
    hErr

lemma EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {decoded : Option (Ethereum.Operation × Option (Ethereum.UInt256 × Nat))}
    {e : Ethereum.EVM.ExecutionException}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = decoded)
    (hErr :
      Ethereum.EVM.decode t.executionEnv.code t.machineState.pc = decoded →
        Ethereum.EVM.Xstep (Ethereum.EVM.D_J t.executionEnv.code ⟨0⟩) t = .error e) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e := by
  have hCode := Ethereum.EVM.ContinueTrace.code_eq_of_initial hTrace
  exact EVM_Xi_of_initial_continue_trace_error_of_le
    (n := n)
    hFuel
    hTrace
    (Ethereum.EVM.Xstep_of_code_eq_of_decode hCode hDecode hErr)

lemma EVM_Xi_of_initial_continue_trace_error_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {decoded : Option (Ethereum.Operation × Option (Ethereum.UInt256 × Nat))}
    {e : Ethereum.EVM.ExecutionException}
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = decoded)
    (hErr :
      Ethereum.EVM.decode t.executionEnv.code t.machineState.pc = decoded →
        Ethereum.EVM.Xstep (Ethereum.EVM.D_J t.executionEnv.code ⟨0⟩) t = .error e) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := decoded)
    (e := e)
    (Ethereum.EVM.ContinueTrace.length_le_initial_gas hTrace)
    hTrace
    hDecode
    hErr

lemma EVM_Xi_of_initial_continue_trace_jumpdest_oog_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.JUMPDEST, .none))
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gjumpdest) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_decode
    (decoded := some (.JUMPDEST, .none))
    (e := .OutOfGass)
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_jumpdest_oog_of_decode hDecode' hGas)

lemma EVM_Xi_of_initial_continue_trace_push0_oog_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.PUSH0, .none))
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gbase) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_decode
    (decoded := some (.PUSH0, .none))
    (e := .OutOfGass)
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_push0_oog_of_decode hDecode' hGas)

lemma EVM_Xi_of_initial_continue_trace_push1_oog_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {arg : Ethereum.UInt256}
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.PUSH1, .some (arg, 1)))
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_decode
    (decoded := some (.PUSH1, .some (arg, 1)))
    (e := .OutOfGass)
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_push1_oog_of_decode hDecode' hGas)

lemma EVM_Xi_of_initial_continue_trace_dup2_oog_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {a b : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.DUP2, .none))
    (hStack : t.machineState.stack = a :: b :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_decode
    (decoded := some (.DUP2, .none))
    (e := .OutOfGass)
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_dup2_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_trace_dup3_oog_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {a b c : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.DUP3, .none))
    (hStack : t.machineState.stack = a :: b :: c :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_decode
    (decoded := some (.DUP3, .none))
    (e := .OutOfGass)
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_dup3_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_trace_iszero_oog_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {a : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.ISZERO, .none))
    (hStack : t.machineState.stack = a :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_decode
    (decoded := some (.ISZERO, .none))
    (e := .OutOfGass)
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_iszero_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_trace_swap1_oog_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {a b : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.SWAP1, .none))
    (hStack : t.machineState.stack = a :: b :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_decode
    (decoded := some (.SWAP1, .none))
    (e := .OutOfGass)
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_swap1_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_trace_pop_oog_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {a : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.POP, .none))
    (hStack : t.machineState.stack = a :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gbase) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_decode
    (decoded := some (.POP, .none))
    (e := .OutOfGass)
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_pop_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_trace_swap2_oog_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {a b c : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.SWAP2, .none))
    (hStack : t.machineState.stack = a :: b :: c :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_decode
    (decoded := some (.SWAP2, .none))
    (e := .OutOfGass)
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_swap2_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_trace_swap3_oog_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {a b c d : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.SWAP3, .none))
    (hStack : t.machineState.stack = a :: b :: c :: d :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_decode
    (decoded := some (.SWAP3, .none))
    (e := .OutOfGass)
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_swap3_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_trace_jump_oog_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {dest : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.JUMP, .none))
    (hStack : t.machineState.stack = dest :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gmid) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_decode
    (decoded := some (.JUMP, .none))
    (e := .OutOfGass)
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_jump_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_trace_mstore_memory_oog_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {offset value : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.MSTORE, .none))
    (hStack : t.machineState.stack = offset :: value :: tail)
    (hMemGas :
      t.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost t .MSTORE) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_decode
    (decoded := some (.MSTORE, .none))
    (e := .OutOfGass)
    hTrace
    hDecode
    (fun hDecode' =>
      Ethereum.EVM.Xstep_mstore_memory_oog_of_decode hDecode' hStack hMemGas)

lemma EVM_Xi_of_initial_continue_trace_mstore_verylow_oog_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {offset value : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.MSTORE, .none))
    (hStack : t.machineState.stack = offset :: value :: tail)
    (hMemGas :
      ¬ t.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost t .MSTORE)
    (hVerylowGas :
      (t.machineState.gasAvailable - Ethereum.UInt256.ofNat
        (Ethereum.EVM.memoryExpansionCost t .MSTORE)).toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_decode
    (decoded := some (.MSTORE, .none))
    (e := .OutOfGass)
    hTrace
    hDecode
    (fun hDecode' =>
      Ethereum.EVM.Xstep_mstore_verylow_oog_of_decode hDecode' hStack hMemGas hVerylowGas)

lemma EVM_Xi_of_initial_continue_trace_jumpi_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {dest cond : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.JUMPI, .none))
    (hStack : t.machineState.stack = dest :: cond :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Ghigh) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.JUMPI, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_jumpi_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_trace_jumpdest_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.JUMPDEST, .none))
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gjumpdest) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.JUMPDEST, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_jumpdest_oog_of_decode hDecode' hGas)

lemma EVM_Xi_of_initial_continue_trace_push0_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.PUSH0, .none))
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gbase) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.PUSH0, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_push0_oog_of_decode hDecode' hGas)

lemma EVM_Xi_of_initial_continue_traces_jumpdest_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n : Nat}
    {mid t : Ethereum.State}
    (hFuel : m + n ≤ g.toNat)
    (hPrefix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) mid)
    (hSuffix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n mid t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.JUMPDEST, .none))
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gjumpdest) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_jumpdest_oog_of_le_of_decode
    (n := m + n)
    hFuel
    (Ethereum.EVM.ContinueTrace.append hPrefix hSuffix)
    hDecode
    hGas

lemma EVM_Xi_of_initial_continue_traces_push0_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n : Nat}
    {mid t : Ethereum.State}
    (hFuel : m + n ≤ g.toNat)
    (hPrefix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) mid)
    (hSuffix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n mid t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.PUSH0, .none))
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gbase) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_push0_oog_of_le_of_decode
    (n := m + n)
    hFuel
    (Ethereum.EVM.ContinueTrace.append hPrefix hSuffix)
    hDecode
    hGas

lemma EVM_Xi_of_initial_continue_trace_calldataload_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {offset : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.CALLDATALOAD, .none))
    (hStack : t.machineState.stack = offset :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.CALLDATALOAD, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_calldataload_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_trace_push1_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {arg : Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.PUSH1, .some (arg, 1)))
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.PUSH1, .some (arg, 1)))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_push1_oog_of_decode hDecode' hGas)

lemma EVM_Xi_of_initial_continue_traces_push1_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n : Nat}
    {mid t : Ethereum.State}
    {arg : Ethereum.UInt256}
    (hFuel : m + n ≤ g.toNat)
    (hPrefix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) mid)
    (hSuffix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n mid t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.PUSH1, .some (arg, 1)))
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_push1_oog_of_le_of_decode
    (n := m + n)
    hFuel
    (Ethereum.EVM.ContinueTrace.append hPrefix hSuffix)
    hDecode
    hGas

lemma EVM_Xi_of_initial_continue_trace_jump_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {dest : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.JUMP, .none))
    (hStack : t.machineState.stack = dest :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gmid) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.JUMP, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_jump_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_traces_jump_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n : Nat}
    {mid t : Ethereum.State}
    {dest : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : m + n ≤ g.toNat)
    (hPrefix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) mid)
    (hSuffix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n mid t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.JUMP, .none))
    (hStack : t.machineState.stack = dest :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gmid) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_jump_oog_of_le_of_decode
    (n := m + n)
    hFuel
    (Ethereum.EVM.ContinueTrace.append hPrefix hSuffix)
    hDecode
    hStack
    hGas

lemma EVM_Xi_of_initial_continue_trace_swap1_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {a b : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.SWAP1, .none))
    (hStack : t.machineState.stack = a :: b :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.SWAP1, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_swap1_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_traces_swap1_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n : Nat}
    {mid t : Ethereum.State}
    {a b : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : m + n ≤ g.toNat)
    (hPrefix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) mid)
    (hSuffix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n mid t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.SWAP1, .none))
    (hStack : t.machineState.stack = a :: b :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_swap1_oog_of_le_of_decode
    (n := m + n)
    hFuel
    (Ethereum.EVM.ContinueTrace.append hPrefix hSuffix)
    hDecode
    hStack
    hGas

lemma EVM_Xi_of_initial_continue_trace_pop_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {a : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.POP, .none))
    (hStack : t.machineState.stack = a :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gbase) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.POP, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_pop_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_traces_pop_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n : Nat}
    {mid t : Ethereum.State}
    {a : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : m + n ≤ g.toNat)
    (hPrefix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) mid)
    (hSuffix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n mid t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.POP, .none))
    (hStack : t.machineState.stack = a :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gbase) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_pop_oog_of_le_of_decode
    (n := m + n)
    hFuel
    (Ethereum.EVM.ContinueTrace.append hPrefix hSuffix)
    hDecode
    hStack
    hGas

lemma EVM_Xi_of_initial_continue_trace_mload_memory_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {offset : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.MLOAD, .none))
    (hStack : t.machineState.stack = offset :: tail)
    (hMemGas : t.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost t .MLOAD) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.MLOAD, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_mload_memory_oog_of_decode hDecode' hStack hMemGas)

lemma EVM_Xi_of_initial_continue_traces_mload_memory_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n : Nat}
    {mid t : Ethereum.State}
    {offset : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : m + n ≤ g.toNat)
    (hPrefix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) mid)
    (hSuffix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n mid t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.MLOAD, .none))
    (hStack : t.machineState.stack = offset :: tail)
    (hMemGas : t.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost t .MLOAD) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_mload_memory_oog_of_le_of_decode
    (n := m + n)
    hFuel
    (Ethereum.EVM.ContinueTrace.append hPrefix hSuffix)
    hDecode
    hStack
    hMemGas

lemma EVM_Xi_of_initial_continue_trace_mload_verylow_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {offset : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.MLOAD, .none))
    (hStack : t.machineState.stack = offset :: tail)
    (hMemGas : ¬ t.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost t .MLOAD)
    (hVerylowGas :
      (t.machineState.gasAvailable - Ethereum.UInt256.ofNat
        (Ethereum.EVM.memoryExpansionCost t .MLOAD)).toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.MLOAD, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' =>
      Ethereum.EVM.Xstep_mload_verylow_oog_of_decode hDecode' hStack hMemGas hVerylowGas)

lemma EVM_Xi_of_initial_continue_traces_mload_verylow_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n : Nat}
    {mid t : Ethereum.State}
    {offset : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : m + n ≤ g.toNat)
    (hPrefix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) mid)
    (hSuffix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n mid t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.MLOAD, .none))
    (hStack : t.machineState.stack = offset :: tail)
    (hMemGas : ¬ t.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost t .MLOAD)
    (hVerylowGas :
      (t.machineState.gasAvailable - Ethereum.UInt256.ofNat
        (Ethereum.EVM.memoryExpansionCost t .MLOAD)).toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_mload_verylow_oog_of_le_of_decode
    (n := m + n)
    hFuel
    (Ethereum.EVM.ContinueTrace.append hPrefix hSuffix)
    hDecode
    hStack
    hMemGas
    hVerylowGas

lemma EVM_Xi_of_initial_continue_trace_swap2_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {a b c : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.SWAP2, .none))
    (hStack : t.machineState.stack = a :: b :: c :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.SWAP2, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_swap2_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_traces_swap2_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n : Nat}
    {mid t : Ethereum.State}
    {a b c : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : m + n ≤ g.toNat)
    (hPrefix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) mid)
    (hSuffix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n mid t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.SWAP2, .none))
    (hStack : t.machineState.stack = a :: b :: c :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_swap2_oog_of_le_of_decode
    (n := m + n)
    hFuel
    (Ethereum.EVM.ContinueTrace.append hPrefix hSuffix)
    hDecode
    hStack
    hGas

lemma EVM_Xi_of_initial_continue_trace_shr_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {a b : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.SHR, .none))
    (hStack : t.machineState.stack = a :: b :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.SHR, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_shr_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_trace_dup1_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {a : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.DUP1, .none))
    (hStack : t.machineState.stack = a :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.DUP1, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_dup1_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_trace_push4_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {arg : Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.PUSH4, .some (arg, 4)))
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.PUSH4, .some (arg, 4)))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_push4_oog_of_decode hDecode' hGas)

lemma EVM_Xi_of_initial_continue_trace_eq_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {a b : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.EQ, .none))
    (hStack : t.machineState.stack = a :: b :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.EQ, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_eq_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_trace_dup2_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {a b : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.DUP2, .none))
    (hStack : t.machineState.stack = a :: b :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.DUP2, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_dup2_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_trace_dup3_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {a b c : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.DUP3, .none))
    (hStack : t.machineState.stack = a :: b :: c :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.DUP3, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_dup3_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_trace_dup4_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {a b c d : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.DUP4, .none))
    (hStack : t.machineState.stack = a :: b :: c :: d :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.DUP4, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_dup4_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_trace_dup5_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {a b c d e : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.DUP5, .none))
    (hStack : t.machineState.stack = a :: b :: c :: d :: e :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.DUP5, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_dup5_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_trace_add_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {a b : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.ADD, .none))
    (hStack : t.machineState.stack = a :: b :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.ADD, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_add_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_trace_sub_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {a b : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.SUB, .none))
    (hStack : t.machineState.stack = a :: b :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.SUB, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_sub_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_trace_iszero_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {a : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.ISZERO, .none))
    (hStack : t.machineState.stack = a :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.ISZERO, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_iszero_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_trace_swap3_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {a b c d : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.SWAP3, .none))
    (hStack : t.machineState.stack = a :: b :: c :: d :: tail)
    (hGas : t.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.SWAP3, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_swap3_oog_of_decode hDecode' hStack hGas)

lemma EVM_Xi_of_initial_continue_trace_mstore_memory_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {offset value : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.MSTORE, .none))
    (hStack : t.machineState.stack = offset :: value :: tail)
    (hMemGas : t.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost t .MSTORE) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.MSTORE, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_mstore_memory_oog_of_decode hDecode' hStack hMemGas)

lemma EVM_Xi_of_initial_continue_trace_mstore_verylow_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {offset value : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.MSTORE, .none))
    (hStack : t.machineState.stack = offset :: value :: tail)
    (hMemGas : ¬ t.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost t .MSTORE)
    (hVerylowGas :
      (t.machineState.gasAvailable - Ethereum.UInt256.ofNat
        (Ethereum.EVM.memoryExpansionCost t .MSTORE)).toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.MSTORE, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' =>
      Ethereum.EVM.Xstep_mstore_verylow_oog_of_decode hDecode' hStack hMemGas hVerylowGas)

lemma EVM_Xi_of_initial_continue_trace_return_memory_oog_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n : Nat}
    {t : Ethereum.State}
    {offset size : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : n ≤ g.toNat)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.RETURN, .none))
    (hStack : t.machineState.stack = offset :: size :: tail)
    (hMemGas : t.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost t .RETURN) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := n)
    (decoded := some (.RETURN, .none))
    (e := .OutOfGass)
    hFuel
    hTrace
    hDecode
    (fun hDecode' => Ethereum.EVM.Xstep_return_memory_oog_of_decode hDecode' hStack hMemGas)

lemma EVM_Xi_of_initial_continue_traces_success_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n : Nat}
    {mid t evmState : Ethereum.State}
    {o : ByteArray}
    (hFuel : m + n ≤ g.toNat)
    (hPrefix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) mid)
    (hSuffix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n mid t)
    (hHalt :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t =
        .ok (evmState, some (true, o))) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success
        (evmState.createdAccounts, evmState.accountMap, evmState.machineState.gasAvailable,
          evmState.substate) o) :=
  EVM_Xi_of_initial_continue_trace_success_of_le
    (n := m + n)
    hFuel
    (Ethereum.EVM.ContinueTrace.append hPrefix hSuffix)
    hHalt

lemma EVM_Xi_of_initial_continue_traces_return_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n : Nat}
    {mid t : Ethereum.State}
    {offset size : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : m + n ≤ g.toNat)
    (hPrefix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) mid)
    (hSuffix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n mid t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.RETURN, .none))
    (hStack : t.machineState.stack = offset :: size :: tail)
    (hMemGas :
      ¬ t.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost t .RETURN)
    (hStackBound : ¬ 1024 < tail.length) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success
        ((Ethereum.EVM.returnNextState t offset size tail).createdAccounts,
          (Ethereum.EVM.returnNextState t offset size tail).accountMap,
          (Ethereum.EVM.returnNextState t offset size tail).machineState.gasAvailable,
          (Ethereum.EVM.returnNextState t offset size tail).substate)
        (Ethereum.EVM.returnOutput t offset size)) :=
  EVM_Xi_of_initial_continue_trace_return_of_le_of_decode
    (n := m + n)
    hFuel
    (Ethereum.EVM.ContinueTrace.append hPrefix hSuffix)
    hDecode
    hStack
    hMemGas
    hStackBound

lemma EVM_Xi_of_initial_continue_traces_revert_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n : Nat}
    {mid t evmState : Ethereum.State}
    {o : ByteArray}
    (hFuel : m + n ≤ g.toNat)
    (hPrefix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) mid)
    (hSuffix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n mid t)
    (hHalt :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t =
        .ok (evmState, some (false, o))) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert evmState.machineState.gasAvailable o) :=
  EVM_Xi_of_initial_continue_trace_revert_of_le
    (n := m + n)
    hFuel
    (Ethereum.EVM.ContinueTrace.append hPrefix hSuffix)
    hHalt

lemma EVM_Xi_of_initial_continue_traces_revert_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n : Nat}
    {mid t : Ethereum.State}
    {offset size : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : m + n ≤ g.toNat)
    (hPrefix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) mid)
    (hSuffix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n mid t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.REVERT, .none))
    (hStack : t.machineState.stack = offset :: size :: tail)
    (hMemGas :
      ¬ t.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost t .REVERT)
    (hStackBound : ¬ 1024 < tail.length) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert
        (Ethereum.EVM.revertNextState t offset size tail).machineState.gasAvailable
        (Ethereum.EVM.revertOutput t offset size)) :=
  EVM_Xi_of_initial_continue_trace_revert_of_le_of_decode
    (n := m + n)
    hFuel
    (Ethereum.EVM.ContinueTrace.append hPrefix hSuffix)
    hDecode
    hStack
    hMemGas
    hStackBound

lemma EVM_Xi_of_initial_continue_traces_revert_zero_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n : Nat}
    {mid t : Ethereum.State}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : m + n ≤ g.toNat)
    (hPrefix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) mid)
    (hSuffix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n mid t)
    (hCode : t.executionEnv.code = I.code)
    (hDecode :
      Ethereum.EVM.decode t.executionEnv.code t.machineState.pc = some (.REVERT, .none))
    (hStack :
      t.machineState.stack =
        (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) :: tail)
    (hStackBound : ¬ 1024 < tail.length) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert
        (Ethereum.EVM.revertNextState t
          (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256) tail).machineState.gasAvailable
        (Ethereum.EVM.revertOutput t
          (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256))) :=
  EVM_Xi_of_initial_continue_trace_revert_zero_of_le
    (n := m + n)
    hFuel
    (Ethereum.EVM.ContinueTrace.append hPrefix hSuffix)
    hCode
    hDecode
    hStack
    hStackBound

lemma EVM_Xi_of_initial_continue_traces_revert_zero_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n : Nat}
    {mid t : Ethereum.State}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : m + n ≤ g.toNat)
    (hPrefix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) mid)
    (hSuffix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n mid t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.REVERT, .none))
    (hStack :
      t.machineState.stack =
        (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) :: tail)
    (hStackBound : ¬ 1024 < tail.length) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert
        (Ethereum.EVM.revertNextState t
          (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256) tail).machineState.gasAvailable
        (Ethereum.EVM.revertOutput t
          (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256))) :=
  EVM_Xi_of_initial_continue_traces_revert_of_le_of_decode
    hFuel
    hPrefix
    hSuffix
    hDecode
    hStack
    (by
      have hCost := Ethereum.EVM.memoryExpansionCost_revert_zero_stack hStack
      simp [hCost])
    hStackBound

lemma EVM_Xi_of_initial_continue_traces_error_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n : Nat}
    {mid t : Ethereum.State}
    {e : Ethereum.EVM.ExecutionException}
    (hFuel : m + n ≤ g.toNat)
    (hPrefix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) mid)
    (hSuffix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n mid t)
    (hErr :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t = .error e) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e :=
  EVM_Xi_of_initial_continue_trace_error_of_le
    (n := m + n)
    hFuel
    (Ethereum.EVM.ContinueTrace.append hPrefix hSuffix)
    hErr

lemma EVM_Xi_of_initial_continue_three_traces_success_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k : Nat}
    {s₁ s₂ t evmState : Ethereum.State}
    {o : ByteArray}
    (hFuel : m + n + k ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ t)
    (hHalt :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t =
        .ok (evmState, some (true, o))) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success
        (evmState.createdAccounts, evmState.accountMap, evmState.machineState.gasAvailable,
          evmState.substate) o) :=
  EVM_Xi_of_initial_continue_trace_success_of_le
    (n := m + n + k)
    hFuel
    (Ethereum.EVM.ContinueTrace.append_three h₁ h₂ h₃)
    hHalt

lemma EVM_Xi_of_initial_continue_three_traces_return_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k : Nat}
    {s₁ s₂ t : Ethereum.State}
    {offset size : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : m + n + k ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.RETURN, .none))
    (hStack : t.machineState.stack = offset :: size :: tail)
    (hMemGas :
      ¬ t.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost t .RETURN)
    (hStackBound : ¬ 1024 < tail.length) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success
        ((Ethereum.EVM.returnNextState t offset size tail).createdAccounts,
          (Ethereum.EVM.returnNextState t offset size tail).accountMap,
          (Ethereum.EVM.returnNextState t offset size tail).machineState.gasAvailable,
          (Ethereum.EVM.returnNextState t offset size tail).substate)
        (Ethereum.EVM.returnOutput t offset size)) :=
  EVM_Xi_of_initial_continue_trace_return_of_le_of_decode
    (n := m + n + k)
    hFuel
    (Ethereum.EVM.ContinueTrace.append_three h₁ h₂ h₃)
    hDecode
    hStack
    hMemGas
    hStackBound

lemma EVM_Xi_of_initial_continue_three_traces_revert_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k : Nat}
    {s₁ s₂ t evmState : Ethereum.State}
    {o : ByteArray}
    (hFuel : m + n + k ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ t)
    (hHalt :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t =
        .ok (evmState, some (false, o))) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert evmState.machineState.gasAvailable o) :=
  EVM_Xi_of_initial_continue_trace_revert_of_le
    (n := m + n + k)
    hFuel
    (Ethereum.EVM.ContinueTrace.append_three h₁ h₂ h₃)
    hHalt

lemma EVM_Xi_of_initial_continue_three_traces_revert_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k : Nat}
    {s₁ s₂ t : Ethereum.State}
    {offset size : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : m + n + k ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.REVERT, .none))
    (hStack : t.machineState.stack = offset :: size :: tail)
    (hMemGas :
      ¬ t.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost t .REVERT)
    (hStackBound : ¬ 1024 < tail.length) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert
        (Ethereum.EVM.revertNextState t offset size tail).machineState.gasAvailable
        (Ethereum.EVM.revertOutput t offset size)) :=
  EVM_Xi_of_initial_continue_trace_revert_of_le_of_decode
    (n := m + n + k)
    hFuel
    (Ethereum.EVM.ContinueTrace.append_three h₁ h₂ h₃)
    hDecode
    hStack
    hMemGas
    hStackBound

lemma EVM_Xi_of_initial_continue_three_traces_revert_zero_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k : Nat}
    {s₁ s₂ t : Ethereum.State}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : m + n + k ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ t)
    (hCode : t.executionEnv.code = I.code)
    (hDecode :
      Ethereum.EVM.decode t.executionEnv.code t.machineState.pc = some (.REVERT, .none))
    (hStack :
      t.machineState.stack =
        (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) :: tail)
    (hStackBound : ¬ 1024 < tail.length) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert
        (Ethereum.EVM.revertNextState t
          (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256) tail).machineState.gasAvailable
        (Ethereum.EVM.revertOutput t
          (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256))) :=
  EVM_Xi_of_initial_continue_trace_revert_zero_of_le
    (n := m + n + k)
    hFuel
    (Ethereum.EVM.ContinueTrace.append_three h₁ h₂ h₃)
    hCode
    hDecode
    hStack
    hStackBound

lemma EVM_Xi_of_initial_continue_three_traces_revert_zero_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k : Nat}
    {s₁ s₂ t : Ethereum.State}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : m + n + k ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.REVERT, .none))
    (hStack :
      t.machineState.stack =
        (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) :: tail)
    (hStackBound : ¬ 1024 < tail.length) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert
        (Ethereum.EVM.revertNextState t
          (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256) tail).machineState.gasAvailable
        (Ethereum.EVM.revertOutput t
          (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256))) :=
  EVM_Xi_of_initial_continue_three_traces_revert_of_le_of_decode
    hFuel
    h₁
    h₂
    h₃
    hDecode
    hStack
    (by
      have hCost := Ethereum.EVM.memoryExpansionCost_revert_zero_stack hStack
      simp [hCost])
    hStackBound

lemma EVM_Xi_of_initial_continue_three_traces_error_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k : Nat}
    {s₁ s₂ t : Ethereum.State}
    {e : Ethereum.EVM.ExecutionException}
    (hFuel : m + n + k ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ t)
    (hErr :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t = .error e) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e :=
  EVM_Xi_of_initial_continue_trace_error_of_le
    (n := m + n + k)
    hFuel
    (Ethereum.EVM.ContinueTrace.append_three h₁ h₂ h₃)
    hErr

lemma EVM_Xi_of_initial_continue_four_traces_success_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k l : Nat}
    {s₁ s₂ s₃ t evmState : Ethereum.State}
    {o : ByteArray}
    (hFuel : m + n + k + l ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ s₃)
    (h₄ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) l s₃ t)
    (hHalt :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t =
        .ok (evmState, some (true, o))) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success
        (evmState.createdAccounts, evmState.accountMap, evmState.machineState.gasAvailable,
          evmState.substate) o) :=
  EVM_Xi_of_initial_continue_trace_success_of_le
    (n := m + n + k + l)
    hFuel
    (Ethereum.EVM.ContinueTrace.append_four h₁ h₂ h₃ h₄)
    hHalt

lemma EVM_Xi_of_initial_continue_four_traces_return_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k l : Nat}
    {s₁ s₂ s₃ t : Ethereum.State}
    {offset size : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : m + n + k + l ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ s₃)
    (h₄ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) l s₃ t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.RETURN, .none))
    (hStack : t.machineState.stack = offset :: size :: tail)
    (hMemGas :
      ¬ t.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost t .RETURN)
    (hStackBound : ¬ 1024 < tail.length) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success
        ((Ethereum.EVM.returnNextState t offset size tail).createdAccounts,
          (Ethereum.EVM.returnNextState t offset size tail).accountMap,
          (Ethereum.EVM.returnNextState t offset size tail).machineState.gasAvailable,
          (Ethereum.EVM.returnNextState t offset size tail).substate)
        (Ethereum.EVM.returnOutput t offset size)) :=
  EVM_Xi_of_initial_continue_trace_return_of_le_of_decode
    (n := m + n + k + l)
    hFuel
    (Ethereum.EVM.ContinueTrace.append_four h₁ h₂ h₃ h₄)
    hDecode
    hStack
    hMemGas
    hStackBound

lemma EVM_Xi_of_initial_continue_four_traces_revert_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k l : Nat}
    {s₁ s₂ s₃ t evmState : Ethereum.State}
    {o : ByteArray}
    (hFuel : m + n + k + l ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ s₃)
    (h₄ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) l s₃ t)
    (hHalt :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t =
        .ok (evmState, some (false, o))) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert evmState.machineState.gasAvailable o) :=
  EVM_Xi_of_initial_continue_trace_revert_of_le
    (n := m + n + k + l)
    hFuel
    (Ethereum.EVM.ContinueTrace.append_four h₁ h₂ h₃ h₄)
    hHalt

lemma EVM_Xi_of_initial_continue_four_traces_revert_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k l : Nat}
    {s₁ s₂ s₃ t : Ethereum.State}
    {offset size : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : m + n + k + l ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ s₃)
    (h₄ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) l s₃ t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.REVERT, .none))
    (hStack : t.machineState.stack = offset :: size :: tail)
    (hMemGas :
      ¬ t.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost t .REVERT)
    (hStackBound : ¬ 1024 < tail.length) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert
        (Ethereum.EVM.revertNextState t offset size tail).machineState.gasAvailable
        (Ethereum.EVM.revertOutput t offset size)) :=
  EVM_Xi_of_initial_continue_trace_revert_of_le_of_decode
    (n := m + n + k + l)
    hFuel
    (Ethereum.EVM.ContinueTrace.append_four h₁ h₂ h₃ h₄)
    hDecode
    hStack
    hMemGas
    hStackBound

lemma EVM_Xi_of_initial_continue_four_traces_revert_zero_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k l : Nat}
    {s₁ s₂ s₃ t : Ethereum.State}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : m + n + k + l ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ s₃)
    (h₄ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) l s₃ t)
    (hCode : t.executionEnv.code = I.code)
    (hDecode :
      Ethereum.EVM.decode t.executionEnv.code t.machineState.pc = some (.REVERT, .none))
    (hStack :
      t.machineState.stack =
        (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) :: tail)
    (hStackBound : ¬ 1024 < tail.length) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert
        (Ethereum.EVM.revertNextState t
          (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256) tail).machineState.gasAvailable
        (Ethereum.EVM.revertOutput t
          (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256))) :=
  EVM_Xi_of_initial_continue_trace_revert_zero_of_le
    (n := m + n + k + l)
    hFuel
    (Ethereum.EVM.ContinueTrace.append_four h₁ h₂ h₃ h₄)
    hCode
    hDecode
    hStack
    hStackBound

lemma EVM_Xi_of_initial_continue_four_traces_revert_zero_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k l : Nat}
    {s₁ s₂ s₃ t : Ethereum.State}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : m + n + k + l ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ s₃)
    (h₄ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) l s₃ t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.REVERT, .none))
    (hStack :
      t.machineState.stack =
        (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) :: tail)
    (hStackBound : ¬ 1024 < tail.length) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert
        (Ethereum.EVM.revertNextState t
          (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256) tail).machineState.gasAvailable
        (Ethereum.EVM.revertOutput t
          (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256))) :=
  EVM_Xi_of_initial_continue_four_traces_revert_of_le_of_decode
    hFuel
    h₁
    h₂
    h₃
    h₄
    hDecode
    hStack
    (by
      have hCost := Ethereum.EVM.memoryExpansionCost_revert_zero_stack hStack
      simp [hCost])
    hStackBound

lemma EVM_Xi_of_initial_continue_four_traces_error_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k l : Nat}
    {s₁ s₂ s₃ t : Ethereum.State}
    {e : Ethereum.EVM.ExecutionException}
    (hFuel : m + n + k + l ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ s₃)
    (h₄ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) l s₃ t)
    (hErr :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t = .error e) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e :=
  EVM_Xi_of_initial_continue_trace_error_of_le
    (n := m + n + k + l)
    hFuel
    (Ethereum.EVM.ContinueTrace.append_four h₁ h₂ h₃ h₄)
    hErr

lemma EVM_Xi_of_initial_continue_five_traces_success_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k l p : Nat}
    {s₁ s₂ s₃ s₄ t evmState : Ethereum.State}
    {o : ByteArray}
    (hFuel : m + n + k + l + p ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ s₃)
    (h₄ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) l s₃ s₄)
    (h₅ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) p s₄ t)
    (hHalt :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t =
        .ok (evmState, some (true, o))) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success
        (evmState.createdAccounts, evmState.accountMap, evmState.machineState.gasAvailable,
          evmState.substate) o) :=
  EVM_Xi_of_initial_continue_trace_success_of_le
    (n := m + n + k + l + p)
    hFuel
    (Ethereum.EVM.ContinueTrace.append_five h₁ h₂ h₃ h₄ h₅)
    hHalt

lemma EVM_Xi_of_initial_continue_five_traces_return_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k l p : Nat}
    {s₁ s₂ s₃ s₄ t : Ethereum.State}
    {offset size : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : m + n + k + l + p ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ s₃)
    (h₄ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) l s₃ s₄)
    (h₅ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) p s₄ t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.RETURN, .none))
    (hStack : t.machineState.stack = offset :: size :: tail)
    (hMemGas :
      ¬ t.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost t .RETURN)
    (hStackBound : ¬ 1024 < tail.length) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success
        ((Ethereum.EVM.returnNextState t offset size tail).createdAccounts,
          (Ethereum.EVM.returnNextState t offset size tail).accountMap,
          (Ethereum.EVM.returnNextState t offset size tail).machineState.gasAvailable,
          (Ethereum.EVM.returnNextState t offset size tail).substate)
        (Ethereum.EVM.returnOutput t offset size)) :=
  EVM_Xi_of_initial_continue_trace_return_of_le_of_decode
    (n := m + n + k + l + p)
    hFuel
    (Ethereum.EVM.ContinueTrace.append_five h₁ h₂ h₃ h₄ h₅)
    hDecode
    hStack
    hMemGas
    hStackBound

lemma EVM_Xi_of_initial_continue_ten_traces_success_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ : Nat}
    {s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t evmState : Ethereum.State}
    {o : ByteArray}
    (hFuel :
      ((m₁ + m₂ + m₃ + m₄ + m₅) + (m₆ + m₇ + m₈ + m₉ + m₁₀)) ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₁
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₂ s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₃ s₂ s₃)
    (h₄ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₄ s₃ s₄)
    (h₅ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₅ s₄ s₅)
    (h₆ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₆ s₅ s₆)
    (h₇ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₇ s₆ s₇)
    (h₈ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₈ s₇ s₈)
    (h₉ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₉ s₈ s₉)
    (h₁₀ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₁₀ s₉ t)
    (hHalt :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t =
        .ok (evmState, some (true, o))) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success
        (evmState.createdAccounts, evmState.accountMap, evmState.machineState.gasAvailable,
          evmState.substate) o) :=
  EVM_Xi_of_initial_continue_trace_success_of_le
    (n := (m₁ + m₂ + m₃ + m₄ + m₅) + (m₆ + m₇ + m₈ + m₉ + m₁₀))
    hFuel
    (Ethereum.EVM.ContinueTrace.append_ten h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀)
    hHalt

lemma EVM_Xi_of_initial_continue_ten_traces_return_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ : Nat}
    {s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t : Ethereum.State}
    {offset size : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel :
      ((m₁ + m₂ + m₃ + m₄ + m₅) + (m₆ + m₇ + m₈ + m₉ + m₁₀)) ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₁
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₂ s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₃ s₂ s₃)
    (h₄ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₄ s₃ s₄)
    (h₅ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₅ s₄ s₅)
    (h₆ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₆ s₅ s₆)
    (h₇ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₇ s₆ s₇)
    (h₈ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₈ s₇ s₈)
    (h₉ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₉ s₈ s₉)
    (h₁₀ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₁₀ s₉ t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = some (.RETURN, .none))
    (hStack : t.machineState.stack = offset :: size :: tail)
    (hMemGas :
      ¬ t.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost t .RETURN)
    (hStackBound : ¬ 1024 < tail.length) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success
        ((Ethereum.EVM.returnNextState t offset size tail).createdAccounts,
          (Ethereum.EVM.returnNextState t offset size tail).accountMap,
          (Ethereum.EVM.returnNextState t offset size tail).machineState.gasAvailable,
          (Ethereum.EVM.returnNextState t offset size tail).substate)
        (Ethereum.EVM.returnOutput t offset size)) :=
  EVM_Xi_of_initial_continue_trace_return_of_le_of_decode
    (n := (m₁ + m₂ + m₃ + m₄ + m₅) + (m₆ + m₇ + m₈ + m₉ + m₁₀))
    hFuel
    (Ethereum.EVM.ContinueTrace.append_ten h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀)
    hDecode
    hStack
    hMemGas
    hStackBound

lemma EVM_Xi_of_initial_continue_ten_traces_revert_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ : Nat}
    {s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t evmState : Ethereum.State}
    {o : ByteArray}
    (hFuel :
      ((m₁ + m₂ + m₃ + m₄ + m₅) + (m₆ + m₇ + m₈ + m₉ + m₁₀)) ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₁
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₂ s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₃ s₂ s₃)
    (h₄ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₄ s₃ s₄)
    (h₅ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₅ s₄ s₅)
    (h₆ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₆ s₅ s₆)
    (h₇ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₇ s₆ s₇)
    (h₈ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₈ s₇ s₈)
    (h₉ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₉ s₈ s₉)
    (h₁₀ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₁₀ s₉ t)
    (hHalt :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t =
        .ok (evmState, some (false, o))) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert evmState.machineState.gasAvailable o) :=
  EVM_Xi_of_initial_continue_trace_revert_of_le
    (n := (m₁ + m₂ + m₃ + m₄ + m₅) + (m₆ + m₇ + m₈ + m₉ + m₁₀))
    hFuel
    (Ethereum.EVM.ContinueTrace.append_ten h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀)
    hHalt

lemma EVM_Xi_of_initial_continue_ten_traces_revert_zero_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ : Nat}
    {s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t : Ethereum.State}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel :
      ((m₁ + m₂ + m₃ + m₄ + m₅) + (m₆ + m₇ + m₈ + m₉ + m₁₀)) ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₁
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₂ s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₃ s₂ s₃)
    (h₄ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₄ s₃ s₄)
    (h₅ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₅ s₄ s₅)
    (h₆ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₆ s₅ s₆)
    (h₇ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₇ s₆ s₇)
    (h₈ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₈ s₇ s₈)
    (h₉ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₉ s₈ s₉)
    (h₁₀ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₁₀ s₉ t)
    (hCode : t.executionEnv.code = I.code)
    (hDecode :
      Ethereum.EVM.decode t.executionEnv.code t.machineState.pc = some (.REVERT, .none))
    (hStack :
      t.machineState.stack =
        (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) :: tail)
    (hStackBound : ¬ 1024 < tail.length) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert
        (Ethereum.EVM.revertNextState t
          (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256) tail).machineState.gasAvailable
        (Ethereum.EVM.revertOutput t
          (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256))) :=
  EVM_Xi_of_initial_continue_trace_revert_zero_of_le
    (n := (m₁ + m₂ + m₃ + m₄ + m₅) + (m₆ + m₇ + m₈ + m₉ + m₁₀))
    hFuel
    (Ethereum.EVM.ContinueTrace.append_ten h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀)
    hCode
    hDecode
    hStack
    hStackBound

lemma EVM_Xi_of_initial_continue_ten_traces_error_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ : Nat}
    {s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t : Ethereum.State}
    {e : Ethereum.EVM.ExecutionException}
    (hFuel :
      ((m₁ + m₂ + m₃ + m₄ + m₅) + (m₆ + m₇ + m₈ + m₉ + m₁₀)) ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₁
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₂ s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₃ s₂ s₃)
    (h₄ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₄ s₃ s₄)
    (h₅ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₅ s₄ s₅)
    (h₆ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₆ s₅ s₆)
    (h₇ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₇ s₆ s₇)
    (h₈ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₈ s₇ s₈)
    (h₉ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₉ s₈ s₉)
    (h₁₀ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₁₀ s₉ t)
    (hErr :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t = .error e) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e :=
  EVM_Xi_of_initial_continue_trace_error_of_le
    (n := (m₁ + m₂ + m₃ + m₄ + m₅) + (m₆ + m₇ + m₈ + m₉ + m₁₀))
    hFuel
    (Ethereum.EVM.ContinueTrace.append_ten h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀)
    hErr

lemma EVM_Xi_of_initial_continue_five_traces_revert_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k l p : Nat}
    {s₁ s₂ s₃ s₄ t evmState : Ethereum.State}
    {o : ByteArray}
    (hFuel : m + n + k + l + p ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ s₃)
    (h₄ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) l s₃ s₄)
    (h₅ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) p s₄ t)
    (hHalt :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t =
        .ok (evmState, some (false, o))) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert evmState.machineState.gasAvailable o) :=
  EVM_Xi_of_initial_continue_trace_revert_of_le
    (n := m + n + k + l + p)
    hFuel
    (Ethereum.EVM.ContinueTrace.append_five h₁ h₂ h₃ h₄ h₅)
    hHalt

lemma EVM_Xi_of_initial_continue_five_traces_revert_zero_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k l p : Nat}
    {s₁ s₂ s₃ s₄ t : Ethereum.State}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hFuel : m + n + k + l + p ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ s₃)
    (h₄ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) l s₃ s₄)
    (h₅ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) p s₄ t)
    (hCode : t.executionEnv.code = I.code)
    (hDecode :
      Ethereum.EVM.decode t.executionEnv.code t.machineState.pc = some (.REVERT, .none))
    (hStack :
      t.machineState.stack =
        (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) :: tail)
    (hStackBound : ¬ 1024 < tail.length) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert
        (Ethereum.EVM.revertNextState t
          (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256) tail).machineState.gasAvailable
        (Ethereum.EVM.revertOutput t
          (⟨0⟩ : Ethereum.UInt256) (⟨0⟩ : Ethereum.UInt256))) :=
  EVM_Xi_of_initial_continue_trace_revert_zero_of_le
    (n := m + n + k + l + p)
    hFuel
    (Ethereum.EVM.ContinueTrace.append_five h₁ h₂ h₃ h₄ h₅)
    hCode
    hDecode
    hStack
    hStackBound

lemma EVM_Xi_of_initial_continue_five_traces_error_of_le
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k l p : Nat}
    {s₁ s₂ s₃ s₄ t : Ethereum.State}
    {e : Ethereum.EVM.ExecutionException}
    (hFuel : m + n + k + l + p ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ s₃)
    (h₄ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) l s₃ s₄)
    (h₅ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) p s₄ t)
    (hErr :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t = .error e) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e :=
  EVM_Xi_of_initial_continue_trace_error_of_le
    (n := m + n + k + l + p)
    hFuel
    (Ethereum.EVM.ContinueTrace.append_five h₁ h₂ h₃ h₄ h₅)
    hErr

lemma EVM_Xi_of_initial_continue_traces_error_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n : Nat}
    {mid t : Ethereum.State}
    {decoded : Option (Ethereum.Operation × Option (Ethereum.UInt256 × Nat))}
    {e : Ethereum.EVM.ExecutionException}
    (hFuel : m + n ≤ g.toNat)
    (hPrefix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) mid)
    (hSuffix :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n mid t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = decoded)
    (hErr :
      Ethereum.EVM.decode t.executionEnv.code t.machineState.pc = decoded →
        Ethereum.EVM.Xstep (Ethereum.EVM.D_J t.executionEnv.code ⟨0⟩) t = .error e) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := m + n)
    hFuel
    (Ethereum.EVM.ContinueTrace.append hPrefix hSuffix)
    hDecode
    hErr

lemma EVM_Xi_of_initial_continue_three_traces_error_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k : Nat}
    {s₁ s₂ t : Ethereum.State}
    {decoded : Option (Ethereum.Operation × Option (Ethereum.UInt256 × Nat))}
    {e : Ethereum.EVM.ExecutionException}
    (hFuel : m + n + k ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = decoded)
    (hErr :
      Ethereum.EVM.decode t.executionEnv.code t.machineState.pc = decoded →
        Ethereum.EVM.Xstep (Ethereum.EVM.D_J t.executionEnv.code ⟨0⟩) t = .error e) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := m + n + k)
    hFuel
    (Ethereum.EVM.ContinueTrace.append_three h₁ h₂ h₃)
    hDecode
    hErr

lemma EVM_Xi_of_initial_continue_four_traces_error_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k l : Nat}
    {s₁ s₂ s₃ t : Ethereum.State}
    {decoded : Option (Ethereum.Operation × Option (Ethereum.UInt256 × Nat))}
    {e : Ethereum.EVM.ExecutionException}
    (hFuel : m + n + k + l ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ s₃)
    (h₄ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) l s₃ t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = decoded)
    (hErr :
      Ethereum.EVM.decode t.executionEnv.code t.machineState.pc = decoded →
        Ethereum.EVM.Xstep (Ethereum.EVM.D_J t.executionEnv.code ⟨0⟩) t = .error e) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := m + n + k + l)
    hFuel
    (Ethereum.EVM.ContinueTrace.append_four h₁ h₂ h₃ h₄)
    hDecode
    hErr

lemma EVM_Xi_of_initial_continue_five_traces_error_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m n k l p : Nat}
    {s₁ s₂ s₃ s₄ t : Ethereum.State}
    {decoded : Option (Ethereum.Operation × Option (Ethereum.UInt256 × Nat))}
    {e : Ethereum.EVM.ExecutionException}
    (hFuel : m + n + k + l + p ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) k s₂ s₃)
    (h₄ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) l s₃ s₄)
    (h₅ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) p s₄ t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = decoded)
    (hErr :
      Ethereum.EVM.decode t.executionEnv.code t.machineState.pc = decoded →
        Ethereum.EVM.Xstep (Ethereum.EVM.D_J t.executionEnv.code ⟨0⟩) t = .error e) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := m + n + k + l + p)
    hFuel
    (Ethereum.EVM.ContinueTrace.append_five h₁ h₂ h₃ h₄ h₅)
    hDecode
    hErr

lemma EVM_Xi_of_initial_continue_ten_traces_error_of_le_of_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ : Nat}
    {s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t : Ethereum.State}
    {decoded : Option (Ethereum.Operation × Option (Ethereum.UInt256 × Nat))}
    {e : Ethereum.EVM.ExecutionException}
    (hFuel :
      ((m₁ + m₂ + m₃ + m₄ + m₅) + (m₆ + m₇ + m₈ + m₉ + m₁₀)) ≤ g.toNat)
    (h₁ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₁
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) s₁)
    (h₂ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₂ s₁ s₂)
    (h₃ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₃ s₂ s₃)
    (h₄ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₄ s₃ s₄)
    (h₅ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₅ s₄ s₅)
    (h₆ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₆ s₅ s₆)
    (h₇ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₇ s₆ s₇)
    (h₈ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₈ s₇ s₈)
    (h₉ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₉ s₈ s₉)
    (h₁₀ :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) m₁₀ s₉ t)
    (hDecode :
      Ethereum.EVM.decode I.code t.machineState.pc = decoded)
    (hErr :
      Ethereum.EVM.decode t.executionEnv.code t.machineState.pc = decoded →
        Ethereum.EVM.Xstep (Ethereum.EVM.D_J t.executionEnv.code ⟨0⟩) t = .error e) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e :=
  EVM_Xi_of_initial_continue_trace_error_of_le_of_decode
    (n := (m₁ + m₂ + m₃ + m₄ + m₅) + (m₆ + m₇ + m₈ + m₉ + m₁₀))
    hFuel
    (Ethereum.EVM.ContinueTrace.append_ten h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀)
    hDecode
    hErr

/-! ## Runtime-equivalence bridges for EVM `RETURN` traces -/

lemma runtimeEquivalenceFor_success_returnNextState
    {cfg : Config} {contract : ContractDecl}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {frame : Frame}
    {retVal : Option Value}
    {returnType : Option ABIType}
    {s : Ethereum.State}
    {offset size g' : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    {A' : Ethereum.Substate}
    {o : ByteArray}
    (hΞ :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .ok (.success
          ((Ethereum.EVM.returnNextState s offset size tail).createdAccounts,
            (Ethereum.EVM.returnNextState s offset size tail).accountMap,
            g', A')
          o))
    (hStateCreated : s.createdAccounts = createdAccounts)
    (hStateAccounts : s.accountMap = σ)
    (hAct :
      actExec cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I
        (.returned frame
          (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
          retVal)
        returnType)
    (hReturn : returnEquiv o retVal returnType) :
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I :=
  runtimeEquivalenceFor_success_initial_of_eq
    hΞ
    (by simpa using hStateCreated)
    (by simpa using hStateAccounts)
    hAct
    hReturn

lemma runtimeEquivalenceFor_success_returnNextState_output
    {cfg : Config} {contract : ContractDecl}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {frame : Frame}
    {retVal : Option Value}
    {returnType : Option ABIType}
    {s : Ethereum.State}
    {offset size : Ethereum.UInt256}
    {tail : Ethereum.Stack Ethereum.UInt256}
    (hΞ :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .ok (.success
          ((Ethereum.EVM.returnNextState s offset size tail).createdAccounts,
            (Ethereum.EVM.returnNextState s offset size tail).accountMap,
            (Ethereum.EVM.returnNextState s offset size tail).machineState.gasAvailable,
            (Ethereum.EVM.returnNextState s offset size tail).substate)
          (Ethereum.EVM.returnOutput s offset size)))
    (hStateCreated : s.createdAccounts = createdAccounts)
    (hStateAccounts : s.accountMap = σ)
    (hAct :
      actExec cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I
        (.returned frame
          (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
          retVal)
        returnType)
    (hReturn : returnEquiv (Ethereum.EVM.returnOutput s offset size) retVal returnType) :
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I :=
  runtimeEquivalenceFor_success_returnNextState
    hΞ
    hStateCreated
    hStateAccounts
    hAct
    hReturn

namespace Act

lemma ExecStmt.require_true_of_eval {cfg : Config} {act : Frame} {evm : EVM.State}
    {condExpr : Expr}
    (hEval : evalExpr? cfg act evm condExpr = .ok (.bool true)) :
    ExecStmt cfg act evm (.require condExpr) (.ok act evm) :=
  ExecStmt.requireTrue hEval

lemma ExecStmt.require_false_of_eval {cfg : Config} {act : Frame} {evm : EVM.State}
    {condExpr : Expr}
    (hEval : evalExpr? cfg act evm condExpr = .ok (.bool false)) :
    ExecStmt cfg act evm (.require condExpr) .reverted :=
  ExecStmt.requireFalse hEval

lemma ExecStmt.require_revert_of_eval {cfg : Config} {act : Frame} {evm : EVM.State}
    {condExpr : Expr}
    (hEval : evalExpr? cfg act evm condExpr = .revert) :
    ExecStmt cfg act evm (.require condExpr) .reverted :=
  ExecStmt.requireRevert hEval

lemma ExecStmt.return_of_eval {cfg : Config} {act : Frame} {evm : EVM.State}
    {expr : Expr} {value : Value}
    (hEval : evalExpr? cfg act evm expr = .ok value) :
    ExecStmt cfg act evm (.return expr) (.returned act evm (some value)) :=
  ExecStmt.return hEval

lemma ExecBlock.cons_ok {cfg : Config} {act act' : Frame} {evm evm' : EVM.State}
    {stmt : Stmt} {stmts : List Stmt} {result : ExecResult}
    (hStmt : ExecStmt cfg act evm stmt (.ok act' evm'))
    (hRest : ExecBlock cfg act' evm' stmts result) :
    ExecBlock cfg act evm (stmt :: stmts) result :=
  ExecBlock.consNormal hStmt hRest

lemma ExecBlock.cons_return {cfg : Config} {act act' : Frame} {evm evm' : EVM.State}
    {stmt : Stmt} {stmts : List Stmt} {value : Option Value}
    (hStmt : ExecStmt cfg act evm stmt (.returned act' evm' value)) :
    ExecBlock cfg act evm (stmt :: stmts) (.returned act' evm' value) :=
  ExecBlock.consReturn hStmt

lemma ExecBlock.cons_revert {cfg : Config} {act : Frame} {evm : EVM.State}
    {stmt : Stmt} {stmts : List Stmt}
    (hStmt : ExecStmt cfg act evm stmt .reverted) :
    ExecBlock cfg act evm (stmt :: stmts) .reverted :=
  ExecBlock.consRevert hStmt

lemma ExecBlock.require_true_then_return {cfg : Config} {act : Frame} {evm : EVM.State}
    {condExpr retExpr : Expr} {value : Value}
    (hCond : evalExpr? cfg act evm condExpr = .ok (.bool true))
    (hRet : evalExpr? cfg act evm retExpr = .ok value) :
    ExecBlock cfg act evm
      [.require condExpr, .return retExpr]
      (.returned act evm (some value)) :=
  ExecBlock.consNormal
    (ExecStmt.require_true_of_eval hCond)
    (ExecBlock.consReturn (ExecStmt.return_of_eval hRet))

lemma ExecBlock.require_false_then_revert {cfg : Config} {act : Frame} {evm : EVM.State}
    {condExpr retExpr : Expr}
    (hCond : evalExpr? cfg act evm condExpr = .ok (.bool false)) :
    ExecBlock cfg act evm [.require condExpr, .return retExpr] .reverted :=
  ExecBlock.consRevert (ExecStmt.require_false_of_eval hCond)

lemma ExecFuncBody.returned_of_block {cfg : Config} {act act' : Frame}
    {evm evm' : EVM.State} {body : List Stmt} {value : Option Value}
    (hBlock : ExecBlock cfg act evm body (.returned act' evm' value)) :
    ExecFuncBody cfg act evm body (.returned act' evm' value) :=
  ExecFuncBody.execBlockRet hBlock

lemma ExecFuncBody.reverted_of_block {cfg : Config} {act : Frame}
    {evm : EVM.State} {body : List Stmt}
    (hBlock : ExecBlock cfg act evm body .reverted) :
    ExecFuncBody cfg act evm body .reverted :=
  ExecFuncBody.execBlockRevert hBlock

lemma ExecFuncBody.fallthrough_of_block_ok {cfg : Config} {act act' : Frame}
    {evm evm' : EVM.State} {body : List Stmt}
    (hBlock : ExecBlock cfg act evm body (.ok act' evm')) :
    ExecFuncBody cfg act evm body (.returned act' evm' none) :=
  ExecFuncBody.execBlockOK hBlock

lemma ExecFuncBody.require_true_then_return {cfg : Config} {act : Frame} {evm : EVM.State}
    {condExpr retExpr : Expr} {value : Value}
    (hCond : evalExpr? cfg act evm condExpr = .ok (.bool true))
    (hRet : evalExpr? cfg act evm retExpr = .ok value) :
    ExecFuncBody cfg act evm
      [.require condExpr, .return retExpr]
      (.returned act evm (some value)) :=
  ExecFuncBody.returned_of_block (ExecBlock.require_true_then_return hCond hRet)

lemma ExecFuncBody.require_false_then_revert {cfg : Config} {act : Frame} {evm : EVM.State}
    {condExpr retExpr : Expr}
    (hCond : evalExpr? cfg act evm condExpr = .ok (.bool false)) :
    ExecFuncBody cfg act evm [.require condExpr, .return retExpr] .reverted :=
  ExecFuncBody.reverted_of_block (ExecBlock.require_false_then_revert hCond)

lemma ExecContractBody.require_true_then_return {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store} {condExpr retExpr : Expr} {value : Value}
    (hCond :
      evalExpr? cfg { contract := contract, locals := locals } evm condExpr =
        .ok (.bool true))
    (hRet :
      evalExpr? cfg { contract := contract, locals := locals } evm retExpr =
        .ok value) :
    ExecContractBody cfg contract evm locals
      [.require condExpr, .return retExpr]
      (.returned { contract := contract, locals := locals } evm (some value)) :=
  ExecFuncBody.require_true_then_return hCond hRet

lemma ExecContractBody.require_false_then_revert {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store} {condExpr retExpr : Expr}
    (hCond :
      evalExpr? cfg { contract := contract, locals := locals } evm condExpr =
        .ok (.bool false)) :
    ExecContractBody cfg contract evm locals [.require condExpr, .return retExpr] .reverted :=
  ExecFuncBody.require_false_then_revert hCond

lemma evalExpr_boolLit {cfg : Config} {act : Frame} {evm : EVM.State} {b : Bool} :
    evalExpr? cfg act evm (.boolLit b) = .ok (.bool b) :=
  by simp [evalExpr?, pure]

lemma evalExpr_intLit {cfg : Config} {act : Frame} {evm : EVM.State} {i : Int} :
    evalExpr? cfg act evm (.intLit i) = .ok (.int i) :=
  by simp [evalExpr?, pure]

lemma evalExpr_callvalue {cfg : Config} {act : Frame} {evm : EVM.State} :
    evalExpr? cfg act evm (.env .callvalue) =
      .ok (.int (Int.ofNat evm.executionEnv.weiValue.val)) :=
  by simp [evalExpr?, envValue, pure]

lemma evalExpr_callvalue_eq_zero_of_weiValue_zero
    {cfg : Config} {act : Frame} {evm : EVM.State}
    (hValue : evm.executionEnv.weiValue = (⟨0⟩ : Ethereum.UInt256)) :
    evalExpr? cfg act evm (.binary .eq (.env .callvalue) (.intLit 0)) =
      .ok (.bool true) := by
  have hNat : evm.executionEnv.weiValue.val.val = 0 := by
    exact congrArg (fun x : Ethereum.UInt256 => x.val.val) hValue
  simp [evalExpr?, envValue, evalBinaryOp?, pure, bind, EvalResult.bind, hNat]

lemma evalExpr_callvalue_eq_zero_of_weiValue_ne_zero
    {cfg : Config} {act : Frame} {evm : EVM.State}
    (hValue : evm.executionEnv.weiValue ≠ (⟨0⟩ : Ethereum.UInt256)) :
    evalExpr? cfg act evm (.binary .eq (.env .callvalue) (.intLit 0)) =
      .ok (.bool false) := by
  have hNat : evm.executionEnv.weiValue.val.val ≠ 0 :=
    Ethereum.UInt256.val_val_ne_zero_of_ne_zero hValue
  simp [evalExpr?, envValue, evalBinaryOp?, pure, bind, EvalResult.bind, hNat]

end Act
