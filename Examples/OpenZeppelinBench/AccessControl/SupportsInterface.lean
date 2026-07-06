import Examples.OpenZeppelinBench.AccessControl.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
set_option linter.unnecessarySimpa false

namespace OpenZeppelinBench.AccessControl

/-!
# AccessControl `supportsInterface(bytes4)` proof

The body is a pure ERC165 check:
`interfaceId == 0x7965db0b || interfaceId == 0x01ffc9a7`.
-/

abbrev supportsInterfaceWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev supportsInterfaceBytes (I : ExecutionEnv) : List UInt8 :=
  ((I.calldata.toList.drop 4).take 32).take 4

abbrev supportsInterfaceStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "interfaceId" (.fixedBytes bytes4Width (supportsInterfaceBytes I))

abbrev supportsInterfaceMask : UInt256 :=
  UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩) ⟨1⟩)

abbrev iaccessControlIdWord : UInt256 :=
  UInt256.shiftLeft (⟨0x7965db0b⟩ : UInt256) ⟨224⟩

abbrev ierc165IdWord : UInt256 :=
  UInt256.shiftLeft (⟨0x01ffc9a7⟩ : UInt256) ⟨224⟩

abbrev supportsInterfaceResult (I : ExecutionEnv) : Bool :=
  (supportsInterfaceBytes I == [0x79, 0x65, 0xdb, 0x0b]) ||
    (supportsInterfaceBytes I == [0x01, 0xff, 0xc9, 0xa7])

abbrev supportsInterfaceResultWord (I : ExecutionEnv) : UInt256 :=
  if supportsInterfaceResult I then ⟨1⟩ else ⟨0⟩

theorem accessControlListUInt8_decide_eq_beq (xs ys : List UInt8) :
    decide (xs = ys) = (xs == ys) := by
  by_cases h : xs = ys
  · subst ys
    simp
  · have hbeq : (xs == ys) = false := by
      apply Bool.eq_false_iff.mpr
      intro hb
      exact h (eq_of_beq hb)
    simp [h, hbeq]

theorem accessControlFixedBytes4_beq (xs ys : List UInt8) :
    (Value.fixedBytes bytes4Width xs == Value.fixedBytes bytes4Width ys) = (xs == ys) := by
  simp [BEq.beq, accessControlListUInt8_decide_eq_beq]

theorem accessControlFromBytesBigEndian_append (a b : List UInt8) :
    fromBytesBigEndian (a ++ b) =
      fromBytesBigEndian a * 2 ^ (8 * b.length) + fromBytesBigEndian b := by
  unfold fromBytesBigEndian Function.comp
  rw [List.reverse_append, fromBytes'_append, List.length_reverse]
  ring

theorem accessControlFromBytesBigEndian_bound (xs : List UInt8) :
    fromBytesBigEndian xs < 2 ^ (8 * xs.length) := by
  unfold fromBytesBigEndian Function.comp
  simpa [List.length_reverse] using (fromBytes'_le (bs := xs.reverse))

theorem accessControlFromBytes'_zero_iff_all_zero (xs : List UInt8) :
    fromBytes' xs = 0 ↔ xs.all (· == 0) = true := by
  induction xs with
  | nil => simp [fromBytes']
  | cons x xs ih =>
      constructor
      · intro h
        simp only [List.all_cons, Bool.and_eq_true]
        unfold fromBytes' at h
        have hxnat : x.toNat = 0 := (Nat.add_eq_zero_iff.mp h).1
        have htail : fromBytes' xs = 0 := by
          have hprod : UInt8.size * fromBytes' xs = 0 := (Nat.add_eq_zero_iff.mp h).2
          have hsize : 0 < UInt8.size := by decide
          omega
        have hx : x = 0 := UInt8.toNat_inj.mp hxnat
        exact ⟨by simpa [hx], ih.mp htail⟩
      · intro h
        simp only [List.all_cons, Bool.and_eq_true] at h
        rcases h with ⟨hx, hxs⟩
        have hx0 : x = 0 := eq_of_beq hx
        unfold fromBytes'
        simp [hx0, ih.mpr hxs]

theorem accessControlFromBytesBigEndian_zero_iff_all_zero (xs : List UInt8) :
    fromBytesBigEndian xs = 0 ↔ xs.all (· == 0) = true := by
  unfold fromBytesBigEndian Function.comp
  rw [accessControlFromBytes'_zero_iff_all_zero]
  simp

theorem accessControlBytesToWord_toNat_of_len (xs : List UInt8) (hlen : xs.length = 32) :
    (ABI.bytesToWord xs).toNat = fromBytesBigEndian xs := by
  unfold ABI.bytesToWord fromByteArrayBigEndian
  rw [ulit_toNat']
  · simp [byteArray_toList_eq]
  · change fromByteArrayBigEndian { data := xs.toArray } < UInt256.size
    unfold fromByteArrayBigEndian
    simp [byteArray_toList_eq]
    rw [show UInt256.size = 2 ^ (8 * xs.length) by rw [hlen]; rfl]
    exact accessControlFromBytesBigEndian_bound xs

theorem supportsInterfaceWord_toNat {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (supportsInterfaceWord I).toNat =
      fromBytesBigEndian ((I.calldata.toList.drop 4).take 32) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword :
      ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) = supportsInterfaceWord I := by
    simpa [supportsInterfaceWord, calldataWord] using
      decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  rw [← hword]
  exact accessControlBytesToWord_toNat_of_len _ hlen

theorem accessControlTestBit_shiftLeft (m k i : Nat) :
    (m <<< k).testBit i = if i < k then false else m.testBit (i - k) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
      rw [← Nat.shiftLeft'_false (m := m) (n := k + 1)]
      change (Nat.bit false (Nat.shiftLeft' false m k)).testBit i = _
      cases i with
      | zero => simp
      | succ i =>
          rw [Nat.testBit_bit_succ, Nat.shiftLeft'_false, ih]
          by_cases hi : i < k
          · have his : i.succ < k.succ := Nat.succ_lt_succ hi
            simp [his, hi]
          · have hns : ¬ i.succ < k.succ := by omega
            simp [hns, hi]

theorem accessControlDivPow224_testBit (n i : Nat) (h224 : 224 ≤ i) :
    (n / 2 ^ 224).testBit (i - 224) = n.testBit i := by
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul]
  change n / (2 ^ 224 * 2 ^ (i - 224)) % 2 = 1 ↔ n / 2 ^ i % 2 = 1
  rw [← Nat.pow_add, show 224 + (i - 224) = i by omega]

theorem accessControlNatLandClearLow224 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n ((2 : Nat) ^ 256 - 2 ^ 224) = (n / 2 ^ 224) * 2 ^ 224 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& ((2 : Nat) ^ 256 - 2 ^ 224)).testBit i =
    ((n / 2 ^ 224) * 2 ^ 224).testBit i
  rw [Nat.testBit_and]
  rw [show (2 : Nat) ^ 256 - 2 ^ 224 = (2 ^ 32 - 1) <<< 224 by
    rw [Nat.shiftLeft_eq]
    norm_num [Nat.pow_add]]
  rw [accessControlTestBit_shiftLeft]
  rw [show (n / 2 ^ 224) * 2 ^ 224 = (n / 2 ^ 224) <<< 224 by
    rw [Nat.shiftLeft_eq]]
  rw [accessControlTestBit_shiftLeft]
  by_cases hi224 : i < 224
  · simp [hi224]
  · simp [hi224]
    have h224 : 224 ≤ i := Nat.le_of_not_gt hi224
    by_cases hi256 : i < 256
    · have hlt : i - 224 < 32 := by omega
      change (n.testBit i && (((2 : Nat) ^ 32 - 1).testBit (i - 224))) =
        (n / 2 ^ 224).testBit (i - 224)
      rw [Nat.testBit_two_pow_sub_one]
      simp [hlt]
      exact (accessControlDivPow224_testBit n i h224).symm
    · have hnlt : ¬ i - 224 < 32 := by omega
      change (n.testBit i && (((2 : Nat) ^ 32 - 1).testBit (i - 224))) =
        (n / 2 ^ 224).testBit (i - 224)
      rw [Nat.testBit_two_pow_sub_one]
      simp [hnlt]
      change (n / 2 ^ 224).testBit (i - 224) = false
      have hq : n / 2 ^ 224 < 2 ^ 32 := by
        apply Nat.div_lt_of_lt_mul
        rw [show 2 ^ 224 * 2 ^ 32 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
        exact hn
      have hpow : n / 2 ^ 224 < 2 ^ (i - 224) := by
        exact lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact Nat.testBit_lt_two_pow hpow

theorem supportsInterfaceMask_toNat :
    supportsInterfaceMask.toNat = 2 ^ 256 - 2 ^ 224 := by
  decide

theorem supportsInterfaceClean_of_mod_zero (w : UInt256)
    (hmod : w.toNat % 2 ^ 224 = 0) :
    UInt256.land w supportsInterfaceMask = w := by
  apply u256_inj
  show Nat.land w.toNat supportsInterfaceMask.toNat % UInt256.size = w.toNat
  rw [supportsInterfaceMask_toNat]
  rw [accessControlNatLandClearLow224 w.toNat (by exact w.val.isLt)]
  have hdiv := Nat.div_add_mod w.toNat (2 ^ 224)
  rw [show w.toNat / 2 ^ 224 * 2 ^ 224 = w.toNat by omega]
  exact Nat.mod_eq_of_lt w.val.isLt

theorem supportsInterfaceModZero_of_padding {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = some ()) :
    (supportsInterfaceWord I).toNat % 2 ^ 224 = 0 := by
  let xs := (I.calldata.toList.drop 4).take 32
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hxsLen : xs.length = 32 := by
    dsimp [xs]
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htailLen : (xs.drop 4).length = 28 := by
    rw [List.length_drop, hxsLen]
  have htailTake : (xs.drop 4).take 28 = xs.drop 4 :=
    List.take_of_length_le (by rw [htailLen])
  have htailAll : (xs.drop 4).all (· == 0) = true := by
    unfold zeroPadding? readBytes? at hpad
    have hlen : ((xs.drop 4).take 28).length = 28 := by rw [htailTake, htailLen]
    rw [if_pos hlen] at hpad
    rw [htailTake] at hpad
    by_cases hall : (xs.drop 4).all (· == 0) = true
    · exact hall
    · simp [hall] at hpad
      simpa using hpad
  have htailZero : fromBytesBigEndian (xs.drop 4) = 0 :=
    (accessControlFromBytesBigEndian_zero_iff_all_zero (xs.drop 4)).mpr htailAll
  have hword := supportsInterfaceWord_toNat (I := I) hsz36
  rw [hword]
  change fromBytesBigEndian xs % 2 ^ 224 = 0
  rw [show xs = xs.take 4 ++ xs.drop 4 from (List.take_append_drop 4 xs).symm]
  rw [accessControlFromBytesBigEndian_append, htailLen, htailZero]
  rw [show 8 * 28 = 224 by norm_num, Nat.add_zero]
  exact Nat.mul_mod_left _ _

theorem supportsInterfaceEqOne_of_padding {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = some ()) :
    UInt256.eq (supportsInterfaceWord I)
      (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask) = ⟨1⟩ := by
  have hclean :
      UInt256.land (supportsInterfaceWord I) supportsInterfaceMask = supportsInterfaceWord I :=
    supportsInterfaceClean_of_mod_zero _
      (supportsInterfaceModZero_of_padding hsz36 hpad)
  rw [hclean]
  exact uInt256_eq_self _

theorem supportsInterfaceModNeZero_of_padding_none {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = none) :
    (supportsInterfaceWord I).toNat % 2 ^ 224 ≠ 0 := by
  let xs := (I.calldata.toList.drop 4).take 32
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hxsLen : xs.length = 32 := by
    dsimp [xs]
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htailLen : (xs.drop 4).length = 28 := by
    rw [List.length_drop, hxsLen]
  have htailTake : (xs.drop 4).take 28 = xs.drop 4 :=
    List.take_of_length_le (by rw [htailLen])
  have htailAllFalse : (xs.drop 4).all (· == 0) = false := by
    unfold zeroPadding? readBytes? at hpad
    have hlen : ((xs.drop 4).take 28).length = 28 := by rw [htailTake, htailLen]
    rw [if_pos hlen] at hpad
    rw [htailTake] at hpad
    by_cases hall : (xs.drop 4).all (· == 0) = true
    · simp [hall] at hpad
      exfalso
      rcases hpad with ⟨x, hxmem, hxne⟩
      have hallProp : ∀ x ∈ xs.drop 4, x = 0 := by simpa using hall
      exact hxne (hallProp x hxmem)
    · exact Bool.eq_false_iff.mpr hall
  have htailNZ : fromBytesBigEndian (xs.drop 4) ≠ 0 := by
    intro hz
    have hall := (accessControlFromBytesBigEndian_zero_iff_all_zero (xs.drop 4)).mp hz
    rw [hall] at htailAllFalse
    contradiction
  have htailBound : fromBytesBigEndian (xs.drop 4) < 2 ^ 224 := by
    have hb := accessControlFromBytesBigEndian_bound (xs.drop 4)
    rw [htailLen] at hb
    simpa using hb
  have hword := supportsInterfaceWord_toNat (I := I) hsz36
  rw [hword]
  change fromBytesBigEndian xs % 2 ^ 224 ≠ 0
  rw [show xs = xs.take 4 ++ xs.drop 4 from (List.take_append_drop 4 xs).symm]
  rw [accessControlFromBytesBigEndian_append, htailLen]
  intro hmod
  have htailMod : fromBytesBigEndian (xs.drop 4) % 2 ^ 224 = 0 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmod
  have htailZero : fromBytesBigEndian (xs.drop 4) = 0 := by
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (by omega))
  exact htailNZ htailZero

theorem supportsInterfaceModZero_of_land_eq (w : UInt256)
    (hclean : UInt256.land w supportsInterfaceMask = w) :
    w.toNat % 2 ^ 224 = 0 := by
  have ht := congrArg UInt256.toNat hclean
  change Nat.land w.toNat supportsInterfaceMask.toNat % UInt256.size = w.toNat at ht
  rw [supportsInterfaceMask_toNat] at ht
  have hclear := accessControlNatLandClearLow224 w.toNat (by exact w.val.isLt)
  rw [hclear] at ht
  have hsmall : w.toNat / 2 ^ 224 * 2 ^ 224 < UInt256.size :=
    lt_of_le_of_lt (by
      simpa [Nat.mul_comm] using Nat.mul_div_le w.toNat (2 ^ 224)) w.val.isLt
  rw [Nat.mod_eq_of_lt hsmall] at ht
  have hdiv := Nat.div_add_mod w.toNat (2 ^ 224)
  omega

theorem accessControlUInt256_eq_one_eq {a b : UInt256}
    (h : UInt256.eq a b = ⟨1⟩) : a = b :=
  Reasoning.Theory.uInt256_eq_one_eq h

theorem supportsInterfaceEqZero_of_padding_none {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = none) :
    UInt256.eq (supportsInterfaceWord I)
      (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask) = ⟨0⟩ := by
  apply uInt256_eq_zero_of_ne
  intro heq
  have hword :
      supportsInterfaceWord I =
        UInt256.land (supportsInterfaceWord I) supportsInterfaceMask :=
    accessControlUInt256_eq_one_eq heq
  exact (supportsInterfaceModNeZero_of_padding_none hsz36 hpad)
    (supportsInterfaceModZero_of_land_eq _ hword.symm)

theorem supportsInterfaceMaskedWord_toNat {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask).toNat =
      fromBytesBigEndian (supportsInterfaceBytes I) * 2 ^ 224 := by
  let xs := (I.calldata.toList.drop 4).take 32
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hxsLen : xs.length = 32 := by
    dsimp [xs]
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htailLen : (xs.drop 4).length = 28 := by rw [List.length_drop, hxsLen]
  have htailBound : fromBytesBigEndian (xs.drop 4) < 2 ^ 224 := by
    have hb := accessControlFromBytesBigEndian_bound (xs.drop 4)
    rw [htailLen] at hb
    simpa using hb
  have hxsBound : fromBytesBigEndian xs < 2 ^ 256 := by
    have hb := accessControlFromBytesBigEndian_bound xs
    rw [hxsLen] at hb
    simpa using hb
  have hword := supportsInterfaceWord_toNat (I := I) hsz36
  change Nat.land (supportsInterfaceWord I).toNat supportsInterfaceMask.toNat % UInt256.size = _
  rw [hword]
  change Nat.land (fromBytesBigEndian xs) supportsInterfaceMask.toNat % UInt256.size =
    fromBytesBigEndian (xs.take 4) * 2 ^ 224
  rw [supportsInterfaceMask_toNat]
  rw [accessControlNatLandClearLow224 (fromBytesBigEndian xs) hxsBound]
  have hsplit :
      fromBytesBigEndian xs =
        fromBytesBigEndian (xs.take 4) * 2 ^ 224 + fromBytesBigEndian (xs.drop 4) := by
    calc
      fromBytesBigEndian xs =
          fromBytesBigEndian (xs.take 4 ++ xs.drop 4) := by
        exact congrArg fromBytesBigEndian (List.take_append_drop 4 xs).symm
      _ = fromBytesBigEndian (xs.take 4) * 2 ^ 224 + fromBytesBigEndian (xs.drop 4) := by
        rw [accessControlFromBytesBigEndian_append, htailLen]
  rw [hsplit]
  have hdiv :
      (fromBytesBigEndian (xs.take 4) * 2 ^ 224 + fromBytesBigEndian (xs.drop 4)) /
          2 ^ 224 = fromBytesBigEndian (xs.take 4) := by
    omega
  rw [hdiv]
  have hheadBound : fromBytesBigEndian (xs.take 4) < 2 ^ 32 := by
    have hb := accessControlFromBytesBigEndian_bound (xs.take 4)
    have hheadLen : (xs.take 4).length = 4 := by rw [List.length_take, hxsLen]; rfl
    rw [hheadLen] at hb
    simpa using hb
  have hprodLt : fromBytesBigEndian (xs.take 4) * 2 ^ 224 < UInt256.size := by
    have hlt : fromBytesBigEndian (xs.take 4) * 2 ^ 224 < 2 ^ 32 * 2 ^ 224 :=
      Nat.mul_lt_mul_of_pos_right hheadBound (by positivity)
    simpa [UInt256.size, Nat.pow_add] using hlt
  rw [Nat.mod_eq_of_lt hprodLt]

theorem supportsInterfaceBytes_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (supportsInterfaceBytes I).length = 4 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  simp [supportsInterfaceBytes, List.length_take, List.length_drop, htlen]
  omega

theorem iaccessControlIdWord_toNat :
    iaccessControlIdWord.toNat = fromBytesBigEndian [0x79, 0x65, 0xdb, 0x0b] * 2 ^ 224 := by
  decide

theorem ierc165IdWord_toNat :
    ierc165IdWord.toNat = fromBytesBigEndian [0x01, 0xff, 0xc9, 0xa7] * 2 ^ 224 := by
  decide

theorem supportsInterfaceEq_accessControl {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    UInt256.eq iaccessControlIdWord
        (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask) =
      if (supportsInterfaceBytes I == [0x79, 0x65, 0xdb, 0x0b]) then ⟨1⟩ else ⟨0⟩ := by
  by_cases h : supportsInterfaceBytes I = [0x79, 0x65, 0xdb, 0x0b]
  · have hbeq : (supportsInterfaceBytes I == [0x79, 0x65, 0xdb, 0x0b]) = true := by
      rw [h]
      decide
    rw [hbeq]
    have heq :
        iaccessControlIdWord =
          UInt256.land (supportsInterfaceWord I) supportsInterfaceMask := by
      apply u256_inj
      rw [iaccessControlIdWord_toNat, supportsInterfaceMaskedWord_toNat hsz36, h]
    rw [heq]
    exact uInt256_eq_self _
  · have hbeq : (supportsInterfaceBytes I == [0x79, 0x65, 0xdb, 0x0b]) = false := by
      apply Bool.eq_false_iff.mpr
      intro hb
      exact h (eq_of_beq hb)
    rw [hbeq]
    apply uInt256_eq_zero_of_ne
    intro heq1
    have heq :
        iaccessControlIdWord =
          UInt256.land (supportsInterfaceWord I) supportsInterfaceMask := by
      by_contra hne
      simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256, hne, decide_false,
        Bool.false_eq_true, ↓reduceIte] at heq1
      exact absurd heq1 (by decide)
    have hn :
        fromBytesBigEndian (supportsInterfaceBytes I) =
          fromBytesBigEndian [0x79, 0x65, 0xdb, 0x0b] := by
      have ht := congrArg UInt256.toNat heq
      rw [iaccessControlIdWord_toNat, supportsInterfaceMaskedWord_toNat hsz36] at ht
      omega
    exact h (fromBytesBigEndian_inj4 (supportsInterfaceBytes_length hsz36) rfl hn)

theorem supportsInterfaceEq_erc165 {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    UInt256.eq ierc165IdWord
        (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask) =
      if (supportsInterfaceBytes I == [0x01, 0xff, 0xc9, 0xa7]) then ⟨1⟩ else ⟨0⟩ := by
  by_cases h : supportsInterfaceBytes I = [0x01, 0xff, 0xc9, 0xa7]
  · have hbeq : (supportsInterfaceBytes I == [0x01, 0xff, 0xc9, 0xa7]) = true := by
      rw [h]
      decide
    rw [hbeq]
    have heq :
        ierc165IdWord =
          UInt256.land (supportsInterfaceWord I) supportsInterfaceMask := by
      apply u256_inj
      rw [ierc165IdWord_toNat, supportsInterfaceMaskedWord_toNat hsz36, h]
    rw [heq]
    exact uInt256_eq_self _
  · have hbeq : (supportsInterfaceBytes I == [0x01, 0xff, 0xc9, 0xa7]) = false := by
      apply Bool.eq_false_iff.mpr
      intro hb
      exact h (eq_of_beq hb)
    rw [hbeq]
    apply uInt256_eq_zero_of_ne
    intro heq1
    have heq :
        ierc165IdWord =
          UInt256.land (supportsInterfaceWord I) supportsInterfaceMask := by
      by_contra hne
      simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256, hne, decide_false,
        Bool.false_eq_true, ↓reduceIte] at heq1
      exact absurd heq1 (by decide)
    have hn :
        fromBytesBigEndian (supportsInterfaceBytes I) =
          fromBytesBigEndian [0x01, 0xff, 0xc9, 0xa7] := by
      have ht := congrArg UInt256.toNat heq
      rw [ierc165IdWord_toNat, supportsInterfaceMaskedWord_toNat hsz36] at ht
      omega
    exact h (fromBytesBigEndian_inj4 (supportsInterfaceBytes_length hsz36) rfl hn)

theorem supportsInterfaceResultWord_norm (I : ExecutionEnv) :
    UInt256.isZero (UInt256.isZero (supportsInterfaceResultWord I)) =
      supportsInterfaceResultWord I := by
  by_cases h : supportsInterfaceResult I <;> simp [supportsInterfaceResultWord, h] <;> decide

theorem supportsInterfaceSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x01, 0xff, 0xc9, 0xa7]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x01, 0xff, 0xc9, 0xa7]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem accessControlDispatch_supportsInterface {cd : ByteArray}
    (hsel : ((⟨#[0x01, 0xff, 0xc9, 0xa7]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some supportsInterfaceTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x01, 0xff, 0xc9, 0xa7]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [defaultAdminRoleTransition, getRoleAdminTransition, grantRoleTransition,
      hasRoleTransition, renounceRoleTransition, revokeRoleTransition])
    (post := []) rfl rfl ?_ (by rw [selectorOf, supportsInterfaceSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, defaultAdminRoleSelectorBytes, hcd]; decide
  · rw [selectorOf, getRoleAdminSelectorBytes, hcd]; decide
  · rw [selectorOf, grantRoleSelectorBytes, hcd]; decide
  · rw [selectorOf, hasRoleSelectorBytes, hcd]; decide
  · rw [selectorOf, renounceRoleSelectorBytes, hcd]; decide
  · rw [selectorOf, revokeRoleSelectorBytes, hcd]; decide

theorem accessControlDecode_supportsInterface_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = some ()) :
    decodeCalldata (supportsInterfaceTransition.params.map Param.name)
      (transitionSignature supportsInterfaceTransition).paramTypes I.calldata =
        some (supportsInterfaceStore I) := by
  show decodeCalldata ["interfaceId"] [bytes4] I.calldata = some (supportsInterfaceStore I)
  simpa [supportsInterfaceStore, supportsInterfaceBytes, calldataBytes4Arg, bytes4, bytes4Width,
    abiBytes4, abiBytes4Width] using
    decodeCalldata_bytes4_ok (cd := I.calldata) (x := "interfaceId") hsz36 hbig hpad

theorem accessControlDecode_supportsInterface_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (supportsInterfaceTransition.params.map Param.name)
      (transitionSignature supportsInterfaceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["interfaceId"] [bytes4] I.calldata = none
  simpa [bytes4, bytes4Width, abiBytes4, abiBytes4Width] using
    decodeCalldata_bytes4_none_short (cd := I.calldata) (x := "interfaceId") hsz4 hshort

theorem accessControlDecode_supportsInterface_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (supportsInterfaceTransition.params.map Param.name)
      (transitionSignature supportsInterfaceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["interfaceId"] [bytes4] I.calldata = none
  simpa [bytes4, bytes4Width, abiBytes4, abiBytes4Width] using
    decodeCalldata_bytes4_none_huge (cd := I.calldata) (x := "interfaceId") hbig

theorem accessControlDecode_supportsInterface_none_pad {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = none) :
    decodeCalldata (supportsInterfaceTransition.params.map Param.name)
      (transitionSignature supportsInterfaceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["interfaceId"] [bytes4] I.calldata = none
  simpa [bytes4, bytes4Width, abiBytes4, abiBytes4Width] using
    decodeCalldata_bytes4_none_pad (cd := I.calldata) (x := "interfaceId") hsz36 hbig hpad

theorem accessControlSupportsInterfaceBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (supportsInterfaceStore I)
      supportsInterfaceTransition.body
      (.returned { contract := contract, locals := supportsInterfaceStore I } evm
        (some [(.bool (supportsInterfaceResult I))])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns ?_
  by_cases hac : supportsInterfaceBytes I == [0x79, 0x65, 0xdb, 0x0b]
  · simp [supportsInterfaceStore, supportsInterfaceResult, iaccessControlId, ierc165Id, evalExpr?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, evalBinaryOp?,
      accessControlFixedBytes4_beq, hac]
  · simp [supportsInterfaceStore, supportsInterfaceResult, iaccessControlId, ierc165Id, evalExpr?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, evalBinaryOp?,
      accessControlFixedBytes4_beq, hac]

theorem accessControlSupportsInterfaceX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨126⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨853⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨140⟩, ⟨145⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push2 ⟨145⟩, push2 ⟨140⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨853⟩, jump (by jump_dest) ]⟩

theorem accessControlSupportsInterfaceX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = some ())
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨126⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨299⟩
      [supportsInterfaceWord I, ⟨145⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  have hclean : UInt256.eq (supportsInterfaceWord I)
      (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask) = ⟨1⟩ :=
    supportsInterfaceEqOne_of_padding hsz36 hpad
  obtain ⟨_, _, rd853⟩ := accessControlSupportsInterfaceX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact ⟨_, _, evm_run rd853 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨869⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub,
    not, dup2, and, dup2, eq, push2 ⟨892⟩,
    jumpiT (by
      change UInt256.eq (supportsInterfaceWord I)
        (UInt256.land (supportsInterfaceWord I)
          (UInt256.lnot
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩) ⟨1⟩))) ≠ ⟨0⟩
      rw [show UInt256.lnot
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩) ⟨1⟩) =
        supportsInterfaceMask from rfl, hclean]
      decide) (by jump_dest),
    jumpdest, swap4, swap3, pop, pop, pop, jump (by jump_dest),
    jumpdest, push2 ⟨299⟩, jump (by jump_dest) ]⟩

theorem accessControlReturnBool145 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {val : UInt256}
    (h : RD accessControlBenchBytecode ee g s0 ⟨145⟩ (val :: R) solcFreePtrMem
        (UInt256.ofNat 3) rdata acc k C)
    (hnorm : UInt256.isZero (UInt256.isZero val) = val)
    (hov : R.length + 8 ≤ 1024) :
    RDret accessControlBenchBytecode g s0 acc (UInt256.toByteArray val) := by
  exact evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 6 (solcReturnMem val) (UInt256.ofNat 5) (by decide)
      mem_cost (by rw [hnorm]; rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (solcReturnMem_mload64 val) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray val) (by decide)
      mem_cost
      (by
        rw [show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32
          from by decide]
        exact solcReturnMem_read128 val)
      (by evm_ov) ]

theorem accessControlSupportsInterfaceX_body {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨299⟩
      [supportsInterfaceWord I, ⟨145⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨145⟩
      [supportsInterfaceResultWord I, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd299⟩ := hreach
  have hmask :
      UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩) ⟨1⟩) =
        supportsInterfaceMask := rfl
  have hac := supportsInterfaceEq_accessControl (I := I) hsz36
  have herc := supportsInterfaceEq_erc165 (I := I) hsz36
  by_cases hAC : (supportsInterfaceBytes I == [0x79, 0x65, 0xdb, 0x0b]) = true
  · have hACeq : UInt256.eq iaccessControlIdWord
        (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask) = ⟨1⟩ := by
      simpa [hAC] using hac
    have hresult : supportsInterfaceResultWord I = ⟨1⟩ := by
      simp [supportsInterfaceResultWord, supportsInterfaceResult, hAC]
    have rd347 := evm_run rd299 with [
      jumpdest, push0, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub, not,
      dup3, and, push4 ⟨0x7965db0b⟩, push1 ⟨224⟩, shl, eq, dup1, push2 ⟨347⟩,
      jumpiT (by
        change UInt256.eq iaccessControlIdWord
          (UInt256.land (supportsInterfaceWord I)
            (UInt256.lnot
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩) ⟨1⟩))) ≠ ⟨0⟩
        rw [hmask, hACeq]
        decide) (by jump_dest) ]
    exact ⟨_, _, by
      simpa [hresult, hmask, hACeq, iaccessControlIdWord] using evm_run rd347 with [
        jumpdest, swap3, swap2, pop, pop, jump (by jump_dest) ]⟩
  · have hACfalse : (supportsInterfaceBytes I == [0x79, 0x65, 0xdb, 0x0b]) = false :=
      Bool.eq_false_iff.mpr hAC
    have hACeq : UInt256.eq iaccessControlIdWord
        (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask) = ⟨0⟩ := by
      simpa [hACfalse] using hac
    have rd326 := evm_run rd299 with [
      jumpdest, push0, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub, not,
      dup3, and, push4 ⟨0x7965db0b⟩, push1 ⟨224⟩, shl, eq, dup1, push2 ⟨347⟩,
      jumpiNT (by
        change UInt256.eq iaccessControlIdWord
          (UInt256.land (supportsInterfaceWord I)
            (UInt256.lnot
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩) ⟨1⟩))) = ⟨0⟩
        rw [hmask, hACeq]) ]
    have rd347 := evm_run rd326 with [
      pop, push4 ⟨0x01ffc9a7⟩, push1 ⟨224⟩, shl, push1 ⟨1⟩, push1 ⟨1⟩,
      push1 ⟨224⟩, shl, sub, not, dup4, and, eq ]
    have hresult :
        UInt256.eq ierc165IdWord
            (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask) =
          supportsInterfaceResultWord I := by
      by_cases h165 : (supportsInterfaceBytes I == [0x01, 0xff, 0xc9, 0xa7]) = true
      · simp [supportsInterfaceResultWord, supportsInterfaceResult, hACfalse, h165] at *
        simpa [h165] using herc
      · have h165false :
            (supportsInterfaceBytes I == [0x01, 0xff, 0xc9, 0xa7]) = false :=
          Bool.eq_false_iff.mpr h165
        simp [supportsInterfaceResultWord, supportsInterfaceResult, hACfalse, h165false] at *
        simpa [h165false] using herc
    have hresultRev :
        UInt256.eq (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask) ierc165IdWord =
          supportsInterfaceResultWord I := by
      rw [uInt256_eq_comm, hresult]
    exact ⟨_, _, by
      simpa [hmask, hresultRev, ierc165IdWord] using evm_run rd347 with [
        jumpdest, swap3, swap2, pop, pop, jump (by jump_dest) ]⟩

theorem accessControlX_supportsInterface {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = some ())
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨126⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (supportsInterfaceResultWord I)) := by
  obtain ⟨_, _, rd299⟩ := accessControlSupportsInterfaceX_decoded (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hpad hreach
  obtain ⟨_, _, rd145⟩ := accessControlSupportsInterfaceX_body (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 ⟨_, _, rd299⟩
  exact accessControlReturnBool145 rd145 (supportsInterfaceResultWord_norm I) (by evm_ov)

theorem accessControlSupportsInterfaceX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨126⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  obtain ⟨_, _, rd853⟩ := accessControlSupportsInterfaceX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd853 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨869⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem accessControlSupportsInterfaceX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (_hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨126⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  obtain ⟨_, _, rd853⟩ := accessControlSupportsInterfaceX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd853 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨869⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem accessControlSupportsInterfaceX_badpad {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = none)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨126⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  have hclean : UInt256.eq (supportsInterfaceWord I)
      (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask) = ⟨0⟩ :=
    supportsInterfaceEqZero_of_padding_none hsz36 hpad
  obtain ⟨_, _, rd853⟩ := accessControlSupportsInterfaceX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd853 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨869⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub,
    not, dup2, and, dup2, eq, push2 ⟨892⟩,
    jumpiNT (by
      change UInt256.eq (supportsInterfaceWord I)
        (UInt256.land (supportsInterfaceWord I)
          (UInt256.lnot
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩) ⟨1⟩))) = ⟨0⟩
      simpa [supportsInterfaceMask, hclean]),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem accessControlSupportsInterfaceBody {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = accessControlBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x01, 0xff, 0xc9, 0xa7]⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨126⟩
      [accessControlSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hperm : I.perm = true := hperm
  have hsz4 := supportsInterfaceSelector_size (by simpa [selIs] using hsel)
  have hd := accessControlDispatch_supportsInterface (cd := I.calldata) (by
    simpa [selIs] using hsel)
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · cases hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 with
      | none =>
          have hdec := accessControlDecode_supportsInterface_none_pad
            (I := I) hsz36 hbig hpad
          exact (accessControlSupportsInterfaceX_badpad (g := Sat256.ofUInt256 g)
              hsz36 hsize hbig hpad hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      | some _ =>
          have hpadSome :
              zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = some () := by
            simpa using hpad
          have hdec := accessControlDecode_supportsInterface_ok
            (I := I) hsz36 hbig hpadSome
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (supportsInterfaceStore I)
                supportsInterfaceTransition.body
                (.returned { contract := contract, locals := supportsInterfaceStore I }
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (some [(.bool (supportsInterfaceResult I))])) := by
            exact accessControlSupportsInterfaceBodyReturns
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv)
          exact (accessControlX_supportsInterface (g := Sat256.ofUInt256 g)
              hsz36 hsize hbig hpadSome hreach)
            |>.reEquivExecutionTransport hcode hd hdec hbody rfl hAccounts
              (returnEquiv_of_encode (by
                by_cases hr : supportsInterfaceResult I
                · simpa [supportsInterfaceResultWord, hr] using boolTrueReturnEncodingAC
                · simpa [boolTy, supportsInterfaceResultWord, hr] using boolFalseReturnEncoding))
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := accessControlDecode_supportsInterface_none_huge (I := I) hbigge
      exact (accessControlSupportsInterfaceX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 36 := by omega
    have hdec := accessControlDecode_supportsInterface_none_short (I := I) hsz4 hshort
    exact (accessControlSupportsInterfaceX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end OpenZeppelinBench.AccessControl
