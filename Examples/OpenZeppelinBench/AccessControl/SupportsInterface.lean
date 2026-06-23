import Examples.OpenZeppelinBench.AccessControl.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

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
        have hxnat : x.toNat = 0 := by omega
        have htail : fromBytes' xs = 0 := by omega
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
    split at hpad
    · assumption
    · contradiction
  have htailZero : fromBytesBigEndian (xs.drop 4) = 0 :=
    (accessControlFromBytesBigEndian_zero_iff_all_zero (xs.drop 4)).mpr htailAll
  have hword := supportsInterfaceWord_toNat (I := I) hsz36
  rw [hword]
  change fromBytesBigEndian xs % 2 ^ 224 = 0
  rw [show xs = xs.take 4 ++ xs.drop 4 from (List.take_append_drop 4 xs).symm]
  rw [accessControlFromBytesBigEndian_append, htailLen, htailZero]
  norm_num

theorem supportsInterfaceEqOne_of_padding {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = some ()) :
    UInt256.eq (supportsInterfaceWord I)
      (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask) = ⟨1⟩ := by
  rw [supportsInterfaceClean_of_mod_zero _
    (supportsInterfaceModZero_of_padding hsz36 hpad)]
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
    · rw [hall] at hpad
      contradiction
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
  rw [supportsInterfaceMask_toNat,
    accessControlNatLandClearLow224 w.toNat (by exact w.val.isLt), Nat.mod_eq_of_lt] at ht
  · have hdiv := Nat.div_add_mod w.toNat (2 ^ 224)
    omega
  · exact lt_of_le_of_lt (Nat.mul_div_le w.toNat (2 ^ 224)) w.val.isLt

theorem accessControlUInt256_eq_one_eq {a b : UInt256}
    (h : UInt256.eq a b = ⟨1⟩) : a = b := by
  by_contra hne
  simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256, hne, decide_false,
    Bool.false_eq_true, ↓reduceIte] at h
  exact absurd h (by decide)

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
  have hword := supportsInterfaceWord_toNat (I := I) hsz36
  change Nat.land (supportsInterfaceWord I).toNat supportsInterfaceMask.toNat % UInt256.size = _
  rw [hword]
  change Nat.land (fromBytesBigEndian xs) supportsInterfaceMask.toNat % UInt256.size =
    fromBytesBigEndian (xs.take 4) * 2 ^ 224
  rw [supportsInterfaceMask_toNat]
  rw [show xs = xs.take 4 ++ xs.drop 4 from (List.take_append_drop 4 xs).symm]
  rw [accessControlFromBytesBigEndian_append, htailLen]
  rw [accessControlNatLandClearLow224 _ (by
    have hw := (supportsInterfaceWord I).val.isLt
    rw [hword] at hw
    change fromBytesBigEndian xs < 2 ^ 256 at hw
    simpa [show xs = xs.take 4 ++ xs.drop 4 from (List.take_append_drop 4 xs).symm,
      accessControlFromBytesBigEndian_append, htailLen] using hw)]
  have hdiv :
      (fromBytesBigEndian (xs.take 4) * 2 ^ 224 + fromBytesBigEndian (xs.drop 4)) /
          2 ^ 224 = fromBytesBigEndian (xs.take 4) := by
    omega
  rw [hdiv]
  rw [Nat.mod_eq_of_lt]
  · rfl
  · have hheadBound : fromBytesBigEndian (xs.take 4) < 2 ^ 32 := by
      have hb := accessControlFromBytesBigEndian_bound (xs.take 4)
      have hheadLen : (xs.take 4).length = 4 := by rw [List.length_take, hxsLen]; rfl
      rw [hheadLen] at hb
      simpa using hb
    have : fromBytesBigEndian (xs.take 4) * 2 ^ 224 < 2 ^ 32 * 2 ^ 224 :=
      Nat.mul_lt_mul_of_pos_right hheadBound (by positivity)
    rwa [← Nat.pow_add, show 32 + 224 = 256 by norm_num]

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
    (accessControlByteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [defaultAdminRoleTransition, getRoleAdminTransition, grantRoleTransition,
      hasRoleTransition, renounceRoleTransition, revokeRoleTransition])
    (post := []) rfl ?_ (by rw [selectorOf, supportsInterfaceSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, defaultAdminRoleSelectorBytes, hcd]; decide
  · rw [selectorOf, getRoleAdminSelectorBytes, hcd]; decide
  · rw [selectorOf, grantRoleSelectorBytes, hcd]; decide
  · rw [selectorOf, hasRoleSelectorBytes, hcd]; decide
  · rw [selectorOf, renounceRoleSelectorBytes, hcd]; decide
  · rw [selectorOf, revokeRoleSelectorBytes, hcd]; decide

-- PROMOTE -> Reasoning.ABI: single fixed-bytes4 calldata decoder.
theorem accessControlDecode_supportsInterface_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = some ()) :
    decodeCalldata (supportsInterfaceTransition.params.map Param.name)
      (transitionSignature supportsInterfaceTransition).paramTypes I.calldata =
        some (supportsInterfaceStore I) := by
  show decodeCalldata ["interfaceId"] [bytes4] I.calldata = some (supportsInterfaceStore I)
  unfold decodeCalldata
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ I.calldata.toList.length < 4 := by
    rw [htlen]
    omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([bytes4].any isDynamicABIType = true ∧
      2 ^ 255 ≤ I.calldata.toList.length) := by
    simp [bytes4, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hnotHuge : ¬ ([bytes4].isEmpty = false ∧ 2 ^ 255 ≤ (I.calldata.toList.drop 4).length) := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnotHuge]
  simp only [List.isEmpty_cons, Bool.false_eq_true, false_and, List.map_cons, List.map_nil,
    transitionSignature, bind, Option.bind]
  have hread : readBytes? (I.calldata.toList.drop 4) 0 32 =
      some ((I.calldata.toList.drop 4).take 32) := by
    unfold readBytes?
    have hlen : (((I.calldata.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_pos hlen, List.drop_zero]
  have hblen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hnotArgShort : ¬ I.calldata.toList.length - 4 < 32 := by
    rw [htlen]
    omega
  simp [decodeCalldata.decodeArgs, decodeCalldata.insertValues, bytes4, ABI.decodeABIValues?,
    ABI.decodeABIValue?, isDynamicABIType, staticABIEncodedSize?, abiTupleHeadSize?, hread, hpad,
    supportsInterfaceStore, supportsInterfaceBytes, bytes4Width, hblen, hnotArgShort]

theorem accessControlDecode_supportsInterface_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (supportsInterfaceTransition.params.map Param.name)
      (transitionSignature supportsInterfaceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["interfaceId"] [bytes4] I.calldata = none
  unfold decodeCalldata
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ I.calldata.toList.length < 4 := by
    rw [htlen]
    omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([bytes4].any isDynamicABIType = true ∧
      2 ^ 255 ≤ I.calldata.toList.length) := by
    simp [bytes4, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hnotHuge : ¬ ([bytes4].isEmpty = false ∧ 2 ^ 255 ≤ (I.calldata.toList.drop 4).length) := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnotHuge]
  simp only [List.isEmpty_cons, Bool.false_eq_true, false_and, List.map_cons, List.map_nil,
    transitionSignature, bind, Option.bind]
  have hread : readBytes? (I.calldata.toList.drop 4) 0 32 = none := by
    unfold readBytes?
    have hlen : ¬ (((I.calldata.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_neg hlen]
  simp [decodeCalldata.decodeArgs, bytes4, ABI.decodeABIValues?, ABI.decodeABIValue?,
    isDynamicABIType, staticABIEncodedSize?, abiTupleHeadSize?, hread]

theorem accessControlDecode_supportsInterface_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (supportsInterfaceTransition.params.map Param.name)
      (transitionSignature supportsInterfaceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["interfaceId"] [bytes4] I.calldata = none
  unfold decodeCalldata
  by_cases hlt4 : I.calldata.toList.length < 4
  · rw [if_pos hlt4]
  · rw [if_neg hlt4]
    have hnotDyn : ¬ ([bytes4].any isDynamicABIType = true ∧
        2 ^ 255 ≤ I.calldata.toList.length) := by
      simp [bytes4, isDynamicABIType]
    rw [if_neg hnotDyn]
    have hHuge : [bytes4].isEmpty = false ∧ 2 ^ 255 ≤ (I.calldata.toList.drop 4).length := by
      have htlen : I.calldata.toList.length = I.calldata.size := by
        rw [byteArray_toList_eq, Array.length_toList]
        rfl
      rw [List.length_drop, htlen]
      simp
      omega
    rw [if_pos hHuge]

theorem accessControlDecode_supportsInterface_none_pad {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = none) :
    decodeCalldata (supportsInterfaceTransition.params.map Param.name)
      (transitionSignature supportsInterfaceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["interfaceId"] [bytes4] I.calldata = none
  unfold decodeCalldata
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ I.calldata.toList.length < 4 := by
    rw [htlen]
    omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([bytes4].any isDynamicABIType = true ∧
      2 ^ 255 ≤ I.calldata.toList.length) := by
    simp [bytes4, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hnotHuge : ¬ ([bytes4].isEmpty = false ∧ 2 ^ 255 ≤ (I.calldata.toList.drop 4).length) := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnotHuge]
  simp only [List.isEmpty_cons, Bool.false_eq_true, false_and, List.map_cons, List.map_nil,
    transitionSignature, bind, Option.bind]
  have hread : readBytes? (I.calldata.toList.drop 4) 0 32 =
      some ((I.calldata.toList.drop 4).take 32) := by
    unfold readBytes?
    have hlen : (((I.calldata.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_pos hlen, List.drop_zero]
  have hnotArgShort : ¬ I.calldata.toList.length - 4 < 32 := by
    rw [htlen]
    omega
  simp [decodeCalldata.decodeArgs, bytes4, ABI.decodeABIValues?, ABI.decodeABIValue?,
    isDynamicABIType, staticABIEncodedSize?, abiTupleHeadSize?, hread, hpad, bytes4Width,
    hnotArgShort]

theorem accessControlSupportsInterfaceBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (supportsInterfaceStore I)
      supportsInterfaceTransition.body
      (.returned { contract := contract, locals := supportsInterfaceStore I } evm
        (some (.bool (supportsInterfaceResult I)))) := by
  refine ExecFuncBody.execBlockRet ?_
  refine (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns ?_
  simp [supportsInterfaceStore, supportsInterfaceResult, iaccessControlId, ierc165Id, evalExpr?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalBinaryOp?,
    accessControlFixedBytes4_beq]

theorem accessControlSupportsInterfaceBody {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I}
    {g : UInt256}
    (hcode : I.code = accessControlBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x01, 0xff, 0xc9, 0xa7]⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I) ⟨126⟩
      [accessControlSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  sorry

end OpenZeppelinBench.AccessControl
