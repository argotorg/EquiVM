import Benchmarks.OpenZeppelinBench.TimelockController.Return
import Benchmarks.OpenZeppelinBench.TimelockController.SolmDispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Dispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Routines

/-!
# OpenZeppelin TimelockController `supportsInterface(bytes4)` refinement

`supportsInterface` peels its non-payable callvalue guard, decodes a `bytes4 interfaceId`
(subroutine @4561: validates `calldata ≥ 36` and clean low-28-bytes, reverting otherwise), computes
`interfaceId == IERC1155Receiver || interfaceId == IAccessControl || interfaceId == IERC165` via a
short-circuit OR (subroutines @1675/@3619/@4235), and ABI-encodes the resulting `bool` (split
encoder @509/@521).  Selector index 26, dispatch group G397 arm 1, body pc 478.

The `bytes4` word/mask coupling lemmas below are adapted from the proven
`Examples/OpenZeppelinBench/AccessControl/SupportsInterface.lean` (identical decoder + comparison
codegen; only the constant set and the extra `IERC1155Receiver` arm differ).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace OpenZeppelinBench.TimelockController

/-! ## Decoded argument, mask, interface-id words, and Solm-side boolean -/

/-- The `bytes4 interfaceId` argument word (`CALLDATALOAD(4)`). -/
abbrev tlcSuppIfaceWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 4

/-- The 4 argument bytes of `bytes4 interfaceId` at calldata offset 4. -/
abbrev tlcSuppIfaceBytes (I : ExecutionEnv) : List UInt8 :=
  ((I.calldata.toList.drop 4).take 32).take 4

/-- The decoded local store for `supportsInterface`. -/
abbrev tlcSuppIfaceStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "interfaceId" (.fixedBytes bytes4Width (tlcSuppIfaceBytes I))

/-- Solc's clean-bytes4 mask `0xffffffff…00 = ~((1 << 224) - 1)`. -/
abbrev tlcSuppIfaceMask : UInt256 :=
  UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩) ⟨1⟩)

-- `IERC1155Receiver` id `0x4e2312e0`: solc builds it as `0x02711897 << 0xe5 = 0x4e2312e0 << 224`.
abbrev tlcIerc1155Word : UInt256 := UInt256.shiftLeft (⟨0x02711897⟩ : UInt256) ⟨0xe5⟩
abbrev tlcIaccessControlWord : UInt256 := UInt256.shiftLeft (⟨0x7965db0b⟩ : UInt256) ⟨224⟩
abbrev tlcIerc165Word : UInt256 := UInt256.shiftLeft (⟨0x01ffc9a7⟩ : UInt256) ⟨224⟩

/-- The Solm-side boolean: the 3-way interface-id disjunction (list-`BEq` form). -/
abbrev tlcSuppIfaceResult (I : ExecutionEnv) : Bool :=
  (tlcSuppIfaceBytes I == [0x4e, 0x23, 0x12, 0xe0]) ||
    ((tlcSuppIfaceBytes I == [0x79, 0x65, 0xdb, 0x0b]) ||
      (tlcSuppIfaceBytes I == [0x01, 0xff, 0xc9, 0xa7]))

abbrev tlcSuppIfaceResultWord (I : ExecutionEnv) : UInt256 :=
  if tlcSuppIfaceResult I then ⟨1⟩ else ⟨0⟩

/-! ## `bytes4` word / mask coupling (adapted from AccessControl; contract-agnostic).
    LIBRARY CANDIDATE: these are pure calldata/word facts, reusable by any `supportsInterface`. -/

theorem tlcListUInt8_decide_eq_beq (xs ys : List UInt8) :
    decide (xs = ys) = (xs == ys) := by
  by_cases h : xs = ys
  · subst ys; simp
  · have hbeq : (xs == ys) = false := by
      apply Bool.eq_false_iff.mpr; intro hb; exact h (eq_of_beq hb)
    simp [h, hbeq]

theorem tlcFixedBytes4_beq (xs ys : List UInt8) :
    (Value.fixedBytes bytes4Width xs == Value.fixedBytes bytes4Width ys) = (xs == ys) := by
  simp [BEq.beq, tlcListUInt8_decide_eq_beq]

theorem tlcFromBytesBigEndian_append (a b : List UInt8) :
    fromBytesBigEndian (a ++ b) =
      fromBytesBigEndian a * 2 ^ (8 * b.length) + fromBytesBigEndian b := by
  unfold fromBytesBigEndian Function.comp
  rw [List.reverse_append, fromBytes'_append, List.length_reverse]
  ring

theorem tlcFromBytesBigEndian_bound (xs : List UInt8) :
    fromBytesBigEndian xs < 2 ^ (8 * xs.length) := by
  unfold fromBytesBigEndian Function.comp
  have h := fromBytes'_le (bs := xs.reverse)
  rwa [List.length_reverse] at h

theorem tlcFromBytes'_zero_iff_all_zero (xs : List UInt8) :
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
        exact ⟨by simp [hx], ih.mp htail⟩
      · intro h
        simp only [List.all_cons, Bool.and_eq_true] at h
        rcases h with ⟨hx, hxs⟩
        have hx0 : x = 0 := eq_of_beq hx
        unfold fromBytes'
        simp [hx0, ih.mpr hxs]

theorem tlcFromBytesBigEndian_zero_iff_all_zero (xs : List UInt8) :
    fromBytesBigEndian xs = 0 ↔ xs.all (· == 0) = true := by
  unfold fromBytesBigEndian Function.comp
  rw [tlcFromBytes'_zero_iff_all_zero]; simp

theorem tlcBytesToWord_toNat_of_len (xs : List UInt8) (hlen : xs.length = 32) :
    (ABI.bytesToWord xs).toNat = fromBytesBigEndian xs := by
  unfold ABI.bytesToWord fromByteArrayBigEndian
  rw [ulit_toNat']
  · simp [byteArray_toList_eq]
  · change fromByteArrayBigEndian { data := xs.toArray } < UInt256.size
    unfold fromByteArrayBigEndian
    simp [byteArray_toList_eq]
    rw [show UInt256.size = 2 ^ (8 * xs.length) by rw [hlen]; rfl]
    exact tlcFromBytesBigEndian_bound xs

theorem tlcSuppIfaceWord_toNat {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (tlcSuppIfaceWord I).toNat = fromBytesBigEndian ((I.calldata.toList.drop 4).take 32) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) = tlcSuppIfaceWord I := by
    simpa [tlcSuppIfaceWord, calldataWord] using
      decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  rw [← hword]
  exact tlcBytesToWord_toNat_of_len _ hlen

theorem tlcSuppIfaceMask_toNat : tlcSuppIfaceMask.toNat = 2 ^ 256 - 2 ^ 224 := by decide

theorem tlcSuppIfaceClean_of_mod_zero (w : UInt256) (hmod : w.toNat % 2 ^ 224 = 0) :
    UInt256.land w tlcSuppIfaceMask = w := by
  apply u256_inj
  show Nat.land w.toNat tlcSuppIfaceMask.toNat % UInt256.size = w.toNat
  rw [tlcSuppIfaceMask_toNat, natLandClearLow w.toNat 224 (by norm_num) w.val.isLt]
  rw [show w.toNat / 2 ^ 224 * 2 ^ 224 = w.toNat by
    have := Nat.div_add_mod w.toNat (2 ^ 224); omega]
  exact Nat.mod_eq_of_lt w.val.isLt

theorem tlcSuppIfaceModZero_of_padding {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = some ()) :
    (tlcSuppIfaceWord I).toNat % 2 ^ 224 = 0 := by
  let xs := (I.calldata.toList.drop 4).take 32
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hxsLen : xs.length = 32 := by
    dsimp [xs]; rw [List.length_take, List.length_drop, htlen]; omega
  have htailLen : (xs.drop 4).length = 28 := by rw [List.length_drop, hxsLen]
  have htailTake : (xs.drop 4).take 28 = xs.drop 4 :=
    List.take_of_length_le (by rw [htailLen])
  have htailAll : (xs.drop 4).all (· == 0) = true := by
    unfold zeroPadding? readBytes? at hpad
    have hlen : ((xs.drop 4).take 28).length = 28 := by rw [htailTake, htailLen]
    rw [if_pos hlen] at hpad
    rw [htailTake] at hpad
    by_cases hall : (xs.drop 4).all (· == 0) = true
    · exact hall
    · simp at hpad; simpa using hpad
  have htailZero : fromBytesBigEndian (xs.drop 4) = 0 :=
    (tlcFromBytesBigEndian_zero_iff_all_zero (xs.drop 4)).mpr htailAll
  have hword := tlcSuppIfaceWord_toNat (I := I) hsz36
  rw [hword]
  change fromBytesBigEndian xs % 2 ^ 224 = 0
  rw [show xs = xs.take 4 ++ xs.drop 4 from (List.take_append_drop 4 xs).symm]
  rw [tlcFromBytesBigEndian_append, htailLen, htailZero]
  rw [show 8 * 28 = 224 by norm_num, Nat.add_zero]
  exact Nat.mul_mod_left _ _

theorem tlcSuppIfaceEqOne_of_padding {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = some ()) :
    UInt256.eq (tlcSuppIfaceWord I) (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask) = ⟨1⟩ := by
  have hclean : UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask = tlcSuppIfaceWord I :=
    tlcSuppIfaceClean_of_mod_zero _ (tlcSuppIfaceModZero_of_padding hsz36 hpad)
  rw [hclean]; exact uInt256_eq_self _

theorem tlcSuppIfaceModNeZero_of_padding_none {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = none) :
    (tlcSuppIfaceWord I).toNat % 2 ^ 224 ≠ 0 := by
  let xs := (I.calldata.toList.drop 4).take 32
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hxsLen : xs.length = 32 := by
    dsimp [xs]; rw [List.length_take, List.length_drop, htlen]; omega
  have htailLen : (xs.drop 4).length = 28 := by rw [List.length_drop, hxsLen]
  have htailTake : (xs.drop 4).take 28 = xs.drop 4 :=
    List.take_of_length_le (by rw [htailLen])
  have htailAllFalse : (xs.drop 4).all (· == 0) = false := by
    unfold zeroPadding? readBytes? at hpad
    have hlen : ((xs.drop 4).take 28).length = 28 := by rw [htailTake, htailLen]
    rw [if_pos hlen] at hpad
    rw [htailTake] at hpad
    by_cases hall : (xs.drop 4).all (· == 0) = true
    · simp at hpad
      exfalso
      rcases hpad with ⟨x, hxmem, hxne⟩
      have hallProp : ∀ x ∈ xs.drop 4, x = 0 := by simpa using hall
      exact hxne (hallProp x hxmem)
    · exact Bool.eq_false_iff.mpr hall
  have htailNZ : fromBytesBigEndian (xs.drop 4) ≠ 0 := by
    intro hz
    have hall := (tlcFromBytesBigEndian_zero_iff_all_zero (xs.drop 4)).mp hz
    rw [hall] at htailAllFalse; contradiction
  have hword := tlcSuppIfaceWord_toNat (I := I) hsz36
  rw [hword]
  change fromBytesBigEndian xs % 2 ^ 224 ≠ 0
  rw [show xs = xs.take 4 ++ xs.drop 4 from (List.take_append_drop 4 xs).symm]
  rw [tlcFromBytesBigEndian_append, htailLen]
  intro hmod
  have htailMod : fromBytesBigEndian (xs.drop 4) % 2 ^ 224 = 0 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmod
  have htailBound : fromBytesBigEndian (xs.drop 4) < 2 ^ 224 := by
    have hb := tlcFromBytesBigEndian_bound (xs.drop 4)
    rw [htailLen] at hb; simpa using hb
  have htailZero : fromBytesBigEndian (xs.drop 4) = 0 :=
    Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (by omega))
  exact htailNZ htailZero

theorem tlcSuppIfaceModZero_of_land_eq (w : UInt256)
    (hclean : UInt256.land w tlcSuppIfaceMask = w) : w.toNat % 2 ^ 224 = 0 := by
  have ht := congrArg UInt256.toNat hclean
  change Nat.land w.toNat tlcSuppIfaceMask.toNat % UInt256.size = w.toNat at ht
  rw [tlcSuppIfaceMask_toNat, natLandClearLow w.toNat 224 (by norm_num) w.val.isLt] at ht
  have hsmall : w.toNat / 2 ^ 224 * 2 ^ 224 < UInt256.size :=
    lt_of_le_of_lt (by simpa [Nat.mul_comm] using Nat.mul_div_le w.toNat (2 ^ 224)) w.val.isLt
  rw [Nat.mod_eq_of_lt hsmall] at ht
  have hdiv := Nat.div_add_mod w.toNat (2 ^ 224)
  omega

theorem tlcSuppIfaceEqZero_of_padding_none {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = none) :
    UInt256.eq (tlcSuppIfaceWord I) (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask) = ⟨0⟩ := by
  apply uInt256_eq_zero_of_ne
  intro heq
  have hword : tlcSuppIfaceWord I = UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask :=
    uInt256_eq_one_eq heq
  exact (tlcSuppIfaceModNeZero_of_padding_none hsz36 hpad)
    (tlcSuppIfaceModZero_of_land_eq _ hword.symm)

theorem tlcSuppIfaceMaskedWord_toNat {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask).toNat =
      fromBytesBigEndian (tlcSuppIfaceBytes I) * 2 ^ 224 := by
  let xs := (I.calldata.toList.drop 4).take 32
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hxsLen : xs.length = 32 := by
    dsimp [xs]; rw [List.length_take, List.length_drop, htlen]; omega
  have htailLen : (xs.drop 4).length = 28 := by rw [List.length_drop, hxsLen]
  have hxsBound : fromBytesBigEndian xs < 2 ^ 256 := by
    have hb := tlcFromBytesBigEndian_bound xs
    rw [hxsLen] at hb; simpa using hb
  have hword := tlcSuppIfaceWord_toNat (I := I) hsz36
  change Nat.land (tlcSuppIfaceWord I).toNat tlcSuppIfaceMask.toNat % UInt256.size = _
  rw [hword]
  change Nat.land (fromBytesBigEndian xs) tlcSuppIfaceMask.toNat % UInt256.size =
    fromBytesBigEndian (xs.take 4) * 2 ^ 224
  rw [tlcSuppIfaceMask_toNat, natLandClearLow (fromBytesBigEndian xs) 224 (by norm_num) hxsBound]
  have hsplit : fromBytesBigEndian xs =
      fromBytesBigEndian (xs.take 4) * 2 ^ 224 + fromBytesBigEndian (xs.drop 4) := by
    calc
      fromBytesBigEndian xs = fromBytesBigEndian (xs.take 4 ++ xs.drop 4) :=
        congrArg fromBytesBigEndian (List.take_append_drop 4 xs).symm
      _ = fromBytesBigEndian (xs.take 4) * 2 ^ 224 + fromBytesBigEndian (xs.drop 4) := by
        rw [tlcFromBytesBigEndian_append, htailLen]
  rw [hsplit]
  have htailBound : fromBytesBigEndian (xs.drop 4) < 2 ^ 224 := by
    have hb := tlcFromBytesBigEndian_bound (xs.drop 4)
    rw [htailLen] at hb; simpa using hb
  have hdiv : (fromBytesBigEndian (xs.take 4) * 2 ^ 224 + fromBytesBigEndian (xs.drop 4)) /
      2 ^ 224 = fromBytesBigEndian (xs.take 4) := by omega
  rw [hdiv]
  have hheadBound : fromBytesBigEndian (xs.take 4) < 2 ^ 32 := by
    have hb := tlcFromBytesBigEndian_bound (xs.take 4)
    have hheadLen : (xs.take 4).length = 4 := by rw [List.length_take, hxsLen]; rfl
    rw [hheadLen] at hb; simpa using hb
  have hprodLt : fromBytesBigEndian (xs.take 4) * 2 ^ 224 < UInt256.size := by
    have hlt : fromBytesBigEndian (xs.take 4) * 2 ^ 224 < 2 ^ 32 * 2 ^ 224 :=
      Nat.mul_lt_mul_of_pos_right hheadBound (by positivity)
    simpa [UInt256.size, Nat.pow_add] using hlt
  rw [Nat.mod_eq_of_lt hprodLt]

theorem tlcSuppIfaceBytes_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (tlcSuppIfaceBytes I).length = 4 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  simp [tlcSuppIfaceBytes, List.length_take, List.length_drop, htlen]; omega

theorem tlcIerc1155Word_toNat :
    tlcIerc1155Word.toNat = fromBytesBigEndian [0x4e, 0x23, 0x12, 0xe0] * 2 ^ 224 := by decide

theorem tlcIaccessControlWord_toNat :
    tlcIaccessControlWord.toNat = fromBytesBigEndian [0x79, 0x65, 0xdb, 0x0b] * 2 ^ 224 := by decide

theorem tlcIerc165Word_toNat :
    tlcIerc165Word.toNat = fromBytesBigEndian [0x01, 0xff, 0xc9, 0xa7] * 2 ^ 224 := by decide

/-- The generic "const-word vs masked-arg" comparison ↔ list equality. -/
theorem tlcSuppIfaceEq_generic {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (cw : UInt256) (cb : List UInt8) (hcb : cb.length = 4)
    (hcw : cw.toNat = fromBytesBigEndian cb * 2 ^ 224) :
    UInt256.eq cw (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask) =
      if (tlcSuppIfaceBytes I == cb) then ⟨1⟩ else ⟨0⟩ := by
  by_cases h : tlcSuppIfaceBytes I = cb
  · have hbeq : (tlcSuppIfaceBytes I == cb) = true := by rw [h]; simp
    rw [hbeq]
    have heq : cw = UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask := by
      apply u256_inj
      rw [hcw, tlcSuppIfaceMaskedWord_toNat hsz36, h]
    rw [heq]; exact uInt256_eq_self _
  · have hbeq : (tlcSuppIfaceBytes I == cb) = false := by
      apply Bool.eq_false_iff.mpr; intro hb; exact h (eq_of_beq hb)
    rw [hbeq]
    apply uInt256_eq_zero_of_ne
    intro heq1
    have heq : cw = UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask := uInt256_eq_one_eq heq1
    have hn : fromBytesBigEndian (tlcSuppIfaceBytes I) = fromBytesBigEndian cb := by
      have ht := congrArg UInt256.toNat heq
      rw [hcw, tlcSuppIfaceMaskedWord_toNat hsz36] at ht
      omega
    exact h (fromBytesBigEndian_inj4 (tlcSuppIfaceBytes_length hsz36) hcb hn)

theorem tlcSuppIfaceEq_ierc1155 {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    UInt256.eq tlcIerc1155Word (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask) =
      if (tlcSuppIfaceBytes I == [0x4e, 0x23, 0x12, 0xe0]) then ⟨1⟩ else ⟨0⟩ :=
  tlcSuppIfaceEq_generic hsz36 _ _ rfl tlcIerc1155Word_toNat

theorem tlcSuppIfaceEq_iaccessControl {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    UInt256.eq tlcIaccessControlWord (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask) =
      if (tlcSuppIfaceBytes I == [0x79, 0x65, 0xdb, 0x0b]) then ⟨1⟩ else ⟨0⟩ :=
  tlcSuppIfaceEq_generic hsz36 _ _ rfl tlcIaccessControlWord_toNat

theorem tlcSuppIfaceEq_ierc165 {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    UInt256.eq tlcIerc165Word (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask) =
      if (tlcSuppIfaceBytes I == [0x01, 0xff, 0xc9, 0xa7]) then ⟨1⟩ else ⟨0⟩ :=
  tlcSuppIfaceEq_generic hsz36 _ _ rfl tlcIerc165Word_toNat

theorem tlcSuppIfaceResultWord_norm (I : ExecutionEnv) :
    UInt256.isZero (UInt256.isZero (tlcSuppIfaceResultWord I)) = tlcSuppIfaceResultWord I := by
  by_cases h : tlcSuppIfaceResult I <;> simp [tlcSuppIfaceResultWord, h] <;> decide

/-! ## Reach the body -/

/-- Reach the `supportsInterface` body pc 478 (G397 arm 1). -/
theorem tlcReachSupportsInterface {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 26)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨478⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : tlcSelWord I = ⟨0x01ffc9a7⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x01 0xff 0xc9 0xa7 ⟨0x01ffc9a7⟩ (by native_decide)
      (by simpa [tlcSelBytes] using hsel)
  refine tlcReachG397Body 1 (by omega) ⟨478⟩ hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by intro j hj; interval_cases j; rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide)

/-! ## ABI decode -/

theorem tlcDecodeSupportsInterface_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = some ()) :
    decodeCalldataWithMode config.abiDecodeMode (supportsInterfaceTransition.params.map Param.name)
      (transitionSignature supportsInterfaceTransition).paramTypes I.calldata =
        some (tlcSuppIfaceStore I) := by
  show decodeCalldata ["interfaceId"] [bytes4] I.calldata = some (tlcSuppIfaceStore I)
  simpa [tlcSuppIfaceStore, tlcSuppIfaceBytes, calldataBytes4Arg, bytes4, bytes4Width,
    abiBytes4, abiBytes4Width] using
    decodeCalldata_bytes4_ok (cd := I.calldata) (x := "interfaceId") hsz36 hbig hpad

theorem tlcDecodeSupportsInterface_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (supportsInterfaceTransition.params.map Param.name)
      (transitionSignature supportsInterfaceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["interfaceId"] [bytes4] I.calldata = none
  simpa [bytes4, bytes4Width, abiBytes4, abiBytes4Width] using
    decodeCalldata_bytes4_none_short (cd := I.calldata) (x := "interfaceId") hsz4 hshort

theorem tlcDecodeSupportsInterface_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (supportsInterfaceTransition.params.map Param.name)
      (transitionSignature supportsInterfaceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["interfaceId"] [bytes4] I.calldata = none
  simpa [bytes4, bytes4Width, abiBytes4, abiBytes4Width] using
    decodeCalldata_bytes4_none_huge (cd := I.calldata) (x := "interfaceId") hbig

theorem tlcDecodeSupportsInterface_none_pad {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = none) :
    decodeCalldataWithMode config.abiDecodeMode (supportsInterfaceTransition.params.map Param.name)
      (transitionSignature supportsInterfaceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["interfaceId"] [bytes4] I.calldata = none
  simpa [bytes4, bytes4Width, abiBytes4, abiBytes4Width] using
    decodeCalldata_bytes4_none_pad (cd := I.calldata) (x := "interfaceId") hsz36 hbig hpad

/-! ## Solm body -/

/-- The Solm `supportsInterface(bytes4)` body returns the 3-way disjunction boolean. -/
theorem tlcSuppIfaceBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (tlcSuppIfaceStore I)
      supportsInterfaceTransition.body
      (.returned { contract := contract, locals := tlcSuppIfaceStore I } evm
        (some [(.bool (tlcSuppIfaceResult I))])) := by
  refine nonpayableReturnExprBodyReturns hwv ?_
  have hvar : evalExpr? config { contract := contract, locals := tlcSuppIfaceStore I } evm
      (.var "interfaceId") = .ok (.fixedBytes bytes4Width (tlcSuppIfaceBytes I)) := by
    simp [evalExpr?, EvalResult.ofOption, tlcSuppIfaceStore]
  have he : ∀ c : List UInt8,
      evalExpr? config { contract := contract, locals := tlcSuppIfaceStore I } evm
        (.binary .eq (.var "interfaceId") (fixedBytes4 c))
        = .ok (.bool (tlcSuppIfaceBytes I == c)) := by
    intro c
    simp only [evalExpr?, hvar, fixedBytes4, EvalResult.bind, bind, evalBinaryOp?, pure,
      tlcFixedBytes4_beq]
  have hor : ∀ (e1 e2 : Expr) (c1 c2 : Bool),
      evalExpr? config { contract := contract, locals := tlcSuppIfaceStore I } evm e1
        = .ok (.bool c1) →
      evalExpr? config { contract := contract, locals := tlcSuppIfaceStore I } evm e2
        = .ok (.bool c2) →
      evalExpr? config { contract := contract, locals := tlcSuppIfaceStore I } evm
        (.binary .or e1 e2) = .ok (.bool (c1 || c2)) := by
    intro e1 e2 c1 c2 h1 h2
    simp only [evalExpr?, h1, EvalResult.bind, bind]
    cases c1 with
    | true => rfl
    | false => rw [h2]; rfl
  show evalExpr? config { contract := contract, locals := tlcSuppIfaceStore I } evm
    (.binary .or (.binary .eq (.var "interfaceId") ierc1155ReceiverId)
      (.binary .or (.binary .eq (.var "interfaceId") iaccessControlId)
        (.binary .eq (.var "interfaceId") ierc165Id))) = .ok (.bool (tlcSuppIfaceResult I))
  exact hor _ _ _ _ (he [0x4e, 0x23, 0x12, 0xe0])
    (hor _ _ _ _ (he [0x79, 0x65, 0xdb, 0x0b]) (he [0x01, 0xff, 0xc9, 0xa7]))

/-! ## EVM trace -/

/-- Peel the guard and jump into the `bytes4` decoder subroutine @4561, leaving the decoder's
    arguments `[offset=4, calldatasize, retPC=504, contPC=509, sel]`. -/
theorem tlcSuppIfaceReachDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 26)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4561⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨504⟩, ⟨509⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h478⟩ := tlcReachSupportsInterface (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h491⟩ := tlcGuardPeelOk (gt := ⟨489⟩) h478 hwv (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by jump_dest)
    (by native_decide) (by native_decide)
  exact ⟨_, _, evm_run h491 with [
    push2 ⟨509⟩, push2 ⟨504⟩, calldatasize, push1 ⟨4⟩, push2 ⟨4561⟩, jump (by jump_dest)]⟩

/-- Split bool-return encoder @509 (store `iszero∘iszero val` at the free pointer, fall through the
    return dispatcher @521, `RETURN(0x80, 0x20)`).  Structurally identical to the proven
    AccessControl `bool` encoder.  LIBRARY CANDIDATE: split analogue of `RD.solcReturnBoolFromMem`. -/
theorem tlcSuppIfaceReturnBool {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {val : UInt256}
    (h : RD timelockControllerBenchBytecode ee g s0 ⟨509⟩ (val :: R) solcFreePtrMem
        (UInt256.ofNat 3) rdata acc k C)
    (hnorm : UInt256.isZero (UInt256.isZero val) = val)
    (hov : R.length + 8 ≤ 1024) :
    RDret timelockControllerBenchBytecode g s0 acc (UInt256.toByteArray val) := by
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
    raw ret 0 (UInt256.toByteArray val) (by decide) mem_cost
      (by rw [show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide]
          exact solcReturnMem_read128 val)
      (by evm_ov) ]

/-- Reach the bool-computing subroutine @1675 with the decoded argument on the stack. -/
theorem tlcSuppIfaceReach1675 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hsel : selIs I (tlcSelBytes 26))
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = some ()) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1675⟩
      [tlcSuppIfaceWord I, ⟨509⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  have hclean : UInt256.eq (tlcSuppIfaceWord I)
      (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask) = ⟨1⟩ :=
    tlcSuppIfaceEqOne_of_padding hsz36 hpad
  obtain ⟨_, _, h4561⟩ := tlcSuppIfaceReachDecoder (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode hwv (by omega) hsize hsel
  exact ⟨_, _, evm_run h4561 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨4577⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub,
    not, dup2, and, dup2, eq, push2 ⟨2110⟩,
    jumpiT (by
      change UInt256.eq (tlcSuppIfaceWord I)
        (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask) ≠ ⟨0⟩
      rw [hclean]; decide) (by jump_dest),
    jumpdest, swap4, swap3, pop, pop, pop, jump (by jump_dest),
    jumpdest, push2 ⟨1675⟩, jump (by jump_dest)]⟩

/-- The bool computer (@1675 → @3619 → @4235 → epilogue @1685) reaches the return encoder @509 with
    the ABI result word on the stack. -/
theorem tlcSuppIfaceCompute {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size)
    (hreach : ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1675⟩
      [tlcSuppIfaceWord I, ⟨509⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨509⟩
      [tlcSuppIfaceResultWord I, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1675⟩ := hreach
  by_cases h1155 : (tlcSuppIfaceBytes I == [0x4e, 0x23, 0x12, 0xe0]) = true
  · -- IERC1155Receiver matches: `@3619` short-circuits to the epilogue.
    have hresult : tlcSuppIfaceResultWord I = ⟨1⟩ := by
      simp [tlcSuppIfaceResultWord, tlcSuppIfaceResult, h1155]
    have hc1eq : UInt256.eq tlcIerc1155Word
        (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask) = ⟨1⟩ := by
      simpa [h1155] using tlcSuppIfaceEq_ierc1155 hsz36
    have rd1685 := evm_run rd1675 with [
      jumpdest, push0, push2 ⟨1685⟩, dup3, push2 ⟨3619⟩, jump (by jump_dest),
      jumpdest, push0, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub, not, dup3, and,
      push4 ⟨0x02711897⟩, push1 ⟨0xe5⟩, shl, eq, dup1, push2 ⟨1685⟩,
      jumpiT (by
        change UInt256.eq tlcIerc1155Word
          (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask) ≠ ⟨0⟩
        rw [hc1eq]; decide) (by jump_dest)]
    exact ⟨_, _, by
      simpa [hresult, hc1eq] using evm_run rd1685 with [
        jumpdest, swap3, swap2, pop, pop, jump (by jump_dest),
        jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]⟩
  · have h1155f : (tlcSuppIfaceBytes I == [0x4e, 0x23, 0x12, 0xe0]) = false := by simpa using h1155
    have hc1z : UInt256.eq tlcIerc1155Word
        (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask) = ⟨0⟩ := by
      simpa [h1155f] using tlcSuppIfaceEq_ierc1155 hsz36
    by_cases hac : (tlcSuppIfaceBytes I == [0x79, 0x65, 0xdb, 0x0b]) = true
    · -- IAccessControl matches: `@4235` short-circuits to the epilogue.
      have hresult : tlcSuppIfaceResultWord I = ⟨1⟩ := by
        simp [tlcSuppIfaceResultWord, tlcSuppIfaceResult, h1155f, hac]
      have hc2eq : UInt256.eq tlcIaccessControlWord
          (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask) = ⟨1⟩ := by
        simpa [hac] using tlcSuppIfaceEq_iaccessControl hsz36
      have rd1685 := evm_run rd1675 with [
        jumpdest, push0, push2 ⟨1685⟩, dup3, push2 ⟨3619⟩, jump (by jump_dest),
        jumpdest, push0, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub, not, dup3, and,
        push4 ⟨0x02711897⟩, push1 ⟨0xe5⟩, shl, eq, dup1, push2 ⟨1685⟩,
        jumpiNT (by
          change UInt256.eq tlcIerc1155Word
            (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask) = ⟨0⟩
          rw [hc1z]),
        pop, push2 ⟨1685⟩, dup3, push2 ⟨4235⟩, jump (by jump_dest),
        jumpdest, push0, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub, not, dup3, and,
        push4 ⟨0x7965db0b⟩, push1 ⟨224⟩, shl, eq, dup1, push2 ⟨1685⟩,
        jumpiT (by
          change UInt256.eq tlcIaccessControlWord
            (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask) ≠ ⟨0⟩
          rw [hc2eq]; decide) (by jump_dest)]
      exact ⟨_, _, by
        simpa [hresult, hc2eq] using evm_run rd1685 with [
          jumpdest, swap3, swap2, pop, pop, jump (by jump_dest),
          jumpdest, swap3, swap2, pop, pop, jump (by jump_dest),
          jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]⟩
    · -- Neither IERC1155Receiver nor IAccessControl; result = IERC165 match (fall-through @4235).
      have hacf : (tlcSuppIfaceBytes I == [0x79, 0x65, 0xdb, 0x0b]) = false := by simpa using hac
      have hc2z : UInt256.eq tlcIaccessControlWord
          (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask) = ⟨0⟩ := by
        simpa [hacf] using tlcSuppIfaceEq_iaccessControl hsz36
      have hc3 : UInt256.eq tlcIerc165Word
          (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask) = tlcSuppIfaceResultWord I := by
        rw [tlcSuppIfaceEq_ierc165 hsz36]
        simp [tlcSuppIfaceResultWord, tlcSuppIfaceResult, h1155f, hacf]
      have hc3rev : UInt256.eq (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask)
          tlcIerc165Word = tlcSuppIfaceResultWord I := by rw [uInt256_eq_comm]; exact hc3
      have rd1685 := evm_run rd1675 with [
        jumpdest, push0, push2 ⟨1685⟩, dup3, push2 ⟨3619⟩, jump (by jump_dest),
        jumpdest, push0, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub, not, dup3, and,
        push4 ⟨0x02711897⟩, push1 ⟨0xe5⟩, shl, eq, dup1, push2 ⟨1685⟩,
        jumpiNT (by
          change UInt256.eq tlcIerc1155Word
            (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask) = ⟨0⟩
          rw [hc1z]),
        pop, push2 ⟨1685⟩, dup3, push2 ⟨4235⟩, jump (by jump_dest),
        jumpdest, push0, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub, not, dup3, and,
        push4 ⟨0x7965db0b⟩, push1 ⟨224⟩, shl, eq, dup1, push2 ⟨1685⟩,
        jumpiNT (by
          change UInt256.eq tlcIaccessControlWord
            (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask) = ⟨0⟩
          rw [hc2z]),
        pop, push4 ⟨0x01ffc9a7⟩, push1 ⟨224⟩, shl, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩,
        shl, sub, not, dup4, and, eq, push2 ⟨1685⟩, jump (by jump_dest)]
      exact ⟨_, _, by
        simpa [hc3rev] using evm_run rd1685 with [
          jumpdest, swap3, swap2, pop, pop, jump (by jump_dest),
          jumpdest, swap3, swap2, pop, pop, jump (by jump_dest),
          jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]⟩

theorem tlcSuppIfaceX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hsel : selIs I (tlcSelBytes 26))
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = some ()) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (tlcSuppIfaceResultWord I)) := by
  obtain ⟨_, _, rd509⟩ := tlcSuppIfaceCompute hsz36
    (tlcSuppIfaceReach1675 hcode hwv hsz36 hsize hszhi hsel hpad)
  exact tlcSuppIfaceReturnBool rd509 (tlcSuppIfaceResultWord_norm I) (by evm_ov)

/-- Decoder bounds-check failure (`calldata < 36` or `≥ 2^255+4`): the decoder reverts. -/
theorem tlcSuppIfaceBoundsRev {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 26))
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h4561⟩ := tlcSuppIfaceReachDecoder (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode hwv hsz4 hsize hsel
  exact evm_run h4561 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨4577⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov)]

/-- Decoder clean-bytes4 check failure (nonzero low 28 bytes): the decoder reverts. -/
theorem tlcSuppIfaceBadpadRev {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (hsel : selIs I (tlcSelBytes 26))
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = none) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hbig hsize
  have hclean : UInt256.eq (tlcSuppIfaceWord I)
      (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask) = ⟨0⟩ :=
    tlcSuppIfaceEqZero_of_padding_none hsz36 hpad
  obtain ⟨_, _, h4561⟩ := tlcSuppIfaceReachDecoder (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode hwv (by omega) hsize hsel
  exact evm_run h4561 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨4577⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub,
    not, dup2, and, dup2, eq, push2 ⟨2110⟩,
    jumpiNT (by
      change UInt256.eq (tlcSuppIfaceWord I)
        (UInt256.land (tlcSuppIfaceWord I) tlcSuppIfaceMask) = ⟨0⟩
      rw [hclean]),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov)]

/-! ## Refinement -/

/-- Refinement of `SupportsInterface` (selector index 26). -/
theorem tlcSupportsInterfaceBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (tlcSelBytes 26))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (tlcSelBytes 26) (by native_decide) hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz36 : 36 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · cases hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 with
        | none =>
            exact tlcReEquivDecodeFailed hcode
              (tlcSuppIfaceBadpadRev (g := Sat256.ofUInt256 g) hcode hwv hsz36 hsize hbig hsel hpad)
              (tlcSelectorDispatchSupportsInterface hsel)
              (tlcDecodeSupportsInterface_none_pad hsz36 hbig hpad)
        | some _ =>
            have hpadSome : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = some () := by
              simpa using hpad
            exact tlcReEquivExecTransport hcode
              (tlcSuppIfaceX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz36 hsize hbig hsel hpadSome)
              (tlcSelectorDispatchSupportsInterface hsel)
              (tlcDecodeSupportsInterface_ok hsz36 hbig hpadSome)
              (tlcSuppIfaceBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv))
              rfl hAccounts
              (returnEquiv_of_encode (by
                by_cases hr : tlcSuppIfaceResult I
                · simpa [tlcSuppIfaceResultWord, hr] using boolTrueReturnEncoding
                · simpa [boolTy, tlcSuppIfaceResultWord, hr] using boolFalseReturnEncoding))
      · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
        exact tlcReEquivDecodeFailed hcode
          (tlcSuppIfaceBoundsRev (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
            (solcDecodeLenCheckHuge_4_32 hbigge hsize))
          (tlcSelectorDispatchSupportsInterface hsel)
          (tlcDecodeSupportsInterface_none_huge hbigge)
    · have hshort : I.calldata.size < 36 := by omega
      exact tlcReEquivDecodeFailed hcode
        (tlcSuppIfaceBoundsRev (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
          (solcDecodeLenCheckShort_4_32 hsz4 hshort hsize))
        (tlcSelectorDispatchSupportsInterface hsel)
        (tlcDecodeSupportsInterface_none_short hsz4 hshort)
  · obtain ⟨_, _, h478⟩ := tlcReachSupportsInterface (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
    have hrev := tlcGuardPeelRev (gt := ⟨489⟩) h478 hwv (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    exact tlcNonpayableRevert hcode hrev (tlcSelectorDispatchSupportsInterface hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end OpenZeppelinBench.TimelockController
