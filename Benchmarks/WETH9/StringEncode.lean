import Benchmarks.WETH9.StringReturnBound
import Benchmarks.WETH9.ConstructorTrusted

/-! # WETH9 dynamic-string ABI-encode reconciliation (shared by `name()` and `symbol()`)

Header/word/slot-parametric machinery connecting the Solm total-decode string value (`.bytes`) to the
EVM encoder's `weth9{Empty,Short}StringAbi` / the long tail-mask.  `Name.lean`/`Symbol.lean` specialise
these to slot 0 / slot 1. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.WETH9

/-! ## Length-word bridge: EVM `weth9StringLen` = the Solm total-decode length word -/

/-- `~0 + Z = Z - 1` (the long-flag mask arithmetic equals a `sub … 1`). -/
theorem lnot_zero_add (Z : UInt256) : UInt256.lnot ⟨0⟩ + Z = UInt256.sub Z ⟨1⟩ := by
  apply u256_inj
  have hlnot : (UInt256.lnot ⟨0⟩).toNat = 2 ^ 256 - 1 := by unfold UInt256.lnot; decide
  have h1 : (⟨1⟩ : UInt256).toNat = 1 := by decide
  have hZ : Z.toNat < UInt256.size := Z.val.isLt
  rw [show UInt256.size = 2 ^ 256 from by decide] at hZ
  rcases Nat.eq_zero_or_pos Z.toNat with hz | hz
  · rw [uadd_toNat, hlnot, usub_toNat_underflow (by rw [hz, h1]; omega), hz, h1,
      show UInt256.size = 2 ^ 256 from by decide]; omega
  · rw [uadd_toNat, hlnot, usub_toNat (by rw [h1]; omega), h1,
      show UInt256.size = 2 ^ 256 from by decide]; omega

theorem weth9StringLen_eq_evmLenWord (H : UInt256) :
    weth9StringLen H = weth9EvmLenWord H := by
  unfold weth9StringLen weth9StringMask weth9EvmLenWord
  rw [lnot_zero_add,
    uland_comm H (UInt256.sub (UInt256.mul ⟨256⟩ (UInt256.isZero (UInt256.land H ⟨1⟩))) ⟨1⟩),
    uland_comm H ⟨1⟩]

/-- The Solm total decode of `H` yields `(weth9StringLen H).toNat`. -/
theorem weth9DecodeBytesLengthHeader_stringLen (H : UInt256) :
    weth9DecodeBytesLengthHeader H = .ok (weth9StringLen H).toNat := by
  rw [weth9DecodeBytesLengthHeader_eq, weth9StringLen_eq_evmLenWord, weth9EvmLenWord_eq]

/-! ## Empty-string encode -/

/-- Empty string: any size-0 `.bytes` ABI-encodes to `weth9EmptyStringAbi`. -/
theorem weth9EncodeEmpty (b : ByteArray) (hb : b.size = 0) :
    encodeReturnValue? stringTy (.bytes b) = some weth9EmptyStringAbi := by
  rw [byteArray_eq_empty_of_size_eq_zero b hb]; native_decide

/-! ## Byte-level encode reconciliation helpers -/

/-- `encodeReturnValue? .string (.bytes b)` reduces to `offset word ‖ length word ‖ padded data`. -/
theorem encode_string_bytes (b : ByteArray) :
    encodeReturnValue? stringTy (.bytes b) =
      some ⟨(ABI.natBytes 32 ++ (ABI.natBytes b.size ++ ABI.padRightToWord b.toList)).toArray⟩ := by
  simp only [encodeReturnValue?, encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?,
    abiTupleHeadSize?, encodeABIValue?, isDynamicABIType, staticABIEncodedSize?, stringTy,
    Option.bind, bind, if_true, List.nil_append, List.append_nil, Nat.add_zero, List.length_nil]

/-- `~x` as a word value: `2^256 - 1 - x`. -/
theorem lnot_toNat_gen (x : UInt256) : (UInt256.lnot x).toNat = 2 ^ 256 - 1 - x.toNat := by
  have hx : x.toNat < 2 ^ 256 := by change x.val.val < 2 ^ 256; simpa [UInt256.size] using x.val.isLt
  have hsz : (UInt256.ofNat (UInt256.size - 1)).toNat = 2 ^ 256 - 1 := by
    rw [ulit_toNat' _ (by simp [UInt256.size])]
    rfl
  show (UInt256.sub (UInt256.ofNat (UInt256.size - 1)) x).toNat = 2 ^ 256 - 1 - x.toNat
  rw [usub_toNat (by rw [hsz]; omega), hsz]

/-- `256^e` fits in a word for `e ≤ 31`, and `EXP 256 e = 256^e`. -/
theorem exp256_toNat (e : ℕ) (he : e ≤ 31) :
    (UInt256.exp ⟨256⟩ (UInt256.ofNat e)).toNat = 256 ^ e := by
  interval_cases e <;> native_decide

theorem byteArray_extract0_toList (b : ByteArray) (r : ℕ) :
    (b.extract 0 r).toList = b.toList.take r := by
  rw [byteArray_toList_eq, byteArray_toList_eq, ByteArray.data_extract, Array.toList_extract]; simp

theorem fromBytesBE_word (w : UInt256) : fromBytesBigEndian (EVM.Word.toBytesBE w) = w.toNat := by
  have h := congrArg fromByteArrayBigEndian (word_toBytesBE_toByteArray_eq_toByteArray w)
  simpa [fromByteArrayBigEndian, byteArray_toList_eq] using
    h.trans (fromByteArrayBigEndian_toByteArray w)

theorem bytesBE_extract_high (w : UInt256) (r : ℕ) (hr : r ≤ 32) :
    fromBytesBigEndian ((w.toByteArray.extract 0 r).toList) = w.toNat / 2 ^ (8 * (32 - r)) := by
  have hbs : (w.toByteArray).toList = EVM.Word.toBytesBE w := by
    rw [toByteArray_eq_toBytesBE]; simp [byteArray_toList_eq]
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    rw [← hbs, byteArray_toList_eq, Array.length_toList]; exact toByteArray_size w
  rw [byteArray_extract0_toList, hbs]
  have hdroplen : ((EVM.Word.toBytesBE w).drop r).length = 32 - r := by
    rw [List.length_drop, hlen]
  have key := fromBytesBigEndian_append_div ((EVM.Word.toBytesBE w).take r)
    ((EVM.Word.toBytesBE w).drop r)
  rw [List.take_append_drop, hdroplen] at key
  rw [← key, fromBytesBE_word]

theorem toBytesBE_length (w : UInt256) : (EVM.Word.toBytesBE w).length = 32 := by
  have hbs : (w.toByteArray).toList = EVM.Word.toBytesBE w := by
    rw [toByteArray_eq_toBytesBE]; simp [byteArray_toList_eq]
  rw [← hbs, byteArray_toList_eq, Array.length_toList]; exact toByteArray_size w

/-- **Tail-mask reconciliation (the crux).**  The runtime's masked last data word `~(2^(8·(32-r))-1) &
    w` — clearing the low `8·(32-r)` bytes — equals the ABI's `w`-prefix `extract 0 r` zero-padded to a
    full word.  Shared by the short case (`r = len`) and the long final word (`r = len mod 32`). -/
theorem tailMask_toByteArray (w L : UInt256) (hr : 0 < L.toNat) (hr31 : L.toNat ≤ 31) :
    UInt256.toByteArray (UInt256.land (UInt256.lnot (UInt256.sub
        (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩ L)) ⟨1⟩)) w) =
      ⟨((w.toByteArray.extract 0 L.toNat).toList ++ List.replicate (32 - L.toNat) 0).toArray⟩ := by
  have hr32 : L.toNat ≤ 32 := by omega
  have h32 : (⟨32⟩ : UInt256).toNat = 32 := by decide
  have h1 : (⟨1⟩ : UInt256).toNat = 1 := by decide
  have hwlt : w.toNat < 2 ^ 256 := by
    change w.val.val < 2 ^ 256; simpa [UInt256.size] using w.val.isLt
  have hsubeq : UInt256.sub ⟨32⟩ L = UInt256.ofNat (32 - L.toNat) := by
    apply u256_inj
    rw [usub_toNat (by rw [h32]; exact hr32), h32,
      ulit_toNat' _ (by rw [show UInt256.size = 2 ^ 256 from by decide]; omega)]
  have hexp : (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩ L)).toNat = 2 ^ (8 * (32 - L.toNat)) := by
    rw [hsubeq, exp256_toNat (32 - L.toNat) (by omega),
      show (256 : ℕ) = 2 ^ 8 from by norm_num, ← Nat.pow_mul]
  have h2mpos : 1 ≤ 2 ^ (8 * (32 - L.toNat)) := Nat.one_le_two_pow
  have h2mle : 2 ^ (8 * (32 - L.toNat)) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hX : (UInt256.sub (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩ L)) ⟨1⟩).toNat
      = 2 ^ (8 * (32 - L.toNat)) - 1 := by
    rw [usub_toNat (by rw [h1, hexp]; exact h2mpos), hexp, h1]
  have hlnotX : (UInt256.lnot (UInt256.sub (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩ L)) ⟨1⟩)).toNat
      = 2 ^ 256 - 2 ^ (8 * (32 - L.toNat)) := by
    rw [lnot_toNat_gen, hX]; omega
  have hlnotXeq : UInt256.lnot (UInt256.sub (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩ L)) ⟨1⟩)
      = UInt256.ofNat (2 ^ 256 - 2 ^ (8 * (32 - L.toNat))) := by
    apply u256_inj
    rw [hlnotX, ulit_toNat' _ (by rw [show UInt256.size = 2 ^ 256 from by decide]; omega)]
  have hmask : (UInt256.land (UInt256.lnot (UInt256.sub
        (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩ L)) ⟨1⟩)) w).toNat
      = w.toNat / 2 ^ (8 * (32 - L.toNat)) * 2 ^ (8 * (32 - L.toNat)) := by
    rw [hlnotXeq]
    exact u256_land_high_mask_toNat w (8 * (32 - L.toNat)) (by omega)
  have hextlen : (w.toByteArray.extract 0 L.toNat).toList.length = L.toNat := by
    rw [byteArray_extract0_toList, List.length_take, byteArray_toList_eq, Array.length_toList]
    have hsz : (w.toByteArray).data.size = 32 := toByteArray_size w
    omega
  have hlist : EVM.Word.toBytesBE (UInt256.land (UInt256.lnot (UInt256.sub
        (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩ L)) ⟨1⟩)) w)
      = (w.toByteArray.extract 0 L.toNat).toList ++ List.replicate (32 - L.toNat) 0 := by
    apply fromBytesBigEndian_inj_of_length
    · rw [toBytesBE_length, List.length_append, hextlen, List.length_replicate]; omega
    · rw [fromBytesBE_word, hmask, fromBytesBigEndian_append_zeros,
        bytesBE_extract_high w L.toNat hr32]
  rw [toByteArray_eq_toBytesBE, hlist]

theorem mk_toArray_eq (l : List UInt8) : (⟨l.toArray⟩ : ByteArray) = l.toByteArray := by
  rw [← List.data_toByteArray]

theorem natBytes_toByteArray (n : ℕ) :
    (ABI.natBytes n).toByteArray = UInt256.toByteArray (UInt256.ofNat n) := by
  show (EVM.Word.toBytesBE (UInt256.ofNat n)).toByteArray = _
  exact word_toBytesBE_toByteArray_eq_toByteArray _

theorem paddedSize_of_pos_le32 (r : ℕ) (h1 : 0 < r) (h2 : r ≤ 32) : ABI.paddedSize r = 32 := by
  unfold ABI.paddedSize; rw [show (r + 31) / 32 = 1 from by omega]

theorem shortDataWord_toNat (H : UInt256) :
    (weth9StringShortDataWord H).toNat = H.toNat / 256 * 256 := by
  have hHlt : H.toNat < 2 ^ 256 := by
    change H.val.val < 2 ^ 256; simpa [UInt256.size] using H.val.isLt
  rw [weth9StringShortDataWord, u256_mul_toNat, udiv_toNat,
    show (⟨256⟩ : UInt256).toNat = 256 from by decide,
    show UInt256.size = 2 ^ 256 from by decide,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self H.toNat 256) hHlt)]

/-- Clearing `H`'s low byte does not change any bit at position `≥ 8`, so the high `≥ 8`-bit
    quotients agree. -/
theorem shortDataWord_div_eq (H : UInt256) (d : ℕ) (hd : 8 ≤ d) :
    (weth9StringShortDataWord H).toNat / 2 ^ d = H.toNat / 2 ^ d := by
  have hpow : (2 : ℕ) ^ d = 256 * 2 ^ (d - 8) := by
    rw [show (256 : ℕ) = 2 ^ 8 from by norm_num, ← pow_add]; congr 1; omega
  rw [shortDataWord_toNat, hpow, Nat.mul_comm (H.toNat / 256) 256,
    Nat.mul_div_mul_left _ _ (by norm_num : 0 < 256), ← Nat.div_div_eq_div_mul]

/-- The high `len` bytes of the inline data word are `H`'s high bytes (`len ≤ 31`). -/
theorem shortExtract_eq (H : UInt256)
    (hlt31 : UInt256.lt ⟨31⟩ (weth9StringLen H) = ⟨0⟩) :
    ((weth9StringShortDataWord H).toByteArray.extract 0 (weth9StringLen H).toNat).toList =
      (H.toByteArray.extract 0 (weth9StringLen H).toNat).toList := by
  have hr31 : (weth9StringLen H).toNat ≤ 31 := weth9StringLen_toNat_le31 hlt31
  apply fromBytesBigEndian_inj_of_length
  · rw [byteArray_extract0_toList, byteArray_extract0_toList, List.length_take, List.length_take,
      byteArray_toList_eq, byteArray_toList_eq, Array.length_toList, Array.length_toList]
    have h1 : (weth9StringShortDataWord H).toByteArray.data.size = 32 := toByteArray_size _
    have h2 : H.toByteArray.data.size = 32 := toByteArray_size _
    rw [h1, h2]
  · rw [bytesBE_extract_high _ _ (by omega), bytesBE_extract_high _ _ (by omega),
      shortDataWord_div_eq H (8 * (32 - (weth9StringLen H).toNat)) (by omega)]

/-- Short string (`0 < len < 32`): the decoded inline bytes ABI-encode to `weth9ShortStringAbi`.
    Header-parametric: applies to any slot's compact header `H`. -/
theorem weth9EncodeShort (H : UInt256) (hne : weth9StringLen H ≠ ⟨0⟩)
    (hlt31 : UInt256.lt ⟨31⟩ (weth9StringLen H) = ⟨0⟩) :
    encodeReturnValue? stringTy (.bytes (H.toByteArray.extract 0 (weth9StringLen H).toNat)) =
      some (weth9ShortStringAbi H) := by
  have hrpos : 0 < (weth9StringLen H).toNat := weth9StringLen_toNat_pos hne
  have hr31 : (weth9StringLen H).toNat ≤ 31 := weth9StringLen_toNat_le31 hlt31
  have hbsize : (H.toByteArray.extract 0 (weth9StringLen H).toNat).size = (weth9StringLen H).toNat := by
    rw [ByteArray.size_extract, toByteArray_size]; omega
  have hblen : (H.toByteArray.extract 0 (weth9StringLen H).toNat).toList.length =
      (weth9StringLen H).toNat := by
    rw [byteArray_toList_eq, Array.length_toList]; exact hbsize
  have e1 : (ABI.natBytes 32).toByteArray = UInt256.toByteArray ⟨32⟩ := by
    rw [natBytes_toByteArray]; rfl
  have e2 : (ABI.natBytes (H.toByteArray.extract 0 (weth9StringLen H).toNat).size).toByteArray
      = UInt256.toByteArray (weth9StringLen H) := by
    rw [natBytes_toByteArray, hbsize, u256_ofNat_toNat]
  have e3 : (ABI.padRightToWord (H.toByteArray.extract 0 (weth9StringLen H).toNat).toList).toByteArray
      = UInt256.toByteArray (weth9ShortMaskWord H) := by
    have hpad : ABI.padRightToWord (H.toByteArray.extract 0 (weth9StringLen H).toNat).toList
        = (H.toByteArray.extract 0 (weth9StringLen H).toNat).toList ++
          List.replicate (32 - (weth9StringLen H).toNat) 0 := by
      unfold ABI.padRightToWord ABI.zeroBytes
      rw [hblen, paddedSize_of_pos_le32 _ hrpos (by omega)]
    have hmaskform : weth9ShortMaskWord H = UInt256.land (UInt256.lnot (UInt256.sub
        (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩ (weth9StringLen H))) ⟨1⟩)) (weth9StringShortDataWord H) := by
      rw [weth9ShortMaskWord, weth9StringLand31_eq hlt31]
    rw [hpad, List.toByteArray_append, hmaskform,
      tailMask_toByteArray (weth9StringShortDataWord H) (weth9StringLen H) hrpos hr31,
      mk_toArray_eq, List.toByteArray_append, ← shortExtract_eq H hlt31]
  rw [encode_string_bytes, weth9ShortStringAbi, mk_toArray_eq, List.toByteArray_append,
    List.toByteArray_append, e1, e2, e3]

/-! ## Long-case shared helpers -/

theorem uadd_zero_r (a : UInt256) : a + ⟨0⟩ = a := by
  apply u256_inj
  rw [uadd_toNat, show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.add_zero]
  exact Nat.mod_eq_of_lt a.val.isLt

theorem ofNat_toNat_mod (k : ℕ) : (UInt256.ofNat k).toNat = k % UInt256.size := rfl

theorem uadd_ofNat_succ (b : UInt256) (k : ℕ) :
    (⟨1⟩ : UInt256) + (b + UInt256.ofNat k) = b + UInt256.ofNat (k + 1) := by
  apply u256_inj
  simp only [uadd_toNat, ofNat_toNat_mod, show (⟨1⟩ : UInt256).toNat = 1 from rfl,
    Nat.add_mod_mod]
  congr 1
  omega

theorem wordConcat_size (f : Nat → UInt256) (idx n : Nat) : (wordConcat f idx n).size = 32 * n := by
  induction n generalizing idx with
  | zero => rfl
  | succ n ih => rw [wordConcat_succ, ByteArray.size_append, ih, toByteArray_size]; ring

theorem toList_toByteArray_roundtrip (b : ByteArray) : b.toList.toByteArray = b := by
  apply ByteArray.ext
  rw [List.data_toByteArray, byteArray_toList_eq]

theorem bytearray_append_list_eq (X : ByteArray) (Y : List UInt8) :
    X ++ Y.toByteArray = ⟨(X.toList ++ Y).toArray⟩ := by
  rw [mk_toArray_eq, List.toByteArray_append, toList_toByteArray_roundtrip]

theorem land31_toNat_mod (H : UInt256) :
    (UInt256.land ⟨31⟩ (weth9StringLen H)).toNat = (weth9StringLen H).toNat % 32 := by
  rw [uland_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide, Nat.and_comm,
    show (31 : ℕ) = 2 ^ 5 - 1 from by norm_num, Nat.and_two_pow_sub_one_eq_mod,
    show (2 : ℕ) ^ 5 = 32 from by norm_num]

/-! ## Solm-side storage helpers (slot-parametric) -/

/-- The storage word at an arbitrary slot, as read from `initState σ`. -/
theorem weth9Header {cA gh bl σ σ₀ A I} {g : Sat256} (slot : UInt256) :
    EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
        (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner slot =
      weth9StringSlotWord σ I slot := by
  simp [EVM.storageLoad, State.lookupAccount, initState, weth9StringSlotWord,
    Account.lookupStorage]

/-- The keccak-data word at an arbitrary slot, as read from `initState σ`. -/
theorem weth9LongStorageLoad {cA gh bl σ σ₀ A I} {g : Sat256} (slot : UInt256) :
    EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
        (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner slot =
      weth9LongStorageWord σ I slot := by
  simp [EVM.storageLoad, State.lookupAccount, initState, weth9LongStorageWord, Account.lookupStorage]

/-- A single storage word agrees between the EVM and Solm storages (`accountMapEquiv`). -/
theorem weth9StorageLoad_bridge {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) (slot : UInt256) :
    EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner slot =
      EVM.storageLoad (initState cA gh bl σ_evm σ₀ g A I)
        (initState cA gh bl σ_evm σ₀ g A I).executionEnv.codeOwner slot := by
  simp only [EVM.storageLoad, State.lookupAccount, initState, Account.lookupStorage]
  exact (accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩).symm

/-- The slot-0/1 header word agrees between the EVM and Solm storages (`accountMapEquiv`). -/
theorem weth9StringSlotWord_bridge {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) (slot : UInt256) :
    weth9StringSlotWord σ_evm I slot = weth9StringSlotWord σ_solm I slot := by
  unfold weth9StringSlotWord
  exact accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩

/-- The keccak-region data words agree between the EVM and Solm storages (`accountMapEquiv`). -/
theorem weth9DataWords_bridge {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) (baseSlot : UInt256) (n : Nat) :
    readSolidityBytesDataWordsFrom (initState cA gh bl σ_solm σ₀ g A I) baseSlot 0 n =
      readSolidityBytesDataWordsFrom (initState cA gh bl σ_evm σ₀ g A I) baseSlot 0 n := by
  suffices key : ∀ m idx,
      readSolidityBytesDataWordsFrom (initState cA gh bl σ_solm σ₀ g A I) baseSlot idx m =
        readSolidityBytesDataWordsFrom (initState cA gh bl σ_evm σ₀ g A I) baseSlot idx m from key n 0
  intro m
  induction m with
  | zero => intro idx; rfl
  | succ m ih =>
    intro idx
    unfold readSolidityBytesDataWordsFrom
    rw [weth9StorageLoad_bridge hAccounts, ih (idx + 1)]

end Benchmarks.WETH9
