import Benchmarks.WETH9.StringReturnBound
import Benchmarks.WETH9.ConstructorTrusted

/-! # WETH9 `Name` refinement

`name()` is a public non-payable getter returning the dynamic string stored at slot 0.  The EVM
return encoder is proved in `StringReturn.lean`/`StringReturnLong2.lean` (empty/short/long); this
module connects those `RDret`s to the Solm `.return [.storage nameRef]` body via `returnEquiv`. -/

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

/-! ## Solm-side `name()` storage read -/

/-- The evaled `name` storage reference. -/
def nameEvaledRef : EvaledStorageRef := { base := "name", steps := [] }

/-- The Solm `name()` body's `.storage nameRef` evaluates through the WETH9 total-decode string
    hook `weth9ReadBytesValue?`. -/
theorem weth9NameStorageRead {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := ∅ } (initState cA gh bl σ σ₀ g A I)
      (.storage nameRef)
    = storageValueResultToEval (weth9ReadBytesValue? storageLayoutRaw
        nameEvaledRef (initState cA gh bl σ σ₀ g A I)) := by
  rw [evalExpr?, resolveStorageRef?_ok (er := nameEvaledRef) (ty := .string)
    (by simp [nameRef])
    (by simp [evalStorageRef, nameRef, nameEvaledRef, EvalResult.bind, bind, pure])
    (by simp [storageTypeAt?, contract, storageDecls, nameEvaledRef])]
  simp only [bind, EvalResult.bind, readStorage?, config, storageLayout, weth9StorageLayout,
    weth9ReadValue?]

/-- The storage word at slot 0 (the compact-string header), as read from `initState σ`. -/
theorem weth9NameHeader {cA gh bl σ σ₀ A I} {g : Sat256} :
    EVM.storageLoad (initState cA gh bl σ σ₀ g A I) (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner ⟨0⟩ =
      weth9StringSlotWord σ I ⟨0⟩ := by
  simp [EVM.storageLoad, State.lookupAccount, initState, weth9StringSlotWord,
    Account.lookupStorage]

theorem weth9NameBaseSlotLen {cA gh bl σ σ₀ A I} {g : Sat256} :
    weth9BytesBaseSlotAndLength? storageLayoutRaw nameEvaledRef (initState cA gh bl σ σ₀ g A I) =
      .ok ((⟨0⟩ : UInt256), (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat) := by
  unfold weth9BytesBaseSlotAndLength?
  simp only [nameEvaledRef, List.nil_append, storageLayoutRaw, bytesLikeLengthLoc,
    apply_ite StorageLoc.slot, ite_self, weth9NameHeader, weth9DecodeBytesLengthHeader_stringLen]

/-- The `.bytes` value the Solm `name()` body returns: the decoded compact string. -/
theorem weth9NameReadValue {cA gh bl σ σ₀ A I} {g : Sat256} :
    weth9ReadBytesValue? storageLayoutRaw nameEvaledRef (initState cA gh bl σ σ₀ g A I) =
      .ok (.bytes (if (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat < 32
        then (weth9StringSlotWord σ I ⟨0⟩).toByteArray.extract 0
          (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat
        else (readSolidityBytesDataWordsFrom (initState cA gh bl σ σ₀ g A I) ⟨0⟩ 0
          (solidityBytesDataWordCount (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat)).extract 0
          (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat)) := by
  unfold weth9ReadBytesValue?
  rw [weth9NameBaseSlotLen]
  simp only [weth9NameHeader]
  split <;> rfl

/-- The full Solm `name()` body `evalExpr?` result. -/
theorem weth9NameEval {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := ∅ } (initState cA gh bl σ σ₀ g A I)
      (.storage nameRef)
    = .ok (.bytes (if (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat < 32
        then (weth9StringSlotWord σ I ⟨0⟩).toByteArray.extract 0
          (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat
        else (readSolidityBytesDataWordsFrom (initState cA gh bl σ σ₀ g A I) ⟨0⟩ 0
          (solidityBytesDataWordCount (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat)).extract 0
          (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat)) := by
  rw [weth9NameStorageRead, weth9NameReadValue]; rfl

/-! ## ABI-encode reconciliation: Solm `.bytes` value ↦ EVM `weth9*StringAbi` -/

/-- Empty string: any size-0 `.bytes` ABI-encodes to `weth9EmptyStringAbi`. -/
theorem weth9NameEncode_empty (b : ByteArray) (hb : b.size = 0) :
    encodeReturnValue? stringTy (.bytes b) = some weth9EmptyStringAbi := by
  rw [byteArray_eq_empty_of_size_eq_zero b hb]; native_decide

/-- The slot-0 header word agrees between the EVM and Solm storages (`accountMapEquiv`). -/
theorem weth9StringSlotWord_bridge {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    weth9StringSlotWord σ_evm I ⟨0⟩ = weth9StringSlotWord σ_solm I ⟨0⟩ := by
  unfold weth9StringSlotWord
  exact accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩

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
    rw [ulit_toNat' _ (by change UInt256.size - 1 < UInt256.size; simp [UInt256.size])]
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

    REMAINING (byte-level masking reconciliation).  `encodeReturnValue? .string (.bytes b)` reduces to
    `⟨(natBytes 32 ++ natBytes b.size ++ padRightToWord b.toList).toArray⟩` (ABI/Encode.lean); the three
    words reconcile to `weth9ShortStringAbi`'s `toByteArray ⟨32⟩ ‖ toByteArray (weth9StringLen H) ‖
    toByteArray (weth9ShortMaskWord H)` via `natBytes n = toByteArray ⟨n⟩` (`toByteArray_eq_toBytesBE`)
    for the first two.  Crux: `⟨(padRightToWord (H.toByteArray.extract 0 len).toList).toArray⟩ =
    toByteArray (weth9ShortMaskWord H)` — prove by the size-32 roundtrip
    `toBytesBE_uInt256OfByteArray_of_size` reducing to `fromByteArrayBigEndian (extract H 0 len ‖
    zeros(32-len)) = (weth9ShortMaskWord H).toNat`, both equal `(H.toNat >>> 8·(32-len)) <<< 8·(32-len)`
    (the mask `land (lnot (256^(32-len)-1)) (shortDataWord H)` clears the low `8·(32-len)` bits). -/
theorem weth9NameEncode_short (H : UInt256) (hne : weth9StringLen H ≠ ⟨0⟩)
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

/-- Long string (`len ≥ 32`): the decoded keccak-data bytes ABI-encode to `weth9LongStringAbi`.

    REMAINING (byte-level, the `wc`-word analog of `weth9NameEncode_short`).  The decoded bytes are
    `(readSolidityBytesDataWordsFrom … 0 wc).extract 0 len` = the `wc` storage data words truncated to
    `len`; `padRightToWord` re-pads to `32·wc`, whose words reconcile to `weth9LongStringAbi`'s
    `wordConcat weth9LongDataWordAt 0 (wc-1) ‖ weth9LongMaskWord` (data words `0..wc-2` verbatim, last
    word tail-masked exactly as the short case) via `byteArray_readWithPadding_split`/`wordConcat` +
    the `weth9LongDataWordAt σ I k = storageLoad (solidityBytesDataSlot ⟨0⟩ k)` identification. -/
theorem weth9NameEncode_long {cA gh bl σ σ₀ A I} {g : Sat256}
    (hge31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) ≠ ⟨0⟩)
    (hfit : 96 + 32 * weth9LongWC σ I < 2 ^ 64) :
    encodeReturnValue? stringTy (.bytes
      ((readSolidityBytesDataWordsFrom (initState cA gh bl σ σ₀ g A I) ⟨0⟩ 0
          (solidityBytesDataWordCount (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat)).extract 0
        (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat)) = some (weth9LongStringAbi σ I) := by
  sorry

/-- A single storage word agrees between the EVM and Solm storages (`accountMapEquiv`). -/
theorem weth9StorageLoad_bridge {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) (slot : UInt256) :
    EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner slot =
      EVM.storageLoad (initState cA gh bl σ_evm σ₀ g A I)
        (initState cA gh bl σ_evm σ₀ g A I).executionEnv.codeOwner slot := by
  simp only [EVM.storageLoad, State.lookupAccount, initState, Account.lookupStorage]
  exact (accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩).symm

/-- The keccak-region data words agree between the EVM and Solm storages (`accountMapEquiv`). -/
theorem weth9NameDataWords_bridge {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) (n : Nat) :
    readSolidityBytesDataWordsFrom (initState cA gh bl σ_solm σ₀ g A I) ⟨0⟩ 0 n =
      readSolidityBytesDataWordsFrom (initState cA gh bl σ_evm σ₀ g A I) ⟨0⟩ 0 n := by
  suffices key : ∀ m idx, readSolidityBytesDataWordsFrom (initState cA gh bl σ_solm σ₀ g A I) ⟨0⟩ idx m =
      readSolidityBytesDataWordsFrom (initState cA gh bl σ_evm σ₀ g A I) ⟨0⟩ idx m from key n 0
  intro m
  induction m with
  | zero => intro idx; rfl
  | succ m ih =>
    intro idx
    unfold readSolidityBytesDataWordsFrom
    rw [weth9StorageLoad_bridge hAccounts, ih (idx + 1)]

/-! ## Dispatch / decode -/

/-- `name()`'s selector (index 0) dispatches to `nameTransition`. -/
theorem weth9SelectorDispatchName {I : ExecutionEnv} (hsel : selIs I (weth9SelBytes 0)) :
    selectorDispatchMsg contract I.calldata = some nameTransition := by
  have hcd : I.calldata.extract 0 4 = weth9SelBytes 0 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp only [contract, dispatchList, selectorOf, hcd,
    weth9NameSelectorBytes, weth9ApproveSelectorBytes, weth9TotalSupplySelectorBytes,
    weth9TransferFromSelectorBytes, weth9WithdrawSelectorBytes, weth9DecimalsSelectorBytes]
  native_decide

/-- `name()` has no parameters: its ABI decode yields the empty store. -/
theorem weth9Decode_name_ok {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (nameTransition.params.map Param.name)
      (transitionSignature nameTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz4

theorem weth9NameBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (weth9SelBytes 0))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (weth9SelBytes 0) (by native_decide) hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · -- string return: the Solm `.return [.storage nameRef]` body ABI-encodes to the EVM encoder's
    -- output (`StringReturnLong2.lean`); `weth9NameReturnSizeBound` handles the ≥2^64-byte regime.
    have hbody := nonpayableReturnExprBodyReturns (cfg := config) (contract := contract)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (locals := ∅)
      (by simp only [initState]; exact hwv) weth9NameEval
    have hHbr : weth9StringSlotWord σ_solm I ⟨0⟩ = weth9StringSlotWord σ_evm I ⟨0⟩ :=
      (weth9StringSlotWord_bridge (I := I) hAccounts).symm
    by_cases hlen0 : weth9StringLen (weth9StringSlotWord σ_evm I ⟨0⟩) = ⟨0⟩
    · -- EMPTY (len = 0)
      have hlen0' : (weth9StringLen (weth9StringSlotWord σ_solm I ⟨0⟩)).toNat = 0 := by
        rw [hHbr, hlen0]; rfl
      exact weth9ReEquivExecTransport hcode
        (weth9NameStringEmptyReturns (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel hlen0)
        (weth9SelectorDispatchName hsel) (weth9Decode_name_ok hsz4)
        (by rw [nameTransition]; exact hbody) rfl hAccounts
        (returnEquiv_of_encode (weth9NameEncode_empty _ (by
          simp only [hlen0', show (0 : Nat) < 32 from by norm_num, if_true, ByteArray.size_extract]
          omega)))
    · by_cases hlt31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ_evm I ⟨0⟩)) = ⟨0⟩
      · -- SHORT (0 < len < 32)
        have hlt32 : (weth9StringLen (weth9StringSlotWord σ_evm I ⟨0⟩)).toNat < 32 := by
          have := weth9StringLen_toNat_le31 hlt31; omega
        exact weth9ReEquivExecTransport hcode
          (weth9NameStringShortReturns (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel hlen0 hlt31)
          (weth9SelectorDispatchName hsel) (weth9Decode_name_ok hsz4)
          (by rw [nameTransition]; exact hbody) rfl hAccounts
          (returnEquiv_of_encode (by
            rw [hHbr, if_pos hlt32]; exact weth9NameEncode_short _ hlen0 hlt31))
      · -- LONG (len ≥ 32)
        have hge31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ_evm I ⟨0⟩)) ≠ ⟨0⟩ := hlt31
        have hge32 : ¬ (weth9StringLen (weth9StringSlotWord σ_evm I ⟨0⟩)).toNat < 32 := by
          have := weth9LongLen_ge32 hge31; omega
        exact weth9ReEquivExecTransport hcode
          (weth9NameStringLongReturns (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel hge31
            (weth9NameReturnSizeBound σ_evm I))
          (weth9SelectorDispatchName hsel) (weth9Decode_name_ok hsz4)
          (by rw [nameTransition]; exact hbody) rfl hAccounts
          (returnEquiv_of_encode (by
            rw [hHbr, if_neg hge32, weth9NameDataWords_bridge hAccounts]
            exact weth9NameEncode_long hge31 (weth9NameReturnSizeBound σ_evm I)))
  · -- non-payable revert: EVM reverts at name's callvalue guard (entry 166, gt 178).
    obtain ⟨_, _, h166⟩ := weth9ReachName (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
    have hrev := weth9GuardPeelRev (gt := ⟨178⟩) h166 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    exact weth9NonpayableRevert hcode hrev (weth9SelectorDispatchName hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.WETH9
