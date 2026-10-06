import Reasoning.StateFacts
import Reasoning.MemoryArithmetic
import Reasoning.WordArithmetic
import Reasoning.Memory
import Benchmarks.WETH9.StringReturnBound
import Benchmarks.WETH9.ConstructorTrusted

/-! # WETH9 dynamic-string ABI-encode reconciliation (shared by `name()` and `symbol()`)

Header/word/slot-parametric machinery connecting the Solm total-decode string value (`.bytes`) to the
EVM encoder's `weth9{Empty,Short}StringAbi` / the long tail-mask.  `Name.lean`/`Symbol.lean` specialise
these to slot 0 / slot 1. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.WETH9

/-! ## Length-word bridge: EVM `weth9StringLen` = the Solm total-decode length word -/


theorem weth9StringLen_eq_evmLenWord (H : UInt256) :
    weth9StringLen H = weth9EvmLenWord H := by
  unfold weth9StringLen weth9StringMask weth9EvmLenWord
  rw [lnot_zero_add,
    u256_land_comm H (UInt256.sub (UInt256.mul ⟨256⟩ (UInt256.isZero (UInt256.land H ⟨1⟩))) ⟨1⟩),
    u256_land_comm H ⟨1⟩]

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
    rw [natBytes_toByteArray']; rfl
  have e2 : (ABI.natBytes (H.toByteArray.extract 0 (weth9StringLen H).toNat).size).toByteArray
      = UInt256.toByteArray (weth9StringLen H) := by
    rw [natBytes_toByteArray', hbsize, u256_ofNat_toNat]
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


theorem wordConcat_size (f : Nat → UInt256) (idx n : Nat) : (wordConcat f idx n).size = 32 * n := by
  induction n generalizing idx with
  | zero => rfl
  | succ n ih => rw [wordConcat_succ, ByteArray.size_append, ih, toByteArray_size]; ring


theorem land31_toNat_mod (H : UInt256) :
    (UInt256.land ⟨31⟩ (weth9StringLen H)).toNat = (weth9StringLen H).toNat % 32 := by
  rw [uland_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide, Nat.and_comm,
    show (31 : ℕ) = 2 ^ 5 - 1 from by norm_num, Nat.and_two_pow_sub_one_eq_mod,
    show (2 : ℕ) ^ 5 = 32 from by norm_num]

/-! ## Solm-side storage helpers (slot-parametric) -/


/-- The keccak-data word at an arbitrary slot, as read from `initState σ`. -/
theorem weth9LongStorageLoad {σ σ₀ A I} {g : Sat256} (slot : UInt256) :
    EVM.storageLoad (initState σ σ₀ g A I)
        (initState σ σ₀ g A I).executionEnv.codeOwner slot =
      weth9LongStorageWord σ I slot := by
  simp [EVM.storageLoad, State.lookupAccount, initState, weth9LongStorageWord, Account.lookupStorage]

/-- A storage load in the shared EVM state is reflexive. -/
theorem weth9StorageLoad_bridge {σ σ₀ A I} {g : Sat256} (slot : UInt256) :
    EVM.storageLoad (initState σ σ₀ g A I)
        (initState σ σ₀ g A I).executionEnv.codeOwner slot =
      EVM.storageLoad (initState σ σ₀ g A I)
        (initState σ σ₀ g A I).executionEnv.codeOwner slot := rfl

/-- The slot word is identical when both sides use the same account map. -/
theorem weth9StringSlotWord_bridge {σ : AccountMap} {I : ExecutionEnv} (slot : UInt256) :
    solcSlotWord σ I slot = solcSlotWord σ I slot := rfl

/-- The keccak-region reads agree when both sides use the same EVM state. -/
theorem weth9DataWords_bridge {σ σ₀ A I} {g : Sat256} (baseSlot : UInt256) (n : Nat) :
    readSolidityBytesDataWordsFrom (initState σ σ₀ g A I) baseSlot 0 n =
      readSolidityBytesDataWordsFrom (initState σ σ₀ g A I) baseSlot 0 n := rfl

end Benchmarks.WETH9
