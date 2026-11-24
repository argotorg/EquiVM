import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_051
import Benchmarks.Safe.V0_cdb2eb5.PackedAddress
import Reasoning.ABIViews
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_031
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_050

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

namespace Benchmarks.Safe.V0_cdb2eb5

set_option maxRecDepth 100000

def bytes4Mask : UInt256 :=
  UInt256.lnot (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨224⟩) ⟨1⟩)

theorem bytes4Mask_eq : bytes4Mask = UInt256.ofNat (2 ^ 256 - 2 ^ 224) := by
  native_decide

theorem bytes4Canonical_iff (w : UInt256) :
    w = UInt256.land w bytes4Mask ↔ w.toNat % 2 ^ 224 = 0 := by
  have hm : (UInt256.land w bytes4Mask).toNat = w.toNat / 2 ^ 224 * 2 ^ 224 := by
    rw [bytes4Mask_eq, u256_land_comm]
    exact u256_land_high_mask_toNat w 224 (by decide)
  constructor
  · intro h
    have he := congrArg UInt256.toNat h
    rw [hm] at he
    omega
  · intro h
    apply u256_inj
    rw [hm]
    omega

theorem bytes4Padding (w : UInt256) :
    zeroPadding? (EVM.Word.toBytesBE w) 4 28 =
      if w = UInt256.land w bytes4Mask then some () else none := by
  have hlen : ((EVM.Word.toBytesBE w).drop 4).length = 28 := by
    rw [List.length_drop, word_toBytesBE_length_32]
  have ht : ((EVM.Word.toBytesBE w).drop 4).take 28 =
      (EVM.Word.toBytesBE w).drop 4 := List.take_of_length_le (by omega)
  have hz : ((EVM.Word.toBytesBE w).drop 4).all (· == 0) = true ↔
      w = UInt256.land w bytes4Mask := by
    rw [← fromBytesBigEndian_zero_iff_all_zero, wordBytesBE_drop_value,
      bytes4Canonical_iff]
    rfl
  simp only [zeroPadding?, readBytes?, ht, hlen, ite_true, bind, Option.bind]
  simp only [hz]

def bytes4WordValue (w : UInt256) : Value :=
  .fixedBytes abiBytes4Width ((EVM.Word.toBytesBE w).take 4)

theorem bytes4WordValue_beq {a b : UInt256}
    (ha : a = UInt256.land a bytes4Mask) (hb : b = UInt256.land b bytes4Mask) :
    (bytes4WordValue a == bytes4WordValue b) = decide (a = b) := by
  have hprefix (w : UInt256) :
      fromBytesBigEndian ((EVM.Word.toBytesBE w).take 4) = w.toNat / 2 ^ 224 := by
    simpa only [byteArray_extract0_toList, ← word_toBytesBE_eq_toByteArray_toList]
      using bytesBE_extract_high w 4 (by decide)
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have he : (EVM.Word.toBytesBE a).take 4 = (EVM.Word.toBytesBE b).take 4 := by
      simpa only [bytes4WordValue, Value.fixedBytes.injEq, true_and] using h
    have hn := congrArg fromBytesBigEndian he
    rw [hprefix, hprefix] at hn
    have ham := (bytes4Canonical_iff a).mp ha
    have hbm := (bytes4Canonical_iff b).mp hb
    apply u256_inj
    omega
  · rintro rfl
    rfl

theorem bytes4WordValue_calldata {out : ByteArray} (hl : 32 ≤ out.size) :
    bytes4WordValue (calldataWord out 0) = .fixedBytes abiBytes4Width (out.toList.take 4) := by
  have hh := congrArg ByteArray.toList (calldataWord_bytes hl)
  rw [← word_toBytesBE_eq_toByteArray_toList] at hh
  unfold bytes4WordValue
  rw [hh]
  simp only [byteArray_toList_eq, ByteArray.data_extract, Array.toList_extract,
    List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero, List.take_take]
  rfl

theorem decodeBytes4ReturnLong {out : ByteArray} (hl : 32 ≤ out.size)
    (hb : out.size < 2 ^ 255) :
    ABI.decodeReturnValueWithMode? .modern abiBytes4 out =
      if calldataWord out 0 = UInt256.land (calldataWord out 0) bytes4Mask then
        some (.fixedBytes abiBytes4Width (out.toList.take 4)) else none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hw : EVM.Word.toBytesBE (calldataWord out 0) = out.toList.take 32 := by
    have hh := congrArg ByteArray.toList (calldataWord_bytes hl)
    rw [word_toBytesBE_eq_toByteArray_toList]
    simpa only [byteArray_toList_eq, ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero] using hh
  have hr : readBytes? out.toList 0 32 = some (out.toList.take 32) := by
    simp [readBytes?, List.length_take, hlen, Nat.min_eq_left hl]
  have hp := bytes4Padding (calldataWord out 0)
  rw [hw] at hp
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValue? ABI.decodeReturnValues?
  rw [if_neg (by rw [hlen]; omega)]
  by_cases hc : calldataWord out 0 = UInt256.land (calldataWord out 0) bytes4Mask
  · simp only [if_pos hc] at hp ⊢
    simp [abiTupleHeadSize?, abiBytes4, abiBytes4Width,
      isDynamicABIType, staticABIEncodedSize?, decodeABIValues?, decodeABIValue?, hr,
      hp, List.take_take]
  · simp only [if_neg hc] at hp ⊢
    simp [abiTupleHeadSize?, abiBytes4, abiBytes4Width,
      isDynamicABIType, staticABIEncodedSize?, decodeABIValues?, decodeABIValue?, hr,
      hp, Nat.not_lt_of_ge hl]

theorem decodeBytes4ReturnShort {out : ByteArray} (hl : out.size < 32) :
    ABI.decodeReturnValueWithMode? .modern abiBytes4 out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hr : readBytes? out.toList 0 32 = none := by
    simp [readBytes?, List.length_take, hlen, Nat.min_eq_right (by omega : out.size ≤ 32),
      Nat.ne_of_lt hl]
  simp [ABI.decodeReturnValueWithMode?, ABI.decodeReturnValue?, ABI.decodeReturnValues?,
    hlen, show ¬2 ^ 255 ≤ out.size by omega, abiTupleHeadSize?, abiBytes4, abiBytes4Width,
    isDynamicABIType, staticABIEncodedSize?, decodeABIValues?, decodeABIValue?, hr, hl]

theorem safeBytes4DecoderHead {I g s0 σ k C aw mem rdata} {start ret : UInt256}
    {len : Nat} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨11600⟩
      (start :: (start + UInt256.ofNat len) :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hl : 32 ≤ len) (hb : len < 2 ^ 255) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨11616⟩
      (⟨0⟩ :: start :: (start + UInt256.ofNat len) :: ret :: R) mem aw rdata σ k' C' := by
  have hlt : UInt256.slt (UInt256.ofNat len) (UInt256.ofNat 32) = ⟨0⟩ := by
    apply slt_lit_zero (by decide)
    · rw [ulit_toNat' len (by change len < 2 ^ 256; omega)]; exact hl
    · rw [ulit_toNat' len (by change len < 2 ^ 256; omega)]; exact hb
  exact ⟨_, _, safeRuntime_block_11600_taken (by simp; omega)
    (by rw [word_add_sub_left, hlt]; decide) (by jump_dest) h⟩

theorem safeBytes4DecoderShort {I g s0 σ k C aw mem rdata} {start ret : UInt256}
    {len : Nat} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨11600⟩
      (start :: (start + UInt256.ofNat len) :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hl : len < 32) : RDrev fork safeBytecode g s0 := by
  have hlt : UInt256.slt (UInt256.ofNat len) (UInt256.ofNat 32) = ⟨1⟩ := by
    apply slt_lit_one_low (by decide)
    rw [ulit_toNat' len (by change len < 2 ^ 256; omega)]; exact hl
  have hr := safeRuntime_block_11600_fallthrough (by simp; omega)
    (by rw [word_add_sub_left, hlt]; decide) h
  exact safeRuntime_block_11613 (by simp [safeRuntime_block_11600_fallthrough_stack]; omega) hr

theorem safeBytes4DecoderValid {I g s0 σ k C aw mem rdata} {start ret word : UInt256}
    {len : Nat} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨11600⟩
      (start :: (start + UInt256.ofNat len) :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hl : 32 ≤ len) (hb : len < 2 ^ 255)
    (hm : memLoad start mem = word) (hw : word = UInt256.land word bytes4Mask)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ret (word :: R) mem aw' rdata σ k' C' := by
  obtain ⟨_, _, hd⟩ := safeBytes4DecoderHead h (by omega) hl hb
  have hr := safeRuntime_block_11616_taken (by simp; omega)
    (by rw [hm]; change UInt256.eq word (UInt256.land word bytes4Mask) ≠ ⟨0⟩
        rw [← hw, uInt256_eq_self]; decide) (by jump_dest) hd
  have he := safeRuntime_block_7075 (by omega) hret hr
  exact ⟨_, _, _, by simpa only [safeRuntime_block_7075_stack,
    safeRuntime_block_11616_taken_stack, hm] using he⟩

theorem safeBytes4DecoderNoncanon {I g s0 σ k C aw mem rdata} {start ret word : UInt256}
    {len : Nat} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨11600⟩
      (start :: (start + UInt256.ofNat len) :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hl : 32 ≤ len) (hb : len < 2 ^ 255)
    (hm : memLoad start mem = word) (hw : word ≠ UInt256.land word bytes4Mask) :
    RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, hd⟩ := safeBytes4DecoderHead h (by omega) hl hb
  have hr := safeRuntime_block_11616_fallthrough (by simp; omega)
    (by
      rw [hm]
      exact uInt256_eq_zero_of_ne
        (fun he ↦ hw (uInt256_eq_one_eq he))) hd
  exact safeRuntime_block_11636 (by simp [safeRuntime_block_11616_fallthrough_stack]; omega) hr

end Benchmarks.Safe.V0_cdb2eb5
