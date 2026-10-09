import Benchmarks.Morpho.MetaMorphoV1_1.BodyCommon
import Reasoning.MemCascade
import Reasoning.ABIViews

/-! Shared encoding and memory facts for multiple return values. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- GENERALIZES Reasoning.MemCascade.twoWordHashMem_read0_64_any to any output offset.
theorem twoWordWrite_read (mem : ByteArray) (off : Nat) (first second : UInt256) :
    (writeWord (writeWord mem off first) (off + 32) second).readWithPadding off 64 =
      first.toByteArray ++ second.toByteArray := by
  rw [byteArray_readWithPadding_split_unbounded _ off 32 32 (by decide) (by decide)
    (by rw [writeWord_sparse_size]; omega)]
  rw [writeWord_sparse_read_preserved _ (off + 32) off second
    (Or.inl ⟨le_refl _, by rw [writeWord_sparse_size]; omega⟩)]
  rw [writeWord_sparse_read_back, writeWord_sparse_read_back]

-- LIBRARY CANDIDATE: return a pair using an end pointer and the saved start pointer.
theorem returnPairMemoryByEnd (mem : ByteArray) (first second : UInt256)
    (hptr : memLoad ⟨64⟩ mem = ⟨128⟩) :
    (second.toByteArray.write 0
      (first.toByteArray.write 0 mem (memLoad ⟨64⟩ mem).toNat 32)
      (memLoad ⟨64⟩ mem + ⟨32⟩).toNat 32).readWithPadding
        (memLoad ⟨64⟩ mem).toNat
        (UInt256.sub (memLoad ⟨64⟩ mem + ⟨64⟩) (memLoad ⟨64⟩ mem)).toNat =
      first.toByteArray ++ second.toByteArray := by
  rw [hptr]
  exact twoWordWrite_read mem 128 first second

-- LIBRARY CANDIDATE: read three consecutive ABI word writes at any memory offset.
theorem threeWordWrite_read (mem : ByteArray) (off : Nat) (a b c : UInt256) :
    (writeWord (writeWord (writeWord mem off a) (off + 32) b) (off + 64) c).readWithPadding
      off 96 = a.toByteArray ++ (b.toByteArray ++ c.toByteArray) := by
  rw [byteArray_readWithPadding_split_unbounded _ off 32 64 (by decide) (by decide)
    (by rw [writeWord_sparse_size]; omega)]
  rw [writeWord_sparse_read_preserved _ (off + 64) off c
    (Or.inl ⟨by omega, by rw [writeWord_sparse_size]; omega⟩)]
  rw [writeWord_sparse_read_preserved _ (off + 32) off b
    (Or.inl ⟨le_refl _, by rw [writeWord_sparse_size]; omega⟩)]
  rw [writeWord_sparse_read_back]
  exact congrArg (fun bytes ↦ a.toByteArray ++ bytes)
    (by simpa only [Nat.add_assoc] using twoWordWrite_read (writeWord mem off a) (off + 32) b c)

-- LIBRARY CANDIDATE: three return words at the saved initial free-memory pointer.
theorem returnTripleMemory (mem : ByteArray) (a b c : UInt256)
    (hptr : memLoad ⟨64⟩ mem = ⟨128⟩) :
    (c.toByteArray.write 0 (b.toByteArray.write 0
      (a.toByteArray.write 0 mem (memLoad ⟨64⟩ mem).toNat 32)
      (memLoad ⟨64⟩ mem + ⟨32⟩).toNat 32)
      (memLoad ⟨64⟩ mem + ⟨64⟩).toNat 32).readWithPadding
        (memLoad ⟨64⟩ mem).toNat 96 = a.toByteArray ++ (b.toByteArray ++ c.toByteArray) := by
  rw [hptr]
  exact threeWordWrite_read mem 128 a b c

-- LIBRARY CANDIDATE: two ABI words returned through the initial solc free-memory pointer.
theorem returnPairMemory (first second : UInt256) :
    (second.toByteArray.write 0
      (first.toByteArray.write 0 solcFreePtrMem (memLoad ⟨64⟩ solcFreePtrMem).toNat 32)
      (memLoad ⟨64⟩ solcFreePtrMem + ⟨32⟩).toNat 32).readWithPadding
        (memLoad ⟨64⟩ solcFreePtrMem).toNat 64 = first.toByteArray ++ second.toByteArray := by
  have hload : memLoad ⟨64⟩ solcFreePtrMem = ⟨128⟩ := solcFreePtrMem_mload64
  rw [hload]
  exact twoWordWrite_read solcFreePtrMem 128 first second

-- GENERALIZES Reasoning.ABIViews.uint256PairReturnEncoding to any two static scalar types.
theorem scalarPairReturnEncoding {t₁ t₂ : ABIType} {v₁ v₂ : Value} {w₁ w₂ : UInt256}
    (hd₁ : isDynamicABIType t₁ = false) (hd₂ : isDynamicABIType t₂ = false)
    (hhead : abiTupleHeadSize? [t₁, t₂] = some 64)
    (hv₁ : encodeABIValue? t₁ v₁ = some (EVM.Word.toBytesBE w₁))
    (hv₂ : encodeABIValue? t₂ v₂ = some (EVM.Word.toBytesBE w₂)) :
    encodeReturnValues? [t₁, t₂] [v₁, v₂] = some (w₁.toByteArray ++ w₂.toByteArray) := by
  simp only [encodeReturnValues?, encodeABIValues?, hhead, encodeABIValuesFrom?, hv₁, hv₂,
    hd₁, hd₂, bind, Option.bind, Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  rw [toByteArray_eq_toBytesBE, toByteArray_eq_toBytesBE]
  apply congrArg some
  apply ByteArray.ext
  simp [ByteArray.data_append]

-- LIBRARY CANDIDATE: recover a scalar's word encoding from its one-word return encoding.
theorem scalarEncoding_of_return {ty : ABIType} {v : Value} {w : UInt256}
    (hdyn : isDynamicABIType ty = false) (hhead : abiTupleHeadSize? [ty] = some 32)
    (henc : encodeReturnValue? ty v = some w.toByteArray) :
    encodeABIValue? ty v = some (EVM.Word.toBytesBE w) := by
  cases hval : encodeABIValue? ty v with
  | none =>
    simp only [encodeReturnValue?, encodeReturnValues?, encodeABIValues?, hhead,
      encodeABIValuesFrom?, hval, bind, Option.bind] at henc
    cases henc
  | some bs =>
    simp only [encodeReturnValue?, encodeReturnValues?, encodeABIValues?, hhead,
      encodeABIValuesFrom?, hval, hdyn, bind, Option.bind, Bool.false_eq_true, if_false,
      List.nil_append, List.append_nil] at henc
    apply congrArg some
    have hlist := congrArg ByteArray.toList (Option.some.inj henc)
    simpa only [toByteArray_eq_toBytesBE, byteArray_toList_eq, List.toList_toArray] using hlist

-- GENERALIZES scalarPairReturnEncoding to a triple of statically encoded words.
theorem scalarTripleReturnEncoding {t₁ t₂ t₃ : ABIType} {v₁ v₂ v₃ : Value}
    {w₁ w₂ w₃ : UInt256}
    (hd₁ : isDynamicABIType t₁ = false) (hd₂ : isDynamicABIType t₂ = false)
    (hd₃ : isDynamicABIType t₃ = false) (hhead : abiTupleHeadSize? [t₁, t₂, t₃] = some 96)
    (hv₁ : encodeABIValue? t₁ v₁ = some (EVM.Word.toBytesBE w₁))
    (hv₂ : encodeABIValue? t₂ v₂ = some (EVM.Word.toBytesBE w₂))
    (hv₃ : encodeABIValue? t₃ v₃ = some (EVM.Word.toBytesBE w₃)) :
    encodeReturnValues? [t₁, t₂, t₃] [v₁, v₂, v₃] =
      some (w₁.toByteArray ++ (w₂.toByteArray ++ w₃.toByteArray)) := by
  simp only [encodeReturnValues?, encodeABIValues?, hhead, encodeABIValuesFrom?, hv₁, hv₂, hv₃,
    hd₁, hd₂, hd₃, bind, Option.bind, Bool.false_eq_true, if_false, List.nil_append,
    List.append_nil]
  simp only [toByteArray_eq_toBytesBE]
  apply congrArg some
  apply ByteArray.ext
  simp [ByteArray.data_append]

-- GENERALIZES Reasoning.ABI.encodeABIValue_uint256 to every unsigned ABI width.
theorem encodeABIValue_uint_word (width : ABI.BitWidth) (w : UInt256)
    (hlt : w.toNat < EVM.twoPow width.val) :
    encodeABIValue? (.elem (.int (.uint width))) (.int (Int.ofNat w.toNat)) =
      some (EVM.Word.toBytesBE w) := by
  have hword : EVM.word w.toNat = w := u256_ofNat_toNat w
  cases width with
  | mk bits hbits =>
    change w.toNat < EVM.twoPow bits at hlt
    simp only [encodeABIValue?, encodeABIWord?]
    rw [if_pos (show 0 ≤ Int.ofNat w.toNat ∧
      Int.ofNat w.toNat < Int.ofNat (EVM.twoPow bits) from
      ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr hlt⟩)]
    rw [if_neg (Nat.ne_of_gt hbits.1)]
    simp [hword]

-- GENERALIZES Reasoning.ABIViews.uint256PairReturnEncoding to arbitrary unsigned widths.
theorem uintPairReturnEncoding (a b : ABI.BitWidth) (first second : UInt256)
    (ha : first.toNat < EVM.twoPow a.val) (hb : second.toNat < EVM.twoPow b.val) :
    encodeReturnValues? [.elem (.int (.uint a)), .elem (.int (.uint b))]
      [.int (Int.ofNat first.toNat), .int (Int.ofNat second.toNat)] =
        some (first.toByteArray ++ second.toByteArray) := by
  exact scalarPairReturnEncoding rfl rfl
    (by simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
        cases a; cases b; rfl)
    (encodeABIValue_uint_word a first ha) (encodeABIValue_uint_word b second hb)

-- GENERALIZES Reasoning.ABIViews.addressUint256PairReturnEncoding to any unsigned width.
theorem addressUintPairReturnEncoding (width : ABI.BitWidth) (first second : UInt256)
    (hsecond : second.toNat < EVM.twoPow width.val) :
    encodeReturnValues? [.elem .address, .elem (.int (.uint width))]
      [.address (AccountAddress.ofNat (UInt256.land first solcAddrMask).toNat),
        .int (Int.ofNat second.toNat)] =
      some ((UInt256.land first solcAddrMask).toByteArray ++ second.toByteArray) := by
  exact scalarPairReturnEncoding rfl rfl (by
      simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
      cases width; rfl)
    (by simpa only [toByteArray_eq_toBytesBE, byteArray_toList_eq, List.toList_toArray] using
      encodeABIValue_address_word first)
    (encodeABIValue_uint_word width second hsecond)

-- LIBRARY CANDIDATE: encoding a packed integer/bool/integer record with arbitrary integer widths.
theorem uintBoolUintReturnEncoding (a b : ABI.BitWidth) (first flag last : UInt256)
    (ha : first.toNat < EVM.twoPow a.val) (hb : last.toNat < EVM.twoPow b.val) :
    encodeReturnValues? [.elem (.int (.uint a)), .elem .bool, .elem (.int (.uint b))]
      [.int (Int.ofNat first.toNat), wordToElem .bool (UInt256.land flag ⟨255⟩),
        .int (Int.ofNat last.toNat)] =
      some (first.toByteArray ++
        ((UInt256.isZero (UInt256.isZero (UInt256.land flag ⟨255⟩))).toByteArray ++
          last.toByteArray)) := by
  exact scalarTripleReturnEncoding rfl rfl rfl
    (by simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
        cases a; cases b; rfl)
    (encodeABIValue_uint_word a first ha)
    (scalarEncoding_of_return rfl
      (by simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
          decide) (boolWordReturnEncoding flag))
    (encodeABIValue_uint_word b last hb)

end Benchmarks.Morpho.MetaMorphoV1_1
