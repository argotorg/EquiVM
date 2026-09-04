import Benchmarks.Dss.Clipper.GetStatusBody
import Reasoning.ExternalCall
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

abbrev clipperStatusPriceSelectorWord : UInt256 :=
  ⟨0x487a2395⟩

abbrev clipperStatusPriceSelectorShifted : UInt256 :=
  UInt256.shiftLeft clipperStatusPriceSelectorWord ⟨224⟩

noncomputable def clipperStatusPriceSelectorMem (mem : ByteArray) : ByteArray :=
  clipperStatusPriceSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def clipperStatusPriceTopMem (top : UInt256) (mem : ByteArray) : ByteArray :=
  top.toByteArray.write 0 (clipperStatusPriceSelectorMem mem) 132 32

noncomputable def clipperStatusPriceCalldataMem
    (top age : UInt256) (mem : ByteArray) : ByteArray :=
  age.toByteArray.write 0 (clipperStatusPriceTopMem top mem) 164 32

noncomputable def clipperStatusPricePostCallMem
    (top age : UInt256) (mem out : ByteArray) : ByteArray :=
  out.write 0 (clipperStatusPriceCalldataMem top age mem) 128
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat

abbrev clipperStatusPriceWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

abbrev clipperStatusPriceValues (out : ByteArray) : List Value :=
  [.int (Int.ofNat (clipperStatusPriceWord out).toNat)]

theorem clipperStatusPriceSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (clipperStatusPriceSelectorMem mem).size = 160 := by
  unfold clipperStatusPriceSelectorMem
  exact toByteArray_write32_size_of_ge mem clipperStatusPriceSelectorShifted 128 96 160 hmem
    (by omega) (by native_decide) (by omega)

theorem clipperStatusPriceSelectorMem_read64 {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperStatusPriceSelectorMem mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperStatusPriceSelectorMem
  have hpreserve :
      ((UInt256.toByteArray clipperStatusPriceSelectorShifted).write 0 mem 128 32).readWithPadding
          64 32 =
        mem.readWithPadding 64 32 :=
    toByteArray_write_read_below_of_gap (b := clipperStatusPriceSelectorShifted) (mem := mem)
      (off := 128) (read := 64) (hread := by simp [hmem])
      (hbelow := by native_decide) (hgap := by rw [hmem]; native_decide)
  rw [hpreserve, hread64]

theorem clipperStatusPriceTopMem_size (top : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (clipperStatusPriceTopMem top mem).size = 164 := by
  unfold clipperStatusPriceTopMem
  exact toByteArray_write32_size_of_le (clipperStatusPriceSelectorMem mem) top 132 160 164
    (clipperStatusPriceSelectorMem_size hmem)
    (by rw [clipperStatusPriceSelectorMem_size hmem]; omega) (by omega)

theorem clipperStatusPriceTopMem_read64 (top : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperStatusPriceTopMem top mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperStatusPriceTopMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [clipperStatusPriceSelectorMem_size hmem]; omega) (by omega)]
  exact clipperStatusPriceSelectorMem_read64 hmem hread64

theorem clipperStatusPriceCalldataMem_size (top age : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (clipperStatusPriceCalldataMem top age mem).size = 196 := by
  unfold clipperStatusPriceCalldataMem
  exact toByteArray_write32_size_of_ge (clipperStatusPriceTopMem top mem) age 164 164 196
    (clipperStatusPriceTopMem_size top hmem)
    (by omega) (by native_decide) (by omega)

theorem clipperStatusPriceCalldataMem_read64 (top age : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperStatusPriceCalldataMem top age mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperStatusPriceCalldataMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [clipperStatusPriceTopMem_size top hmem]) (by native_decide)]
  exact clipperStatusPriceTopMem_read64 top hmem hread64

theorem clipperStatusPriceCalldataMem_mload64 (top age : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperStatusPriceCalldataMem top age mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperStatusPriceCalldataMem top age mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [clipperStatusPriceCalldataMem_size top age hmem]; native_decide)
    (by native_decide)
    (clipperStatusPriceCalldataMem_read64 top age hmem hread64)

theorem clipperStatusPriceSelectorMem_read128_4 {mem : ByteArray}
    (hmem : mem.size = 96) :
    (clipperStatusPriceSelectorMem mem).readWithPadding 128 4 = priceSelector := by
  unfold clipperStatusPriceSelectorMem
  rw [toByteArray_write_read_window_of_gap clipperStatusPriceSelectorShifted mem 128 0 4
    (by norm_num) (by norm_num) (by norm_num) (by rw [hmem]; native_decide)]
  rw [toByteArray_eq_toBytesBE]
  native_decide

theorem clipperStatusPriceCalldataMem_read128_4 (top age : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (clipperStatusPriceCalldataMem top age mem).readWithPadding 128 4 = priceSelector := by
  unfold clipperStatusPriceCalldataMem
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by rw [clipperStatusPriceTopMem_size top hmem])
    (by omega) (by rw [clipperStatusPriceTopMem_size top hmem]; omega)
    (by norm_num) (by norm_num)]
  unfold clipperStatusPriceTopMem
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [clipperStatusPriceSelectorMem_size hmem]; omega)
    (by omega) (by rw [clipperStatusPriceSelectorMem_size hmem]; omega)
    (by norm_num) (by norm_num)]
  exact clipperStatusPriceSelectorMem_read128_4 hmem

theorem clipperStatusPriceCalldataMem_read132_32 (top age : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (clipperStatusPriceCalldataMem top age mem).readWithPadding 132 32 =
      UInt256.toByteArray top := by
  unfold clipperStatusPriceCalldataMem
  rw [write32_read_below _ _ 164 132 (by rw [toByteArray_size])
    (by rw [clipperStatusPriceTopMem_size top hmem]) (by omega)]
  unfold clipperStatusPriceTopMem
  rw [write32_read_back _ _ 132 (by rw [toByteArray_size])
    (by rw [clipperStatusPriceSelectorMem_size hmem]; omega)]
  rw [show (UInt256.toByteArray top).extract 0 32 = UInt256.toByteArray top by
    rw [show 32 = (UInt256.toByteArray top).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem clipperStatusPriceCalldataMem_read164_32 (top age : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (clipperStatusPriceCalldataMem top age mem).readWithPadding 164 32 =
      UInt256.toByteArray age := by
  unfold clipperStatusPriceCalldataMem
  rw [write32_read_back _ _ 164 (by rw [toByteArray_size])
    (by rw [clipperStatusPriceTopMem_size top hmem])]
  rw [show (UInt256.toByteArray age).extract 0 32 = UInt256.toByteArray age by
    rw [show 32 = (UInt256.toByteArray age).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem clipperStatusPriceCalldataMem_read128_68 (top age : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (clipperStatusPriceCalldataMem top age mem).readWithPadding 128 68 =
      priceSelector ++ UInt256.toByteArray top ++ UInt256.toByteArray age := by
  rw [byteArray_readWithPadding_split _ 128 4 64 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperStatusPriceCalldataMem_size top age hmem])]
  rw [byteArray_readWithPadding_split _ 132 32 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperStatusPriceCalldataMem_size top age hmem])]
  rw [clipperStatusPriceCalldataMem_read128_4 top age hmem,
    clipperStatusPriceCalldataMem_read132_32 top age hmem,
    clipperStatusPriceCalldataMem_read164_32 top age hmem, ByteArray.append_assoc]

theorem clipperStatusPriceEncode_eq (v : ClipperImmutables) (top age : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (config v).externalABI.encode? "price"
        [.int (Int.ofNat top.toNat), .int (Int.ofNat age.toNat)] =
      some ((clipperStatusPriceCalldataMem top age mem).readWithPadding 128 68) := by
  rw [clipperStatusPriceCalldataMem_read128_68 top age hmem]
  change externalABI.encode? "price" [.int (Int.ofNat top.toNat), .int (Int.ofNat age.toNat)] =
    some (priceSelector ++ UInt256.toByteArray top ++ UInt256.toByteArray age)
  have htopWord : EVM.word top.toNat = top := u256_ofNat_toNat top
  have hageWord : EVM.word age.toNat = age := u256_ofNat_toNat age
  have htopLt : top.toNat < EVM.twoPow 256 := by
    change top.val.val < UInt256.size
    exact top.val.isLt
  have hageLt : age.toNat < EVM.twoPow 256 := by
    change age.val.val < UInt256.size
    exact age.val.isLt
  unfold externalABI ABI.encodeCallWithSelector? ABI.encodeABIValues?
  simp [uint256, uint256Int, ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
    ABI.isDynamicABIType, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.encodeABIValuesFrom?,
    htopLt, hageLt, htopWord, hageWord, word_toBytesBE_toByteArray_eq_toByteArray]
  rw [ByteArray.append_assoc]

theorem clipperStatusPriceDecode_none_short {v : ClipperImmutables} {out : ByteArray}
    (hshort : out.size < 32) :
    (config v).externalABI.decode? "price" out = none := by
  simpa [config, externalABI, decodeReturn?, uint256, uint256Int, abiUInt256] using
    (decodeReturnValueWithMode_solcV1Signed_uint256_none_short (returndata := out) hshort)

theorem clipperStatusPriceDecode_ok {v : ClipperImmutables} {out : ByteArray}
    (hlo : 32 ≤ out.size) :
    (config v).externalABI.decode? "price" out =
      some (clipperStatusPriceValues out) := by
  have hword :
      (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))).toNat =
        fromByteArrayBigEndian (out.extract 0 32) :=
    UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt (returndata := out) hlo)
  simpa [config, externalABI, decodeReturn?, clipperStatusPriceValues,
    clipperStatusPriceWord, uint256, uint256Int, abiUInt256, hword] using
    (decodeReturnValueWithMode_solcV1Signed_uint256_ok (returndata := out) hlo)

abbrev clipperGetStatusNeedsRedoWord (usr done : UInt256) : UInt256 :=
  if UInt256.isZero (UInt256.land usr solcAddrMask) = ⟨0⟩ then done else ⟨0⟩

def clipperGetStatusReturnWrites (needs price lot tab : UInt256) : List (Nat × UInt256) :=
  [(128, UInt256.isZero (UInt256.isZero needs)), (160, price), (192, lot), (224, tab)]

noncomputable def clipperGetStatusReturnMem
    (scratch : ByteArray) (needs price lot tab : UInt256) : ByteArray :=
  writeCascade scratch (clipperGetStatusReturnWrites needs price lot tab)

abbrev clipperGetStatusReturnBytes (needs price lot tab : UInt256) : ByteArray :=
  UInt256.toByteArray (UInt256.isZero (UInt256.isZero needs)) ++ UInt256.toByteArray price ++
    UInt256.toByteArray lot ++ UInt256.toByteArray tab

theorem clipperEncodeABIValue_bool (b : Bool) :
    encodeABIValue? (.elem .bool) (.bool b) =
      some (EVM.Word.toBytesBE b.toUInt256) := by
  cases b <;> native_decide

theorem clipperGetStatusReturnEncoding
    (needsWord : UInt256) (needs : Bool) (price lot tab : UInt256)
    (hneeds : UInt256.isZero (UInt256.isZero needsWord) = needs.toUInt256) :
    encodeReturnValues? [.elem .bool, uint256, uint256, uint256]
      [.bool needs, .int (Int.ofNat price.toNat), .int (Int.ofNat lot.toNat),
        .int (Int.ofNat tab.toNat)] =
      some (clipperGetStatusReturnBytes needsWord price lot tab) := by
  have hencNeeds := clipperEncodeABIValue_bool needs
  have hencPrice := clipperEncodeABIValue_uint256 price
  have hencLot := clipperEncodeABIValue_uint256 lot
  have hencTab := clipperEncodeABIValue_uint256 tab
  have hhead : abiTupleHeadSize? [.elem .bool, uint256, uint256, uint256] = some 128 := by
    native_decide
  have hdb : isDynamicABIType (.elem .bool) = false := by rfl
  have hdu : isDynamicABIType uint256 = false := by rfl
  unfold clipperGetStatusReturnBytes
  rw [hneeds, toByteArray_eq_toBytesBE needs.toUInt256, toByteArray_eq_toBytesBE price,
    toByteArray_eq_toBytesBE lot, toByteArray_eq_toBytesBE tab]
  simp only [encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?, hhead, hencNeeds,
    hencPrice, hencLot, hencTab, hdb, hdu, bind, Option.bind, Bool.false_eq_true,
    if_false, List.nil_append, List.append_nil]
  rfl

theorem clipperGetStatusNeedsRedoWord_bool
    (usr doneWord : UInt256) (done : Bool)
    (hdone : UInt256.isZero (UInt256.isZero doneWord) = done.toUInt256) :
    UInt256.isZero (UInt256.isZero (clipperGetStatusNeedsRedoWord usr doneWord)) =
      ((!(Value.address (AccountAddress.ofNat usr.toNat) ==
          Value.address (AccountAddress.ofNat 0))) && done).toUInt256 := by
  let masked := UInt256.land usr solcAddrMask
  have haddrMasked :
      Value.address (AccountAddress.ofNat usr.toNat) =
        Value.address (AccountAddress.ofNat masked.toNat) := by
    rw [solcAddressValue_masked usr]
    rw [u256_land_comm solcAddrMask usr]
  by_cases hzero : masked = ⟨0⟩
  · have hmaskZero : UInt256.isZero masked ≠ ⟨0⟩ := by
      rw [hzero]
      native_decide
    have haddrEq :
        Value.address (AccountAddress.ofNat usr.toNat) =
          Value.address (AccountAddress.ofNat 0) := by
      simpa using (by rw [haddrMasked, hzero] :
        Value.address (AccountAddress.ofNat usr.toNat) =
          Value.address (AccountAddress.ofNat (⟨0⟩ : UInt256).toNat))
    rw [clipperGetStatusNeedsRedoWord]
    have hif : ¬UInt256.isZero masked = ⟨0⟩ := hmaskZero
    rw [if_neg hif]
    rw [haddrEq]
    cases done <;> native_decide
  · have hisZero : UInt256.isZero masked = ⟨0⟩ := isZero_eq_zero_of_ne hzero
    have haddrNe :
        Value.address (AccountAddress.ofNat usr.toNat) ≠
          Value.address (AccountAddress.ofNat 0) := by
      intro hbad
      have hbad' : AccountAddress.ofNat masked.toNat = AccountAddress.ofNat 0 := by
        exact Value.address.inj (haddrMasked.symm.trans hbad)
      have hmaskedNat : masked.toNat = 0 := by
        have hval := congrArg Fin.val hbad'
        have hcanon : masked.toNat < AccountAddress.size := by
          simpa [masked] using solcAddrMask_result_canonical usr
        simpa [AccountAddress.ofNat, Fin.ofNat, Nat.mod_eq_of_lt hcanon] using hval
      exact hzero (uint256_toNat_eq_zero hmaskedNat)
    have hbeq :
        (Value.address (AccountAddress.ofNat usr.toNat) ==
          Value.address (AccountAddress.ofNat 0)) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      exact haddrNe (beq_iff_eq.mp h)
    rw [clipperGetStatusNeedsRedoWord, if_pos hisZero, hdone, hbeq]
    cases done <;> rfl

theorem twoWordHashMem_size_ge_64_of_ge {mem : ByteArray} (key slot : UInt256)
    (_hmem : 64 ≤ mem.size) :
    64 ≤ (twoWordHashMem key slot mem).size := by
  have hword0 : 32 ≤ (wordAt0Mem key mem).size := by
    simpa [wordAt0Mem] using
      toByteArray_write_size_ge_off_add32 key mem 0 (by simp)
  simpa [twoWordHashMem, wordAt32Mem] using
    toByteArray_write_size_ge_off_add32 slot (wordAt0Mem key mem) 32
      (lt_usize (32 - (wordAt0Mem key mem).size) (by omega))

theorem twoWordHashMem_size_of_ge_64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  unfold twoWordHashMem wordAt32Mem wordAt0Mem
  change (writeCascade mem [(0, key), (32, slot)]).size = mem.size
  exact writeCascade_size_of_base mem [(0, key), (32, slot)] rfl
    (by simp [WriteGapsOk])
    (by
      simp [writeCascadeSize]
      omega)

theorem twoWordHashMem_read0_of_ge {mem : ByteArray} (key slot : UInt256)
    (_hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by
        have hword0 : 32 ≤ (wordAt0Mem key mem).size := by
          simpa [wordAt0Mem] using
            toByteArray_write_size_ge_off_add32 key mem 0 (by simp)
        omega)
      (by omega)]
  unfold wordAt0Mem
  rw [write32_read_back _ _ 0 (by rw [toByteArray_size]) (by omega)]
  rw [toByteArray_extract_all]

theorem twoWordHashMem_read32_of_ge {mem : ByteArray} (key slot : UInt256)
    (_hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ 32 (by rw [toByteArray_size])
      (by
        have hword0 : 32 ≤ (wordAt0Mem key mem).size := by
          simpa [wordAt0Mem] using
            toByteArray_write_size_ge_off_add32 key mem 0 (by simp)
        omega)]
  rw [toByteArray_extract_all]

set_option maxHeartbeats 800000 in
theorem twoWordHashMem_read0_64_of_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [byteArray_readWithPadding_split _ 0 32 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (twoWordHashMem_size_ge_64_of_ge key slot hmem)]
  rw [twoWordHashMem_read0_of_ge key slot hmem, twoWordHashMem_read32_of_ge key slot hmem]

theorem twoWordHashMem_read64_of_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold twoWordHashMem wordAt32Mem wordAt0Mem
  change (writeCascade mem [(0, key), (32, slot)]).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [writeCascade_read_preserved_of_base mem [(0, key), (32, slot)] rfl]
  · exact hread64
  · simp [WindowDisjointFromWrites]
    omega

theorem twoWordHashMem_solcMappingSlot_of_ge (baseSlot key : UInt256) {mem : ByteArray}
    (hmem : 64 ≤ mem.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64_of_ge key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

theorem clipperGetStatusReturnMem_size {scratch : ByteArray}
    (needs price lot tab : UInt256) (hscratch : scratch.size = 196) :
    (clipperGetStatusReturnMem scratch needs price lot tab).size = 256 := by
  unfold clipperGetStatusReturnMem clipperGetStatusReturnWrites
  exact writeCascade_size_of_base scratch
    [(128, UInt256.isZero (UInt256.isZero needs)), (160, price), (192, lot), (224, tab)]
    hscratch
    (by simp [WriteGapsOk])
    (by rfl)

theorem clipperGetStatusReturnMem_read64 {scratch : ByteArray}
    (needs price lot tab : UInt256) (hscratch : scratch.size = 196)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperGetStatusReturnMem scratch needs price lot tab).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperGetStatusReturnMem
  rw [writeCascade_read_preserved_of_base scratch
    (clipperGetStatusReturnWrites needs price lot tab) hscratch]
  · exact hread64
  · simp [clipperGetStatusReturnWrites, WindowDisjointFromWrites]

theorem clipperGetStatusReturnMem_mload64 {scratch : ByteArray}
    (needs price lot tab : UInt256) (hscratch : scratch.size = 196)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperGetStatusReturnMem scratch needs price lot tab).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperGetStatusReturnMem scratch needs price lot tab).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [clipperGetStatusReturnMem_size needs price lot tab hscratch]; decide)
    (by decide)
    (clipperGetStatusReturnMem_read64 needs price lot tab hscratch hread64)

theorem clipperGetStatusReturnMem_readWord128 {scratch : ByteArray}
    (needs price lot tab : UInt256) (hscratch : scratch.size = 196) :
    (clipperGetStatusReturnMem scratch needs price lot tab).readWithPadding 128 32 =
      UInt256.toByteArray (UInt256.isZero (UInt256.isZero needs)) := by
  unfold clipperGetStatusReturnMem clipperGetStatusReturnWrites
  exact writeCascade_read_word_of_head_of_base scratch (UInt256.isZero (UInt256.isZero needs))
    [(160, price), (192, lot), (224, tab)]
    hscratch (by native_decide) (by simp [WindowDisjointFromWrites])

theorem clipperGetStatusReturnMem_readWord160 {scratch : ByteArray}
    (needs price lot tab : UInt256) (hscratch : scratch.size = 196) :
    (clipperGetStatusReturnMem scratch needs price lot tab).readWithPadding 160 32 =
      UInt256.toByteArray price := by
  unfold clipperGetStatusReturnMem clipperGetStatusReturnWrites
  rw [writeCascade_cons]
  have hbase :
      (writeWord scratch 128 (UInt256.isZero (UInt256.isZero needs))).size = 196 := by
    rw [writeWord_size]
    · rw [hscratch]
      norm_num
    · rw [hscratch]
      native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord scratch 128 (UInt256.isZero (UInt256.isZero needs))) price
    [(192, lot), (224, tab)] hbase (by native_decide) (by simp [WindowDisjointFromWrites])

theorem clipperGetStatusReturnMem_readWord192 {scratch : ByteArray}
    (needs price lot tab : UInt256) (hscratch : scratch.size = 196) :
    (clipperGetStatusReturnMem scratch needs price lot tab).readWithPadding 192 32 =
      UInt256.toByteArray lot := by
  unfold clipperGetStatusReturnMem clipperGetStatusReturnWrites
  rw [writeCascade_cons, writeCascade_cons]
  have hbase0 :
      (writeWord scratch 128 (UInt256.isZero (UInt256.isZero needs))).size = 196 := by
    rw [writeWord_size]
    · rw [hscratch]
      norm_num
    · rw [hscratch]
      native_decide
  have hbase1 :
      (writeWord (writeWord scratch 128 (UInt256.isZero (UInt256.isZero needs))) 160 price).size =
        196 := by
    rw [writeWord_size]
    · rw [hbase0]
      norm_num
    · rw [hbase0]
      native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord (writeWord scratch 128 (UInt256.isZero (UInt256.isZero needs))) 160 price) lot
    [(224, tab)] hbase1 (by native_decide) (by simp [WindowDisjointFromWrites])

theorem clipperGetStatusReturnMem_readWord224 {scratch : ByteArray}
    (needs price lot tab : UInt256) (hscratch : scratch.size = 196) :
    (clipperGetStatusReturnMem scratch needs price lot tab).readWithPadding 224 32 =
      UInt256.toByteArray tab := by
  unfold clipperGetStatusReturnMem clipperGetStatusReturnWrites
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons]
  have hbase0 :
      (writeWord scratch 128 (UInt256.isZero (UInt256.isZero needs))).size = 196 := by
    rw [writeWord_size]
    · rw [hscratch]
      norm_num
    · rw [hscratch]
      native_decide
  have hbase1 :
      (writeWord (writeWord scratch 128 (UInt256.isZero (UInt256.isZero needs))) 160 price).size =
        196 := by
    rw [writeWord_size]
    · rw [hbase0]
      norm_num
    · rw [hbase0]
      native_decide
  have hbase2 :
      (writeWord
          (writeWord (writeWord scratch 128 (UInt256.isZero (UInt256.isZero needs))) 160 price)
          192 lot).size = 224 := by
    rw [writeWord_size]
    · rw [hbase1]
      norm_num
    · rw [hbase1]
      native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord (writeWord scratch 128 (UInt256.isZero (UInt256.isZero needs))) 160 price)
      192 lot)
    tab [] hbase2 (by native_decide) (by simp [WindowDisjointFromWrites])

theorem clipperGetStatusReturnMem_read128_128 {scratch : ByteArray}
    (needs price lot tab : UInt256) (hscratch : scratch.size = 196) :
    (clipperGetStatusReturnMem scratch needs price lot tab).readWithPadding 128 128 =
      clipperGetStatusReturnBytes needs price lot tab := by
  rw [byteArray_readWithPadding_split _ 128 32 96 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by
      rw [clipperGetStatusReturnMem_size needs price lot tab hscratch])]
  rw [byteArray_readWithPadding_split _ 160 32 64 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by
      rw [clipperGetStatusReturnMem_size needs price lot tab hscratch])]
  rw [byteArray_readWithPadding_split _ 192 32 32 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by
      rw [clipperGetStatusReturnMem_size needs price lot tab hscratch])]
  rw [clipperGetStatusReturnMem_readWord128 (scratch := scratch) needs price lot tab hscratch,
    clipperGetStatusReturnMem_readWord160 (scratch := scratch) needs price lot tab hscratch,
    clipperGetStatusReturnMem_readWord192 (scratch := scratch) needs price lot tab hscratch,
    clipperGetStatusReturnMem_readWord224 (scratch := scratch) needs price lot tab hscratch]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [clipperGetStatusReturnBytes, ByteArray.data_append, Array.toList_append]

theorem clipperStatusPricePostCallMem_size (top age : UInt256) {mem out : ByteArray}
    (hmem : mem.size = 96) (hout : out.size < UInt256.size) :
    (clipperStatusPricePostCallMem top age mem out).size = 196 := by
  unfold clipperStatusPricePostCallMem
  have hbase :
      (clipperStatusPriceCalldataMem top age mem).size = 196 :=
    clipperStatusPriceCalldataMem_size top age hmem
  by_cases hshort : out.size < 32
  · have hlen :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := out.size) (by decide) hshort hout
    rw [hlen]
    by_cases hzero : out.size = 0
    · rw [hzero, byteArray_write_len_zero, hbase]
    · rw [write_eq_gen out (clipperStatusPriceCalldataMem top age mem) 128 out.size
        hzero le_rfl (by rw [hbase]; omega)]
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, hbase]
      omega
  · have hlo : 32 ≤ out.size := by omega
    have hlen :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size) (by decide) hlo hout
    rw [hlen]
    rw [write_eq_gen out (clipperStatusPriceCalldataMem top age mem) 128 32
      (by omega) (by omega) (by rw [hbase]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hbase]
    omega

theorem clipperStatusPricePostCallMem_read64 (top age : UInt256) {mem out : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hout : out.size < UInt256.size) :
    (clipperStatusPricePostCallMem top age mem out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperStatusPricePostCallMem
  have hbase :
      (clipperStatusPriceCalldataMem top age mem).size = 196 :=
    clipperStatusPriceCalldataMem_size top age hmem
  by_cases hshort : out.size < 32
  · have hlen :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := out.size) (by decide) hshort hout
    rw [hlen]
    by_cases hzero : out.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact clipperStatusPriceCalldataMem_read64 top age hmem hread64
    · rw [write_read_below_gen_extend out (clipperStatusPriceCalldataMem top age mem)
        128 out.size 64 hzero le_rfl (by rw [hbase]; omega) (by omega)]
      exact clipperStatusPriceCalldataMem_read64 top age hmem hread64
  · have hlo : 32 ≤ out.size := by omega
    have hlen :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size) (by decide) hlo hout
    rw [hlen]
    rw [write_read_below_gen_extend out (clipperStatusPriceCalldataMem top age mem)
      128 32 64 (by omega) (by omega) (by rw [hbase]; omega) (by omega)]
    exact clipperStatusPriceCalldataMem_read64 top age hmem hread64

theorem clipperStatusPricePostCallMem_mload64 (top age : UInt256) {mem out : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperStatusPricePostCallMem top age mem out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperStatusPricePostCallMem top age mem out).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [clipperStatusPricePostCallMem_size top age hmem hout]; decide)
    (by decide)
    (clipperStatusPricePostCallMem_read64 top age hmem hread64 hout)

theorem clipperStatusPricePostCallMem_read128 (top age : UInt256) {mem out : ByteArray}
    (hmem : mem.size = 96) (hlo : 32 ≤ out.size) (hout : out.size < UInt256.size) :
    (clipperStatusPricePostCallMem top age mem out).readWithPadding 128 32 =
      out.extract 0 32 := by
  unfold clipperStatusPricePostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size) (by decide) hlo hout
  rw [hlen]
  exact write32_read_back out (clipperStatusPriceCalldataMem top age mem) 128 hlo
    (by rw [clipperStatusPriceCalldataMem_size top age hmem]; omega)

theorem clipperStatusPricePostCallMem_mload128 (top age : UInt256) {mem out : ByteArray}
    (hmem : mem.size = 96) (hlo : 32 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (clipperStatusPricePostCallMem top age mem out).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperStatusPricePostCallMem top age mem out).readWithPadding
          (⟨128⟩ : UInt256).toNat 32))) =
      clipperStatusPriceWord out := by
  have hsize := clipperStatusPricePostCallMem_size top age hmem hout
  have hread := clipperStatusPricePostCallMem_read128 top age hmem hlo hout
  have hcond :
      ¬ ((⟨128⟩ : UInt256).toNat ≥ (clipperStatusPricePostCallMem top age mem out).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩) := by
    rw [hsize]
    decide
  rw [if_neg hcond]
  change UInt256.ofNat
      (fromByteArrayBigEndian
        ((clipperStatusPricePostCallMem top age mem out).readWithPadding 128 32)) =
    clipperStatusPriceWord out
  rw [hread]

theorem clipperJumpDest8460 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8460⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest8502 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8502⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest8561 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8561⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest8581 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8581⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest8603 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8603⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest3258 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨3258⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 4000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest3283 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨3283⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 4000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest8630 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8630⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest8652 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8652⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest8650 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8650⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest9274 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨9274⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9300) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest9290 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨9290⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9400) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

end Benchmarks.Dss.Clipper

namespace Reasoning.Reach

-- LIBRARY CANDIDATE: `Reasoning.Reach` — missing `SWAP9` one-step and `RD` wrapper,
-- matching the existing `swap8`/`swap10` primitives.
theorem swap9_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP9, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t)
    (hov : t.length + 10 ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
       else .ok (stSwap s (jj :: b :: c :: d :: e :: f :: gg :: hh :: ii :: a :: t),
        .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP9, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap9 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t).length - 10
        + 10 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem RD.swap9
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP9, .none)) (hov : t.length + 10 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (jj :: b :: c :: d :: e :: f :: gg :: hh :: ii :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => swap9_xstep hc hp hdec hs hov)

end Reasoning.Reach

namespace Benchmarks.Dss.Clipper
namespace Reasoning.Reach

set_option maxHeartbeats 2000000 in
theorem RD.clipperGetStatusToStatus {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {k C : ℕ}
    {id ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 ⟨3185⟩ (id :: ret :: R) mem (UInt256.ofNat 3) rdata
      (cA, σ) k C)
    (hmem : mem.size = 96)
    (hov : R.length + 64 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8460⟩
      (solcSlotWord σ ee ((solcMappingSlot ⟨12⟩ id) + ⟨4⟩) ::
        clipperSalesPackedTicWord
          (solcSlotWord σ ee ((solcMappingSlot ⟨12⟩ id) + ⟨3⟩)) ::
        ⟨3258⟩ :: ⟨0⟩ ::
        clipperSalesPackedTicWord
          (solcSlotWord σ ee ((solcMappingSlot ⟨12⟩ id) + ⟨3⟩)) ::
        UInt256.land (solcSlotWord σ ee ((solcMappingSlot ⟨12⟩ id) + ⟨3⟩))
          solcAddrMask ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: id :: ret :: R)
      (twoWordHashMem id ⟨12⟩ mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  let base : UInt256 := solcMappingSlot ⟨12⟩ id
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem id (⟨12⟩ : UInt256) mem).readWithPadding 0 64))) =
        base := by
    simpa [base] using twoWordHashMem_solcMappingSlot (⟨12⟩ : UInt256) id hmem
  have rd3199 := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (wordAt0Mem id mem) (UInt256.ofNat 3)
      (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨12⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (twoWordHashMem id (⟨12⟩ : UInt256) mem) (UInt256.ofNat 3)
      (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw keccak256 0 base (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost hslot
      (by native_decide) (by evm_ov),
    raw push1 ⟨3⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd3205⟩ := rd3199.sload (by clipper_runtime_decode) (by evm_ov)
  have rd3209 := evm_run rd3205 with [
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd3210⟩ := rd3209.sload (by clipper_runtime_decode) (by evm_ov)
  have rd8460 := evm_run rd3210 with [
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw div (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨96⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨3258⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8460⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) (clipperJumpDest8460 v hpatch) (by evm_ov)]
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  exact ⟨_, _, by
    simpa [base, clipperSalesPackedTicWord, solcSlotWord, haddrMask, u256_land_comm]
      using rd8460⟩

set_option maxHeartbeats 2000000 in
theorem RD.clipperStatusAgeForPrice {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {k C : ℕ}
    {top tic ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 ⟨8460⟩ (top :: tic :: ret :: R) mem aw rdata (cA, σ) k C)
    (hle : (UInt256.land tic clipperSalesUint96Mask).toNat ≤
      (UInt256.ofNat ee.header.timestamp).toNat)
    (hov : R.length + 80 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8502⟩
      (UInt256.sub (UInt256.ofNat ee.header.timestamp)
          (UInt256.land tic clipperSalesUint96Mask) ::
        top :: clipperStatusPriceSelectorWord ::
          UInt256.land (solcSlotWord σ ee ⟨4⟩) solcAddrMask ::
        ⟨0⟩ :: ⟨0⟩ :: top :: tic :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  have rd8463pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd8464⟩ := rd8463pre.sload (by clipper_runtime_decode) (by evm_ov)
  have rd9274pre := evm_run rd8464 with [
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push4 clipperStatusPriceSelectorWord (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8502⟩ (by clipper_runtime_decode) (by evm_ov),
    raw timestamp (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨96⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup10 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9274⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd9274 := rd9274pre.jump (by clipper_runtime_decode) (clipperJumpDest9274 v hpatch)
    (by evm_ov)
  obtain ⟨_, _, rd8502⟩ :=
    RD.clipperSubRoutine v hpatch rd9274 hle (clipperJumpDest8502 v hpatch) (by evm_ov)
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  exact ⟨_, _, by
    simpa [clipperSalesUint96Mask, clipperStatusPriceSelectorWord, solcSlotWord, haddrMask,
      u256_land_comm] using rd8502⟩

set_option maxHeartbeats 2000000 in
theorem RD.clipperStatusPriceExtcodesizeGuard {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {k C : ℕ}
    {age top calcAddr tic ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 ⟨8502⟩
      (age :: top :: clipperStatusPriceSelectorWord :: calcAddr ::
        ⟨0⟩ :: ⟨0⟩ :: top :: tic :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 90 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8549⟩
      (calcAddr :: calcAddr :: ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨32⟩ :: ⟨196⟩ ::
        clipperStatusPriceSelectorWord :: calcAddr :: ⟨0⟩ :: ⟨0⟩ :: top :: tic :: ret :: R)
      (clipperStatusPriceCalldataMem top age mem) (UInt256.ofNat 7) rdata
      (cA, σ) k' C' := by
  have hselectorMask :
      UInt256.land (⟨4294967295⟩ : UInt256) clipperStatusPriceSelectorWord =
        clipperStatusPriceSelectorWord := by
    native_decide
  have rd8538 := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by clipper_runtime_decode)
      mem_cost hmload64 (by native_decide) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw push4 ⟨4294967295⟩ (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨224⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 6 (clipperStatusPriceSelectorMem mem) (UInt256.ofNat 5)
      (by clipper_runtime_decode) mem_cost
      (by
        simp [clipperStatusPriceSelectorMem, clipperStatusPriceSelectorShifted, hselectorMask,
          show (⟨128⟩ : UInt256).toNat = 128 from by decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 3 (clipperStatusPriceTopMem top mem) (UInt256.ofNat 6)
      (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 3 (clipperStatusPriceCalldataMem top age mem) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov)]
  have hmload64Call := clipperStatusPriceCalldataMem_mload64 top age hmem hread64
  have rd8549 := evm_run rd8538 with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by clipper_runtime_decode)
      mem_cost hmload64Call (by native_decide) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw dup7 (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, by
    simpa [clipperStatusPriceCalldataMem, clipperStatusPriceTopMem,
      clipperStatusPriceSelectorMem, clipperStatusPriceSelectorShifted, hselectorMask] using
      rd8549⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperStatusPricePostStaticcall {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ σ₀ A I} {g age top calcAddr tic ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8549⟩
      (calcAddr :: calcAddr :: ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨32⟩ :: ⟨196⟩ ::
        clipperStatusPriceSelectorWord :: calcAddr :: ⟨0⟩ :: ⟨0⟩ :: top :: tic :: ret :: R)
      (clipperStatusPriceCalldataMem top age mem) (UInt256.ofNat 7) rdata
      (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ calcAddr ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hmem : mem.size = 96)
    (hov : R.length + 100 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD code I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8565⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨196⟩ :: clipperStatusPriceSelectorWord ::
          calcAddr :: ⟨0⟩ :: ⟨0⟩ :: top :: tic :: ret :: R)
        (clipperStatusPricePostCallMem top age mem o)
        (UInt256.ofNat 7) o (cA', σ') k' C'
    ∧ typedCallViaEVM (config v)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofUInt256 calcAddr)) "price" 0
        [.int (Int.ofNat top.toNat), .int (Int.ofNat age.toNat)]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, o) false
    ∧ o.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd8564⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨8549⟩) (okPc := ⟨8561⟩)
      h hcodeSize
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (clipperJumpDest8561 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode)
      (by simp only [List.length_cons]; omega)
  obtain ⟨cA', σ', z, o, A_in, callGas, k8565, C8565, hΘpack, rd8565raw, hosz⟩ :=
    RD.solcStaticcall rd8564 (by clipper_runtime_decode) hdepth
      (by simp only [List.length_cons]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, o, A', k8565, C8565, ?_, ?_, hosz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
          (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) =
          UInt256.ofNat 7 := by
      native_decide
    simpa [clipperStatusPricePostCallMem] using haw ▸ rd8565raw
  · refine callCoincides (cfg := config v)
      (evm := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (name := "price")
      (args := [.int (Int.ofNat top.toNat), .int (Int.ofNat age.toNat)])
      (tgt := EVM.address (AccountAddress.ofUInt256 calcAddr)) (targetWord := calcAddr)
      (cA' := cA') (σ' := σ') (A' := A') (A_in := A_in) (z := z)
      (o := o) (g'' := g'') (callGas := callGas)
      (mem := clipperStatusPriceCalldataMem top age mem)
      (inOff := ⟨128⟩) (inSize := ⟨68⟩) (callPerm := false)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      ?_ ?_ ?_
    · apply Fin.ext
      simp [EVM.address, EVM.uintN]
      exact Nat.mod_eq_of_lt (by simp [EVM.twoPow, AccountAddress.size])
    · simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        show (⟨68⟩ : UInt256).toNat = 68 from by decide] using
        clipperStatusPriceEncode_eq v top age hmem
    · simpa [initState] using hΘ

theorem RD.clipperStatusPriceCallFailure
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD code ee g s0 ⟨8565⟩ (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨8565⟩) (okPc := ⟨8581⟩)
    rd (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    hosz hov

theorem RD.clipperStatusPriceCallSuccessToDecode
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD code ee g s0 ⟨8565⟩ (⟨1⟩ :: R) mem aw o acc k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8583⟩ R mem aw o acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨8565⟩) (okPc := ⟨8581⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (clipperJumpDest8581 v hpatch)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    hov

theorem RD.clipperStatusPriceReturnDecodeShortReverts
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {top age d0 d1 d2 : UInt256} {baseMem out : ByteArray} {k C : ℕ}
    {R : List UInt256}
    (rd8583 : RD code ee g s0 ⟨8583⟩ (d0 :: d1 :: d2 :: R)
      (clipperStatusPricePostCallMem top age baseMem out) (UInt256.ofNat 7) out acc k C)
    (hmem : baseMem.size = 96)
    (hread64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hshort : out.size < 32) (hout : out.size < UInt256.size)
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcUint256ReturnWordDecodeShortReverts
    (pc := ⟨8583⟩) (okPc := ⟨8603⟩) rd8583 hshort hout
    mem_cost (by native_decide)
    (clipperStatusPricePostCallMem_mload64 top age hmem hread64 hout)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode)
    hov

theorem RD.clipperStatusPriceReturnDecodeOk
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {top age d0 d1 d2 : UInt256} {baseMem out : ByteArray} {k C : ℕ}
    {R : List UInt256}
    (rd8583 : RD code ee g s0 ⟨8583⟩ (d0 :: d1 :: d2 :: R)
      (clipperStatusPricePostCallMem top age baseMem out) (UInt256.ofNat 7) out acc k C)
    (hmem : baseMem.size = 96)
    (hread64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlo : 32 ≤ out.size) (hout : out.size < UInt256.size)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8606⟩
      (clipperStatusPriceWord out :: R)
      (clipperStatusPricePostCallMem top age baseMem out) (UInt256.ofNat 7) out acc k' C' := by
  exact RD.solcUint256ReturnWordDecodeOk
    (pc := ⟨8583⟩) (okPc := ⟨8603⟩) rd8583 hlo hout
    mem_cost (by native_decide)
    (clipperStatusPricePostCallMem_mload64 top age hmem hread64 hout)
    (clipperStatusPricePostCallMem_mload128 top age hmem hlo hout)
    mem_cost (by native_decide)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (clipperJumpDest8603 v hpatch)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode)
    hov

set_option maxHeartbeats 1000000 in
theorem RD.clipperStatusAfterPriceDoneTailTrue
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price d0 d1 top tic ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd8606 : RD code ee g s0 ⟨8606⟩ (price :: d0 :: d1 :: top :: tic :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hleDone :
      (UInt256.land tic clipperSalesUint96Mask).toNat ≤
        (UInt256.ofNat ee.header.timestamp).toNat)
    (htail :
      (solcSlotWord σ ee ⟨6⟩).toNat <
        (UInt256.sub (UInt256.ofNat ee.header.timestamp)
          (UInt256.land tic clipperSalesUint96Mask)).toNat)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 80 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (price :: (⟨1⟩ : UInt256) :: R)
      mem aw rdata (cA, σ) k' C' := by
  let ageForDone : UInt256 :=
    UInt256.sub (UInt256.ofNat ee.header.timestamp) (UInt256.land tic clipperSalesUint96Mask)
  let tail : UInt256 := solcSlotWord σ ee ⟨6⟩
  have rd9274pre := evm_run rd8606 with [
    raw push1 ⟨6⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd8608⟩ := rd9274pre.sload (by clipper_runtime_decode) (by evm_ov)
  have rd9274pre' := evm_run rd8608 with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8630⟩ (by clipper_runtime_decode) (by evm_ov),
    raw timestamp (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨96⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9274⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd9274 :=
    rd9274pre'.jump (by clipper_runtime_decode) (clipperJumpDest9274 v hpatch) (by evm_ov)
  obtain ⟨_, _, rd8630⟩ :=
    RD.clipperSubRoutine v hpatch rd9274 hleDone (clipperJumpDest8630 v hpatch)
      (by simp only [List.length_cons]; omega)
  have hgtTail : UInt256.gt ageForDone tail ≠ ⟨0⟩ := by
    have hgtTailOne : UInt256.gt ageForDone tail = ⟨1⟩ := by
      exact ugt_one (by simpa [ageForDone, tail] using htail)
    rw [hgtTailOne]
    decide
  have hgtTailOne : UInt256.gt ageForDone tail = ⟨1⟩ := by
    exact ugt_one (by simpa [ageForDone, tail] using htail)
  have rd8652 := evm_run rd8630 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8652⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jumpiT (by clipper_runtime_decode) (by simpa [ageForDone, tail] using hgtTail)
      (clipperJumpDest8652 v hpatch) (by evm_ov)]
  have rdret := evm_run rd8652 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) hret (by evm_ov)]
  exact ⟨_, _, by simpa [ageForDone, tail, hgtTailOne] using rdret⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperStatusAfterPriceRdivBranch
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price d0 d1 top tic ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd8606 : RD code ee g s0 ⟨8606⟩ (price :: d0 :: d1 :: top :: tic :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hleDone :
      (UInt256.land tic clipperSalesUint96Mask).toNat ≤
        (UInt256.ofNat ee.header.timestamp).toNat)
    (htail :
      (UInt256.sub (UInt256.ofNat ee.header.timestamp)
          (UInt256.land tic clipperSalesUint96Mask)).toNat ≤
        (solcSlotWord σ ee ⟨6⟩).toNat)
    (hmul : price.toNat * clipperRayWord.toNat < UInt256.size)
    (htop : top ≠ ⟨0⟩)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 100 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (price ::
        UInt256.lt (UInt256.div (UInt256.mul price clipperRayWord) top)
          (solcSlotWord σ ee ⟨7⟩) :: R)
      mem aw rdata (cA, σ) k' C' := by
  let ageForDone : UInt256 :=
    UInt256.sub (UInt256.ofNat ee.header.timestamp) (UInt256.land tic clipperSalesUint96Mask)
  let tail : UInt256 := solcSlotWord σ ee ⟨6⟩
  let cusp : UInt256 := solcSlotWord σ ee ⟨7⟩
  let ratio : UInt256 := UInt256.div (UInt256.mul price clipperRayWord) top
  have rd9274pre := evm_run rd8606 with [
    raw push1 ⟨6⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd8608⟩ := rd9274pre.sload (by clipper_runtime_decode) (by evm_ov)
  have rd9274pre' := evm_run rd8608 with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8630⟩ (by clipper_runtime_decode) (by evm_ov),
    raw timestamp (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨96⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9274⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd9274 :=
    rd9274pre'.jump (by clipper_runtime_decode) (clipperJumpDest9274 v hpatch) (by evm_ov)
  obtain ⟨_, _, rd8630⟩ :=
    RD.clipperSubRoutine v hpatch rd9274 hleDone (clipperJumpDest8630 v hpatch)
      (by simp only [List.length_cons]; omega)
  have hgtTailZero : UInt256.gt ageForDone tail = ⟨0⟩ := by
    exact ugt_zero (by simpa [ageForDone, tail] using htail)
  have rd8637 := evm_run rd8630 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8652⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jumpiNT (by clipper_runtime_decode) (by simpa [ageForDone, tail] using hgtTailZero)
      (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨7⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd8640⟩ := rd8637.sload (by clipper_runtime_decode) (by evm_ov)
  have rd9290 := evm_run rd8640 with [
    raw push2 ⟨8650⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup6 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9290⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) (clipperJumpDest9290 v hpatch) (by evm_ov)]
  obtain ⟨_, _, rd8650⟩ :=
    RD.clipperRdivRoutine v hpatch rd9290 hmul htop (clipperJumpDest8650 v hpatch)
      (by simp only [List.length_cons]; omega)
  have rdret := evm_run rd8650 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) hret (by evm_ov)]
  exact ⟨_, _, by simpa [ageForDone, tail, cusp, ratio] using rdret⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperGetStatusReturnLoadsFrom3283
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {needs done tic usr b0 c0 price e0 id ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (rd3283 : RD code ee g s0 ⟨3283⟩
      (needs :: done :: tic :: usr :: b0 :: c0 :: price :: e0 :: id :: ret :: R)
      mem (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hmem : 64 ≤ mem.size)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 80 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee ((solcMappingSlot ⟨12⟩ id) + ⟨1⟩) ::
        solcSlotWord σ ee ((solcMappingSlot ⟨12⟩ id) + ⟨2⟩) ::
        price :: needs :: R)
      (twoWordHashMem id ⟨12⟩ mem) (UInt256.ofNat 7) rdata (cA, σ) k' C' := by
  let base : UInt256 := solcMappingSlot ⟨12⟩ id
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem id (⟨12⟩ : UInt256) mem).readWithPadding 0 64))) =
        base := by
    simpa [base] using twoWordHashMem_solcMappingSlot_of_ge (⟨12⟩ : UInt256) id hmem
  have rdHash := evm_run rd3283 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap9 (by clipper_runtime_decode) (by evm_ov),
    raw dup10 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (wordAt0Mem id mem) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨12⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (twoWordHashMem id (⟨12⟩ : UInt256) mem) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap9 (by clipper_runtime_decode) (by evm_ov),
    raw keccak256 0 base (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost hslot
      (by native_decide) (by evm_ov),
    raw push1 ⟨2⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rdLot⟩ := rdHash.sload (by clipper_runtime_decode) (by evm_ov)
  have rdTabSlot := evm_run rdLot with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rdTab⟩ := rdTabSlot.sload (by clipper_runtime_decode) (by evm_ov)
  have rdRet := evm_run rdTab with [
    raw swap9 (by clipper_runtime_decode) (by evm_ov),
    raw swap10 (by clipper_runtime_decode) (by evm_ov),
    raw swap7 (by clipper_runtime_decode) (by evm_ov),
    raw swap9 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap8 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw swap6 (by clipper_runtime_decode) (by evm_ov),
    raw swap5 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) hret (by evm_ov)]
  exact ⟨_, _, by simpa [base, solcSlotWord] using rdRet⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperGetStatusAfterStatusToReturnEncoder
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price done a0 tic usr b0 c0 d0 e0 id ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (rd3258 : RD code ee g s0 ⟨3258⟩
      (price :: done :: a0 :: tic :: usr :: b0 :: c0 :: d0 :: e0 :: id :: ret :: R)
      mem (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hmem : 64 ≤ mem.size)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 100 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee ((solcMappingSlot ⟨12⟩ id) + ⟨1⟩) ::
        solcSlotWord σ ee ((solcMappingSlot ⟨12⟩ id) + ⟨2⟩) ::
        price :: clipperGetStatusNeedsRedoWord usr done :: R)
      (twoWordHashMem id ⟨12⟩ mem) (UInt256.ofNat 7) rdata (cA, σ) k' C' := by
  let usrMasked : UInt256 := UInt256.land usr solcAddrMask
  let usrIsZero : UInt256 := UInt256.isZero usrMasked
  let usrNonzero : UInt256 := UInt256.isZero usrIsZero
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have rd3277 := evm_run rd3258 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw swap7 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨3283⟩ (by clipper_runtime_decode) (by evm_ov)]
  by_cases huser : usrIsZero = ⟨0⟩
  · have rd3283 := evm_run rd3277 with [
      raw jumpiNT (by clipper_runtime_decode) (by simpa [usrMasked, usrIsZero, haddrMask] using huser)
        (by evm_ov),
      raw pop (by clipper_runtime_decode) (by evm_ov),
      raw dup1 (by clipper_runtime_decode) (by evm_ov)]
    obtain ⟨_, _, rdRet⟩ :=
      RD.clipperGetStatusReturnLoadsFrom3283 v hpatch rd3283 hmem hret (by omega)
    exact ⟨_, _, by
      simpa [clipperGetStatusNeedsRedoWord, usrMasked, usrIsZero, huser, haddrMask] using
        rdRet⟩
  · have hnonzero : usrNonzero = ⟨0⟩ := by
      exact isZero_eq_zero_of_ne huser
    have rd3283 := evm_run rd3277 with [
      raw jumpiT (by clipper_runtime_decode)
        (by
          intro hzero
          exact huser (by simpa [usrMasked, usrIsZero, haddrMask] using hzero))
        (clipperJumpDest3283 v hpatch) (by evm_ov)]
    obtain ⟨_, _, rdRet⟩ :=
      RD.clipperGetStatusReturnLoadsFrom3283 v hpatch rd3283 hmem hret (by omega)
    exact ⟨_, _, by
      simpa [clipperGetStatusNeedsRedoWord, usrMasked, usrIsZero, usrNonzero, huser,
        hnonzero, haddrMask] using rdRet⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperGetStatusReturnEncode
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tab lot price needs : UInt256} {R : List UInt256}
    {mem memBool memPrice memLot memTab retBytes rdata : ByteArray} {k C : ℕ}
    (rd789 : RD code ee g s0 ⟨789⟩ (tab :: lot :: price :: needs :: R)
      mem (UInt256.ofNat 7) rdata acc k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hmemBool :
      (UInt256.toByteArray (UInt256.isZero (UInt256.isZero needs))).write 0 mem
        (⟨128⟩ : UInt256).toNat 32 = memBool)
    (hmemPrice :
      (UInt256.toByteArray price).write 0 memBool
        ((⟨32⟩ : UInt256) + ⟨128⟩).toNat 32 = memPrice)
    (hmemLot :
      (UInt256.toByteArray lot).write 0 memPrice
        ((⟨64⟩ : UInt256) + ⟨128⟩).toNat 32 = memLot)
    (hmemTab :
      (UInt256.toByteArray tab).write 0 memLot
        ((⟨96⟩ : UInt256) + ⟨128⟩).toNat 32 = memTab)
    (hmload64Final :
      (if (⟨64⟩ : UInt256).toNat ≥ memTab.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memTab.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hretBytes :
      memTab.readWithPadding (⟨128⟩ : UInt256).toNat
        (((⟨128⟩ : UInt256) - ⟨128⟩) + ⟨128⟩).toNat = retBytes)
    (hov : R.length + 16 ≤ 1024) :
    RDret code g s0 acc retBytes := by
  exact evm_run rd789 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost
      hmload64 (by native_decide) (by evm_ov),
    raw swap5 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw dup6 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 memBool (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost
      hmemBool (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup6 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap4 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap4 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 memPrice (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost
      hmemPrice (by native_decide) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 memLot (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost
      hmemLot (by native_decide) (by evm_ov),
    raw push1 ⟨96⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 3 memTab (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost
      hmemTab (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost
      hmload64Final (by native_decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨128⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw ret 0 retBytes (by clipper_runtime_decode) mem_cost hretBytes (by evm_ov)]

theorem RD.clipperGetStatusReturnEncodeConcrete
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tab lot price needs : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (rd789 : RD code ee g s0 ⟨789⟩ (tab :: lot :: price :: needs :: R)
      mem (UInt256.ofNat 7) rdata acc k C)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 16 ≤ 1024) :
    RDret code g s0 acc (clipperGetStatusReturnBytes needs price lot tab) := by
  exact RD.clipperGetStatusReturnEncode v hpatch rd789
    (memBool := writeWord mem 128 (UInt256.isZero (UInt256.isZero needs)))
    (memPrice := writeWord
      (writeWord mem 128 (UInt256.isZero (UInt256.isZero needs))) 160 price)
    (memLot := writeWord
      (writeWord (writeWord mem 128 (UInt256.isZero (UInt256.isZero needs))) 160 price)
      192 lot)
    (memTab := clipperGetStatusReturnMem mem needs price lot tab)
    (retBytes := clipperGetStatusReturnBytes needs price lot tab)
    (by
      exact mloadFreePtrValue
        (by rw [hmem]; decide)
        (by decide)
        hread64)
    (by rfl)
    (by
      change writeWord (writeWord mem 128 (UInt256.isZero (UInt256.isZero needs))) 160 price =
        writeWord (writeWord mem 128 (UInt256.isZero (UInt256.isZero needs))) 160 price
      rfl)
    (by
      change
        writeWord
          (writeWord (writeWord mem 128 (UInt256.isZero (UInt256.isZero needs))) 160 price)
          192 lot =
        writeWord
          (writeWord (writeWord mem 128 (UInt256.isZero (UInt256.isZero needs))) 160 price)
          192 lot
      rfl)
    (by
      change
        writeWord
          (writeWord
            (writeWord (writeWord mem 128 (UInt256.isZero (UInt256.isZero needs))) 160 price)
            192 lot) 224 tab =
        clipperGetStatusReturnMem mem needs price lot tab
      rfl)
    (clipperGetStatusReturnMem_mload64 needs price lot tab hmem hread64)
    (by
      change (clipperGetStatusReturnMem mem needs price lot tab).readWithPadding 128 128 =
        clipperGetStatusReturnBytes needs price lot tab
      exact clipperGetStatusReturnMem_read128_128 needs price lot tab hmem)
    hov

end Reasoning.Reach

end Benchmarks.Dss.Clipper
