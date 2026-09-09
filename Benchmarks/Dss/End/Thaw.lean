import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `thaw()` transition -/

abbrev endThawConcreteSelector : ByteArray := selectorBytes 0x59 0x20 0x37 0x5c

abbrev endThawEntryPc : UInt256 := ⟨707⟩
abbrev endThawReturnPc : UInt256 := ⟨562⟩
abbrev endThawBodyPc : UInt256 := ⟨4525⟩

abbrev endThawLiveWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
    endSlotWord ⟨8⟩ σ I

abbrev endThawDebtWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
    endSlotWord ⟨11⟩ σ I

abbrev endThawWhenWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
    endSlotWord ⟨9⟩ σ I

abbrev endThawWaitWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
    endSlotWord ⟨10⟩ σ I

abbrev endThawDeadlineWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
    endThawWhenWord σ I + endThawWaitWord σ I

abbrev endThawTimestampWord (I : ExecutionEnv) : UInt256 :=
    UInt256.ofNat I.header.timestamp

abbrev endThawVatWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
    UInt256.land (endSlotWord ⟨1⟩ σ I) solcAddrMask

abbrev endThawVowWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
    UInt256.land (endSlotWord ⟨4⟩ σ I) solcAddrMask

abbrev endThawCureWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
    UInt256.land (endSlotWord ⟨7⟩ σ I) solcAddrMask

abbrev endThawVatAddr (σ : AccountMap) (I : ExecutionEnv) : AccountAddress :=
    AccountAddress.ofNat (endThawVatWord σ I).toNat

abbrev endThawVowAddr (σ : AccountMap) (I : ExecutionEnv) : AccountAddress :=
    AccountAddress.ofNat (endThawVowWord σ I).toNat

abbrev endThawCureAddr (σ : AccountMap) (I : ExecutionEnv) : AccountAddress :=
    AccountAddress.ofNat (endThawCureWord σ I).toNat

abbrev endThawLiveEvaledRef : EvaledStorageRef :=
    { base := "live", steps := [] }

abbrev endThawDebtEvaledRef : EvaledStorageRef :=
    { base := "debt", steps := [] }

abbrev endThawDaiSelectorRaw : UInt256 := ⟨0x3612d9a3⟩
abbrev endThawDaiSelectorWord : UInt256 := ⟨0x6c25b346⟩
abbrev endThawDaiOutPtr : UInt256 := ⟨128⟩
abbrev endThawDaiInSize : UInt256 := ⟨36⟩
abbrev endThawDaiOutSize : UInt256 := ⟨32⟩
abbrev endThawDaiEndPtr : UInt256 := ⟨164⟩

abbrev endThawDebtSelectorWord : UInt256 := ⟨0x0dca59c1⟩
abbrev endThawTellSelectorWord : UInt256 := ⟨0x53d700e5⟩
abbrev endThawNoArgOutPtr : UInt256 := ⟨128⟩
abbrev endThawNoArgInSize : UInt256 := ⟨4⟩
abbrev endThawNoArgOutSize : UInt256 := ⟨32⟩
abbrev endThawNoArgEndPtr : UInt256 := ⟨132⟩

abbrev endThawDaiWord (out : ByteArray) : UInt256 :=
    UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

abbrev endThawReturnWord (out : ByteArray) : UInt256 :=
    UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

abbrev endThawStoreVatDai (out : ByteArray) : Store :=
    (∅ : Store).insert "vatDai" (.int (Int.ofNat (endThawDaiWord out).toNat))

abbrev endThawStoreDeadlineWord (out : ByteArray) (deadline : UInt256) : Store :=
    (endThawStoreVatDai out).insert "deadline" (.int (Int.ofNat deadline.toNat))

abbrev endThawStoreDeadline (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) : Store :=
    endThawStoreDeadlineWord out (endThawDeadlineWord σ I)

abbrev endThawStoreVatDebt (out debtOut : ByteArray) (deadline : UInt256) : Store :=
    (endThawStoreDeadlineWord out deadline).insert "vatDebt"
    (.int (Int.ofNat (endThawReturnWord debtOut).toNat))

abbrev endThawStoreCureTell (out debtOut tellOut : ByteArray) (deadline : UInt256) :
    Store :=
    (endThawStoreVatDebt out debtOut deadline).insert "cureTell"
    (.int (Int.ofNat (endThawReturnWord tellOut).toNat))

abbrev endThawStoreDebtNew (out debtOut tellOut : ByteArray) (deadline debtNew : UInt256) :
    Store :=
    (endThawStoreCureTell out debtOut tellOut deadline).insert "debtNew"
    (.int (Int.ofNat debtNew.toNat))

noncomputable def endThawDaiSelectorMem (mem : ByteArray) : ByteArray :=
    (UInt256.shiftLeft endThawDaiSelectorRaw ⟨225⟩).toByteArray.write 0 mem
    endThawDaiOutPtr.toNat 32

noncomputable def endThawDaiCalldataMem (σ : AccountMap) (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
    (endThawVowWord σ I).toByteArray.write 0 (endThawDaiSelectorMem mem)
    (endThawDaiOutPtr + ⟨4⟩).toNat 32

noncomputable def endThawDaiPostCallMem (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) : ByteArray :=
    out.write 0 (endThawDaiCalldataMem σ I solcFreePtrMem) endThawDaiOutPtr.toNat
    (min endThawDaiOutSize (UInt256.ofNat out.size)).toNat

noncomputable def endThawNoArgCalldataMem (selector : UInt256) (mem : ByteArray) :
    ByteArray :=
    (UInt256.shiftLeft selector ⟨224⟩).toByteArray.write 0 mem
    endThawNoArgOutPtr.toNat 32

noncomputable def endThawNoArgPostCallMem (selector : UInt256) (mem out : ByteArray) :
    ByteArray :=
    out.write 0 (endThawNoArgCalldataMem selector mem) endThawNoArgOutPtr.toNat
    (min endThawNoArgOutSize (UInt256.ofNat out.size)).toNat

theorem endThawDaiSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (endThawDaiSelectorMem mem).size = 160 := by
  unfold endThawDaiSelectorMem
  exact toByteArray_write32_size_of_ge mem (UInt256.shiftLeft endThawDaiSelectorRaw ⟨225⟩)
    endThawDaiOutPtr.toNat 96 160 hmem (by decide +native) (by decide +native)
    (by decide +native)

theorem endThawDaiSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (endThawDaiSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold endThawDaiSelectorMem
  rw [toByteArray_write_read_below_of_gap (UInt256.shiftLeft endThawDaiSelectorRaw ⟨225⟩)
    mem endThawDaiOutPtr.toNat 64 (by rw [hmem]) (by decide +native)
    (by rw [hmem]; decide +native), hread64]

theorem endThawDaiCalldataMem_size (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endThawDaiCalldataMem σ I mem).size = 164 := by
  unfold endThawDaiCalldataMem
  exact toByteArray_write32_size_of_le (endThawDaiSelectorMem mem) (endThawVowWord σ I)
    132 160 164 (endThawDaiSelectorMem_size hmem)
    (by rw [endThawDaiSelectorMem_size hmem]; omega) (by omega)

theorem endThawDaiCalldataMem_read64 (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (endThawDaiCalldataMem σ I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endThawDaiCalldataMem
  change ((endThawVowWord σ I).toByteArray.write 0 (endThawDaiSelectorMem mem) 132
      32).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [endThawDaiSelectorMem_size hmem]; omega) (by omega),
    endThawDaiSelectorMem_read64 hmem hread64]

theorem endThawDaiSelectorMem_selector {mem : ByteArray} (hmem : mem.size = 96) :
    (endThawDaiSelectorMem mem).extract 128 132 = daiSelector := by
  unfold endThawDaiSelectorMem
  rw [show endThawDaiOutPtr.toNat = 128 by decide +native]
  have hgap : 128 - mem.size < USize.size := by
    rw [hmem]
    decide +native
  rw [toByteArray_write_eq (UInt256.shiftLeft endThawDaiSelectorRaw ⟨225⟩) mem 128
    (by omega) hgap]
  have hprefix :
      (mem ++ ffi.ByteArray.zeroes (128 - mem.size)).size = 128 := by
    rw [ByteArray.size_append, ByteArray_zeroes_size, hmem]
  rw [extract_append_right_window _ _ 128 132 (by rw [hprefix]), hprefix,
    show 128 - 128 = 0 from rfl, show 132 - 128 = 4 from rfl,
    toByteArray_eq_toBytesBE]
  decide +native

theorem endThawDaiCalldataMem_read128_36 (σ : AccountMap) (I : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (endThawDaiCalldataMem σ I mem).readWithPadding 128 36 =
      daiSelector ++ (endThawVowWord σ I).toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
      (by rw [endThawDaiCalldataMem_size σ I hmem])]
  unfold endThawDaiCalldataMem
  rw [show (endThawDaiOutPtr + ⟨4⟩).toNat = 132 by decide +native,
    write32_eq _ (endThawDaiSelectorMem mem) 132 (by rw [toByteArray_size])
      (by rw [endThawDaiSelectorMem_size hmem]; omega)]
  have hAsz : ((endThawDaiSelectorMem mem).extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, endThawDaiSelectorMem_size hmem]
    omega
  have hBsz : ((endThawVowWord σ I).toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hPsz :
      ((endThawDaiSelectorMem mem).extract 0 132 ++
        (endThawVowWord σ I).toByteArray.extract 0 32).size = 164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull :
      (endThawVowWord σ I).toByteArray.extract 0 32 =
        (endThawVowWord σ I).toByteArray := by
    have h := @ByteArray.extract_zero_size (endThawVowWord σ I).toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
    extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 132 128 132 (by omega), endThawDaiSelectorMem_selector hmem,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
  show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

theorem endThawDaiEncode_eq (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    config.externalABI.encode? "dai" [.address (endThawVowAddr σ I)] =
      some ((endThawDaiCalldataMem σ I mem).readWithPadding
        endThawDaiOutPtr.toNat endThawDaiInSize.toNat) := by
  change config.externalABI.encode? "dai" [.address (endThawVowAddr σ I)] =
    some ((endThawDaiCalldataMem σ I mem).readWithPadding 128 36)
  rw [endThawDaiCalldataMem_read128_36 σ I hmem]
  have hvowCanon : (endThawVowWord σ I).toNat < EVM.addressModulus := by
    simpa [endThawVowWord] using
      solcAddrMask_result_canonical (endSlotWord ⟨4⟩ σ I)
  have hvowVal :
      (endThawVowAddr σ I).val = (endThawVowWord σ I).toNat := by
    unfold endThawVowAddr AccountAddress.ofNat
    simp only [Fin.val_ofNat]
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hvowCanon
  have hvowWord : EVM.word ↑(endThawVowAddr σ I) = endThawVowWord σ I := by
    change UInt256.ofNat (endThawVowAddr σ I).val = endThawVowWord σ I
    rw [hvowVal]
    exact u256_ofNat_toNat _
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr, daiSelector, selectorBytes, hvowWord]
  apply ByteArray.ext
  simp [word_toBytesBE_toByteArray_eq_toByteArray]

theorem endThawDaiWriteLen_eq {out : ByteArray} (hout : out.size < UInt256.size) :
    (min endThawDaiOutSize (UInt256.ofNat out.size)).toNat = min 32 out.size := by
  change (min (UInt256.ofNat 32) (UInt256.ofNat out.size)).toNat = min 32 out.size
  by_cases hle : 32 ≤ out.size
  · rw [Nat.min_eq_left hle]
    exact umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size) (by decide) hle hout
  · have hlt : out.size < 32 := by omega
    rw [Nat.min_eq_right (by omega : out.size ≤ 32)]
    exact umin_ofNat_right_toNat_of_lt (c := 32) (n := out.size) (by decide) hlt hout

theorem endThawDaiPostCallMem_size (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) :
    (endThawDaiPostCallMem σ I out).size = 164 := by
  unfold endThawDaiPostCallMem
  rw [endThawDaiWriteLen_eq hout]
  rw [show endThawDaiOutPtr.toNat = 128 by decide +native]
  by_cases hlen0 : min 32 out.size = 0
  · rw [hlen0, byteArray_write_len_zero, endThawDaiCalldataMem_size σ I solcFreePtrMem_size]
  · rw [write_eq_gen out (endThawDaiCalldataMem σ I solcFreePtrMem) 128
      (min 32 out.size) hlen0 (Nat.min_le_right _ _)
      (by rw [endThawDaiCalldataMem_size σ I solcFreePtrMem_size]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      endThawDaiCalldataMem_size σ I solcFreePtrMem_size]
    have hleout : min 32 out.size ≤ out.size := Nat.min_le_right _ _
    omega

theorem endThawDaiPostCallMem_read128_32 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hout : out.size < UInt256.size) (hlo : 32 ≤ out.size) :
    (endThawDaiPostCallMem σ I out).readWithPadding 128 32 =
      out.extract 0 32 := by
  unfold endThawDaiPostCallMem
  rw [show endThawDaiOutPtr.toNat = 128 by decide +native]
  rw [endThawDaiWriteLen_eq hout, show min 32 out.size = 32 from Nat.min_eq_left hlo]
  rw [write_eq_gen out (endThawDaiCalldataMem σ I solcFreePtrMem) 128 32
    (by decide) (by omega)
    (by rw [endThawDaiCalldataMem_size σ I solcFreePtrMem_size]; omega)]
  rw [readWithPadding_eq_extract _ 128 (by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      endThawDaiCalldataMem_size σ I solcFreePtrMem_size]
    omega)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      endThawDaiCalldataMem_size σ I solcFreePtrMem_size]
    omega)]
  rw [extract_append_right_window _ _ _ _ (by rw [ByteArray.size_extract]; omega)]
  rw [ByteArray.size_extract]
  rw [show min 128 (endThawDaiCalldataMem σ I solcFreePtrMem).size - 0 = 128 by
    rw [endThawDaiCalldataMem_size σ I solcFreePtrMem_size]
    omega]
  rw [show 128 - 128 = 0 by omega, show 160 - 128 = 32 by omega]
  rw [extract_extract_BA]
  rw [show 0 + 0 = 0 by omega, show min (0 + 32) 32 = 32 by omega]

theorem endThawDaiPostCallMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hout : out.size < UInt256.size) :
    (endThawDaiPostCallMem σ I out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endThawDaiPostCallMem
  rw [show endThawDaiOutPtr.toNat = 128 by decide +native, endThawDaiWriteLen_eq hout]
  by_cases hlen0 : min 32 out.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    exact endThawDaiCalldataMem_read64 σ I solcFreePtrMem_size solcFreePtrMem_read64
  · rw [write_read_below_gen out (endThawDaiCalldataMem σ I solcFreePtrMem)
      128 (min 32 out.size) 64 hlen0 (Nat.min_le_right _ _)
      (by rw [endThawDaiCalldataMem_size σ I solcFreePtrMem_size]; omega)
      (by decide +native)]
    exact endThawDaiCalldataMem_read64 σ I solcFreePtrMem_size solcFreePtrMem_read64

theorem endThawDaiPostCallMem_mload64 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (endThawDaiPostCallMem σ I out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endThawDaiPostCallMem σ I out).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [endThawDaiPostCallMem_size σ I out hout]; decide)
    (by decide)
    (endThawDaiPostCallMem_read64 σ I out hout)

theorem endThawDaiPostCallMem_mload128 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hout : out.size < UInt256.size) (hlo : 32 ≤ out.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (endThawDaiPostCallMem σ I out).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endThawDaiPostCallMem σ I out).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) =
      endThawDaiWord out := by
  rw [show (⟨128⟩ : UInt256).toNat = 128 by decide]
  rw [endThawDaiPostCallMem_size σ I out hout,
    endThawDaiPostCallMem_read128_32 σ I out hout hlo]
  change (if False ∨ False then (⟨0⟩ : UInt256) else endThawDaiWord out) =
    endThawDaiWord out
  simp

theorem endThawNoArgCalldataMem_size {selector : UInt256} {mem : ByteArray}
    (hmem : mem.size = 164) :
    (endThawNoArgCalldataMem selector mem).size = 164 := by
  unfold endThawNoArgCalldataMem
  exact toByteArray_write32_size_of_le mem (UInt256.shiftLeft selector ⟨224⟩)
    endThawNoArgOutPtr.toNat 164 164 hmem
    (by rw [hmem]; decide +native)
    (by decide +native)

theorem endThawNoArgCalldataMem_read64 {selector : UInt256} {mem : ByteArray}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (endThawNoArgCalldataMem selector mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endThawNoArgCalldataMem
  change
    (((UInt256.shiftLeft selector ⟨224⟩).toByteArray).write 0 mem 128 32).readWithPadding
      64 32 = UInt256.toByteArray ⟨128⟩
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
    (by omega), hread64]

theorem endThawDebtCalldataMem_read128_4 {mem : ByteArray} (hmem : mem.size = 164) :
    (endThawNoArgCalldataMem endThawDebtSelectorWord mem).readWithPadding 128 4 =
      debtSelector := by
  unfold endThawNoArgCalldataMem endThawDebtSelectorWord
  change
    (((UInt256.shiftLeft (⟨0x0dca59c1⟩ : UInt256) ⟨224⟩).toByteArray).write 0 mem
      128 32).readWithPadding 128 4 = debtSelector
  rw [toByteArray_write_read_window_of_gap
    (UInt256.shiftLeft (⟨0x0dca59c1⟩ : UInt256) ⟨224⟩) mem 128 0 4
    (by omega) (by omega) (by omega) (by rw [hmem]; decide +native)]
  unfold debtSelector selectorBytes
  decide +native

theorem endThawTellCalldataMem_read128_4 {mem : ByteArray} (hmem : mem.size = 164) :
    (endThawNoArgCalldataMem endThawTellSelectorWord mem).readWithPadding 128 4 =
      tellSelector := by
  unfold endThawNoArgCalldataMem endThawTellSelectorWord
  change
    (((UInt256.shiftLeft (⟨0x53d700e5⟩ : UInt256) ⟨224⟩).toByteArray).write 0 mem
      128 32).readWithPadding 128 4 = tellSelector
  rw [toByteArray_write_read_window_of_gap
    (UInt256.shiftLeft (⟨0x53d700e5⟩ : UInt256) ⟨224⟩) mem 128 0 4
    (by omega) (by omega) (by omega) (by rw [hmem]; decide +native)]
  unfold tellSelector selectorBytes
  decide +native

theorem endThawDebtEncode_eq {mem : ByteArray} (hmem : mem.size = 164) :
    config.externalABI.encode? "debt" [] =
      some ((endThawNoArgCalldataMem endThawDebtSelectorWord mem).readWithPadding
        endThawNoArgOutPtr.toNat endThawNoArgInSize.toNat) := by
  change config.externalABI.encode? "debt" [] =
    some ((endThawNoArgCalldataMem endThawDebtSelectorWord mem).readWithPadding 128 4)
  rw [endThawDebtCalldataMem_read128_4 hmem]
  simp [config, externalABI, debtSelector]

theorem endThawTellEncode_eq {mem : ByteArray} (hmem : mem.size = 164) :
    config.externalABI.encode? "tell" [] =
      some ((endThawNoArgCalldataMem endThawTellSelectorWord mem).readWithPadding
        endThawNoArgOutPtr.toNat endThawNoArgInSize.toNat) := by
  change config.externalABI.encode? "tell" [] =
    some ((endThawNoArgCalldataMem endThawTellSelectorWord mem).readWithPadding 128 4)
  rw [endThawTellCalldataMem_read128_4 hmem]
  simp [config, externalABI, tellSelector]

theorem endThawNoArgWriteLen_eq {out : ByteArray} (hout : out.size < UInt256.size) :
    (min endThawNoArgOutSize (UInt256.ofNat out.size)).toNat = min 32 out.size := by
  change (min (UInt256.ofNat 32) (UInt256.ofNat out.size)).toNat = min 32 out.size
  by_cases hle : 32 ≤ out.size
  · rw [Nat.min_eq_left hle]
    exact umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size) (by decide) hle hout
  · have hlt : out.size < 32 := by omega
    rw [Nat.min_eq_right (by omega : out.size ≤ 32)]
    exact umin_ofNat_right_toNat_of_lt (c := 32) (n := out.size) (by decide) hlt hout

theorem endThawNoArgPostCallMem_size {selector : UInt256} {mem out : ByteArray}
    (hmem : mem.size = 164) (hout : out.size < UInt256.size) :
    (endThawNoArgPostCallMem selector mem out).size = 164 := by
  unfold endThawNoArgPostCallMem
  rw [show endThawNoArgOutPtr.toNat = 128 by decide +native, endThawNoArgWriteLen_eq hout]
  by_cases hlen0 : min 32 out.size = 0
  · rw [hlen0, byteArray_write_len_zero, endThawNoArgCalldataMem_size hmem]
  · rw [write_eq_gen out (endThawNoArgCalldataMem selector mem) 128
      (min 32 out.size) hlen0 (Nat.min_le_right _ _)
      (by rw [endThawNoArgCalldataMem_size hmem]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, endThawNoArgCalldataMem_size hmem]
    have hleout : min 32 out.size ≤ out.size := Nat.min_le_right _ _
    omega

theorem endThawNoArgPostCallMem_read128_32 {selector : UInt256} {mem out : ByteArray}
    (hmem : mem.size = 164) (hout : out.size < UInt256.size) (hlo : 32 ≤ out.size) :
    (endThawNoArgPostCallMem selector mem out).readWithPadding 128 32 =
      out.extract 0 32 := by
  unfold endThawNoArgPostCallMem
  rw [show endThawNoArgOutPtr.toNat = 128 by decide +native]
  rw [endThawNoArgWriteLen_eq hout, show min 32 out.size = 32 from Nat.min_eq_left hlo]
  rw [write_eq_gen out (endThawNoArgCalldataMem selector mem) 128 32
    (by decide) (by omega) (by rw [endThawNoArgCalldataMem_size hmem]; omega)]
  rw [readWithPadding_eq_extract _ 128 (by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, endThawNoArgCalldataMem_size hmem]
    omega)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      endThawNoArgCalldataMem_size hmem]
    omega)]
  rw [extract_append_right_window _ _ _ _ (by rw [ByteArray.size_extract]; omega)]
  rw [ByteArray.size_extract]
  rw [show min 128 (endThawNoArgCalldataMem selector mem).size - 0 = 128 by
    rw [endThawNoArgCalldataMem_size hmem]
    omega]
  rw [show 128 - 128 = 0 by omega, show 160 - 128 = 32 by omega]
  rw [extract_extract_BA]
  rw [show 0 + 0 = 0 by omega, show min (0 + 32) 32 = 32 by omega]

theorem endThawNoArgPostCallMem_read64 {selector : UInt256} {mem out : ByteArray}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hout : out.size < UInt256.size) :
    (endThawNoArgPostCallMem selector mem out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endThawNoArgPostCallMem
  rw [show endThawNoArgOutPtr.toNat = 128 by decide +native, endThawNoArgWriteLen_eq hout]
  by_cases hlen0 : min 32 out.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    exact endThawNoArgCalldataMem_read64 hmem hread64
  · rw [write_read_below_gen out (endThawNoArgCalldataMem selector mem)
      128 (min 32 out.size) 64 hlen0 (Nat.min_le_right _ _)
      (by rw [endThawNoArgCalldataMem_size hmem]; omega)
      (by decide +native)]
    exact endThawNoArgCalldataMem_read64 hmem hread64

theorem endThawNoArgPostCallMem_mload64 {selector : UInt256} {mem out : ByteArray}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (endThawNoArgPostCallMem selector mem out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endThawNoArgPostCallMem selector mem out).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [endThawNoArgPostCallMem_size hmem hout]; decide)
    (by decide)
    (endThawNoArgPostCallMem_read64 hmem hread64 hout)

theorem endThawNoArgPostCallMem_mload128 {selector : UInt256} {mem out : ByteArray}
    (hmem : mem.size = 164) (hout : out.size < UInt256.size) (hlo : 32 ≤ out.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (endThawNoArgPostCallMem selector mem out).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endThawNoArgPostCallMem selector mem out).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) =
      endThawReturnWord out := by
  rw [show (⟨128⟩ : UInt256).toNat = 128 by decide]
  rw [endThawNoArgPostCallMem_size hmem hout,
    endThawNoArgPostCallMem_read128_32 hmem hout hlo]
  change (if False ∨ False then (⟨0⟩ : UInt256) else endThawReturnWord out) =
    endThawReturnWord out
  simp

theorem endThawDebtDecode_ok (out : ByteArray) (hlo : 32 ≤ out.size) :
    config.externalABI.decode? "debt" out =
      some [.int (Int.ofNat (endThawReturnWord out).toNat)] := by
  change decodeReturn? uint256 out =
    some [.int (Int.ofNat (endThawReturnWord out).toNat)]
  unfold decodeReturn?
  change Option.map (fun v => [v])
      (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 abiUInt256 out) =
    some [Value.int (Int.ofNat (endThawReturnWord out).toNat)]
  rw [decodeReturnValueWithMode_legacy_uint256_ok (returndata := out) hlo]
  change some [Value.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))] =
    some [Value.int (Int.ofNat (endThawReturnWord out).toNat)]
  rw [show (endThawReturnWord out).toNat = fromByteArrayBigEndian (out.extract 0 32) by
    unfold endThawReturnWord
    exact UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt hlo)]

theorem endThawDebtDecode_short (out : ByteArray) (hshort : out.size < 32) :
    config.externalABI.decode? "debt" out = none := by
  change decodeReturn? uint256 out = none
  unfold decodeReturn?
  change Option.map (fun v => [v])
      (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 abiUInt256 out) = none
  rw [decodeReturnValueWithMode_legacy_uint256_none_short (returndata := out) hshort]
  rfl

theorem endThawTellDecode_ok (out : ByteArray) (hlo : 32 ≤ out.size) :
    config.externalABI.decode? "tell" out =
      some [.int (Int.ofNat (endThawReturnWord out).toNat)] := by
  change decodeReturn? uint256 out =
    some [.int (Int.ofNat (endThawReturnWord out).toNat)]
  unfold decodeReturn?
  change Option.map (fun v => [v])
      (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 abiUInt256 out) =
    some [Value.int (Int.ofNat (endThawReturnWord out).toNat)]
  rw [decodeReturnValueWithMode_legacy_uint256_ok (returndata := out) hlo]
  change some [Value.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))] =
    some [Value.int (Int.ofNat (endThawReturnWord out).toNat)]
  rw [show (endThawReturnWord out).toNat = fromByteArrayBigEndian (out.extract 0 32) by
    unfold endThawReturnWord
    exact UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt hlo)]

theorem endThawTellDecode_short (out : ByteArray) (hshort : out.size < 32) :
    config.externalABI.decode? "tell" out = none := by
  change decodeReturn? uint256 out = none
  unfold decodeReturn?
  change Option.map (fun v => [v])
      (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 abiUInt256 out) = none
  rw [decodeReturnValueWithMode_legacy_uint256_none_short (returndata := out) hshort]
  rfl

theorem endThawDaiDecode_ok (out : ByteArray) (hlo : 32 ≤ out.size) :
    config.externalABI.decode? "dai" out =
      some [.int (Int.ofNat (endThawDaiWord out).toNat)] := by
  change decodeReturn? uint256 out =
    some [.int (Int.ofNat (endThawDaiWord out).toNat)]
  unfold decodeReturn?
  change Option.map (fun v => [v])
      (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 abiUInt256 out) =
    some [Value.int (Int.ofNat (endThawDaiWord out).toNat)]
  rw [decodeReturnValueWithMode_legacy_uint256_ok (returndata := out) hlo]
  change some [Value.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))] =
    some [Value.int (Int.ofNat (endThawDaiWord out).toNat)]
  rw [show (endThawDaiWord out).toNat = fromByteArrayBigEndian (out.extract 0 32) by
    unfold endThawDaiWord
    exact UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt hlo)]

theorem endThawDaiDecode_short (out : ByteArray) (hshort : out.size < 32) :
    config.externalABI.decode? "dai" out = none := by
  change decodeReturn? uint256 out = none
  unfold decodeReturn?
  change Option.map (fun v => [v])
      (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 abiUInt256 out) = none
  rw [decodeReturnValueWithMode_legacy_uint256_none_short (returndata := out) hshort]
  rfl

theorem endThawEvalExpr_ge_uint256_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hlt : a.toNat < b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ge lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact hlt

theorem endThawEvalExpr_le_uint256_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hle : a.toNat ≤ b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hle

theorem endThawEvalExpr_sub256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b diff : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hdiff : diff = UInt256.sub a b)
    (hle : b.toNat ≤ a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (u256 (.binary .sub x y)) = .ok (.int (Int.ofNat diff.toNat)) := by
  have hdiffNat : diff.toNat = a.toNat - b.toNat := by
    rw [hdiff, usub_toNat hle]
  have hsubInt : (a.toNat : Int) - (b.toNat : Int) = ((a.toNat - b.toNat : Nat) : Int) :=
    (Int.ofNat_sub hle).symm
  have hltNat : a.toNat - b.toNat < UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    omega
  have hlt : ¬ ((a.toNat - b.toNat : Nat) : Int) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hltNat))
  simp [u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  rw [if_neg]
  · rw [hsubInt, ← hdiffNat]
    rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_le.mpr hbad) hle
    · rw [hsubInt] at hbad
      exact hlt hbad

theorem endThawEvalExpr_sub256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hlt : a.toNat < b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (u256 (.binary .sub x y)) = .revert := by
  simp [u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  intro hle
  omega

theorem endExecSubFunctionReturn (evm : EVM.State) {x y diff : UInt256}
    (hdiff : diff = UInt256.sub x y) (hle : y.toNat ≤ x.toNat) :
    ExecFuncBody config { contract := contract, locals := endUintBinaryLocals x y } evm
      subFunction.body
      (.returned { contract := contract, locals := endUintBinaryLocalsZ x y diff } evm
        (some [.int (Int.ofNat diff.toNat)])) := by
  let locals := endUintBinaryLocals x y
  let localsZ := endUintBinaryLocalsZ x y diff
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
      simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
        (locals := locals) (name := "x") (value := x) (endUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
      simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
        (locals := locals) (name := "y") (value := y) (endUintBinaryLocals_get_y x y)
  have hSub :
      evalExpr? config { contract := contract, locals := locals } evm
        (u256 (.binary .sub (.var "x") (.var "y"))) =
          .ok (.int (Int.ofNat diff.toNat)) :=
    endThawEvalExpr_sub256_ok hx hy hdiff hle
  have hz :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat diff.toNat)) := by
      simpa [localsZ] using endEvalExpr_varUInt256 (evm := evm)
        (locals := localsZ) (name := "z") (value := diff)
        (endUintBinaryLocalsZ_get_z x y diff)
  have hxZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
      simpa [localsZ] using endEvalExpr_varUInt256 (evm := evm)
        (locals := localsZ) (name := "x") (value := x)
        (endUintBinaryLocalsZ_get_x x y diff)
  have hdiffLe : diff.toNat ≤ x.toNat := by
    rw [hdiff, usub_toNat hle]
    omega
  have hReq :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .le (.var "z") (.var "x")) = .ok (.bool true) :=
    endThawEvalExpr_le_uint256_true hz hxZ hdiffLe
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (u256 (.binary .sub (.var "x") (.var "y"))),
          .require (.binary .le (.var "z") (.var "x")),
          .return [.var "z"] ]
        (.returned { contract := contract, locals := localsZ } evm
          (some [.int (Int.ofNat diff.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hSub) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hz))
  simpa [subFunction, locals, localsZ] using ExecFuncBody.execBlockRet hblock

theorem endExecSubFunctionRevert (evm : EVM.State) {x y : UInt256}
    (hlt : x.toNat < y.toNat) :
    ExecFuncBody config { contract := contract, locals := endUintBinaryLocals x y } evm
      subFunction.body .reverted := by
  let locals := endUintBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
      simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
        (locals := locals) (name := "x") (value := x) (endUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
      simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
        (locals := locals) (name := "y") (value := y) (endUintBinaryLocals_get_y x y)
  have hSubRev :
      evalExpr? config { contract := contract, locals := locals } evm
        (u256 (.binary .sub (.var "x") (.var "y"))) = .revert :=
    endThawEvalExpr_sub256_revert hx hy hlt
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (u256 (.binary .sub (.var "x") (.var "y"))),
          .require (.binary .le (.var "z") (.var "x")),
          .return [.var "z"] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hSubRev)
  simpa [subFunction, locals] using ExecFuncBody.execBlockRevert hblock

theorem endThawVatWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    endThawVatWord σ I = endThawVatWord τ I := by
  simp [endThawVatWord, endSlotWord, solcSlotWord,
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩]

theorem endThawVatCodeSize_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hzero : Reasoning.Theory.extCodeSizeWord σ (endThawVatWord σ I) = ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (endThawVatWord τ I) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (endThawVatWord σ I)
  have htarget : endThawVatWord σ I = endThawVatWord τ I :=
    endThawVatWord_accountMapEquiv hAccounts
  rw [← htarget, ← hsame]
  exact hzero

theorem endThawVatCodeSize_ne_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hne : Reasoning.Theory.extCodeSizeWord σ (endThawVatWord σ I) ≠ ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (endThawVatWord τ I) ≠ ⟨0⟩ := by
  intro hbad
  apply hne
  have hsame :=
    Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (endThawVatWord σ I)
  have htarget : endThawVatWord σ I = endThawVatWord τ I :=
    endThawVatWord_accountMapEquiv hAccounts
  rw [← htarget, ← hsame] at hbad
  exact hbad

theorem endThawVatAddr_eq_ofUInt256 (σ : AccountMap) (I : ExecutionEnv) :
    endThawVatAddr σ I = AccountAddress.ofUInt256 (endThawVatWord σ I) := by
  simpa [endThawVatAddr] using
    (accountAddress_ofUInt256_eq_ofNat_toNat (endThawVatWord σ I)).symm

theorem endThawVatCode_zero_of_codeSize_zero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hzero : Reasoning.Theory.extCodeSizeWord σ (endThawVatWord σ I) = ⟨0⟩) :
    (UInt256.ofNat
      (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (endThawVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  simpa [initState, State.lookupAccount] using
    endUniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := endThawVatWord σ I) (addr := endThawVatAddr σ I)
      (endThawVatAddr_eq_ofUInt256 σ I) hzero

theorem endThawVatCode_pos_of_codeSize_ne {cA gh bl σ σ₀ A I} {g : UInt256}
    (hne : Reasoning.Theory.extCodeSizeWord σ (endThawVatWord σ I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (endThawVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
  simpa [initState, State.lookupAccount] using
    endUniswapExtCodeSizeWord_ne_zero_lookup_code_pos
      (σ := σ) (target := endThawVatWord σ I) (addr := endThawVatAddr σ I)
      (endThawVatAddr_eq_ofUInt256 σ I) hne

theorem endThawCureWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    endThawCureWord σ I = endThawCureWord τ I := by
  simp [endThawCureWord, endSlotWord, solcSlotWord,
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨7⟩ ⟨0⟩]

theorem endThawCureCodeSize_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hzero : Reasoning.Theory.extCodeSizeWord σ (endThawCureWord σ I) = ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (endThawCureWord τ I) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (endThawCureWord σ I)
  have htarget : endThawCureWord σ I = endThawCureWord τ I :=
    endThawCureWord_accountMapEquiv hAccounts
  rw [← htarget, ← hsame]
  exact hzero

theorem endThawCureCodeSize_ne_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hne : Reasoning.Theory.extCodeSizeWord σ (endThawCureWord σ I) ≠ ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (endThawCureWord τ I) ≠ ⟨0⟩ := by
  intro hbad
  apply hne
  have hsame :=
    Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (endThawCureWord σ I)
  have htarget : endThawCureWord σ I = endThawCureWord τ I :=
    endThawCureWord_accountMapEquiv hAccounts
  rw [← htarget, ← hsame] at hbad
  exact hbad

theorem endThawCureAddr_eq_ofUInt256 (σ : AccountMap) (I : ExecutionEnv) :
    endThawCureAddr σ I = AccountAddress.ofUInt256 (endThawCureWord σ I) := by
  simpa [endThawCureAddr] using
    (accountAddress_ofUInt256_eq_ofNat_toNat (endThawCureWord σ I)).symm

theorem endDecode_thaw {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (thawTransition.params.map Param.name)
      (transitionSignature thawTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem endReachThawBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endThawConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endThawEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x5920375c⟩ :=
    endSelWord_eq_of_beq I hsz 0x59 0x20 0x37 0x5c ⟨0x5920375c⟩
      (by decide +native)
      (by simpa [selIs, endThawConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachGroup403FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; decide +native)
      (by rw [hword]; decide +native)
      (by rw [hword]; decide +native)
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup403FirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide +native
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup403FirstArmPc 3))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact RD.dispatchTo endThawEntryPc 3 hfirst
    (fun j hj => endGroup403ArmsWellFormed j (by omega))
    heq0 htake (by jump_dest) (by decide +native) (by simp)

theorem endThawX_entry {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endThawEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endThawBodyPc [endThawReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  simpa [endThawEntryPc, endThawReturnPc, endThawBodyPc] using
    RD.solcGetterThunk (code := endBytecode) (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
      (entry := endThawEntryPc) (returnPc := endThawReturnPc) (routine := endThawBodyPc)
      hreach
      (by
        unfold solcGetterEntryWf
        repeat' first | apply And.intro | decide +native)
      (by jump_dest)

theorem endThawX_liveNonzero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hlive : endThawLiveWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endThawBodyPc
      [endThawReturnPc, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd4528 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨8⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd4529raw⟩ := rd4528.sload (by decide +native) (by evm_ov)
  have rd4529 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4529⟩
        (endThawLiveWord σ I :: endThawReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endThawLiveWord, endSlotWord, solcSlotWord] using rd4529raw⟩
  obtain ⟨_, _, rd4529⟩ := rd4529
  have rd4530raw := rd4529.iszero (by decide +native) (by evm_ov)
  have hzero : UInt256.isZero (endThawLiveWord σ I) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hlive
  have rd4530 := rd4530raw
  rw [hzero] at rd4530
  have rd4533 := rd4530.push2 ⟨4595⟩ (by decide +native) (by evm_ov)
  have rd4534 := rd4533.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨4534⟩) (len := ⟨14⟩)
    (rawWord := ⟨0x456e642f7374696c6c2d6c697665⟩) (shift := ⟨144⟩)
    (word := UInt256.shiftLeft ⟨0x456e642f7374696c6c2d6c697665⟩ ⟨144⟩)
    (op := .PUSH14) (width := 14)
    (by simpa using rd4534)
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | decide +native)
    (by decide) rfl
    solcFreePtrMem_size solcFreePtrMem_read64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endThawX_debtNonzero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hlive : endThawLiveWord σ I = ⟨0⟩)
    (hdebt : endThawDebtWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endThawBodyPc
      [endThawReturnPc, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd4528 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨8⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd4529raw⟩ := rd4528.sload (by decide +native) (by evm_ov)
  have hliveRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨8⟩ ⟨0⟩)) =
        ⟨0⟩ := by
      simpa [endThawLiveWord, endSlotWord, solcSlotWord] using hlive
  have rd4529zero := rd4529raw
  rw [hliveRaw] at rd4529zero
  obtain ⟨_, _, rd4529⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4529⟩
        (⟨0⟩ :: endThawReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endThawBodyPc] using rd4529zero⟩
  have rd4530raw := rd4529.iszero (by decide +native) (by evm_ov)
  have rd4530 := rd4530raw
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4530
  have rd4533 := rd4530.push2 ⟨4595⟩ (by decide +native) (by evm_ov)
  have rd4595 := rd4533.jumpiT (by decide +native)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have rd4598 := evm_run rd4595 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨11⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd4599raw⟩ := rd4598.sload (by decide +native) (by evm_ov)
  have rd4599 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4599⟩
        (endThawDebtWord σ I :: endThawReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endThawDebtWord, endSlotWord, solcSlotWord] using rd4599raw⟩
  obtain ⟨_, _, rd4599⟩ := rd4599
  have rd4600raw := rd4599.iszero (by decide +native) (by evm_ov)
  have hzero : UInt256.isZero (endThawDebtWord σ I) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hdebt
  have rd4600 := rd4600raw
  rw [hzero] at rd4600
  have rd4603 := rd4600.push2 ⟨4668⟩ (by decide +native) (by evm_ov)
  have rd4604 := rd4603.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨4604⟩) (len := ⟨17⟩)
    (rawWord := ⟨0x456e642f646562742d6e6f742d7a65726f⟩) (shift := ⟨120⟩)
    (word := UInt256.shiftLeft ⟨0x456e642f646562742d6e6f742d7a65726f⟩ ⟨120⟩)
    (op := .PUSH17) (width := 17)
    (by simpa using rd4604)
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | decide +native)
    (by decide) rfl
    solcFreePtrMem_size solcFreePtrMem_read64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endThawX_daiExtcodesizeGuard {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (hlive : endThawLiveWord σ I = ⟨0⟩)
    (hdebt : endThawDebtWord σ I = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endThawBodyPc
      [endThawReturnPc, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4737⟩
      (endThawVatWord σ I :: endThawVatWord σ I :: endThawDaiOutPtr ::
        endThawDaiInSize :: endThawDaiOutPtr :: endThawDaiOutSize ::
        endThawDaiEndPtr :: endThawDaiSelectorWord :: endThawVatWord σ I ::
        endThawReturnPc :: sel :: [])
      (endThawDaiCalldataMem σ I solcFreePtrMem) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k' C' := by
  have rd4528 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨8⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd4529raw⟩ := rd4528.sload (by decide +native) (by evm_ov)
  have hliveRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨8⟩ ⟨0⟩)) =
        ⟨0⟩ := by
      simpa [endThawLiveWord, endSlotWord, solcSlotWord] using hlive
  have rd4529zero := rd4529raw
  rw [hliveRaw] at rd4529zero
  obtain ⟨_, _, rd4529⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4529⟩
        (⟨0⟩ :: endThawReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endThawBodyPc] using rd4529zero⟩
  have rd4530raw := rd4529.iszero (by decide +native) (by evm_ov)
  have rd4530 := rd4530raw
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4530
  have rd4533 := rd4530.push2 ⟨4595⟩ (by decide +native) (by evm_ov)
  have rd4595 := rd4533.jumpiT (by decide +native)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have rd4598 := evm_run rd4595 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨11⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd4599raw⟩ := rd4598.sload (by decide +native) (by evm_ov)
  have hdebtRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨11⟩ ⟨0⟩)) =
        ⟨0⟩ := by
      simpa [endThawDebtWord, endSlotWord, solcSlotWord] using hdebt
  have rd4599zero := rd4599raw
  rw [hdebtRaw] at rd4599zero
  obtain ⟨_, _, rd4599⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4599⟩
        (⟨0⟩ :: endThawReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa using rd4599zero⟩
  have rd4600raw := rd4599.iszero (by decide +native) (by evm_ov)
  have rd4600 := rd4600raw
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4600
  have rd4603 := rd4600.push2 ⟨4668⟩ (by decide +native) (by evm_ov)
  have rd4668 := rd4603.jumpiT (by decide +native)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have rd4670 := evm_run rd4668 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd4671raw⟩ := rd4670.sload (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd4672⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4672⟩
        (endSlotWord ⟨1⟩ σ I :: endThawReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd4671raw⟩
  have rd4675pre := evm_run rd4672 with [
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd4675raw⟩ := rd4675pre.sload (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd4676⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4676⟩
        (endSlotWord ⟨4⟩ σ I :: ⟨4⟩ :: endSlotWord ⟨1⟩ σ I ::
          endThawReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd4675raw⟩
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ solcFreePtrMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            (solcFreePtrMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [solcFreePtrMem_size]; decide) (by decide) solcFreePtrMem_read64
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (endThawDaiCalldataMem σ I solcFreePtrMem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endThawDaiCalldataMem σ I solcFreePtrMem).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue
      (by rw [endThawDaiCalldataMem_size σ I solcFreePtrMem_size]; decide)
      (by decide)
      (endThawDaiCalldataMem_read64 σ I solcFreePtrMem_size solcFreePtrMem_read64)
  have hvatMask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (endSlotWord ⟨1⟩ σ I) = endThawVatWord σ I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide +native]
  have hvowMask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (endSlotWord ⟨4⟩ σ I) = endThawVowWord σ I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide +native]
  have rd4737pre := evm_run rd4676 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push4 endThawDaiSelectorRaw (by decide +native) (by evm_ov),
    raw push1 ⟨225⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 6 (endThawDaiSelectorMem solcFreePtrMem) (UInt256.ofNat 5)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw mstore 3 (endThawDaiCalldataMem σ I solcFreePtrMem) (UInt256.ofNat 6)
      (by decide +native) mem_cost
      (by
        rw [hvowMask]
        rfl)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push4 endThawDaiSelectorWord (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push1 ⟨36⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  have hinSize :
      UInt256.sub endThawDaiOutPtr endThawDaiOutPtr + endThawDaiInSize =
        endThawDaiInSize := by
    decide +native
  have hendPtr : endThawDaiOutPtr + endThawDaiInSize = endThawDaiEndPtr := by
    decide +native
  exact ⟨_, _, by
    simpa [endThawDaiSelectorMem, endThawDaiCalldataMem, endThawDaiOutPtr,
      endThawDaiInSize, endThawDaiOutSize, endThawDaiEndPtr, endThawDaiSelectorWord,
      endThawDaiSelectorRaw, endThawVatWord, endThawVowWord, endSlotWord, solcSlotWord,
      solcAddrMask, hvatMask, hvowMask, u256_land_comm, hinSize, hendPtr] using rd4737pre⟩

theorem endThawX_daiCallReady {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (hlive : endThawLiveWord σ I = ⟨0⟩)
    (hdebt : endThawDebtWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endThawVatWord σ I) ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endThawBodyPc
      [endThawReturnPc, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4752⟩
      (gasWord :: endThawVatWord σ I :: endThawDaiOutPtr ::
        endThawDaiInSize :: endThawDaiOutPtr :: endThawDaiOutSize ::
        endThawDaiEndPtr :: endThawDaiSelectorWord :: endThawVatWord σ I ::
        endThawReturnPc :: sel :: [])
      (endThawDaiCalldataMem σ I solcFreePtrMem) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd4737⟩ := endThawX_daiExtcodesizeGuard hlive hdebt h
  obtain ⟨gasWord, k', C', rd4752⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨4737⟩) (okPc := ⟨4749⟩) rd4737
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨gasWord, k', C', by simpa using rd4752⟩

theorem endThawX_daiPostStaticcall {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel gasWord : UInt256} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4752⟩
      (gasWord :: endThawVatWord σ I :: endThawDaiOutPtr ::
        endThawDaiInSize :: endThawDaiOutPtr :: endThawDaiOutSize ::
        endThawDaiEndPtr :: endThawDaiSelectorWord :: endThawVatWord σ I ::
        endThawReturnPc :: sel :: [])
      (endThawDaiCalldataMem σ I solcFreePtrMem) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl σ σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endThawVatWord σ I))
          (toExecute σ (AccountAddress.ofUInt256 (endThawVatWord σ I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endThawDaiCalldataMem σ I solcFreePtrMem).readWithPadding
            endThawDaiOutPtr.toNat endThawDaiInSize.toNat)
          (I.depth + 1) I.header false)
      ∧ RD endBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4753⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endThawDaiEndPtr ::
            endThawDaiSelectorWord :: endThawVatWord σ I :: endThawReturnPc :: sel :: [])
          (endThawDaiPostCallMem σ I out) (UInt256.ofNat 6) out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA', σ', z, out, Ain, callGas, k', C', hΘ, rd4753raw, hout⟩ :=
    RD.solcStaticcall h (by decide +native) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨cA', σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          endThawDaiOutPtr.toNat endThawDaiInSize.toNat)
          endThawDaiOutPtr.toNat endThawDaiOutSize.toNat) = UInt256.ofNat 6 := by
      unfold endThawDaiOutPtr endThawDaiInSize endThawDaiOutSize
      decide +native
    simpa [endThawDaiPostCallMem, endThawDaiOutPtr, endThawDaiInSize,
      endThawDaiOutSize, endThawDaiEndPtr, haw] using rd4753raw

theorem endThawX_daiStaticcallDepthLimit {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel gasWord : UInt256} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4752⟩
      (gasWord :: endThawVatWord σ I :: endThawDaiOutPtr ::
        endThawDaiInSize :: endThawDaiOutPtr :: endThawDaiOutSize ::
        endThawDaiEndPtr :: endThawDaiSelectorWord :: endThawVatWord σ I ::
        endThawReturnPc :: sel :: [])
      (endThawDaiCalldataMem σ I solcFreePtrMem) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4753⟩
      (⟨0⟩ :: endThawDaiEndPtr :: endThawDaiSelectorWord :: endThawVatWord σ I ::
        endThawReturnPc :: sel :: [])
      (endThawDaiCalldataMem σ I solcFreePtrMem) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', C', rd4753raw⟩ :=
    RD.solcStaticcallDepthLimit h (by decide +native) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endThawDaiOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    unfold endThawDaiOutSize
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        endThawDaiOutPtr.toNat endThawDaiInSize.toNat)
        endThawDaiOutPtr.toNat endThawDaiOutSize.toNat) = UInt256.ofNat 6 := by
    unfold endThawDaiOutPtr endThawDaiInSize endThawDaiOutSize
    decide +native
  simpa [endThawDaiOutPtr, endThawDaiInSize, endThawDaiOutSize,
    endThawDaiEndPtr, hmin, byteArray_write_len_zero, haw] using rd4753raw

theorem endThawX_daiCallFailed {cA cA' gh bl σ σ' σ₀ A I} {g sel : UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4753⟩
      (⟨0⟩ :: endThawDaiEndPtr :: endThawDaiSelectorWord :: endThawVatWord σ I ::
        endThawReturnPc :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨4753⟩) (okPc := ⟨4769⟩) h
    rfl
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endThawX_daiCallSucceeded {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4753⟩
      (⟨1⟩ :: endThawDaiEndPtr :: endThawDaiSelectorWord :: endThawVatWord σ I ::
        endThawReturnPc :: sel :: [])
      mem (UInt256.ofNat 6) rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4771⟩
      (endThawDaiEndPtr :: endThawDaiSelectorWord :: endThawVatWord σ I ::
        endThawReturnPc :: sel :: [])
      mem (UInt256.ofNat 6) rdata acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨4753⟩) (okPc := ⟨4769⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endThawX_daiReturnDecodeOk {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4771⟩
      (endThawDaiEndPtr :: endThawDaiSelectorWord :: endThawVatWord σ I ::
        endThawReturnPc :: sel :: [])
      (endThawDaiPostCallMem σ I out) (UInt256.ofNat 6) out (cA', σ') k C)
    (hlo : 32 ≤ out.size) (hout : out.size < UInt256.size) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4794⟩
      (endThawDaiWord out :: endThawReturnPc :: sel :: [])
      (endThawDaiPostCallMem σ I out) (UInt256.ofNat 6) out (cA', σ') k' C' := by
  have hmload64 := endThawDaiPostCallMem_mload64 σ I out hout
  have hmload128 := endThawDaiPostCallMem_mload128 σ I out hout hlo
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' out.size hout]
    exact hlo
  have rd4786 := evm_run h with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨4791⟩ (by decide +native) (by evm_ov)]
  have rdJump := rd4786
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rdJump
  have rd4794 := evm_run rdJump with [
    raw jumpiT (by decide +native) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov),
    raw jumpdest (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw mload 0 (endThawDaiWord out) (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload128 (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endThawDaiEndPtr, endThawDaiSelectorWord, endThawDaiOutPtr,
      endThawDaiInSize, endThawDaiOutSize] using rd4794⟩

theorem endThawX_daiReturnDecodeShort {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4771⟩
      (endThawDaiEndPtr :: endThawDaiSelectorWord :: endThawVatWord σ I ::
        endThawReturnPc :: sel :: [])
      (endThawDaiPostCallMem σ I out) (UInt256.ofNat 6) out (cA', σ') k C)
    (hshort : out.size < 32) (hout : out.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmload64 := endThawDaiPostCallMem_mload64 σ I out hout
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' out.size hout]
    exact hshort
  have rd4786 := evm_run h with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨4791⟩ (by decide +native) (by evm_ov)]
  have rdShort := rd4786
  rw [hlt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rdShort
  have rdFall := rdShort.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFall
    (by decide +native) (by decide +native) (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endThawX_daiZeroDeadlineEntry {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (hdai : endThawDaiWord out = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4794⟩
      (endThawDaiWord out :: endThawReturnPc :: sel :: [])
      (endThawDaiPostCallMem σ I out) (UInt256.ofNat 6) out (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4866⟩
      (endThawReturnPc :: sel :: [])
      (endThawDaiPostCallMem σ I out) (UInt256.ofNat 6) out (cA', σ') k' C' := by
  have rd4795raw := h.iszero (by decide +native) (by evm_ov)
  have rd4795 := rd4795raw
  rw [hdai, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4795
  have rd4798 := rd4795.push2 ⟨4866⟩ (by decide +native) (by evm_ov)
  have rd4866 := rd4798.jumpiT (by decide +native)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa using rd4866⟩

theorem endThawX_deadlineAddEntry {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4866⟩
      (endThawReturnPc :: sel :: []) mem (UInt256.ofNat 6) out (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10092⟩
      [endThawWaitWord σ' I, endThawWhenWord σ' I, ⟨4880⟩, endThawReturnPc, sel]
      mem (UInt256.ofNat 6) out (cA', σ') k' C' := by
  have rd4872 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push2 ⟨4880⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨9⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd4873raw⟩ := rd4872.sload (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd4873⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4873⟩
        (endThawWhenWord σ' I :: ⟨4880⟩ :: endThawReturnPc :: sel :: [])
        mem (UInt256.ofNat 6) out (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endThawWhenWord, endSlotWord, solcSlotWord] using rd4873raw⟩
  have rd4875 := evm_run rd4873 with [
    raw push1 ⟨10⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd4876raw⟩ := rd4875.sload (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd4876⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4876⟩
        (endThawWaitWord σ' I :: endThawWhenWord σ' I :: ⟨4880⟩ ::
          endThawReturnPc :: sel :: [])
        mem (UInt256.ofNat 6) out (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endThawWaitWord, endSlotWord, solcSlotWord] using rd4876raw⟩
  have rd4879 := evm_run rd4876 with [
    raw push2 ⟨10092⟩ (by decide +native) (by evm_ov)]
  exact ⟨_, _, rd4879.jump (by decide +native) (by jump_dest) (by evm_ov)⟩

theorem endThawX_deadlineAddOverflow {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem out : ByteArray} {k C : ℕ}
    (hover :
      UInt256.size ≤ (endThawWhenWord σ' I).toNat + (endThawWaitWord σ' I).toNat)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10092⟩
      [endThawWaitWord σ' I, endThawWhenWord σ' I, ⟨4880⟩, endThawReturnPc, sel]
      mem (UInt256.ofNat 6) out (cA', σ') k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let whenWord := endThawWhenWord σ' I
  let waitWord := endThawWaitWord σ' I
  have hover' : UInt256.size ≤ waitWord.toNat + whenWord.toNat := by
    dsimp [whenWord, waitWord]
    simpa [Nat.add_comm] using hover
  have hsum_lt2 : waitWord.toNat + whenWord.toNat < 2 * UInt256.size := by
    have hwhen : whenWord.toNat < UInt256.size := whenWord.val.isLt
    have hwait : waitWord.toNat < UInt256.size := waitWord.val.isLt
    omega
  have hmod : (waitWord.toNat + whenWord.toNat) % UInt256.size =
      waitWord.toNat + whenWord.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover']
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat : (waitWord + whenWord).toNat =
      waitWord.toNat + whenWord.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt : UInt256.lt (waitWord + whenWord) whenWord = ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hwaitLt : waitWord.toNat < UInt256.size := waitWord.val.isLt
    omega
  have rd10099pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd10099 := evm_run rd10099pre with [raw lt (by decide +native) (by evm_ov)]
  have rd10099' := by
    simpa [whenWord, waitWord] using rd10099
  rw [hlt] at rd10099'
  have rd10100pre := evm_run rd10099' with [raw iszero (by decide +native) (by evm_ov)]
  have rd10100 := by
    simpa using rd10100pre
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd10100
  have rd10104pre := evm_run rd10100 with [raw push2 ⟨10108⟩ (by decide +native) (by evm_ov)]
  have rd10104 := rd10104pre.jumpiNT (by decide +native) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.solcPush1Dup1Revert0 rd10104 (by decide +native) (by decide +native)
    (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endThawX_deadlineAddSuccess {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem out : ByteArray} {k C : ℕ}
    (hfit :
      (endThawWhenWord σ' I).toNat + (endThawWaitWord σ' I).toNat < UInt256.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10092⟩
      [endThawWaitWord σ' I, endThawWhenWord σ' I, ⟨4880⟩, endThawReturnPc, sel]
      mem (UInt256.ofNat 6) out (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4880⟩
      (endThawDeadlineWord σ' I :: endThawReturnPc :: sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k' C' := by
  let whenWord := endThawWhenWord σ' I
  let waitWord := endThawWaitWord σ' I
  have hfit' : waitWord.toNat + whenWord.toNat < UInt256.size := by
    dsimp [whenWord, waitWord]
    simpa [Nat.add_comm] using hfit
  have haddNat : (waitWord + whenWord).toNat = waitWord.toNat + whenWord.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hfit']
  have hlt : UInt256.lt (waitWord + whenWord) whenWord = ⟨0⟩ :=
    ult_zero (by rw [haddNat]; omega)
  have rd10099pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd10099 := evm_run rd10099pre with [raw lt (by decide +native) (by evm_ov)]
  have rd10099' := by
    simpa [whenWord, waitWord] using rd10099
  rw [hlt] at rd10099'
  have rd10100pre := evm_run rd10099' with [raw iszero (by decide +native) (by evm_ov)]
  have rd10100 := by
    simpa using rd10100pre
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd10100
  have rd10108pre := evm_run rd10100 with [
    raw push2 ⟨10108⟩ (by decide +native) (by evm_ov),
    raw jumpiT (by decide +native) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  have rd4880 := evm_run rd10108pre with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw jump (by decide +native) (by jump_dest) (by evm_ov)]
  have hcomm : waitWord + whenWord = whenWord + waitWord :=
    u256_add_comm waitWord whenWord
  exact ⟨_, _, by
    simpa [endThawDeadlineWord, whenWord, waitWord, hcomm] using rd4880⟩

set_option maxHeartbeats 1000000 in
theorem endThaw_solcErrorStringRevertTail_aw6_size164 {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {pc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 6) rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) hd3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 6)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 7) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst rawWord (width := width) (op := op)
    hpush hd27 (by simp only [List.length_cons]; omega)
  have rdWord := evm_run rdRaw with [
    raw push1 shift hdRawOut (by evm_ov),
    raw shl hdShl (by evm_ov)]
  rw [hword] at rdWord
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 len word mem)
      (UInt256.ofNat 8) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hdMload
      mem_cost
      (solcErrorStringMem3_mload64_of_size164 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

theorem endThawX_daiNonzero {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (hdai : endThawDaiWord out ≠ ⟨0⟩)
    (hout : out.size < UInt256.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4794⟩
      (endThawDaiWord out :: endThawReturnPc :: sel :: [])
      (endThawDaiPostCallMem σ I out) (UInt256.ofNat 6) out (cA', σ') k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmem := endThawDaiPostCallMem_size σ I out hout
  have hread64 := endThawDaiPostCallMem_read64 σ I out hout
  have rd4795raw := h.iszero (by decide +native) (by evm_ov)
  have hzero : UInt256.isZero (endThawDaiWord out) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hdai
  have rd4795 := rd4795raw
  rw [hzero] at rd4795
  have rd4798 := rd4795.push2 ⟨4866⟩ (by decide +native) (by evm_ov)
  have rd4799 := rd4798.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact endThaw_solcErrorStringRevertTail_aw6_size164
    (pc := ⟨4799⟩) (len := ⟨20⟩)
    (rawWord := ⟨396382172534018756375957589142925699600051696239⟩)
    (shift := ⟨96⟩)
    (word := UInt256.shiftLeft ⟨396382172534018756375957589142925699600051696239⟩ ⟨96⟩)
    (op := .PUSH20) (width := 20)
    (by simpa using rd4799)
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | decide +native)
    (by decide) rfl hmem hread64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endThawX_deadlineNotFinished {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem out : ByteArray} {k C : ℕ}
    (hwait : (endThawTimestampWord I).toNat < (endThawDeadlineWord σ' I).toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4880⟩
      (endThawDeadlineWord σ' I :: endThawReturnPc :: sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt : UInt256.lt (endThawTimestampWord I) (endThawDeadlineWord σ' I) = ⟨1⟩ :=
    ult_one hwait
  have rd4887 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw timestamp (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨4956⟩ (by decide +native) (by evm_ov)]
  have rdWait := rd4887
  rw [hlt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rdWait
  have rd4888 := rdWait.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact endThaw_solcErrorStringRevertTail_aw6_size164
    (pc := ⟨4888⟩) (len := ⟨21⟩)
    (rawWord := ⟨25368459042510824971369391205765018885210945231193⟩)
    (shift := ⟨90⟩)
    (word :=
      UInt256.shiftLeft ⟨25368459042510824971369391205765018885210945231193⟩ ⟨90⟩)
    (op := .PUSH21) (width := 21)
    (by simpa using rd4888)
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | decide +native)
    (by decide) rfl hmem hread64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endThawX_deadlineReady {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem out : ByteArray} {k C : ℕ}
    (hready : (endThawDeadlineWord σ' I).toNat ≤ (endThawTimestampWord I).toNat)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4880⟩
      (endThawDeadlineWord σ' I :: endThawReturnPc :: sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4956⟩
      (endThawReturnPc :: sel :: []) mem (UInt256.ofNat 6) out (cA', σ') k' C' := by
  have hlt : UInt256.lt (endThawTimestampWord I) (endThawDeadlineWord σ' I) = ⟨0⟩ :=
    ult_zero hready
  have rd4887 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw timestamp (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨4956⟩ (by decide +native) (by evm_ov)]
  have rdReady := rd4887
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rdReady
  exact ⟨_, _, rdReady.jumpiT (by decide +native)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)⟩

theorem endThawX_debtCallReady {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem out : ByteArray} {k C : ℕ}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (endThawVatWord σ' I) ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4956⟩
      [endThawReturnPc, sel] mem (UInt256.ofNat 6) out (cA', σ') k C) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5031⟩
      (gasWord :: endThawVatWord σ' I :: ⟨0⟩ :: endThawNoArgOutPtr ::
        endThawNoArgInSize :: endThawNoArgOutPtr :: endThawNoArgOutSize ::
        endThawNoArgEndPtr :: endThawDebtSelectorWord :: endThawVatWord σ' I ::
        ⟨5190⟩ :: endThawReturnPc :: sel :: [])
      (endThawNoArgCalldataMem endThawDebtSelectorWord mem) (UInt256.ofNat 6)
      out (cA', σ') k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endThawNoArgCalldataMem endThawDebtSelectorWord mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endThawNoArgCalldataMem endThawDebtSelectorWord mem).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue
      (by rw [endThawNoArgCalldataMem_size hmem]; decide)
      (by decide)
      (endThawNoArgCalldataMem_read64 hmem hread64)
  have hvatMask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (endSlotWord ⟨1⟩ σ' I) = endThawVatWord σ' I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide +native]
  have rd4959 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd4960raw⟩ := rd4959.sload (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd4960⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4960⟩
        (endSlotWord ⟨1⟩ σ' I :: endThawReturnPc :: sel :: [])
        mem (UInt256.ofNat 6) out (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd4960raw⟩
  have rd5016pre := evm_run rd4960 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push4 endThawDebtSelectorWord (by decide +native) (by evm_ov),
    raw push1 ⟨224⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (endThawNoArgCalldataMem endThawDebtSelectorWord mem) (UInt256.ofNat 6)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push2 ⟨5190⟩ (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push4 endThawDebtSelectorWord (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  have hinSize :
      UInt256.sub endThawNoArgOutPtr endThawNoArgOutPtr + endThawNoArgInSize =
        endThawNoArgInSize := by
    decide +native
  have hendPtr : endThawNoArgOutPtr + endThawNoArgInSize = endThawNoArgEndPtr := by
    decide +native
  have rd5016 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5016⟩
        (endThawVatWord σ' I :: endThawVatWord σ' I :: ⟨0⟩ ::
          endThawNoArgOutPtr :: endThawNoArgInSize :: endThawNoArgOutPtr ::
          endThawNoArgOutSize :: endThawNoArgEndPtr :: endThawDebtSelectorWord ::
          endThawVatWord σ' I :: ⟨5190⟩ :: endThawReturnPc :: sel :: [])
        (endThawNoArgCalldataMem endThawDebtSelectorWord mem) (UInt256.ofNat 6)
        out (cA', σ') k' C' := by
    exact ⟨_, _, by
      have rd5016norm := rd5016pre
      rw [hvatMask] at rd5016norm
      convert rd5016norm using 1⟩
  rcases rd5016 with ⟨_, _, rd5016ok⟩
  obtain ⟨gasWord, k', C', rd5031⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨5016⟩) (okPc := ⟨5028⟩) rd5016ok
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨gasWord, k', C', by simpa using rd5031⟩

theorem endThawX_debtNoCode {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem out : ByteArray} {k C : ℕ}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (endThawVatWord σ' I) = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4956⟩
      [endThawReturnPc, sel] mem (UInt256.ofNat 6) out (cA', σ') k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endThawNoArgCalldataMem endThawDebtSelectorWord mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endThawNoArgCalldataMem endThawDebtSelectorWord mem).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue
      (by rw [endThawNoArgCalldataMem_size hmem]; decide)
      (by decide)
      (endThawNoArgCalldataMem_read64 hmem hread64)
  have hvatMask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (endSlotWord ⟨1⟩ σ' I) = endThawVatWord σ' I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide +native]
  have rd4959 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd4960raw⟩ := rd4959.sload (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd4960⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4960⟩
        (endSlotWord ⟨1⟩ σ' I :: endThawReturnPc :: sel :: [])
        mem (UInt256.ofNat 6) out (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd4960raw⟩
  have rd5016pre := evm_run rd4960 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push4 endThawDebtSelectorWord (by decide +native) (by evm_ov),
    raw push1 ⟨224⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (endThawNoArgCalldataMem endThawDebtSelectorWord mem) (UInt256.ofNat 6)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push2 ⟨5190⟩ (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push4 endThawDebtSelectorWord (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  have rd5016 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5016⟩
        (endThawVatWord σ' I :: endThawVatWord σ' I :: ⟨0⟩ ::
          endThawNoArgOutPtr :: endThawNoArgInSize :: endThawNoArgOutPtr ::
          endThawNoArgOutSize :: endThawNoArgEndPtr :: endThawDebtSelectorWord ::
          endThawVatWord σ' I :: ⟨5190⟩ :: endThawReturnPc :: sel :: [])
        (endThawNoArgCalldataMem endThawDebtSelectorWord mem) (UInt256.ofNat 6)
        out (cA', σ') k' C' := by
    exact ⟨_, _, by
      have rd5016norm := rd5016pre
      rw [hvatMask] at rd5016norm
      convert rd5016norm using 1⟩
  rcases rd5016 with ⟨_, _, rd5016zero⟩
  exact RD.solcExtcodesizeGuardMissing (okPc := ⟨5028⟩) rd5016zero
    hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endThawX_debtPostCall {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel gasWord : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5031⟩
      (gasWord :: endThawVatWord σ' I :: ⟨0⟩ :: endThawNoArgOutPtr ::
        endThawNoArgInSize :: endThawNoArgOutPtr :: endThawNoArgOutSize ::
        endThawNoArgEndPtr :: endThawDebtSelectorWord :: endThawVatWord σ' I ::
        ⟨5190⟩ :: endThawReturnPc :: sel :: [])
      (endThawNoArgCalldataMem endThawDebtSelectorWord mem) (UInt256.ofNat 6)
      rdata (cA', σ') k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
      (z : Bool) (debtOut : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', z, debtOut) = Ethereum.EVM.Θ I.blobVersionedHashes cA'
          gh bl σ' σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endThawVatWord σ' I))
          (toExecute σ' (AccountAddress.ofUInt256 (endThawVatWord σ' I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endThawNoArgCalldataMem endThawDebtSelectorWord mem).readWithPadding
            endThawNoArgOutPtr.toNat endThawNoArgInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5032⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endThawNoArgEndPtr ::
            endThawDebtSelectorWord :: endThawVatWord σ' I :: ⟨5190⟩ ::
            endThawReturnPc :: sel :: [])
          (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut)
          (UInt256.ofNat 6) debtOut (cA'', σ'') k' C'
      ∧ debtOut.size < UInt256.size := by
  obtain ⟨cA'', σ'', z, debtOut, Ain, callGas, k', C', hΘ, rd5032raw, hout⟩ :=
    RD.call h (by decide +native) hdepth (by evm_ov)
  refine ⟨cA'', σ'', z, debtOut, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have hmin := endThawNoArgWriteLen_eq (out := debtOut) hout
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          endThawNoArgOutPtr.toNat endThawNoArgInSize.toNat)
          endThawNoArgOutPtr.toNat endThawNoArgOutSize.toNat) = UInt256.ofNat 6 := by
      unfold endThawNoArgOutPtr endThawNoArgInSize endThawNoArgOutSize
      decide +native
    simpa [endThawNoArgPostCallMem, endThawNoArgOutPtr, endThawNoArgInSize,
      endThawNoArgOutSize, endThawNoArgEndPtr, hmin, haw] using rd5032raw

theorem endThawX_debtCallFailed {cA cA' gh bl σ σTarget σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5032⟩
      (⟨0⟩ :: endThawNoArgEndPtr :: endThawDebtSelectorWord ::
        endThawVatWord σTarget I :: ⟨5190⟩ :: endThawReturnPc :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨5032⟩) (okPc := ⟨5048⟩) h
    rfl
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endThawX_debtCallSucceeded {cA cA' gh bl σ σTarget σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5032⟩
      (⟨1⟩ :: endThawNoArgEndPtr :: endThawDebtSelectorWord ::
        endThawVatWord σTarget I :: ⟨5190⟩ :: endThawReturnPc :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5050⟩
      (endThawNoArgEndPtr :: endThawDebtSelectorWord :: endThawVatWord σTarget I ::
        ⟨5190⟩ :: endThawReturnPc :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA', σ') k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨5032⟩) (okPc := ⟨5048⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
    (by evm_ov)

theorem endThawX_debtReturnDecodeOk {cA cA' gh bl σ σTarget σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem debtOut : ByteArray} {k C : ℕ}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5050⟩
      (endThawNoArgEndPtr :: endThawDebtSelectorWord :: endThawVatWord σTarget I ::
        ⟨5190⟩ :: endThawReturnPc :: sel :: [])
      (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut) (UInt256.ofNat 6)
      debtOut (cA', σ') k C)
    (hlo : 32 ≤ debtOut.size) (hout : debtOut.size < UInt256.size) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5073⟩
      (endThawReturnWord debtOut :: ⟨5190⟩ :: endThawReturnPc :: sel :: [])
      (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut) (UInt256.ofNat 6)
      debtOut (cA', σ') k' C' := by
  exact RD.solcUint256ReturnWordDecodeOk (pc := ⟨5050⟩) (okPc := ⟨5070⟩)
    (retWord := endThawReturnWord debtOut) h hlo hout
    mem_cost
    (by decide +native)
    (endThawNoArgPostCallMem_mload64 hmem hread64 hout)
    (endThawNoArgPostCallMem_mload128 hmem hout hlo)
    mem_cost
    (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest)
    (by decide +native) (by decide +native) (by decide +native)
    (by evm_ov)

theorem endThawX_debtReturnDecodeShort {cA cA' gh bl σ σTarget σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem debtOut : ByteArray} {k C : ℕ}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5050⟩
      (endThawNoArgEndPtr :: endThawDebtSelectorWord :: endThawVatWord σTarget I ::
        ⟨5190⟩ :: endThawReturnPc :: sel :: [])
      (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut) (UInt256.ofNat 6)
      debtOut (cA', σ') k C)
    (hshort : debtOut.size < 32) (hout : debtOut.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨5050⟩) (okPc := ⟨5070⟩)
    h hshort hout
    mem_cost
    (by decide +native)
    (endThawNoArgPostCallMem_mload64 hmem hread64 hout)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native)
    (by evm_ov)

theorem endThawX_tellCallReady {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem debtOut rdata : ByteArray} {k C : ℕ}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hdebtOut : debtOut.size < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (endThawCureWord σ' I) ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5073⟩
      (endThawReturnWord debtOut :: ⟨5190⟩ :: endThawReturnPc :: sel :: [])
      (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut) (UInt256.ofNat 6)
      rdata (cA', σ') k C) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5144⟩
      (gasWord :: endThawCureWord σ' I :: endThawNoArgOutPtr ::
        endThawNoArgInSize :: endThawNoArgOutPtr :: endThawNoArgOutSize ::
        endThawNoArgEndPtr :: endThawTellSelectorWord :: endThawCureWord σ' I ::
        endThawReturnWord debtOut :: ⟨5190⟩ :: endThawReturnPc :: sel :: [])
      (endThawNoArgCalldataMem endThawTellSelectorWord
        (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut))
      (UInt256.ofNat 6) rdata (cA', σ') k' C' := by
  have hpostSize :
      (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut).size = 164 :=
    endThawNoArgPostCallMem_size hmem hdebtOut
  have hpostRead64 :
      (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut).readWithPadding
          64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    endThawNoArgPostCallMem_read64 hmem hread64 hdebtOut
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    endThawNoArgPostCallMem_mload64 hmem hread64 hdebtOut
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endThawNoArgCalldataMem endThawTellSelectorWord
              (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endThawNoArgCalldataMem endThawTellSelectorWord
                (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut)).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue
      (by rw [endThawNoArgCalldataMem_size hpostSize]; decide)
      (by decide)
      (endThawNoArgCalldataMem_read64 hpostSize hpostRead64)
  have hcureMask :
      UInt256.land (endSlotWord ⟨7⟩ σ' I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        endThawCureWord σ' I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide +native]
  have rd5075 := evm_run h with [
    raw push1 ⟨7⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd5076raw⟩ := rd5075.sload (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd5076⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5076⟩
        (endSlotWord ⟨7⟩ σ' I :: endThawReturnWord debtOut :: ⟨5190⟩ ::
          endThawReturnPc :: sel :: [])
        (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut) (UInt256.ofNat 6)
        rdata (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd5076raw⟩
  have rd5129pre := evm_run rd5076 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push4 endThawTellSelectorWord (by decide +native) (by evm_ov),
    raw push1 ⟨224⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0
      (endThawNoArgCalldataMem endThawTellSelectorWord
        (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut))
      (UInt256.ofNat 6) (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push4 endThawTellSelectorWord (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  have hinSize :
      UInt256.sub endThawNoArgOutPtr endThawNoArgOutPtr + endThawNoArgInSize =
        endThawNoArgInSize := by
    decide +native
  have hendPtr : endThawNoArgOutPtr + endThawNoArgInSize = endThawNoArgEndPtr := by
    decide +native
  have rd5129 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5129⟩
        (endThawCureWord σ' I :: endThawCureWord σ' I ::
          endThawNoArgOutPtr :: endThawNoArgInSize :: endThawNoArgOutPtr ::
          endThawNoArgOutSize :: endThawNoArgEndPtr :: endThawTellSelectorWord ::
          endThawCureWord σ' I :: endThawReturnWord debtOut :: ⟨5190⟩ ::
          endThawReturnPc :: sel :: [])
        (endThawNoArgCalldataMem endThawTellSelectorWord
          (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut))
        (UInt256.ofNat 6) rdata (cA', σ') k' C' := by
    exact ⟨_, _, by
      have rd5129norm := rd5129pre
      rw [hcureMask] at rd5129norm
      convert rd5129norm using 1⟩
  rcases rd5129 with ⟨_, _, rd5129ok⟩
  obtain ⟨gasWord, k', C', rd5144⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨5129⟩) (okPc := ⟨5141⟩) rd5129ok
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native)
      (by evm_ov)
  exact ⟨gasWord, k', C', by simpa using rd5144⟩

theorem endThawX_tellNoCode {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem debtOut rdata : ByteArray} {k C : ℕ}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hdebtOut : debtOut.size < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (endThawCureWord σ' I) = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5073⟩
      (endThawReturnWord debtOut :: ⟨5190⟩ :: endThawReturnPc :: sel :: [])
      (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut) (UInt256.ofNat 6)
      rdata (cA', σ') k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hpostSize :
      (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut).size = 164 :=
    endThawNoArgPostCallMem_size hmem hdebtOut
  have hpostRead64 :
      (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut).readWithPadding
          64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    endThawNoArgPostCallMem_read64 hmem hread64 hdebtOut
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    endThawNoArgPostCallMem_mload64 hmem hread64 hdebtOut
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endThawNoArgCalldataMem endThawTellSelectorWord
              (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endThawNoArgCalldataMem endThawTellSelectorWord
                (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut)).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue
      (by rw [endThawNoArgCalldataMem_size hpostSize]; decide)
      (by decide)
      (endThawNoArgCalldataMem_read64 hpostSize hpostRead64)
  have hcureMask :
      UInt256.land (endSlotWord ⟨7⟩ σ' I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        endThawCureWord σ' I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide +native]
  have rd5075 := evm_run h with [
    raw push1 ⟨7⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd5076raw⟩ := rd5075.sload (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd5076⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5076⟩
        (endSlotWord ⟨7⟩ σ' I :: endThawReturnWord debtOut :: ⟨5190⟩ ::
          endThawReturnPc :: sel :: [])
        (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut) (UInt256.ofNat 6)
        rdata (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd5076raw⟩
  have rd5129pre := evm_run rd5076 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push4 endThawTellSelectorWord (by decide +native) (by evm_ov),
    raw push1 ⟨224⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0
      (endThawNoArgCalldataMem endThawTellSelectorWord
        (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut))
      (UInt256.ofNat 6) (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push4 endThawTellSelectorWord (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  have rd5129 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5129⟩
        (endThawCureWord σ' I :: endThawCureWord σ' I ::
          endThawNoArgOutPtr :: endThawNoArgInSize :: endThawNoArgOutPtr ::
          endThawNoArgOutSize :: endThawNoArgEndPtr :: endThawTellSelectorWord ::
          endThawCureWord σ' I :: endThawReturnWord debtOut :: ⟨5190⟩ ::
          endThawReturnPc :: sel :: [])
        (endThawNoArgCalldataMem endThawTellSelectorWord
          (endThawNoArgPostCallMem endThawDebtSelectorWord mem debtOut))
        (UInt256.ofNat 6) rdata (cA', σ') k' C' := by
    exact ⟨_, _, by
      have rd5129norm := rd5129pre
      rw [hcureMask] at rd5129norm
      convert rd5129norm using 1⟩
  rcases rd5129 with ⟨_, _, rd5129zero⟩
  exact RD.solcExtcodesizeGuardMissing (okPc := ⟨5141⟩) rd5129zero
    hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by evm_ov)

theorem endThawX_tellPostStaticcall {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel gasWord : UInt256} {mem debtOut rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5144⟩
      (gasWord :: endThawCureWord σ' I :: endThawNoArgOutPtr ::
        endThawNoArgInSize :: endThawNoArgOutPtr :: endThawNoArgOutSize ::
        endThawNoArgEndPtr :: endThawTellSelectorWord :: endThawCureWord σ' I ::
        endThawReturnWord debtOut :: ⟨5190⟩ :: endThawReturnPc :: sel :: [])
      (endThawNoArgCalldataMem endThawTellSelectorWord mem) (UInt256.ofNat 6)
      rdata (cA', σ') k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
      (z : Bool) (tellOut : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', z, tellOut) = Ethereum.EVM.Θ I.blobVersionedHashes cA'
          gh bl σ' σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endThawCureWord σ' I))
          (toExecute σ' (AccountAddress.ofUInt256 (endThawCureWord σ' I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endThawNoArgCalldataMem endThawTellSelectorWord mem).readWithPadding
            endThawNoArgOutPtr.toNat endThawNoArgInSize.toNat)
          (I.depth + 1) I.header false)
      ∧ RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5145⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endThawNoArgEndPtr ::
            endThawTellSelectorWord :: endThawCureWord σ' I ::
            endThawReturnWord debtOut :: ⟨5190⟩ :: endThawReturnPc :: sel :: [])
          (endThawNoArgPostCallMem endThawTellSelectorWord mem tellOut)
          (UInt256.ofNat 6) tellOut (cA'', σ'') k' C'
      ∧ tellOut.size < UInt256.size := by
  obtain ⟨cA'', σ'', z, tellOut, Ain, callGas, k', C', hΘ, rd5145raw, hout⟩ :=
    RD.solcStaticcall h (by decide +native) hdepth (by evm_ov)
  refine ⟨cA'', σ'', z, tellOut, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have hmin := endThawNoArgWriteLen_eq (out := tellOut) hout
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          endThawNoArgOutPtr.toNat endThawNoArgInSize.toNat)
          endThawNoArgOutPtr.toNat endThawNoArgOutSize.toNat) = UInt256.ofNat 6 := by
      unfold endThawNoArgOutPtr endThawNoArgInSize endThawNoArgOutSize
      decide +native
    simpa [endThawNoArgPostCallMem, endThawNoArgOutPtr, endThawNoArgInSize,
      endThawNoArgOutSize, endThawNoArgEndPtr, hmin, haw] using rd5145raw

theorem endThawX_tellCallFailed {cA cA' gh bl σ σTarget σ' σ₀ A I} {g : Sat256}
    {sel debtWord : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5145⟩
      (⟨0⟩ :: endThawNoArgEndPtr :: endThawTellSelectorWord ::
        endThawCureWord σTarget I :: debtWord :: ⟨5190⟩ ::
        endThawReturnPc :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨5145⟩) (okPc := ⟨5161⟩) h
    rfl
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    hrdataSize (by evm_ov)

theorem endThawX_tellCallSucceeded {cA cA' gh bl σ σTarget σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {debtWord : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5145⟩
      (⟨1⟩ :: endThawNoArgEndPtr :: endThawTellSelectorWord ::
        endThawCureWord σTarget I :: debtWord :: ⟨5190⟩ :: endThawReturnPc :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5163⟩
      (endThawNoArgEndPtr :: endThawTellSelectorWord :: endThawCureWord σTarget I ::
        debtWord :: ⟨5190⟩ :: endThawReturnPc :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA', σ') k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨5145⟩) (okPc := ⟨5161⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
    (by evm_ov)

theorem endThawX_tellReturnDecodeOk {cA cA' gh bl σ σTarget σ' σ₀ A I}
    {g : Sat256} {sel debtWord : UInt256} {mem tellOut : ByteArray} {k C : ℕ}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5163⟩
      (endThawNoArgEndPtr :: endThawTellSelectorWord :: endThawCureWord σTarget I ::
        debtWord :: ⟨5190⟩ :: endThawReturnPc :: sel :: [])
      (endThawNoArgPostCallMem endThawTellSelectorWord mem tellOut) (UInt256.ofNat 6)
      tellOut (cA', σ') k C)
    (hlo : 32 ≤ tellOut.size) (hout : tellOut.size < UInt256.size) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5186⟩
      (endThawReturnWord tellOut :: debtWord :: ⟨5190⟩ :: endThawReturnPc :: sel :: [])
      (endThawNoArgPostCallMem endThawTellSelectorWord mem tellOut) (UInt256.ofNat 6)
      tellOut (cA', σ') k' C' := by
  exact RD.solcUint256ReturnWordDecodeOk (pc := ⟨5163⟩) (okPc := ⟨5183⟩)
    (retWord := endThawReturnWord tellOut) h hlo hout
    mem_cost
    (by decide +native)
    (endThawNoArgPostCallMem_mload64 hmem hread64 hout)
    (endThawNoArgPostCallMem_mload128 hmem hout hlo)
    mem_cost
    (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest)
    (by decide +native) (by decide +native) (by decide +native)
    (by evm_ov)

theorem endThawX_tellReturnDecodeShort {cA cA' gh bl σ σTarget σ' σ₀ A I}
    {g : Sat256} {sel debtWord : UInt256} {mem tellOut : ByteArray} {k C : ℕ}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5163⟩
      (endThawNoArgEndPtr :: endThawTellSelectorWord :: endThawCureWord σTarget I ::
        debtWord :: ⟨5190⟩ :: endThawReturnPc :: sel :: [])
      (endThawNoArgPostCallMem endThawTellSelectorWord mem tellOut) (UInt256.ofNat 6)
      tellOut (cA', σ') k C)
    (hshort : tellOut.size < 32) (hout : tellOut.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨5163⟩) (okPc := ⟨5183⟩)
    h hshort hout
    mem_cost
    (by decide +native)
    (endThawNoArgPostCallMem_mload64 hmem hread64 hout)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native)
    (by evm_ov)

abbrev endThawDebtStoreLogTopic : UInt256 :=
    ⟨0x4df15159e645ba7d02cadde0bc937abef5ad0134623c00de50a31750b85978b9⟩

theorem endThawX_subSuccess {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel debtWord tellWord : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (hle : tellWord.toNat ≤ debtWord.toNat)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5186⟩
      (tellWord :: debtWord :: ⟨5190⟩ :: endThawReturnPc :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5190⟩
      (UInt256.sub debtWord tellWord :: endThawReturnPc :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA', σ') k' C' := by
  have rd10154 := evm_run h with [
    raw push2 ⟨10154⟩ (by decide +native) (by evm_ov),
    raw jump (by decide +native) (by jump_dest) (by evm_ov)]
  exact RD.solcCheckedSubSuccess
    (pc := ⟨10154⟩) (okPc := ⟨10108⟩)
    (a := debtWord) (b := tellWord) (ret := ⟨5190⟩)
    (R := [endThawReturnPc, sel])
    rd10154
    (by
      unfold solcCheckedSubSuccessWf
      repeat' first | apply And.intro | decide +native)
    hle (by jump_dest) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endThawX_subUnderflow {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel debtWord tellWord : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (hlt : debtWord.toNat < tellWord.toNat)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5186⟩
      (tellWord :: debtWord :: ⟨5190⟩ :: endThawReturnPc :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA', σ') k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsubNat : (UInt256.sub debtWord tellWord).toNat =
      UInt256.size + debtWord.toNat - tellWord.toNat :=
    usub_toNat_underflow hlt
  have hgt : UInt256.gt (UInt256.sub debtWord tellWord) debtWord = ⟨1⟩ := by
    show UInt256.fromBool (decide (UInt256.sub debtWord tellWord > debtWord)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub debtWord tellWord).toNat > debtWord.toNat
      rw [hsubNat]
      have htell : tellWord.toNat < UInt256.size := tellWord.val.isLt
      omega
  have rd10165pre := evm_run h with [
    raw push2 ⟨10154⟩ (by decide +native) (by evm_ov),
    raw jump (by decide +native) (by jump_dest) (by evm_ov),
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw gt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨10108⟩ (by decide +native) (by evm_ov)]
  have rd10165 := rd10165pre
  rw [hgt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd10165
  have rd10166 := rd10165.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd10166 with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw rev 0 (by decide +native) mem_cost (by evm_ov)]

theorem endThawX_debtStoreLogReturn {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel debtNew : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5190⟩
      (debtNew :: endThawReturnPc :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA', σ') k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', sstoreAccountMap I.codeOwner σ' ⟨11⟩ debtNew) ByteArray.empty := by
  have rd5193 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨11⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rdStored⟩ := rd5193.sstore hperm (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have rd5196 := rdStored.push1 ⟨64⟩ (by decide +native) (by evm_ov)
  have rdMload := rd5196.mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
    mem_cost hmload64 (by decide +native) (by evm_ov)
  have rdTopic := rdMload.pushConst endThawDebtStoreLogTopic
    (width := 32) (op := .PUSH32) (by decide) (by decide +native) (by evm_ov)
  have rdLogReady := evm_run rdTopic with [
    raw swap1 (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rdLog := RD.log1
    (a := ⟨128⟩) (b := ⟨0⟩) (c := endThawDebtStoreLogTopic)
    (t := [endThawReturnPc, sel])
    0 (UInt256.ofNat (MachineState.M (UInt256.ofNat 6).toNat (⟨128⟩ : UInt256).toNat 0))
    rdLogReady (by decide +native) hperm mem_cost (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd562 := RD.jump (a := endThawReturnPc) (t := [sel]) rdLog
    (by decide +native) (by jump_dest) (by evm_ov)
  have rd563 := RD.jumpdest (pc := endThawReturnPc) (stk := [sel]) rd562
    (by decide +native) (by evm_ov)
  exact RD.stop rd563 (by decide +native) (by evm_ov)

theorem endThawX_daiNoCode {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hlive : endThawLiveWord σ I = ⟨0⟩)
    (hdebt : endThawDebtWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endThawVatWord σ I) = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endThawBodyPc
      [endThawReturnPc, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd4528 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨8⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd4529raw⟩ := rd4528.sload (by decide +native) (by evm_ov)
  have hliveRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨8⟩ ⟨0⟩)) =
        ⟨0⟩ := by
      simpa [endThawLiveWord, endSlotWord, solcSlotWord] using hlive
  have rd4529zero := rd4529raw
  rw [hliveRaw] at rd4529zero
  obtain ⟨_, _, rd4529⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4529⟩
        (⟨0⟩ :: endThawReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endThawBodyPc] using rd4529zero⟩
  have rd4530raw := rd4529.iszero (by decide +native) (by evm_ov)
  have rd4530 := rd4530raw
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4530
  have rd4533 := rd4530.push2 ⟨4595⟩ (by decide +native) (by evm_ov)
  have rd4595 := rd4533.jumpiT (by decide +native)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have rd4598 := evm_run rd4595 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨11⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd4599raw⟩ := rd4598.sload (by decide +native) (by evm_ov)
  have hdebtRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨11⟩ ⟨0⟩)) =
        ⟨0⟩ := by
      simpa [endThawDebtWord, endSlotWord, solcSlotWord] using hdebt
  have rd4599zero := rd4599raw
  rw [hdebtRaw] at rd4599zero
  obtain ⟨_, _, rd4599⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4599⟩
        (⟨0⟩ :: endThawReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa using rd4599zero⟩
  have rd4600raw := rd4599.iszero (by decide +native) (by evm_ov)
  have rd4600 := rd4600raw
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4600
  have rd4603 := rd4600.push2 ⟨4668⟩ (by decide +native) (by evm_ov)
  have rd4668 := rd4603.jumpiT (by decide +native)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have rd4670 := evm_run rd4668 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd4671raw⟩ := rd4670.sload (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd4672⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4672⟩
        (endSlotWord ⟨1⟩ σ I :: endThawReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd4671raw⟩
  have rd4675pre := evm_run rd4672 with [
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd4675raw⟩ := rd4675pre.sload (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd4676⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4676⟩
        (endSlotWord ⟨4⟩ σ I :: ⟨4⟩ :: endSlotWord ⟨1⟩ σ I :: endThawReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd4675raw⟩
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ solcFreePtrMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            (solcFreePtrMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [solcFreePtrMem_size]; decide) (by decide) solcFreePtrMem_read64
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (endThawDaiCalldataMem σ I solcFreePtrMem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endThawDaiCalldataMem σ I solcFreePtrMem).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue
      (by rw [endThawDaiCalldataMem_size σ I solcFreePtrMem_size]; decide)
      (by decide)
      (endThawDaiCalldataMem_read64 σ I solcFreePtrMem_size solcFreePtrMem_read64)
  have hvatMask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (endSlotWord ⟨1⟩ σ I) = endThawVatWord σ I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide +native]
  have hvowMask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (endSlotWord ⟨4⟩ σ I) = endThawVowWord σ I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide +native]
  have rd4737pre := evm_run rd4676 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push4 endThawDaiSelectorRaw (by decide +native) (by evm_ov),
    raw push1 ⟨225⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 6 (endThawDaiSelectorMem solcFreePtrMem) (UInt256.ofNat 5)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw mstore 3 (endThawDaiCalldataMem σ I solcFreePtrMem) (UInt256.ofNat 6)
      (by decide +native) mem_cost
      (by
        rw [hvowMask]
        rfl)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push4 endThawDaiSelectorWord (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push1 ⟨36⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  have rd4737 :=
    (by
      simpa [endThawDaiSelectorMem, endThawDaiCalldataMem, endThawDaiOutPtr,
        endThawDaiInSize, endThawDaiEndPtr, endThawDaiSelectorWord, endThawDaiSelectorRaw,
        endThawVatWord, endThawVowWord, endSlotWord, solcSlotWord, solcAddrMask,
        hvatMask, hvowMask, u256_land_comm] using rd4737pre)
  have hcodeSizeGuard := hcodeSize
  rw [← hvatMask] at hcodeSizeGuard
  exact RD.solcExtcodesizeGuardMissing (okPc := ⟨4749⟩) rd4737
    hcodeSizeGuard
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)

theorem evalStorageRef_endThaw_live (evm : EVM.State) :
    evalStorageRef config { contract := contract, locals := (∅ : Store) } evm
      liveRef = .ok endThawLiveEvaledRef := by
  simp [endThawLiveEvaledRef, liveRef, evalStorageRef, evalStorageRefSteps,
    EvalResult.bind, pure, bind]

theorem evalStorageRef_endThaw_debt (evm : EVM.State) :
    evalStorageRef config { contract := contract, locals := (∅ : Store) } evm
      debtRef = .ok endThawDebtEvaledRef := by
  simp [endThawDebtEvaledRef, debtRef, evalStorageRef, evalStorageRefSteps,
    EvalResult.bind, pure, bind]

theorem evalStorageRef_endThaw_vat {locals : Store} (_hbase : locals.get? "vat" = none)
    (evm : EVM.State) :
    evalStorageRef config { contract := contract, locals := locals } evm
      vatRef = .ok ({ base := "vat", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind]

theorem evalStorageRef_endThaw_vow {locals : Store} (_hbase : locals.get? "vow" = none)
    (evm : EVM.State) :
    evalStorageRef config { contract := contract, locals := locals } evm
      vowRef = .ok ({ base := "vow", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind]

theorem evalStorageRef_endThaw_cure {locals : Store} (_hbase : locals.get? "cure" = none)
    (evm : EVM.State) :
    evalStorageRef config { contract := contract, locals := locals } evm
      cureRef = .ok ({ base := "cure", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, cureRef, EvalResult.bind, pure, bind]

theorem evalStorageRef_endThaw_when {locals : Store} (_hbase : locals.get? "when" = none)
    (evm : EVM.State) :
    evalStorageRef config { contract := contract, locals := locals } evm
      whenRef = .ok ({ base := "when", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, whenRef, EvalResult.bind, pure, bind]

theorem evalStorageRef_endThaw_wait {locals : Store} (_hbase : locals.get? "wait" = none)
    (evm : EVM.State) :
    evalStorageRef config { contract := contract, locals := locals } evm
      waitRef = .ok ({ base := "wait", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, waitRef, EvalResult.bind, pure, bind]

theorem evalExpr_endThaw_vat {locals : Store} (evm : EVM.State)
    (hbase : locals.get? "vat" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := vatRef)
    (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
    (t := .address)
    (loc := addrLoc ⟨1⟩)
    (hbase := hbase)
    (her := evalStorageRef_endThaw_vat hbase evm)
    (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hload := endStorageLocLoad_address_offset0 evm ⟨1⟩)

theorem evalExpr_endThaw_vow {locals : Store} (evm : EVM.State)
    (hbase : locals.get? "vow" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vowRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := vowRef)
    (er := ({ base := "vow", steps := [] } : EvaledStorageRef))
    (t := .address)
    (loc := addrLoc ⟨4⟩)
    (hbase := hbase)
    (her := evalStorageRef_endThaw_vow hbase evm)
    (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hload := endStorageLocLoad_address_offset0 evm ⟨4⟩)

theorem evalExpr_endThaw_cure {locals : Store} (evm : EVM.State)
    (hbase : locals.get? "cure" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage cureRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩)
          solcAddrMask).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := cureRef)
    (er := ({ base := "cure", steps := [] } : EvaledStorageRef))
    (t := .address)
    (loc := addrLoc ⟨7⟩)
    (hbase := hbase)
    (her := evalStorageRef_endThaw_cure hbase evm)
    (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hload := endStorageLocLoad_address_offset0 evm ⟨7⟩)

theorem evalExpr_endThaw_when {locals : Store} (evm : EVM.State)
    (hbase : locals.get? "when" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage whenRef) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := whenRef)
    (er := ({ base := "when", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int)
    (loc := wordLoc ⟨9⟩)
    (hbase := hbase)
    (her := evalStorageRef_endThaw_when hbase evm)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm ⟨9⟩)

theorem evalExpr_endThaw_wait {locals : Store} (evm : EVM.State)
    (hbase : locals.get? "wait" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage waitRef) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := waitRef)
    (er := ({ base := "wait", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int)
    (loc := wordLoc ⟨10⟩)
    (hbase := hbase)
    (her := evalStorageRef_endThaw_wait hbase evm)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm ⟨10⟩)

theorem evalExpr_endThaw_timestamp {locals : Store} (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals } evm nowT =
      .ok (.int (Int.ofNat (endThawTimestampWord evm.executionEnv).toNat)) := by
  simp [nowT, evalExpr?, envValue, endThawTimestampWord, pure]

theorem evalExpr_endThaw_live_zero_false (evm : EVM.State)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := (∅ : Store) } evm
      (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm
        (.storage liveRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := (∅ : Store) })
      (slot := liveRef)
      (er := endThawLiveEvaledRef)
      (t := .int uint256Int)
      (loc := wordLoc ⟨8⟩)
      (hbase := by simp [liveRef])
      (her := evalStorageRef_endThaw_live evm)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact endStorageLocLoad_uint256 evm ⟨8⟩)
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ≠
        Value.int 0 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact uint256_toNat_eq_zero (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ==
        Value.int 0) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat))
      (Value.int 0) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem endThawBodyReverts_liveNonzero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endThawLiveWord σ I ≠ ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (∅ : Store) thawTransition.body .reverted := by
  intro evm0
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩ ≠ ⟨0⟩ := by
    intro hbad
    apply hlive
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawLiveWord, endSlotWord, solcSlotWord] using hbad
  have hguard :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_endThaw_live_zero_false evm0 hliveLoad
  refine ExecFuncBody.execBlockRevert ?_
  simpa [thawTransition, nonpayable, checkedExternalCallStmts] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := (∅ : Store) })
      (evm := evm0)
      (guard := .binary .eq (.storage liveRef) (.intLit 0))
      (rest :=
        [ .require (.binary .eq (.storage debtRef) (.intLit 0)) ] ++
        checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
          (perm := false) ++
        [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
          .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
          .require (.binary .ge nowT (.var "deadline")) ] ++
        checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
        checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
          (perm := false) ++
        [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
          .assign .storage debtRef (.var "debtNew") ])
      (by simp only [evm0, initState]; exact hwv)
      hguard

theorem evalExpr_endThaw_debt_zero_false (evm : EVM.State)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := (∅ : Store) } evm
      (.binary .eq (.storage debtRef) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm
        (.storage debtRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := (∅ : Store) })
      (slot := debtRef)
      (er := endThawDebtEvaledRef)
      (t := .int uint256Int)
      (loc := wordLoc ⟨11⟩)
      (hbase := by simp [debtRef])
      (her := evalStorageRef_endThaw_debt evm)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact endStorageLocLoad_uint256 evm ⟨11⟩)
  have hzero :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  apply endEvalExpr_eq_int_false hstorage hzero
  intro hbad
  apply hload
  exact uint256_toNat_eq_zero (Int.ofNat.inj hbad)

theorem endThawBodyReverts_debtNonzero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endThawLiveWord σ I = ⟨0⟩)
    (hdebt : endThawDebtWord σ I ≠ ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (∅ : Store) thawTransition.body .reverted := by
  intro evm0
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawLiveWord, endSlotWord, solcSlotWord] using hlive
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
    intro hbad
    apply hdebt
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawDebtWord, endSlotWord, solcSlotWord] using hbad
  have hguardLive :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.storage liveRef) = .ok (.int 0) := by
        rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := (∅ : Store) })
        (slot := liveRef)
        (er := endThawLiveEvaledRef)
        (t := .int uint256Int)
        (loc := wordLoc ⟨8⟩)
        (value := .int 0)
        (hbase := by simp [liveRef])
        (her := evalStorageRef_endThaw_live evm0)
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by simpa [hliveLoad] using endStorageLocLoad_uint256 evm0 ⟨8⟩)]
    have hzero :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.intLit 0) = .ok (.int 0) := by
        simp [evalExpr?, pure]
    exact endEvalExpr_eq_int_true hstorage hzero rfl
  have hguardDebt :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .eq (.storage debtRef) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_endThaw_debt_zero_false evm0 hdebtLoad
  have hblock :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        thawTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardDebt)
  simpa [ExecTransitionBody, thawTransition, nonpayable, checkedExternalCallStmts, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem endThawBodyReverts_daiNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endThawLiveWord σ I = ⟨0⟩)
    (hdebt : endThawDebtWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endThawVatWord σ I) = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (∅ : Store) thawTransition.body .reverted := by
  intro evm0
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawLiveWord, endSlotWord, solcSlotWord] using hlive
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawDebtWord, endSlotWord, solcSlotWord] using hdebt
  have hguardLive :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.storage liveRef) = .ok (.int 0) := by
        rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := (∅ : Store) })
        (slot := liveRef)
        (er := endThawLiveEvaledRef)
        (t := .int uint256Int)
        (loc := wordLoc ⟨8⟩)
        (value := .int 0)
        (hbase := by simp [liveRef])
        (her := evalStorageRef_endThaw_live evm0)
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by simpa [hliveLoad] using endStorageLocLoad_uint256 evm0 ⟨8⟩)]
    have hzero :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.intLit 0) = .ok (.int 0) := by
        simp [evalExpr?, pure]
    exact endEvalExpr_eq_int_true hstorage hzero rfl
  have hguardDebt :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .eq (.storage debtRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.storage debtRef) = .ok (.int 0) := by
        rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := (∅ : Store) })
        (slot := debtRef)
        (er := endThawDebtEvaledRef)
        (t := .int uint256Int)
        (loc := wordLoc ⟨11⟩)
        (value := .int 0)
        (hbase := by simp [debtRef])
        (her := evalStorageRef_endThaw_debt evm0)
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by simpa [hdebtLoad] using endStorageLocLoad_uint256 evm0 ⟨11⟩)]
    have hzero :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.intLit 0) = .ok (.int 0) := by
        simp [evalExpr?, pure]
    exact endEvalExpr_eq_int_true hstorage hzero rfl
  have hreceiver :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.storage vatRef) = .ok (.address (endThawVatAddr σ I)) := by
      simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawVatAddr, endThawVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endThaw_vat (locals := (∅ : Store)) evm0 (by simp)
  have hcodeZero :
      (UInt256.ofNat
        ((evm0.lookupAccount (endThawVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat =
        0 := by
      simpa [evm0] using
      endThawVatCode_zero_of_codeSize_zero
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguardDai :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  have hdaiBlock :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        (checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
          (perm := false)) .reverted := by
      simpa [checkedExternalCallStmts] using
      checkedExternalCallNoCode
        (cfg := config) (C := contract) (evm := evm0)
        (locals := (∅ : Store)) (receiver := .storage vatRef)
        (retVar := "vatDai") (name := "dai") (sendVal := 0)
        (args := [vowAddr]) (perm := false) hguardDai
  have hdaiWithTail :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        (checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
          (perm := false) ++
          [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
            .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
            .require (.binary .ge nowT (.var "deadline")) ] ++
          checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
          checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
            (perm := false) ++
          [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
            .assign .storage debtRef (.var "debtNew") ])
        .reverted := by
    exact execBlock_append_term
      (s2 :=
          [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
            .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
            .require (.binary .ge nowT (.var "deadline")) ] ++
          checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
          checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
            (perm := false) ++
          [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
            .assign .storage debtRef (.var "debtNew") ])
      hdaiBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        thawTransition.body .reverted := by
    simp only [thawTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardDebt) ?_
    simpa [checkedExternalCallStmts, List.append_assoc] using hdaiWithTail
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endThawBodyReverts_daiCallFailed {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmDai : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endThawLiveWord σ I = ⟨0⟩)
    (hdebt : endThawDebtWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endThawVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endThawVatAddr σ I)) "dai" 0
        [.address (endThawVowAddr σ I)] (false, evmDai, out) false) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (∅ : Store) thawTransition.body .reverted := by
  intro evm0
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawLiveWord, endSlotWord, solcSlotWord] using hlive
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawDebtWord, endSlotWord, solcSlotWord] using hdebt
  have hguardLive :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.storage liveRef) = .ok (.int 0) := by
        rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := (∅ : Store) })
        (slot := liveRef)
        (er := endThawLiveEvaledRef)
        (t := .int uint256Int)
        (loc := wordLoc ⟨8⟩)
        (value := .int 0)
        (hbase := by simp [liveRef])
        (her := evalStorageRef_endThaw_live evm0)
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by simpa [hliveLoad] using endStorageLocLoad_uint256 evm0 ⟨8⟩)]
    have hzero :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.intLit 0) = .ok (.int 0) := by
        simp [evalExpr?, pure]
    exact endEvalExpr_eq_int_true hstorage hzero rfl
  have hguardDebt :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .eq (.storage debtRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.storage debtRef) = .ok (.int 0) := by
        rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := (∅ : Store) })
        (slot := debtRef)
        (er := endThawDebtEvaledRef)
        (t := .int uint256Int)
        (loc := wordLoc ⟨11⟩)
        (value := .int 0)
        (hbase := by simp [debtRef])
        (her := evalStorageRef_endThaw_debt evm0)
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by simpa [hdebtLoad] using endStorageLocLoad_uint256 evm0 ⟨11⟩)]
    have hzero :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.intLit 0) = .ok (.int 0) := by
        simp [evalExpr?, pure]
    exact endEvalExpr_eq_int_true hstorage hzero rfl
  have hreceiver :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.storage vatRef) = .ok (.address (endThawVatAddr σ I)) := by
      simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawVatAddr, endThawVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endThaw_vat (locals := (∅ : Store)) evm0 (by simp)
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endThawVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [evm0] using
      endThawVatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguardDai :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hvow :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        vowAddr = .ok (.address (endThawVowAddr σ I)) := by
      simpa [vowAddr, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawVowAddr, endThawVowWord, endSlotWord, solcSlotWord] using
      evalExpr_endThaw_vow (locals := (∅ : Store)) evm0 (by simp)
  have hargs :
      evalExprs? config { contract := contract, locals := (∅ : Store) } evm0 [vowAddr] =
        .ok [.address (endThawVowAddr σ I)] := by
    simp [evalExprs?, hvow, EvalResult.bind, bind, pure]
  have hdaiBlock :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        (checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
          (perm := false)) .reverted := by
      simpa [checkedExternalCallStmts] using
      checkedExternalCallFailure
        (cfg := config) (C := contract) (evm := evm0)
        (locals := (∅ : Store)) (receiver := .storage vatRef)
        (retVar := "vatDai") (name := "dai") (target := endThawVatAddr σ I)
        (sendVal := 0) (args := [vowAddr])
        (argVals := [.address (endThawVowAddr σ I)]) (out := out)
        (perm := false) hguardDai hreceiver hargs (by simpa [evm0] using hcall)
  have hdaiWithTail :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        (checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
          (perm := false) ++
          [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
            .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
            .require (.binary .ge nowT (.var "deadline")) ] ++
          checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
          checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
            (perm := false) ++
          [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
            .assign .storage debtRef (.var "debtNew") ])
        .reverted := by
    exact execBlock_append_term
      (s2 :=
          [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
            .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
            .require (.binary .ge nowT (.var "deadline")) ] ++
          checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
          checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
            (perm := false) ++
          [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
            .assign .storage debtRef (.var "debtNew") ])
      hdaiBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        thawTransition.body .reverted := by
    simp only [thawTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardDebt) ?_
    simpa [checkedExternalCallStmts, List.append_assoc] using hdaiWithTail
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endThawBodyReverts_daiBlockReverted {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endThawLiveWord σ I = ⟨0⟩)
    (hdebt : endThawDebtWord σ I = ⟨0⟩)
    (hdaiBlock :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        (checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
          (perm := false)) .reverted) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (∅ : Store) thawTransition.body .reverted := by
  intro evm0
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawLiveWord, endSlotWord, solcSlotWord] using hlive
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawDebtWord, endSlotWord, solcSlotWord] using hdebt
  have hguardLive :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.storage liveRef) = .ok (.int 0) := by
        rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := (∅ : Store) })
        (slot := liveRef)
        (er := endThawLiveEvaledRef)
        (t := .int uint256Int)
        (loc := wordLoc ⟨8⟩)
        (value := .int 0)
        (hbase := by simp [liveRef])
        (her := evalStorageRef_endThaw_live evm0)
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by simpa [hliveLoad] using endStorageLocLoad_uint256 evm0 ⟨8⟩)]
    have hzero :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.intLit 0) = .ok (.int 0) := by
        simp [evalExpr?, pure]
    exact endEvalExpr_eq_int_true hstorage hzero rfl
  have hguardDebt :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .eq (.storage debtRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.storage debtRef) = .ok (.int 0) := by
        rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := (∅ : Store) })
        (slot := debtRef)
        (er := endThawDebtEvaledRef)
        (t := .int uint256Int)
        (loc := wordLoc ⟨11⟩)
        (value := .int 0)
        (hbase := by simp [debtRef])
        (her := evalStorageRef_endThaw_debt evm0)
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by simpa [hdebtLoad] using endStorageLocLoad_uint256 evm0 ⟨11⟩)]
    have hzero :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.intLit 0) = .ok (.int 0) := by
        simp [evalExpr?, pure]
    exact endEvalExpr_eq_int_true hstorage hzero rfl
  have hdaiWithTail :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        (checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
          (perm := false) ++
          [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
            .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
            .require (.binary .ge nowT (.var "deadline")) ] ++
          checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
          checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
            (perm := false) ++
          [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
            .assign .storage debtRef (.var "debtNew") ])
        .reverted := by
    exact execBlock_append_term
      (s2 :=
          [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
            .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
            .require (.binary .ge nowT (.var "deadline")) ] ++
          checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
          checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
            (perm := false) ++
          [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
            .assign .storage debtRef (.var "debtNew") ])
      (by simpa [evm0] using hdaiBlock) (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        thawTransition.body .reverted := by
    simp only [thawTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardDebt) ?_
    simpa [checkedExternalCallStmts, List.append_assoc] using hdaiWithTail
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endThawBodyReverts_daiDecodeShort {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmDai : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endThawLiveWord σ I = ⟨0⟩)
    (hdebt : endThawDebtWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endThawVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endThawVatAddr σ I)) "dai" 0
        [.address (endThawVowAddr σ I)] (true, evmDai, out) false)
    (hshort : out.size < 32) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (∅ : Store) thawTransition.body .reverted := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.storage vatRef) = .ok (.address (endThawVatAddr σ I)) := by
      simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawVatAddr, endThawVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endThaw_vat (locals := (∅ : Store)) evm0 (by simp)
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endThawVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [evm0] using
      endThawVatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguardDai :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hvow :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        vowAddr = .ok (.address (endThawVowAddr σ I)) := by
      simpa [vowAddr, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawVowAddr, endThawVowWord, endSlotWord, solcSlotWord] using
      evalExpr_endThaw_vow (locals := (∅ : Store)) evm0 (by simp)
  have hargs :
      evalExprs? config { contract := contract, locals := (∅ : Store) } evm0 [vowAddr] =
        .ok [.address (endThawVowAddr σ I)] := by
    simp [evalExprs?, hvow, EvalResult.bind, bind, pure]
  have hdaiBlock :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        (checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
          (perm := false)) .reverted := by
      simpa [checkedExternalCallStmts] using
      checkedExternalCallDecodeRevert
        (cfg := config) (C := contract) (evm := evm0)
        (locals := (∅ : Store)) (receiver := .storage vatRef)
        (retVar := "vatDai") (name := "dai") (target := endThawVatAddr σ I)
        (sendVal := 0) (args := [vowAddr])
        (argVals := [.address (endThawVowAddr σ I)]) (out := out)
        (perm := false) hguardDai hreceiver hargs
        (by simpa [evm0] using hcall) (endThawDaiDecode_short out hshort)
  simpa [evm0] using
    endThawBodyReverts_daiBlockReverted
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hwv hlive hdebt (by simpa [evm0] using hdaiBlock)

theorem endThawBodyReverts_daiOkTailReverted {cA gh bl σ σ₀ A I} {g : UInt256}
    {fDai : Frame} {evmDai : EVM.State}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endThawLiveWord σ I = ⟨0⟩)
    (hdebt : endThawDebtWord σ I = ⟨0⟩)
    (hdaiBlock :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        (checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
          (perm := false)) (.ok fDai evmDai))
    (htail :
      ExecBlock config fDai evmDai
        ([ .require (.binary .eq (.var "vatDai") (.intLit 0)),
          .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
          .require (.binary .ge nowT (.var "deadline")) ] ++
        checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
        checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
          (perm := false) ++
        [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
          .assign .storage debtRef (.var "debtNew") ])
        .reverted) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (∅ : Store) thawTransition.body .reverted := by
  intro evm0
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawLiveWord, endSlotWord, solcSlotWord] using hlive
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawDebtWord, endSlotWord, solcSlotWord] using hdebt
  have hguardLive :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.storage liveRef) = .ok (.int 0) := by
        rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := (∅ : Store) })
        (slot := liveRef)
        (er := endThawLiveEvaledRef)
        (t := .int uint256Int)
        (loc := wordLoc ⟨8⟩)
        (value := .int 0)
        (hbase := by simp [liveRef])
        (her := evalStorageRef_endThaw_live evm0)
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by simpa [hliveLoad] using endStorageLocLoad_uint256 evm0 ⟨8⟩)]
    have hzero :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.intLit 0) = .ok (.int 0) := by
        simp [evalExpr?, pure]
    exact endEvalExpr_eq_int_true hstorage hzero rfl
  have hguardDebt :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .eq (.storage debtRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.storage debtRef) = .ok (.int 0) := by
        rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := (∅ : Store) })
        (slot := debtRef)
        (er := endThawDebtEvaledRef)
        (t := .int uint256Int)
        (loc := wordLoc ⟨11⟩)
        (value := .int 0)
        (hbase := by simp [debtRef])
        (her := evalStorageRef_endThaw_debt evm0)
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by simpa [hdebtLoad] using endStorageLocLoad_uint256 evm0 ⟨11⟩)]
    have hzero :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.intLit 0) = .ok (.int 0) := by
        simp [evalExpr?, pure]
    exact endEvalExpr_eq_int_true hstorage hzero rfl
  have hdaiWithTail :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        (checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
          (perm := false) ++
          [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
            .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
            .require (.binary .ge nowT (.var "deadline")) ] ++
          checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
          checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
            (perm := false) ++
          [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
            .assign .storage debtRef (.var "debtNew") ])
        .reverted := by
    exact execBlock_append
      (s2 :=
          [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
            .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
            .require (.binary .ge nowT (.var "deadline")) ] ++
          checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
          checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
            (perm := false) ++
          [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
            .assign .storage debtRef (.var "debtNew") ])
      (by simpa [evm0] using hdaiBlock) htail
  have hblock :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        thawTransition.body .reverted := by
    simp only [thawTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardDebt) ?_
    simpa [checkedExternalCallStmts, List.append_assoc] using hdaiWithTail
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endThawBodyReverts_daiNonzero {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmDai : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endThawLiveWord σ I = ⟨0⟩)
    (hdebt : endThawDebtWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endThawVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endThawVatAddr σ I)) "dai" 0
        [.address (endThawVowAddr σ I)] (true, evmDai, out) false)
    (hlo : 32 ≤ out.size)
    (hdai : endThawDaiWord out ≠ ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (∅ : Store) thawTransition.body .reverted := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.storage vatRef) = .ok (.address (endThawVatAddr σ I)) := by
      simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawVatAddr, endThawVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endThaw_vat (locals := (∅ : Store)) evm0 (by simp)
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endThawVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [evm0] using
      endThawVatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguardDai :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hvow :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        vowAddr = .ok (.address (endThawVowAddr σ I)) := by
      simpa [vowAddr, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawVowAddr, endThawVowWord, endSlotWord, solcSlotWord] using
      evalExpr_endThaw_vow (locals := (∅ : Store)) evm0 (by simp)
  have hargs :
      evalExprs? config { contract := contract, locals := (∅ : Store) } evm0 [vowAddr] =
        .ok [.address (endThawVowAddr σ I)] := by
    simp [evalExprs?, hvow, EvalResult.bind, bind, pure]
  have hdaiBlock :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        (checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
          (perm := false))
        (.ok { contract := contract, locals := endThawStoreVatDai out } evmDai) := by
    have hblock := checkedExternalCallSuccess
      (cfg := config) (C := contract) (evm := evm0)
      (locals := (∅ : Store)) (receiver := .storage vatRef)
      (retVar := "vatDai") (name := "dai") (target := endThawVatAddr σ I)
      (sendVal := 0) (args := [vowAddr])
      (argVals := [.address (endThawVowAddr σ I)]) (out := out)
      (perm := false) hguardDai hreceiver hargs
      (by simpa [evm0] using hcall) (endThawDaiDecode_ok out hlo)
    simpa [checkedExternalCallStmts, endThawStoreVatDai, collapseReturns] using hblock
  have hvatDai :
      evalExpr? config { contract := contract, locals := endThawStoreVatDai out } evmDai
        (.var "vatDai") = .ok (.int (Int.ofNat (endThawDaiWord out).toNat)) := by
      simpa [endThawStoreVatDai] using
      endEvalExpr_varUInt256 (evm := evmDai) (locals := endThawStoreVatDai out)
        (name := "vatDai") (value := endThawDaiWord out) (by simp [endThawStoreVatDai])
  have hzero :
      evalExpr? config { contract := contract, locals := endThawStoreVatDai out } evmDai
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hreq :
      evalExpr? config { contract := contract, locals := endThawStoreVatDai out } evmDai
        (.binary .eq (.var "vatDai") (.intLit 0)) = .ok (.bool false) := by
    apply endEvalExpr_eq_int_false hvatDai hzero
    intro hbad
    apply hdai
    exact uint256_toNat_eq_zero (Int.ofNat.inj hbad)
  have htailHead :
      ExecBlock config { contract := contract, locals := endThawStoreVatDai out } evmDai
        [ .require (.binary .eq (.var "vatDai") (.intLit 0)) ] .reverted :=
    ExecBlock.consRevert (ExecStmt.requireFalse hreq)
  have htail :
      ExecBlock config { contract := contract, locals := endThawStoreVatDai out } evmDai
        ([ .require (.binary .eq (.var "vatDai") (.intLit 0)),
          .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
          .require (.binary .ge nowT (.var "deadline")) ] ++
        checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
        checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
          (perm := false) ++
        [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
          .assign .storage debtRef (.var "debtNew") ])
        .reverted := by
    exact execBlock_append_term
      (s2 :=
        [ .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
          .require (.binary .ge nowT (.var "deadline")) ] ++
        checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
        checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
          (perm := false) ++
        [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
          .assign .storage debtRef (.var "debtNew") ])
      htailHead (by intro f' e' h; cases h)
  simpa [evm0] using
    endThawBodyReverts_daiOkTailReverted
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g)
      (fDai := { contract := contract, locals := endThawStoreVatDai out })
      (evmDai := evmDai) hwv hlive hdebt (by simpa [evm0] using hdaiBlock) htail

theorem endThawBodyReverts_deadlineAddOverflow {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmDai : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endThawLiveWord σ I = ⟨0⟩)
    (hdebt : endThawDebtWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endThawVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endThawVatAddr σ I)) "dai" 0
        [.address (endThawVowAddr σ I)] (true, evmDai, out) false)
    (hlo : 32 ≤ out.size)
    (hdai : endThawDaiWord out = ⟨0⟩)
    (hover :
      UInt256.size ≤
        (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩).toNat +
          (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨10⟩).toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (∅ : Store) thawTransition.body .reverted := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.storage vatRef) = .ok (.address (endThawVatAddr σ I)) := by
      simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawVatAddr, endThawVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endThaw_vat (locals := (∅ : Store)) evm0 (by simp)
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endThawVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [evm0] using
      endThawVatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguardDai :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hvow :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        vowAddr = .ok (.address (endThawVowAddr σ I)) := by
      simpa [vowAddr, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawVowAddr, endThawVowWord, endSlotWord, solcSlotWord] using
      evalExpr_endThaw_vow (locals := (∅ : Store)) evm0 (by simp)
  have hargs :
      evalExprs? config { contract := contract, locals := (∅ : Store) } evm0 [vowAddr] =
        .ok [.address (endThawVowAddr σ I)] := by
    simp [evalExprs?, hvow, EvalResult.bind, bind, pure]
  have hdaiBlock :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        (checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
          (perm := false))
        (.ok { contract := contract, locals := endThawStoreVatDai out } evmDai) := by
    have hblock := checkedExternalCallSuccess
      (cfg := config) (C := contract) (evm := evm0)
      (locals := (∅ : Store)) (receiver := .storage vatRef)
      (retVar := "vatDai") (name := "dai") (target := endThawVatAddr σ I)
      (sendVal := 0) (args := [vowAddr])
      (argVals := [.address (endThawVowAddr σ I)]) (out := out)
      (perm := false) hguardDai hreceiver hargs
      (by simpa [evm0] using hcall) (endThawDaiDecode_ok out hlo)
    simpa [checkedExternalCallStmts, endThawStoreVatDai, collapseReturns] using hblock
  have hvatDai :
      evalExpr? config { contract := contract, locals := endThawStoreVatDai out } evmDai
        (.var "vatDai") = .ok (.int 0) := by
    have hvar :
        evalExpr? config { contract := contract, locals := endThawStoreVatDai out } evmDai
          (.var "vatDai") = .ok (.int (Int.ofNat (endThawDaiWord out).toNat)) := by
        simpa [endThawStoreVatDai] using
        endEvalExpr_varUInt256 (evm := evmDai) (locals := endThawStoreVatDai out)
          (name := "vatDai") (value := endThawDaiWord out) (by simp [endThawStoreVatDai])
    simpa [hdai] using hvar
  have hzero :
      evalExpr? config { contract := contract, locals := endThawStoreVatDai out } evmDai
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hreqDai :
      evalExpr? config { contract := contract, locals := endThawStoreVatDai out } evmDai
        (.binary .eq (.var "vatDai") (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_eq_int_true hvatDai hzero rfl
  let whenWord := Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩
  let waitWord := Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨10⟩
  have hwhen :
      evalExpr? config { contract := contract, locals := endThawStoreVatDai out } evmDai
        (.storage whenRef) = .ok (.int (Int.ofNat whenWord.toNat)) := by
      simpa [whenWord] using
      evalExpr_endThaw_when (locals := endThawStoreVatDai out) evmDai
        (by simp [endThawStoreVatDai])
  have hwait :
      evalExpr? config { contract := contract, locals := endThawStoreVatDai out } evmDai
        (.storage waitRef) = .ok (.int (Int.ofNat waitWord.toNat)) := by
      simpa [waitWord] using
      evalExpr_endThaw_wait (locals := endThawStoreVatDai out) evmDai
        (by simp [endThawStoreVatDai])
  have haddArgs :
      evalExprs? config { contract := contract, locals := endThawStoreVatDai out } evmDai
        [.storage whenRef, .storage waitRef] =
          .ok [.int (Int.ofNat whenWord.toNat), .int (Int.ofNat waitWord.toNat)] := by
    simp [evalExprs?, hwhen, hwait, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? addFunction.params
          [.int (Int.ofNat whenWord.toNat), .int (Int.ofNat waitWord.toNat)] =
        some (endUintBinaryLocals whenWord waitWord) := by
    simp [addFunction, uint256, bindParams?, endUintBinaryLocals]
  have haddStmt :
      ExecStmt config { contract := contract, locals := endThawStoreVatDai out } evmDai
        (.internalCall "add" [.storage whenRef, .storage waitRef] "deadline")
        .reverted := by
    have hbody :=
      endExecAddFunctionRevert (evm := evmDai) (x := whenWord) (y := waitWord)
        (by simpa [whenWord, waitWord] using hover)
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := endThawStoreVatDai out })
      (evm := evmDai) (name := "add") (retVar := "deadline")
      (args := [.storage whenRef, .storage waitRef])
      (argVals := [.int (Int.ofNat whenWord.toNat), .int (Int.ofNat waitWord.toNat)])
      (callee := addFunction) (locals := endUintBinaryLocals whenWord waitWord)
      haddArgs (by rfl) hbind hbody
  have htailHead :
      ExecBlock config { contract := contract, locals := endThawStoreVatDai out } evmDai
        [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
          .internalCall "add" [.storage whenRef, .storage waitRef] "deadline" ]
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqDai) ?_
    exact ExecBlock.consRevert haddStmt
  have htail :
      ExecBlock config { contract := contract, locals := endThawStoreVatDai out } evmDai
        ([ .require (.binary .eq (.var "vatDai") (.intLit 0)),
          .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
          .require (.binary .ge nowT (.var "deadline")) ] ++
        checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
        checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
          (perm := false) ++
        [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
          .assign .storage debtRef (.var "debtNew") ])
        .reverted := by
    exact execBlock_append_term
      (s2 :=
        [ .require (.binary .ge nowT (.var "deadline")) ] ++
        checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
        checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
          (perm := false) ++
        [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
          .assign .storage debtRef (.var "debtNew") ])
      htailHead (by intro f' e' h; cases h)
  simpa [evm0] using
    endThawBodyReverts_daiOkTailReverted
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g)
      (fDai := { contract := contract, locals := endThawStoreVatDai out })
      (evmDai := evmDai) hwv hlive hdebt (by simpa [evm0] using hdaiBlock) htail

theorem endThawBodyReverts_waitNotFinished {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmDai : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endThawLiveWord σ I = ⟨0⟩)
    (hdebt : endThawDebtWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endThawVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endThawVatAddr σ I)) "dai" 0
        [.address (endThawVowAddr σ I)] (true, evmDai, out) false)
    (hlo : 32 ≤ out.size)
    (hdai : endThawDaiWord out = ⟨0⟩)
    (hfit :
      (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩).toNat +
          (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨10⟩).toNat <
        UInt256.size)
    (hwait :
      (endThawTimestampWord evmDai.executionEnv).toNat <
        (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩ +
          Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨10⟩).toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (∅ : Store) thawTransition.body .reverted := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.storage vatRef) = .ok (.address (endThawVatAddr σ I)) := by
      simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawVatAddr, endThawVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endThaw_vat (locals := (∅ : Store)) evm0 (by simp)
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endThawVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [evm0] using
      endThawVatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguardDai :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hvow :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        vowAddr = .ok (.address (endThawVowAddr σ I)) := by
      simpa [vowAddr, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawVowAddr, endThawVowWord, endSlotWord, solcSlotWord] using
      evalExpr_endThaw_vow (locals := (∅ : Store)) evm0 (by simp)
  have hargs :
      evalExprs? config { contract := contract, locals := (∅ : Store) } evm0 [vowAddr] =
        .ok [.address (endThawVowAddr σ I)] := by
    simp [evalExprs?, hvow, EvalResult.bind, bind, pure]
  have hdaiBlock :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        (checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
          (perm := false))
        (.ok { contract := contract, locals := endThawStoreVatDai out } evmDai) := by
    have hblock := checkedExternalCallSuccess
      (cfg := config) (C := contract) (evm := evm0)
      (locals := (∅ : Store)) (receiver := .storage vatRef)
      (retVar := "vatDai") (name := "dai") (target := endThawVatAddr σ I)
      (sendVal := 0) (args := [vowAddr])
      (argVals := [.address (endThawVowAddr σ I)]) (out := out)
      (perm := false) hguardDai hreceiver hargs
      (by simpa [evm0] using hcall) (endThawDaiDecode_ok out hlo)
    simpa [checkedExternalCallStmts, endThawStoreVatDai, collapseReturns] using hblock
  have hvatDai :
      evalExpr? config { contract := contract, locals := endThawStoreVatDai out } evmDai
        (.var "vatDai") = .ok (.int 0) := by
    have hvar :
        evalExpr? config { contract := contract, locals := endThawStoreVatDai out } evmDai
          (.var "vatDai") = .ok (.int (Int.ofNat (endThawDaiWord out).toNat)) := by
        simpa [endThawStoreVatDai] using
        endEvalExpr_varUInt256 (evm := evmDai) (locals := endThawStoreVatDai out)
          (name := "vatDai") (value := endThawDaiWord out) (by simp [endThawStoreVatDai])
    simpa [hdai] using hvar
  have hzero :
      evalExpr? config { contract := contract, locals := endThawStoreVatDai out } evmDai
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hreqDai :
      evalExpr? config { contract := contract, locals := endThawStoreVatDai out } evmDai
        (.binary .eq (.var "vatDai") (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_eq_int_true hvatDai hzero rfl
  let whenWord := Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩
  let waitWord := Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨10⟩
  let deadlineWord := whenWord + waitWord
  have hwhen :
      evalExpr? config { contract := contract, locals := endThawStoreVatDai out } evmDai
        (.storage whenRef) = .ok (.int (Int.ofNat whenWord.toNat)) := by
      simpa [whenWord] using
      evalExpr_endThaw_when (locals := endThawStoreVatDai out) evmDai
        (by simp [endThawStoreVatDai])
  have hwaitExpr :
      evalExpr? config { contract := contract, locals := endThawStoreVatDai out } evmDai
        (.storage waitRef) = .ok (.int (Int.ofNat waitWord.toNat)) := by
      simpa [waitWord] using
      evalExpr_endThaw_wait (locals := endThawStoreVatDai out) evmDai
        (by simp [endThawStoreVatDai])
  have haddArgs :
      evalExprs? config { contract := contract, locals := endThawStoreVatDai out } evmDai
        [.storage whenRef, .storage waitRef] =
          .ok [.int (Int.ofNat whenWord.toNat), .int (Int.ofNat waitWord.toNat)] := by
    simp [evalExprs?, hwhen, hwaitExpr, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? addFunction.params
          [.int (Int.ofNat whenWord.toNat), .int (Int.ofNat waitWord.toNat)] =
        some (endUintBinaryLocals whenWord waitWord) := by
    simp [addFunction, uint256, bindParams?, endUintBinaryLocals]
  have haddStmt :
      ExecStmt config { contract := contract, locals := endThawStoreVatDai out } evmDai
        (.internalCall "add" [.storage whenRef, .storage waitRef] "deadline")
        (.ok { contract := contract, locals := endThawStoreDeadlineWord out deadlineWord }
          evmDai) := by
    have hbody :=
      endExecAddFunctionReturn (evm := evmDai) (x := whenWord) (y := waitWord)
        (sum := deadlineWord) rfl (by simpa [whenWord, waitWord] using hfit)
    have hstmt := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := endThawStoreVatDai out })
      (evm := evmDai) (name := "add") (retVar := "deadline")
      (args := [.storage whenRef, .storage waitRef])
      (argVals := [.int (Int.ofNat whenWord.toNat), .int (Int.ofNat waitWord.toNat)])
      (callee := addFunction) (locals := endUintBinaryLocals whenWord waitWord)
      haddArgs (by rfl) hbind hbody
    simpa [endThawStoreDeadlineWord, resumeAfterInternalCall, collapseReturns, deadlineWord]
      using hstmt
  have hnow :
      evalExpr? config
        { contract := contract, locals := endThawStoreDeadlineWord out deadlineWord } evmDai
        nowT = .ok (.int (Int.ofNat (endThawTimestampWord evmDai.executionEnv).toNat)) :=
    evalExpr_endThaw_timestamp (locals := endThawStoreDeadlineWord out deadlineWord) evmDai
  have hdeadline :
      evalExpr? config
        { contract := contract, locals := endThawStoreDeadlineWord out deadlineWord } evmDai
        (.var "deadline") = .ok (.int (Int.ofNat deadlineWord.toNat)) := by
      simpa [endThawStoreDeadlineWord] using
      endEvalExpr_varUInt256 (evm := evmDai)
        (locals := endThawStoreDeadlineWord out deadlineWord)
        (name := "deadline") (value := deadlineWord) (by simp [endThawStoreDeadlineWord])
  have hreqWait :
      evalExpr? config
        { contract := contract, locals := endThawStoreDeadlineWord out deadlineWord } evmDai
        (.binary .ge nowT (.var "deadline")) = .ok (.bool false) := by
    exact endThawEvalExpr_ge_uint256_false hnow hdeadline (by simpa [deadlineWord] using hwait)
  have htailHead :
      ExecBlock config { contract := contract, locals := endThawStoreVatDai out } evmDai
        [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
          .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
          .require (.binary .ge nowT (.var "deadline")) ]
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqDai) ?_
    refine ExecBlock.consNormal haddStmt ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqWait)
  have htail :
      ExecBlock config { contract := contract, locals := endThawStoreVatDai out } evmDai
        ([ .require (.binary .eq (.var "vatDai") (.intLit 0)),
          .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
          .require (.binary .ge nowT (.var "deadline")) ] ++
        checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
        checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
          (perm := false) ++
        [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
          .assign .storage debtRef (.var "debtNew") ])
        .reverted := by
    exact execBlock_append_term
      (s2 :=
        checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
        checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
          (perm := false) ++
        [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
          .assign .storage debtRef (.var "debtNew") ])
      htailHead (by intro f' e' h; cases h)
  simpa [evm0] using
    endThawBodyReverts_daiOkTailReverted
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g)
      (fDai := { contract := contract, locals := endThawStoreVatDai out })
      (evmDai := evmDai) hwv hlive hdebt (by simpa [evm0] using hdaiBlock) htail

theorem endThawTailReadyPrefix (evmDai : EVM.State) (out : ByteArray)
    (hdai : endThawDaiWord out = ⟨0⟩)
    (hfit :
      (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩).toNat +
          (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨10⟩).toNat <
        UInt256.size)
    (hready :
      (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩ +
          Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨10⟩).toNat ≤
        (endThawTimestampWord evmDai.executionEnv).toNat) :
    let whenWord := Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩
    let waitWord := Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨10⟩
    let deadlineWord := whenWord + waitWord
    ExecBlock config { contract := contract, locals := endThawStoreVatDai out } evmDai
      [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
        .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
        .require (.binary .ge nowT (.var "deadline")) ]
      (.ok { contract := contract, locals := endThawStoreDeadlineWord out deadlineWord }
        evmDai) := by
  intro whenWord waitWord deadlineWord
  have hvatDai :
      evalExpr? config { contract := contract, locals := endThawStoreVatDai out } evmDai
        (.var "vatDai") = .ok (.int 0) := by
    have hvar :
        evalExpr? config { contract := contract, locals := endThawStoreVatDai out } evmDai
          (.var "vatDai") = .ok (.int (Int.ofNat (endThawDaiWord out).toNat)) := by
        simpa [endThawStoreVatDai] using
        endEvalExpr_varUInt256 (evm := evmDai) (locals := endThawStoreVatDai out)
          (name := "vatDai") (value := endThawDaiWord out) (by simp [endThawStoreVatDai])
    simpa [hdai] using hvar
  have hzero :
      evalExpr? config { contract := contract, locals := endThawStoreVatDai out } evmDai
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hreqDai :
      evalExpr? config { contract := contract, locals := endThawStoreVatDai out } evmDai
        (.binary .eq (.var "vatDai") (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_eq_int_true hvatDai hzero rfl
  have hwhen :
      evalExpr? config { contract := contract, locals := endThawStoreVatDai out } evmDai
        (.storage whenRef) = .ok (.int (Int.ofNat whenWord.toNat)) := by
      simpa [whenWord] using
      evalExpr_endThaw_when (locals := endThawStoreVatDai out) evmDai
        (by simp [endThawStoreVatDai])
  have hwaitExpr :
      evalExpr? config { contract := contract, locals := endThawStoreVatDai out } evmDai
        (.storage waitRef) = .ok (.int (Int.ofNat waitWord.toNat)) := by
      simpa [waitWord] using
      evalExpr_endThaw_wait (locals := endThawStoreVatDai out) evmDai
        (by simp [endThawStoreVatDai])
  have haddArgs :
      evalExprs? config { contract := contract, locals := endThawStoreVatDai out } evmDai
        [.storage whenRef, .storage waitRef] =
          .ok [.int (Int.ofNat whenWord.toNat), .int (Int.ofNat waitWord.toNat)] := by
    simp [evalExprs?, hwhen, hwaitExpr, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? addFunction.params
          [.int (Int.ofNat whenWord.toNat), .int (Int.ofNat waitWord.toNat)] =
        some (endUintBinaryLocals whenWord waitWord) := by
    simp [addFunction, uint256, bindParams?, endUintBinaryLocals]
  have haddStmt :
      ExecStmt config { contract := contract, locals := endThawStoreVatDai out } evmDai
        (.internalCall "add" [.storage whenRef, .storage waitRef] "deadline")
        (.ok { contract := contract, locals := endThawStoreDeadlineWord out deadlineWord }
          evmDai) := by
    have hbody :=
      endExecAddFunctionReturn (evm := evmDai) (x := whenWord) (y := waitWord)
        (sum := deadlineWord) rfl (by simpa [whenWord, waitWord] using hfit)
    have hstmt := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := endThawStoreVatDai out })
      (evm := evmDai) (name := "add") (retVar := "deadline")
      (args := [.storage whenRef, .storage waitRef])
      (argVals := [.int (Int.ofNat whenWord.toNat), .int (Int.ofNat waitWord.toNat)])
      (callee := addFunction) (locals := endUintBinaryLocals whenWord waitWord)
      haddArgs (by rfl) hbind hbody
    simpa [endThawStoreDeadlineWord, resumeAfterInternalCall, collapseReturns, deadlineWord]
      using hstmt
  have hnow :
      evalExpr? config
        { contract := contract, locals := endThawStoreDeadlineWord out deadlineWord } evmDai
        nowT = .ok (.int (Int.ofNat (endThawTimestampWord evmDai.executionEnv).toNat)) :=
    evalExpr_endThaw_timestamp (locals := endThawStoreDeadlineWord out deadlineWord) evmDai
  have hdeadline :
      evalExpr? config
        { contract := contract, locals := endThawStoreDeadlineWord out deadlineWord } evmDai
        (.var "deadline") = .ok (.int (Int.ofNat deadlineWord.toNat)) := by
      simpa [endThawStoreDeadlineWord] using
      endEvalExpr_varUInt256 (evm := evmDai)
        (locals := endThawStoreDeadlineWord out deadlineWord)
        (name := "deadline") (value := deadlineWord) (by simp [endThawStoreDeadlineWord])
  have hreqReady :
      evalExpr? config
        { contract := contract, locals := endThawStoreDeadlineWord out deadlineWord } evmDai
        (.binary .ge nowT (.var "deadline")) = .ok (.bool true) :=
    endEvalExpr_ge_uint256_true hnow hdeadline (by simpa [deadlineWord] using hready)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqDai) ?_
  refine ExecBlock.consNormal haddStmt ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hreqReady) ExecBlock.nil

theorem endThawVatCode_zero_of_state {evm : EVM.State}
    (hzero :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
          (endThawVatWord evm.accountMap evm.executionEnv) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (endThawVatAddr evm.accountMap evm.executionEnv)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  simpa [State.lookupAccount] using
    endUniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := evm.accountMap) (target := endThawVatWord evm.accountMap evm.executionEnv)
      (addr := endThawVatAddr evm.accountMap evm.executionEnv)
      (endThawVatAddr_eq_ofUInt256 evm.accountMap evm.executionEnv) hzero

theorem endThawVatCode_pos_of_state {evm : EVM.State}
    (hne :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
          (endThawVatWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((evm.lookupAccount (endThawVatAddr evm.accountMap evm.executionEnv)).option 0
        (fun acc => acc.code.size))).toNat := by
  simpa [State.lookupAccount] using
    endUniswapExtCodeSizeWord_ne_zero_lookup_code_pos
      (σ := evm.accountMap) (target := endThawVatWord evm.accountMap evm.executionEnv)
      (addr := endThawVatAddr evm.accountMap evm.executionEnv)
      (endThawVatAddr_eq_ofUInt256 evm.accountMap evm.executionEnv) hne

theorem endThawCureCode_zero_of_state {evm : EVM.State}
    (hzero :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
          (endThawCureWord evm.accountMap evm.executionEnv) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (endThawCureAddr evm.accountMap evm.executionEnv)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  simpa [State.lookupAccount] using
    endUniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := evm.accountMap) (target := endThawCureWord evm.accountMap evm.executionEnv)
      (addr := endThawCureAddr evm.accountMap evm.executionEnv)
      (endThawCureAddr_eq_ofUInt256 evm.accountMap evm.executionEnv) hzero

theorem endThawCureCode_pos_of_state {evm : EVM.State}
    (hne :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
          (endThawCureWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((evm.lookupAccount (endThawCureAddr evm.accountMap evm.executionEnv)).option 0
        (fun acc => acc.code.size))).toNat := by
  simpa [State.lookupAccount] using
    endUniswapExtCodeSizeWord_ne_zero_lookup_code_pos
      (σ := evm.accountMap) (target := endThawCureWord evm.accountMap evm.executionEnv)
      (addr := endThawCureAddr evm.accountMap evm.executionEnv)
      (endThawCureAddr_eq_ofUInt256 evm.accountMap evm.executionEnv) hne

theorem evalStorageRef_endThaw_debt_of_locals {locals : Store}
    (_hbase : locals.get? "debt" = none) (evm : EVM.State) :
    evalStorageRef config { contract := contract, locals := locals } evm
      debtRef = .ok endThawDebtEvaledRef := by
  simp [endThawDebtEvaledRef, debtRef, evalStorageRef, evalStorageRefSteps,
    EvalResult.bind, pure, bind]

def endThawPostState (evm : EVM.State) (debtNew : UInt256) : EVM.State :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨11⟩ debtNew

theorem endThawAssignDebt {locals : Store} (evm : EVM.State) (debtNew : UInt256)
    (hbase : locals.get? "debt" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage debtRef (.int (Int.ofNat debtNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, endThawPostState evm debtNew) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := endThawDebtEvaledRef)
      (loc := wordLoc ⟨11⟩)
      (hbase := hbase)
      (her := evalStorageRef_endThaw_debt_of_locals hbase evm)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (by simpa [endThawPostState] using endStorageLocStore_uint256 evm ⟨11⟩ debtNew)

theorem endThawCheckedDebtNoCode (evm : EVM.State) (out : ByteArray)
    (deadline : UInt256)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (endThawVatWord evm.accountMap evm.executionEnv) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endThawStoreDeadlineWord out deadline }
      evm (checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt")
      .reverted := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := endThawStoreDeadlineWord out deadline }
        evm (.storage vatRef) =
          .ok (.address (endThawVatAddr evm.accountMap evm.executionEnv)) := by
      simpa [endThawVatAddr, endThawVatWord, endSlotWord, solcSlotWord,
      Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_endThaw_vat (locals := endThawStoreDeadlineWord out deadline) evm
        (by simp [endThawStoreDeadlineWord, endThawStoreVatDai])
  have hguard :
      evalExpr? config { contract := contract, locals := endThawStoreDeadlineWord out deadline }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver (endThawVatCode_zero_of_state hcodeSize)
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := endThawStoreDeadlineWord out deadline) (receiver := .storage vatRef)
      (retVar := "vatDebt") (name := "debt") (sendVal := 0) (args := [])
      (perm := true) hguard

theorem endThawCheckedDebtFailure {evm evm' : EVM.State} {out debtOut : ByteArray}
    {deadline : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (endThawVatWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (endThawVatAddr evm.accountMap evm.executionEnv)) "debt" 0 []
        (false, evm', debtOut) true) :
    ExecBlock config { contract := contract, locals := endThawStoreDeadlineWord out deadline }
      evm (checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt")
      .reverted := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := endThawStoreDeadlineWord out deadline }
        evm (.storage vatRef) =
          .ok (.address (endThawVatAddr evm.accountMap evm.executionEnv)) := by
      simpa [endThawVatAddr, endThawVatWord, endSlotWord, solcSlotWord,
      Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_endThaw_vat (locals := endThawStoreDeadlineWord out deadline) evm
        (by simp [endThawStoreDeadlineWord, endThawStoreVatDai])
  have hguard :
      evalExpr? config { contract := contract, locals := endThawStoreDeadlineWord out deadline }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver (endThawVatCode_pos_of_state hcodeSize)
  have hargs :
      evalExprs? config { contract := contract, locals := endThawStoreDeadlineWord out deadline }
        evm [] = .ok [] := by
    rfl
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := endThawStoreDeadlineWord out deadline) (receiver := .storage vatRef)
      (retVar := "vatDebt") (name := "debt")
      (target := endThawVatAddr evm.accountMap evm.executionEnv)
      (sendVal := 0) (args := []) (argVals := []) (out := debtOut) (perm := true)
      hguard hreceiver hargs hcall

theorem endThawCheckedDebtDecodeRevert {evm evm' : EVM.State} {out debtOut : ByteArray}
    {deadline : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (endThawVatWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (endThawVatAddr evm.accountMap evm.executionEnv)) "debt" 0 []
        (true, evm', debtOut) true)
    (hshort : debtOut.size < 32) :
    ExecBlock config { contract := contract, locals := endThawStoreDeadlineWord out deadline }
      evm (checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt")
      .reverted := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := endThawStoreDeadlineWord out deadline }
        evm (.storage vatRef) =
          .ok (.address (endThawVatAddr evm.accountMap evm.executionEnv)) := by
      simpa [endThawVatAddr, endThawVatWord, endSlotWord, solcSlotWord,
      Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_endThaw_vat (locals := endThawStoreDeadlineWord out deadline) evm
        (by simp [endThawStoreDeadlineWord, endThawStoreVatDai])
  have hguard :
      evalExpr? config { contract := contract, locals := endThawStoreDeadlineWord out deadline }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver (endThawVatCode_pos_of_state hcodeSize)
  have hargs :
      evalExprs? config { contract := contract, locals := endThawStoreDeadlineWord out deadline }
        evm [] = .ok [] := by
    rfl
  simpa [checkedExternalCallStmts] using
    checkedExternalCallDecodeRevert
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := endThawStoreDeadlineWord out deadline) (receiver := .storage vatRef)
      (retVar := "vatDebt") (name := "debt")
      (target := endThawVatAddr evm.accountMap evm.executionEnv)
      (sendVal := 0) (args := []) (argVals := []) (out := debtOut) (perm := true)
      hguard hreceiver hargs hcall (endThawDebtDecode_short debtOut hshort)

theorem endThawCheckedDebtSuccess {evm evm' : EVM.State} {out debtOut : ByteArray}
    {deadline : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (endThawVatWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (endThawVatAddr evm.accountMap evm.executionEnv)) "debt" 0 []
        (true, evm', debtOut) true)
    (hlo : 32 ≤ debtOut.size) :
    ExecBlock config { contract := contract, locals := endThawStoreDeadlineWord out deadline }
      evm (checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt")
      (.ok { contract := contract, locals := endThawStoreVatDebt out debtOut deadline }
        evm') := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := endThawStoreDeadlineWord out deadline }
        evm (.storage vatRef) =
          .ok (.address (endThawVatAddr evm.accountMap evm.executionEnv)) := by
      simpa [endThawVatAddr, endThawVatWord, endSlotWord, solcSlotWord,
      Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_endThaw_vat (locals := endThawStoreDeadlineWord out deadline) evm
        (by simp [endThawStoreDeadlineWord, endThawStoreVatDai])
  have hguard :
      evalExpr? config { contract := contract, locals := endThawStoreDeadlineWord out deadline }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver (endThawVatCode_pos_of_state hcodeSize)
  have hargs :
      evalExprs? config { contract := contract, locals := endThawStoreDeadlineWord out deadline }
        evm [] = .ok [] := by
    rfl
  have hblock :=
    checkedExternalCallSuccess
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := endThawStoreDeadlineWord out deadline) (receiver := .storage vatRef)
      (retVar := "vatDebt") (name := "debt")
      (target := endThawVatAddr evm.accountMap evm.executionEnv)
      (sendVal := 0) (args := []) (argVals := []) (out := debtOut) (perm := true)
      (value := [.int (Int.ofNat (endThawReturnWord debtOut).toNat)])
      hguard hreceiver hargs hcall (endThawDebtDecode_ok debtOut hlo)
  simpa [checkedExternalCallStmts, endThawStoreVatDebt, collapseReturns] using hblock

theorem endThawCheckedTellNoCode (evm : EVM.State) (out debtOut : ByteArray)
    (deadline : UInt256)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (endThawCureWord evm.accountMap evm.executionEnv) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endThawStoreVatDebt out debtOut deadline }
      evm (checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
        (perm := false)) .reverted := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := endThawStoreVatDebt out debtOut deadline }
        evm (.storage cureRef) =
          .ok (.address (endThawCureAddr evm.accountMap evm.executionEnv)) := by
      simpa [endThawCureAddr, endThawCureWord, endSlotWord, solcSlotWord,
      Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_endThaw_cure (locals := endThawStoreVatDebt out debtOut deadline) evm
        (by simp [endThawStoreVatDebt, endThawStoreDeadlineWord, endThawStoreVatDai])
  have hguard :
      evalExpr? config { contract := contract, locals := endThawStoreVatDebt out debtOut deadline }
        evm (.binary .gt (.extCodeSize (.storage cureRef)) (.intLit 0)) =
          .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver (endThawCureCode_zero_of_state hcodeSize)
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := endThawStoreVatDebt out debtOut deadline) (receiver := .storage cureRef)
      (retVar := "cureTell") (name := "tell") (sendVal := 0) (args := [])
      (perm := false) hguard

theorem endThawCheckedTellFailure {evm evm' : EVM.State}
    {out debtOut tellOut : ByteArray} {deadline : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (endThawCureWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (endThawCureAddr evm.accountMap evm.executionEnv)) "tell" 0 []
        (false, evm', tellOut) false) :
    ExecBlock config { contract := contract, locals := endThawStoreVatDebt out debtOut deadline }
      evm (checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
        (perm := false)) .reverted := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := endThawStoreVatDebt out debtOut deadline }
        evm (.storage cureRef) =
          .ok (.address (endThawCureAddr evm.accountMap evm.executionEnv)) := by
      simpa [endThawCureAddr, endThawCureWord, endSlotWord, solcSlotWord,
      Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_endThaw_cure (locals := endThawStoreVatDebt out debtOut deadline) evm
        (by simp [endThawStoreVatDebt, endThawStoreDeadlineWord, endThawStoreVatDai])
  have hguard :
      evalExpr? config { contract := contract, locals := endThawStoreVatDebt out debtOut deadline }
        evm (.binary .gt (.extCodeSize (.storage cureRef)) (.intLit 0)) =
          .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver (endThawCureCode_pos_of_state hcodeSize)
  have hargs :
      evalExprs? config { contract := contract, locals := endThawStoreVatDebt out debtOut deadline }
        evm [] = .ok [] := by
    rfl
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := endThawStoreVatDebt out debtOut deadline) (receiver := .storage cureRef)
      (retVar := "cureTell") (name := "tell")
      (target := endThawCureAddr evm.accountMap evm.executionEnv)
      (sendVal := 0) (args := []) (argVals := []) (out := tellOut) (perm := false)
      hguard hreceiver hargs hcall

theorem endThawCheckedTellDecodeRevert {evm evm' : EVM.State}
    {out debtOut tellOut : ByteArray} {deadline : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (endThawCureWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (endThawCureAddr evm.accountMap evm.executionEnv)) "tell" 0 []
        (true, evm', tellOut) false)
    (hshort : tellOut.size < 32) :
    ExecBlock config { contract := contract, locals := endThawStoreVatDebt out debtOut deadline }
      evm (checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
        (perm := false)) .reverted := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := endThawStoreVatDebt out debtOut deadline }
        evm (.storage cureRef) =
          .ok (.address (endThawCureAddr evm.accountMap evm.executionEnv)) := by
      simpa [endThawCureAddr, endThawCureWord, endSlotWord, solcSlotWord,
      Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_endThaw_cure (locals := endThawStoreVatDebt out debtOut deadline) evm
        (by simp [endThawStoreVatDebt, endThawStoreDeadlineWord, endThawStoreVatDai])
  have hguard :
      evalExpr? config { contract := contract, locals := endThawStoreVatDebt out debtOut deadline }
        evm (.binary .gt (.extCodeSize (.storage cureRef)) (.intLit 0)) =
          .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver (endThawCureCode_pos_of_state hcodeSize)
  have hargs :
      evalExprs? config { contract := contract, locals := endThawStoreVatDebt out debtOut deadline }
        evm [] = .ok [] := by
    rfl
  simpa [checkedExternalCallStmts] using
    checkedExternalCallDecodeRevert
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := endThawStoreVatDebt out debtOut deadline) (receiver := .storage cureRef)
      (retVar := "cureTell") (name := "tell")
      (target := endThawCureAddr evm.accountMap evm.executionEnv)
      (sendVal := 0) (args := []) (argVals := []) (out := tellOut) (perm := false)
      hguard hreceiver hargs hcall (endThawTellDecode_short tellOut hshort)

theorem endThawCheckedTellSuccess {evm evm' : EVM.State}
    {out debtOut tellOut : ByteArray} {deadline : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (endThawCureWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (endThawCureAddr evm.accountMap evm.executionEnv)) "tell" 0 []
        (true, evm', tellOut) false)
    (hlo : 32 ≤ tellOut.size) :
    ExecBlock config { contract := contract, locals := endThawStoreVatDebt out debtOut deadline }
      evm (checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
        (perm := false))
      (.ok { contract := contract, locals := endThawStoreCureTell out debtOut tellOut deadline }
        evm') := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := endThawStoreVatDebt out debtOut deadline }
        evm (.storage cureRef) =
          .ok (.address (endThawCureAddr evm.accountMap evm.executionEnv)) := by
      simpa [endThawCureAddr, endThawCureWord, endSlotWord, solcSlotWord,
      Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_endThaw_cure (locals := endThawStoreVatDebt out debtOut deadline) evm
        (by simp [endThawStoreVatDebt, endThawStoreDeadlineWord, endThawStoreVatDai])
  have hguard :
      evalExpr? config { contract := contract, locals := endThawStoreVatDebt out debtOut deadline }
        evm (.binary .gt (.extCodeSize (.storage cureRef)) (.intLit 0)) =
          .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver (endThawCureCode_pos_of_state hcodeSize)
  have hargs :
      evalExprs? config { contract := contract, locals := endThawStoreVatDebt out debtOut deadline }
        evm [] = .ok [] := by
    rfl
  have hblock :=
    checkedExternalCallSuccess
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := endThawStoreVatDebt out debtOut deadline) (receiver := .storage cureRef)
      (retVar := "cureTell") (name := "tell")
      (target := endThawCureAddr evm.accountMap evm.executionEnv)
      (sendVal := 0) (args := []) (argVals := []) (out := tellOut) (perm := false)
      (value := [.int (Int.ofNat (endThawReturnWord tellOut).toNat)])
      hguard hreceiver hargs hcall (endThawTellDecode_ok tellOut hlo)
  simpa [checkedExternalCallStmts, endThawStoreCureTell, collapseReturns] using hblock

theorem endThawTailSubUnderflow (evm : EVM.State) (out debtOut tellOut : ByteArray)
    (deadline : UInt256)
    (hlt : (endThawReturnWord debtOut).toNat < (endThawReturnWord tellOut).toNat) :
    let locals := endThawStoreCureTell out debtOut tellOut deadline
    ExecBlock config { contract := contract, locals := locals } evm
      [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
        .assign .storage debtRef (.var "debtNew") ]
      .reverted := by
  intro locals
  have hvatDebt :
      evalExpr? config { contract := contract, locals := locals } evm
        (.var "vatDebt") = .ok (.int (Int.ofNat (endThawReturnWord debtOut).toNat)) := by
      simpa [endThawStoreVatDebt] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := locals)
        (name := "vatDebt") (value := endThawReturnWord debtOut)
        (by
          dsimp [locals, endThawStoreCureTell]
          simpa [Std.HashMap.get?_eq_getElem?, endThawStoreVatDebt] using
            store_get_ne (endThawStoreVatDebt out debtOut deadline)
              (k := "cureTell") (a := "vatDebt")
              (.int (Int.ofNat (endThawReturnWord tellOut).toNat)) (by decide +native))
  have hcureTell :
      evalExpr? config { contract := contract, locals := locals } evm
        (.var "cureTell") = .ok (.int (Int.ofNat (endThawReturnWord tellOut).toNat)) := by
      simpa [locals, endThawStoreCureTell] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endThawStoreCureTell out debtOut tellOut deadline)
        (name := "cureTell") (value := endThawReturnWord tellOut)
        (by simp [endThawStoreCureTell])
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm
        [.var "vatDebt", .var "cureTell"] =
          .ok [.int (Int.ofNat (endThawReturnWord debtOut).toNat),
            .int (Int.ofNat (endThawReturnWord tellOut).toNat)] := by
    simp [evalExprs?, hvatDebt, hcureTell, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? subFunction.params
          [.int (Int.ofNat (endThawReturnWord debtOut).toNat),
            .int (Int.ofNat (endThawReturnWord tellOut).toNat)] =
        some (endUintBinaryLocals (endThawReturnWord debtOut) (endThawReturnWord tellOut)) := by
    simp [subFunction, uint256, bindParams?, endUintBinaryLocals]
  have hstmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew")
        .reverted := by
    have hbody := endExecSubFunctionRevert (evm := evm)
      (x := endThawReturnWord debtOut) (y := endThawReturnWord tellOut) hlt
    exact internalCallFunctionRevert
      (cfg := config)
      (caller := { contract := contract, locals := locals })
      (evm := evm) (name := "sub") (retVar := "debtNew")
      (args := [.var "vatDebt", .var "cureTell"])
      (argVals :=
        [.int (Int.ofNat (endThawReturnWord debtOut).toNat),
          .int (Int.ofNat (endThawReturnWord tellOut).toNat)])
      (callee := subFunction)
      (locals := endUintBinaryLocals (endThawReturnWord debtOut) (endThawReturnWord tellOut))
      hargs (by rfl) hbind hbody
  exact ExecBlock.consRevert hstmt

theorem endThawTailSubAssign (evm : EVM.State) (out debtOut tellOut : ByteArray)
    (deadline : UInt256)
    (hle : (endThawReturnWord tellOut).toNat ≤ (endThawReturnWord debtOut).toNat) :
    let debtNew := UInt256.sub (endThawReturnWord debtOut) (endThawReturnWord tellOut)
    let locals := endThawStoreCureTell out debtOut tellOut deadline
    let postLocals := endThawStoreDebtNew out debtOut tellOut deadline debtNew
    ExecBlock config { contract := contract, locals := locals } evm
      [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
        .assign .storage debtRef (.var "debtNew") ]
      (.ok { contract := contract, locals := postLocals }
        (endThawPostState evm debtNew)) := by
  intro debtNew locals postLocals
  have hvatDebt :
      evalExpr? config { contract := contract, locals := locals } evm
        (.var "vatDebt") = .ok (.int (Int.ofNat (endThawReturnWord debtOut).toNat)) := by
      simpa [endThawStoreVatDebt] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := locals)
        (name := "vatDebt") (value := endThawReturnWord debtOut)
        (by
          dsimp [locals, endThawStoreCureTell]
          simpa [Std.HashMap.get?_eq_getElem?, endThawStoreVatDebt] using
            store_get_ne (endThawStoreVatDebt out debtOut deadline)
              (k := "cureTell") (a := "vatDebt")
              (.int (Int.ofNat (endThawReturnWord tellOut).toNat)) (by decide +native))
  have hcureTell :
      evalExpr? config { contract := contract, locals := locals } evm
        (.var "cureTell") = .ok (.int (Int.ofNat (endThawReturnWord tellOut).toNat)) := by
      simpa [locals, endThawStoreCureTell] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endThawStoreCureTell out debtOut tellOut deadline)
        (name := "cureTell") (value := endThawReturnWord tellOut)
        (by simp [endThawStoreCureTell])
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm
        [.var "vatDebt", .var "cureTell"] =
          .ok [.int (Int.ofNat (endThawReturnWord debtOut).toNat),
            .int (Int.ofNat (endThawReturnWord tellOut).toNat)] := by
    simp [evalExprs?, hvatDebt, hcureTell, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? subFunction.params
          [.int (Int.ofNat (endThawReturnWord debtOut).toNat),
            .int (Int.ofNat (endThawReturnWord tellOut).toNat)] =
        some (endUintBinaryLocals (endThawReturnWord debtOut) (endThawReturnWord tellOut)) := by
    simp [subFunction, uint256, bindParams?, endUintBinaryLocals]
  have hsubStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew")
        (.ok { contract := contract, locals := postLocals } evm) := by
    have hbody := endExecSubFunctionReturn (evm := evm)
      (x := endThawReturnWord debtOut) (y := endThawReturnWord tellOut)
      (diff := debtNew) rfl hle
    have hstmt := internalCallFunctionReturn
      (cfg := config)
      (caller := { contract := contract, locals := locals })
      (evm := evm) (name := "sub") (retVar := "debtNew")
      (args := [.var "vatDebt", .var "cureTell"])
      (argVals :=
        [.int (Int.ofNat (endThawReturnWord debtOut).toNat),
          .int (Int.ofNat (endThawReturnWord tellOut).toNat)])
      (callee := subFunction)
      (locals := endUintBinaryLocals (endThawReturnWord debtOut) (endThawReturnWord tellOut))
      hargs (by rfl) hbind hbody
    simpa [locals, postLocals, endThawStoreDebtNew, resumeAfterInternalCall, collapseReturns,
      debtNew] using hstmt
  have hdebtNew :
      evalExpr? config { contract := contract, locals := postLocals } evm
        (.var "debtNew") = .ok (.int (Int.ofNat debtNew.toNat)) := by
      simpa [postLocals, endThawStoreDebtNew] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endThawStoreDebtNew out debtOut tellOut deadline debtNew)
        (name := "debtNew") (value := debtNew) (by simp [endThawStoreDebtNew])
  have hassign :
      assignStorageRef? config
        { contract := contract, locals := postLocals }
        evm .storage debtRef (.int (Int.ofNat debtNew.toNat)) =
          .ok ({ contract := contract, locals := postLocals },
            endThawPostState evm debtNew) := by
    simpa [postLocals] using
      endThawAssignDebt (locals := postLocals) evm debtNew
        (by
          simp [Std.HashMap.get?_eq_getElem?, postLocals, endThawStoreDebtNew,
            endThawStoreCureTell, endThawStoreVatDebt, endThawStoreDeadlineWord,
            endThawStoreVatDai])
  refine ExecBlock.consNormal hsubStmt ?_
  exact ExecBlock.consNormal (ExecStmt.assign hdebtNew hassign) ExecBlock.nil

theorem endThawBodyReturns_daiOkTail {cA gh bl σ σ₀ A I} {g : UInt256}
    {fDai fPost : Frame} {evmDai evmPost : EVM.State}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endThawLiveWord σ I = ⟨0⟩)
    (hdebt : endThawDebtWord σ I = ⟨0⟩)
    (hdaiBlock :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        (checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
          (perm := false)) (.ok fDai evmDai))
    (htail :
      ExecBlock config fDai evmDai
        ([ .require (.binary .eq (.var "vatDai") (.intLit 0)),
          .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
          .require (.binary .ge nowT (.var "deadline")) ] ++
        checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
        checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
          (perm := false) ++
        [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
          .assign .storage debtRef (.var "debtNew") ])
        (.ok fPost evmPost)) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (∅ : Store) thawTransition.body
      (.returned fPost evmPost none) := by
  intro evm0
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawLiveWord, endSlotWord, solcSlotWord] using hlive
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawDebtWord, endSlotWord, solcSlotWord] using hdebt
  have hguardLive :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.storage liveRef) = .ok (.int 0) := by
        rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := (∅ : Store) })
        (slot := liveRef)
        (er := endThawLiveEvaledRef)
        (t := .int uint256Int)
        (loc := wordLoc ⟨8⟩)
        (value := .int 0)
        (hbase := by simp [liveRef])
        (her := evalStorageRef_endThaw_live evm0)
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by simpa [hliveLoad] using endStorageLocLoad_uint256 evm0 ⟨8⟩)]
    have hzero :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.intLit 0) = .ok (.int 0) := by
        simp [evalExpr?, pure]
    exact endEvalExpr_eq_int_true hstorage hzero rfl
  have hguardDebt :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .eq (.storage debtRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.storage debtRef) = .ok (.int 0) := by
        rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := (∅ : Store) })
        (slot := debtRef)
        (er := endThawDebtEvaledRef)
        (t := .int uint256Int)
        (loc := wordLoc ⟨11⟩)
        (value := .int 0)
        (hbase := by simp [debtRef])
        (her := evalStorageRef_endThaw_debt evm0)
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by simpa [hdebtLoad] using endStorageLocLoad_uint256 evm0 ⟨11⟩)]
    have hzero :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.intLit 0) = .ok (.int 0) := by
        simp [evalExpr?, pure]
    exact endEvalExpr_eq_int_true hstorage hzero rfl
  have hdaiWithTail :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        (checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
          (perm := false) ++
          [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
            .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
            .require (.binary .ge nowT (.var "deadline")) ] ++
          checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
          checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
            (perm := false) ++
          [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
            .assign .storage debtRef (.var "debtNew") ])
        (.ok fPost evmPost) := by
    exact execBlock_append
      (s2 :=
          [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
            .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
            .require (.binary .ge nowT (.var "deadline")) ] ++
          checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
          checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
            (perm := false) ++
          [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
            .assign .storage debtRef (.var "debtNew") ])
      (by simpa [evm0] using hdaiBlock) htail
  have hblock :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        thawTransition.body (.ok fPost evmPost) := by
    simp only [thawTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardDebt) ?_
    simpa [checkedExternalCallStmts, List.append_assoc] using hdaiWithTail
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockOK hblock

theorem endThaw_EVM_address_id (a : AccountAddress) : EVM.address a = a := by
  apply Fin.ext
  show ↑a % EVM.twoPow 160 = ↑a
  rw [Nat.mod_eq_of_lt]
  exact a.isLt

theorem endThawVatAddr_source_eq_evmWord {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    EVM.address (endThawVatAddr τ I) = AccountAddress.ofUInt256 (endThawVatWord σ I) := by
  have hword : endThawVatWord σ I = endThawVatWord τ I :=
    endThawVatWord_accountMapEquiv hAccounts
  rw [hword]
  rw [endThawVatAddr_eq_ofUInt256]
  exact endThaw_EVM_address_id (AccountAddress.ofUInt256 (endThawVatWord τ I))

theorem endThawCureAddr_source_eq_evmWord {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    EVM.address (endThawCureAddr τ I) = AccountAddress.ofUInt256 (endThawCureWord σ I) := by
  have hword : endThawCureWord σ I = endThawCureWord τ I :=
    endThawCureWord_accountMapEquiv hAccounts
  rw [hword]
  rw [endThawCureAddr_eq_ofUInt256]
  exact endThaw_EVM_address_id (AccountAddress.ofUInt256 (endThawCureWord τ I))

theorem endThawDebtCallMadeBridge {evmE evmS : EVM.State}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {A' Ain : Substate} {z : Bool} {out : ByteArray} {g'' callGas : UInt256}
    {mem : ByteArray}
    (hmem : mem.size = 164)
    (hdepth : evmE.executionEnv.depth ≠ 1024)
    (hΘ : (cA', σ', g'', A', z, out) =
        Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes evmE.createdAccounts
          evmE.genesisBlockHeader evmE.blocks evmE.accountMap evmE.σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner))
          evmE.executionEnv.sender
          (AccountAddress.ofUInt256 (endThawVatWord evmE.accountMap evmE.executionEnv))
          (toExecute evmE.accountMap
            (AccountAddress.ofUInt256 (endThawVatWord evmE.accountMap evmE.executionEnv)))
          callGas (UInt256.ofNat evmE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((endThawNoArgCalldataMem endThawDebtSelectorWord mem).readWithPadding
            endThawNoArgOutPtr.toNat endThawNoArgInSize.toNat)
          (evmE.executionEnv.depth + 1) evmE.executionEnv.header true)
    (hState : EVMStateEquiv evmE evmS)
    (hOriginalAccounts : evmE.σ₀ = evmS.σ₀)
    (hGenesis : evmS.genesisBlockHeader = evmE.genesisBlockHeader)
    (hBlocks : evmS.blocks = evmE.blocks) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM config evmS
        (EVM.address (endThawVatAddr evmS.accountMap evmS.executionEnv))
        "debt" 0 [] (z,
          { evmS with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          out) true ∧
      EVMStateEquiv
        { evmE with accountMap := σ', substate := A', createdAccounts := cA' }
        { evmS with
            accountMap := σ'_solm
            substate := A'_solm
            createdAccounts := cA' } := by
  have htgt :
      EVM.address (endThawVatAddr evmS.accountMap evmS.executionEnv) =
        AccountAddress.ofUInt256 (endThawVatWord evmE.accountMap evmE.executionEnv) := by
    rw [hState.executionEnv]
    exact endThawVatAddr_source_eq_evmWord hState.accountMap
  obtain ⟨σ'_solm, A'_solm, hcall, hAccountsPost, hSubstate⟩ :=
    endCallMade_accountMapEquiv_with_substate
      (cfg := config) (evm_evm := evmE) (evm_solm := evmS)
      (tgt := EVM.address (endThawVatAddr evmS.accountMap evmS.executionEnv))
      (targetWord := endThawVatWord evmE.accountMap evmE.executionEnv)
      (name := "debt") (args := [])
      (cA' := cA') (σ' := σ') (A' := A') (A_in := Ain)
      (z := z) (out := out) (g'' := g'') (callGas := callGas)
      (mem := endThawNoArgCalldataMem endThawDebtSelectorWord mem)
      (inOff := endThawNoArgOutPtr) (inSize := endThawNoArgInSize)
      (callPerm := true)
      hdepth htgt (endThawDebtEncode_eq hmem) hΘ hState.accountMap
      hOriginalAccounts hState.createdAccounts.symm hGenesis hBlocks hState.executionEnv.symm
  refine ⟨σ'_solm, A'_solm, hcall, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [hState.executionEnv]
  · rfl
  · exact hAccountsPost

theorem endThawTellCallMadeBridge {evmE evmS : EVM.State}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {A' Ain : Substate} {z : Bool} {out : ByteArray} {g'' callGas : UInt256}
    {mem : ByteArray}
    (hmem : mem.size = 164)
    (hdepth : evmE.executionEnv.depth ≠ 1024)
    (hΘ : (cA', σ', g'', A', z, out) =
        Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes evmE.createdAccounts
          evmE.genesisBlockHeader evmE.blocks evmE.accountMap evmE.σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner))
          evmE.executionEnv.sender
          (AccountAddress.ofUInt256 (endThawCureWord evmE.accountMap evmE.executionEnv))
          (toExecute evmE.accountMap
            (AccountAddress.ofUInt256 (endThawCureWord evmE.accountMap evmE.executionEnv)))
          callGas (UInt256.ofNat evmE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((endThawNoArgCalldataMem endThawTellSelectorWord mem).readWithPadding
            endThawNoArgOutPtr.toNat endThawNoArgInSize.toNat)
          (evmE.executionEnv.depth + 1) evmE.executionEnv.header false)
    (hState : EVMStateEquiv evmE evmS)
    (hOriginalAccounts : evmE.σ₀ = evmS.σ₀)
    (hGenesis : evmS.genesisBlockHeader = evmE.genesisBlockHeader)
    (hBlocks : evmS.blocks = evmE.blocks) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM config evmS
        (EVM.address (endThawCureAddr evmS.accountMap evmS.executionEnv))
        "tell" 0 [] (z,
          { evmS with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          out) false ∧
      EVMStateEquiv
        { evmE with accountMap := σ', substate := A', createdAccounts := cA' }
        { evmS with
            accountMap := σ'_solm
            substate := A'_solm
            createdAccounts := cA' } := by
  have htgt :
      EVM.address (endThawCureAddr evmS.accountMap evmS.executionEnv) =
        AccountAddress.ofUInt256 (endThawCureWord evmE.accountMap evmE.executionEnv) := by
    rw [hState.executionEnv]
    exact endThawCureAddr_source_eq_evmWord hState.accountMap
  obtain ⟨σ'_solm, A'_solm, hcall, hAccountsPost, hSubstate⟩ :=
    endCallMade_accountMapEquiv_with_substate
      (cfg := config) (evm_evm := evmE) (evm_solm := evmS)
      (tgt := EVM.address (endThawCureAddr evmS.accountMap evmS.executionEnv))
      (targetWord := endThawCureWord evmE.accountMap evmE.executionEnv)
      (name := "tell") (args := [])
      (cA' := cA') (σ' := σ') (A' := A') (A_in := Ain)
      (z := z) (out := out) (g'' := g'') (callGas := callGas)
      (mem := endThawNoArgCalldataMem endThawTellSelectorWord mem)
      (inOff := endThawNoArgOutPtr) (inSize := endThawNoArgInSize)
      (callPerm := false)
      hdepth htgt (endThawTellEncode_eq hmem) hΘ hState.accountMap
      hOriginalAccounts hState.createdAccounts.symm hGenesis hBlocks hState.executionEnv.symm
  refine ⟨σ'_solm, A'_solm, hcall, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [hState.executionEnv]
  · rfl
  · exact hAccountsPost

theorem endThawReadyTailRevertsAtDebt (evmDai : EVM.State) (out : ByteArray)
    (hdai : endThawDaiWord out = ⟨0⟩)
    (hfit :
      (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩).toNat +
          (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨10⟩).toNat <
        UInt256.size)
    (hready :
      (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩ +
          Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨10⟩).toNat ≤
        (endThawTimestampWord evmDai.executionEnv).toNat) :
    let whenWord := Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩
    let waitWord := Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨10⟩
    let deadlineWord := whenWord + waitWord
    ExecBlock config { contract := contract, locals := endThawStoreDeadlineWord out deadlineWord }
      evmDai (checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt")
      .reverted →
    ExecBlock config { contract := contract, locals := endThawStoreVatDai out } evmDai
      ([ .require (.binary .eq (.var "vatDai") (.intLit 0)),
        .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
        .require (.binary .ge nowT (.var "deadline")) ] ++
      checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
      checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
        (perm := false) ++
      [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
        .assign .storage debtRef (.var "debtNew") ])
      .reverted := by
  intro whenWord waitWord deadlineWord hdebt
  have hprefix :=
    endThawTailReadyPrefix evmDai out hdai hfit hready
  have hafterDebt :
      ExecBlock config { contract := contract, locals := endThawStoreDeadlineWord out deadlineWord }
        evmDai
        (checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
        checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
          (perm := false) ++
        [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
          .assign .storage debtRef (.var "debtNew") ])
        .reverted := by
    exact execBlock_append_term
      (s2 :=
        checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
          (perm := false) ++
        [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
          .assign .storage debtRef (.var "debtNew") ])
      hdebt (by intro f' e' h; cases h)
  exact execBlock_append
    (s2 :=
      checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
      checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
        (perm := false) ++
      [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
        .assign .storage debtRef (.var "debtNew") ])
    (by simpa [whenWord, waitWord, deadlineWord] using hprefix) hafterDebt

theorem endThawReadyTailRevertsAfterDebt (evmDai evmDebt : EVM.State)
    (out debtOut : ByteArray)
    (hdai : endThawDaiWord out = ⟨0⟩)
    (hfit :
      (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩).toNat +
          (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨10⟩).toNat <
        UInt256.size)
    (hready :
      (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩ +
          Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨10⟩).toNat ≤
        (endThawTimestampWord evmDai.executionEnv).toNat) :
    let whenWord := Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩
    let waitWord := Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨10⟩
    let deadlineWord := whenWord + waitWord
    ExecBlock config { contract := contract, locals := endThawStoreDeadlineWord out deadlineWord }
      evmDai (checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt")
      (.ok { contract := contract, locals := endThawStoreVatDebt out debtOut deadlineWord }
        evmDebt) →
    ExecBlock config { contract := contract, locals := endThawStoreVatDebt out debtOut deadlineWord }
      evmDebt
      (checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
        (perm := false) ++
      [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
        .assign .storage debtRef (.var "debtNew") ])
      .reverted →
    ExecBlock config { contract := contract, locals := endThawStoreVatDai out } evmDai
      ([ .require (.binary .eq (.var "vatDai") (.intLit 0)),
        .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
        .require (.binary .ge nowT (.var "deadline")) ] ++
      checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
      checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
        (perm := false) ++
      [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
        .assign .storage debtRef (.var "debtNew") ])
      .reverted := by
  intro whenWord waitWord deadlineWord hdebt htellTail
  have hprefix :=
    endThawTailReadyPrefix evmDai out hdai hfit hready
  have hafterDebt :
      ExecBlock config { contract := contract, locals := endThawStoreDeadlineWord out deadlineWord }
        evmDai
        (checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
        checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
          (perm := false) ++
        [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
          .assign .storage debtRef (.var "debtNew") ])
        .reverted := by
    exact execBlock_append
      (s2 :=
        checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
          (perm := false) ++
        [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
          .assign .storage debtRef (.var "debtNew") ])
      hdebt htellTail
  exact execBlock_append
    (s2 :=
      checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
      checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
        (perm := false) ++
      [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
        .assign .storage debtRef (.var "debtNew") ])
    (by simpa [whenWord, waitWord, deadlineWord] using hprefix) hafterDebt

theorem endThawReadyTailReturnsAfterDebt (evmDai evmDebt evmTell : EVM.State)
    (out debtOut tellOut : ByteArray)
    (hdai : endThawDaiWord out = ⟨0⟩)
    (hfit :
      (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩).toNat +
          (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨10⟩).toNat <
        UInt256.size)
    (hready :
      (Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩ +
          Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨10⟩).toNat ≤
        (endThawTimestampWord evmDai.executionEnv).toNat)
    (hle : (endThawReturnWord tellOut).toNat ≤ (endThawReturnWord debtOut).toNat) :
    let whenWord := Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩
    let waitWord := Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨10⟩
    let deadlineWord := whenWord + waitWord
    let debtNew := UInt256.sub (endThawReturnWord debtOut) (endThawReturnWord tellOut)
    let postLocals := endThawStoreDebtNew out debtOut tellOut deadlineWord debtNew
    ExecBlock config { contract := contract, locals := endThawStoreDeadlineWord out deadlineWord }
      evmDai (checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt")
      (.ok { contract := contract, locals := endThawStoreVatDebt out debtOut deadlineWord }
        evmDebt) →
    ExecBlock config { contract := contract, locals := endThawStoreVatDebt out debtOut deadlineWord }
      evmDebt
      (checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
        (perm := false))
      (.ok { contract := contract, locals := endThawStoreCureTell out debtOut tellOut deadlineWord }
        evmTell) →
    ExecBlock config { contract := contract, locals := endThawStoreVatDai out } evmDai
      ([ .require (.binary .eq (.var "vatDai") (.intLit 0)),
        .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
        .require (.binary .ge nowT (.var "deadline")) ] ++
      checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
      checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
        (perm := false) ++
      [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
        .assign .storage debtRef (.var "debtNew") ])
      (.ok { contract := contract, locals := postLocals }
        (endThawPostState evmTell debtNew)) := by
  intro whenWord waitWord deadlineWord debtNew postLocals hdebt htell
  have hprefix :=
    endThawTailReadyPrefix evmDai out hdai hfit hready
  have hsub := endThawTailSubAssign evmTell out debtOut tellOut deadlineWord hle
  have hafterTell :
      ExecBlock config { contract := contract, locals := endThawStoreVatDebt out debtOut deadlineWord }
        evmDebt
        (checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
          (perm := false) ++
        [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
          .assign .storage debtRef (.var "debtNew") ])
        (.ok { contract := contract, locals := postLocals }
          (endThawPostState evmTell debtNew)) := by
    exact execBlock_append
      (s2 :=
        [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
          .assign .storage debtRef (.var "debtNew") ])
      htell (by simpa [debtNew, postLocals] using hsub)
  have hafterDebt :
      ExecBlock config { contract := contract, locals := endThawStoreDeadlineWord out deadlineWord }
        evmDai
        (checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
        checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
          (perm := false) ++
        [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
          .assign .storage debtRef (.var "debtNew") ])
        (.ok { contract := contract, locals := postLocals }
          (endThawPostState evmTell debtNew)) := by
    exact execBlock_append
      (s2 :=
        checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
          (perm := false) ++
        [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
          .assign .storage debtRef (.var "debtNew") ])
      hdebt hafterTell
  exact execBlock_append
    (s2 :=
      checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
      checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
        (perm := false) ++
      [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
        .assign .storage debtRef (.var "debtNew") ])
    (by simpa [whenWord, waitWord, deadlineWord] using hprefix) hafterDebt

theorem endThawBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf thawTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endThawConcreteSelector := by
    simpa [endThawSelectorBytes, endThawConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endThawConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some thawTransition :=
    endDispatchThaw hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (thawTransition.params.map Param.name)
        (transitionSignature thawTransition).paramTypes I.calldata = some ∅ :=
    endDecode_thaw hsz4
  have hreach := endReachThawBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  obtain ⟨_, _, hbodyReach⟩ := endThawX_entry hreach
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveCouple : endThawLiveWord σ_evm I = endThawLiveWord σ_solm I := by
    simpa [endThawLiveWord, endSlotWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
  by_cases hlive : endThawLiveWord σ_evm I = ⟨0⟩
  · have hliveSolm : endThawLiveWord σ_solm I = ⟨0⟩ := by
      rw [← hliveCouple]
      exact hlive
    have hdebtCouple : endThawDebtWord σ_evm I = endThawDebtWord σ_solm I := by
      simpa [endThawDebtWord, endSlotWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨11⟩ ⟨0⟩
    by_cases hdebt : endThawDebtWord σ_evm I = ⟨0⟩
    · have hdebtSolm : endThawDebtWord σ_solm I = ⟨0⟩ := by
        rw [← hdebtCouple]
        exact hdebt
      by_cases hvatCode :
          Reasoning.Theory.extCodeSizeWord σ_evm (endThawVatWord σ_evm I) =
            ⟨0⟩
      · have hvatCodeSolm :
            Reasoning.Theory.extCodeSizeWord σ_solm
              (endThawVatWord σ_solm I) = ⟨0⟩ :=
          endThawVatCodeSize_zero_accountMapEquiv hAccounts hvatCode
        have hbody :
            ExecTransitionBody config contract evmSolm (∅ : Store) thawTransition.body
              .reverted := by
            simpa [evmSolm] using
            endThawBodyReverts_daiNoCode
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) hwv hliveSolm hdebtSolm hvatCodeSolm
        exact (endThawX_daiNoCode (g := Sat256.ofUInt256 g) hlive hdebt hvatCode hbodyReach)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hvatCodeNE :
            Reasoning.Theory.extCodeSizeWord σ_evm
              (endThawVatWord σ_evm I) ≠ ⟨0⟩ := hvatCode
        have hvatCodeSolmNE :
            Reasoning.Theory.extCodeSizeWord σ_solm
              (endThawVatWord σ_solm I) ≠ ⟨0⟩ :=
          endThawVatCodeSize_ne_accountMapEquiv hAccounts hvatCodeNE
        obtain ⟨gasWord, _, _, hdaiReady⟩ :=
          endThawX_daiCallReady (g := Sat256.ofUInt256 g) hlive hdebt hvatCodeNE hbodyReach
        by_cases hdepthLt : I.depth.val < 1024
        · obtain ⟨cA', σ', z, out, Ain, callGas, _, _, hΘ, rd4753, hout⟩ :=
            endThawX_daiPostStaticcall (g := g) hdaiReady hdepthLt
          rcases hΘ with ⟨g'', A', hΘeq⟩
          have hdepthNe :
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.depth ≠
                1024 := by
            intro hbad
            have hbadI : I.depth = 1024 := by
              simpa [initState] using hbad
            have hbadVal : I.depth.val = 1024 := congrArg Fin.val hbadI
            omega
          have htgt :
              EVM.address (endThawVatAddr σ_evm I) =
                AccountAddress.ofUInt256 (endThawVatWord σ_evm I) := by
            have hAddressId (a : AccountAddress) : EVM.address a = a := by
              apply Fin.ext
              show ↑a % EVM.twoPow 160 = ↑a
              rw [Nat.mod_eq_of_lt]
              exact a.isLt
            calc
              EVM.address (endThawVatAddr σ_evm I)
                  = EVM.address (AccountAddress.ofUInt256 (endThawVatWord σ_evm I)) := by
                    rw [endThawVatAddr_eq_ofUInt256]
              _ = AccountAddress.ofUInt256 (endThawVatWord σ_evm I) :=
                    hAddressId (AccountAddress.ofUInt256 (endThawVatWord σ_evm I))
          have hcallEvm :
              typedCallViaEVM config
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (EVM.address (endThawVatAddr σ_evm I)) "dai" 0
                [.address (endThawVowAddr σ_evm I)]
                (z,
                  { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                    accountMap := σ'
                    substate := A'
                    createdAccounts := cA' },
                  out) false := by
              exact callCoincides
                (cfg := config)
                (evm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (name := "dai")
                (args := [.address (endThawVowAddr σ_evm I)])
                (tgt := EVM.address (endThawVatAddr σ_evm I))
                (targetWord := endThawVatWord σ_evm I)
                (cA' := cA') (σ' := σ') (A' := A') (A_in := Ain)
                (z := z) (o := out) (g'' := g'') (callGas := callGas)
                (mem := endThawDaiCalldataMem σ_evm I solcFreePtrMem)
                (inOff := endThawDaiOutPtr) (inSize := endThawDaiInSize)
                (callPerm := false)
                hdepthNe htgt (endThawDaiEncode_eq σ_evm I solcFreePtrMem_size)
                (by simpa [initState] using hΘeq)
          obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, hStateCall⟩ :=
            typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallEvm)
              (by simp [initState]) hAccounts
          have hVatAddr : endThawVatAddr σ_evm I = endThawVatAddr σ_solm I := by
            simp [endThawVatAddr, endThawVatWord_accountMapEquiv hAccounts]
          have hVowWord : endThawVowWord σ_evm I = endThawVowWord σ_solm I := by
            simp [endThawVowWord, endSlotWord, solcSlotWord,
              accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨4⟩ ⟨0⟩]
          have hVowAddr : endThawVowAddr σ_evm I = endThawVowAddr σ_solm I := by
            simp [endThawVowAddr, hVowWord]
          have hcallSolm :
              typedCallViaEVM config evmSolm
                (EVM.address (endThawVatAddr σ_solm I)) "dai" 0
                [.address (endThawVowAddr σ_solm I)]
                (z,
                  { evmSolm with
                    accountMap := σ'_solm
                    substate := A'_solm
                    createdAccounts := cA' },
                  out) false := by
              simpa [evmSolm, hVatAddr, hVowAddr] using hcallSolmRaw
          cases z
          · have hbody :
                ExecTransitionBody config contract evmSolm (∅ : Store) thawTransition.body
                  .reverted := by
                simpa [evmSolm] using
                endThawBodyReverts_daiCallFailed
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                  (A := A) (I := I) (g := g)
                  (evmDai :=
                    { evmSolm with
                      accountMap := σ'_solm
                      substate := A'_solm
                      createdAccounts := cA' })
                  (out := out) hwv hliveSolm hdebtSolm hvatCodeSolmNE
                  (by simpa [evmSolm] using hcallSolm)
            exact (endThawX_daiCallFailed (g := g) rd4753 hout)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · let evmDaiSolm :=
                { evmSolm with
                  accountMap := σ'_solm
                  substate := A'_solm
                  createdAccounts := cA' }
            let evmDaiEvm :=
                { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ'
                  substate := A'
                  createdAccounts := cA' }
            obtain ⟨_, _, rd4771⟩ := endThawX_daiCallSucceeded (g := g) rd4753
            by_cases hshort : out.size < 32
            · have hbody :
                  ExecTransitionBody config contract evmSolm (∅ : Store) thawTransition.body
                    .reverted := by
                  simpa [evmSolm, evmDaiSolm] using
                  endThawBodyReverts_daiDecodeShort
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g) (evmDai := evmDaiSolm) (out := out)
                    hwv hliveSolm hdebtSolm hvatCodeSolmNE
                    (by simpa [evmSolm, evmDaiSolm] using hcallSolm) hshort
              exact (endThawX_daiReturnDecodeShort rd4771 hshort hout)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have hlo : 32 ≤ out.size := by omega
              obtain ⟨_, _, rd4794⟩ := endThawX_daiReturnDecodeOk rd4771 hlo hout
              by_cases hdai : endThawDaiWord out = ⟨0⟩
              · obtain ⟨_, _, rd4866⟩ := endThawX_daiZeroDeadlineEntry hdai rd4794
                obtain ⟨_, _, rdAddEntry⟩ := endThawX_deadlineAddEntry rd4866
                have hwhenCouple :
                    endThawWhenWord σ' I =
                      Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner
                        ⟨9⟩ := by
                    have hload := hStateCall.storageLoad_codeOwner ⟨9⟩
                    simpa [evmDaiEvm, evmDaiSolm, initState, Solm.EVM.storageLoad,
                      State.lookupAccount, endThawWhenWord, endSlotWord, solcSlotWord] using hload
                have hwaitCouple :
                    endThawWaitWord σ' I =
                      Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner
                        ⟨10⟩ := by
                    have hload := hStateCall.storageLoad_codeOwner ⟨10⟩
                    simpa [evmDaiEvm, evmDaiSolm, initState, Solm.EVM.storageLoad,
                      State.lookupAccount, endThawWaitWord, endSlotWord, solcSlotWord] using hload
                by_cases hoverDeadline :
                    UInt256.size ≤
                      (endThawWhenWord σ' I).toNat + (endThawWaitWord σ' I).toNat
                · have hoverSolm :
                      UInt256.size ≤
                        (Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner
                            ⟨9⟩).toNat +
                          (Solm.EVM.storageLoad evmDaiSolm
                            evmDaiSolm.executionEnv.codeOwner ⟨10⟩).toNat := by
                      rw [← hwhenCouple, ← hwaitCouple]
                      exact hoverDeadline
                  have hbody :
                      ExecTransitionBody config contract evmSolm (∅ : Store) thawTransition.body
                        .reverted := by
                      simpa [evmSolm, evmDaiSolm] using
                      endThawBodyReverts_deadlineAddOverflow
                        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                        (A := A) (I := I) (g := g) (evmDai := evmDaiSolm)
                        (out := out) hwv hliveSolm hdebtSolm hvatCodeSolmNE
                        (by simpa [evmSolm, evmDaiSolm] using hcallSolm) hlo hdai hoverSolm
                  exact (endThawX_deadlineAddOverflow hoverDeadline rdAddEntry)
                    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · have hfitDeadline :
                      (endThawWhenWord σ' I).toNat + (endThawWaitWord σ' I).toNat <
                        UInt256.size :=
                    Nat.lt_of_not_ge hoverDeadline
                  obtain ⟨_, _, rd4880⟩ :=
                    endThawX_deadlineAddSuccess hfitDeadline rdAddEntry
                  by_cases hready :
                      (endThawDeadlineWord σ' I).toNat ≤ (endThawTimestampWord I).toNat
                  · obtain ⟨_, _, rd4956⟩ := endThawX_deadlineReady hready rd4880
                    let whenSolm :=
                      Solm.EVM.storageLoad evmDaiSolm
                        evmDaiSolm.executionEnv.codeOwner ⟨9⟩
                    let waitSolm :=
                      Solm.EVM.storageLoad evmDaiSolm
                        evmDaiSolm.executionEnv.codeOwner ⟨10⟩
                    let deadlineSolm := whenSolm + waitSolm
                    have hfitSolm :
                        (Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner
                            ⟨9⟩).toNat +
                            (Solm.EVM.storageLoad evmDaiSolm
                              evmDaiSolm.executionEnv.codeOwner ⟨10⟩).toNat <
                          UInt256.size := by
                        rw [← hwhenCouple, ← hwaitCouple]
                        exact hfitDeadline
                    have hreadySolm :
                        (Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner
                            ⟨9⟩ +
                            Solm.EVM.storageLoad evmDaiSolm
                              evmDaiSolm.executionEnv.codeOwner ⟨10⟩).toNat ≤
                          (endThawTimestampWord evmDaiSolm.executionEnv).toNat := by
                        simpa [evmDaiSolm, evmSolm, initState, endThawDeadlineWord,
                        hwhenCouple, hwaitCouple] using hready
                    have hmemDai : (endThawDaiPostCallMem σ_evm I out).size = 164 :=
                      endThawDaiPostCallMem_size σ_evm I out hout
                    have hreadDai :
                        (endThawDaiPostCallMem σ_evm I out).readWithPadding 64 32 =
                          UInt256.toByteArray ⟨128⟩ :=
                      endThawDaiPostCallMem_read64 σ_evm I out hout
                    have hdepthNeDai : evmDaiEvm.executionEnv.depth ≠ 1024 := by
                      simpa [evmDaiEvm, initState] using hdepthNe
                    have hdaiBlock :
                        ExecBlock config { contract := contract, locals := (∅ : Store) }
                          evmSolm
                          (checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0)
                            [vowAddr] "vatDai" (perm := false))
                          (.ok { contract := contract, locals := endThawStoreVatDai out }
                            evmDaiSolm) := by
                        have hreceiver :
                          evalExpr? config { contract := contract, locals := (∅ : Store) }
                            evmSolm (.storage vatRef) =
                              .ok (.address (endThawVatAddr σ_solm I)) := by
                          simpa [evmSolm, initState, Solm.EVM.storageLoad, State.lookupAccount,
                          endThawVatAddr, endThawVatWord, endSlotWord, solcSlotWord] using
                          evalExpr_endThaw_vat (locals := (∅ : Store)) evmSolm (by simp)
                        have hcodePos :
                            0 < (UInt256.ofNat
                              ((evmSolm.lookupAccount
                                (endThawVatAddr σ_solm I)).option 0
                                  (fun acc => acc.code.size))).toNat := by
                            simpa [evmSolm] using
                            endThawVatCode_pos_of_codeSize_ne
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                              (σ₀ := σ₀) (A := A) (I := I) (g := g) hvatCodeSolmNE
                        have hguard :
                            evalExpr? config { contract := contract, locals := (∅ : Store) }
                              evmSolm
                              (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
                                .ok (.bool true) :=
                          endEvalExpr_extCodeGuard_true hreceiver hcodePos
                        have hvow :
                            evalExpr? config { contract := contract, locals := (∅ : Store) }
                              evmSolm vowAddr =
                                .ok (.address (endThawVowAddr σ_solm I)) := by
                            simpa [vowAddr, evmSolm, initState, Solm.EVM.storageLoad,
                            State.lookupAccount, endThawVowAddr, endThawVowWord,
                            endSlotWord, solcSlotWord] using
                            evalExpr_endThaw_vow (locals := (∅ : Store)) evmSolm (by simp)
                        have hargs :
                            evalExprs? config { contract := contract, locals := (∅ : Store) }
                              evmSolm [vowAddr] =
                                .ok [.address (endThawVowAddr σ_solm I)] := by
                            simp [evalExprs?, hvow, EvalResult.bind, bind, pure]
                        have hblock := checkedExternalCallSuccess
                          (cfg := config) (C := contract) (evm := evmSolm)
                          (evm' := evmDaiSolm)
                          (locals := (∅ : Store)) (receiver := .storage vatRef)
                          (retVar := "vatDai") (name := "dai")
                          (target := endThawVatAddr σ_solm I)
                          (sendVal := 0) (args := [vowAddr])
                          (argVals := [.address (endThawVowAddr σ_solm I)])
                          (out := out) (perm := false)
                          (value := [.int (Int.ofNat (endThawDaiWord out).toNat)])
                          hguard hreceiver hargs
                          (by simpa [evmDaiSolm] using hcallSolm)
                          (endThawDaiDecode_ok out hlo)
                        simpa [checkedExternalCallStmts, endThawStoreVatDai,
                          collapseReturns] using hblock
                    by_cases hvatCodeDebt :
                        Reasoning.Theory.extCodeSizeWord σ'
                          (endThawVatWord σ' I) = ⟨0⟩
                    · have hrev :=
                        endThawX_debtNoCode hmemDai hreadDai hvatCodeDebt rd4956
                      have hvatCodeDebtSolm :
                          Reasoning.Theory.extCodeSizeWord evmDaiSolm.accountMap
                            (endThawVatWord evmDaiSolm.accountMap
                              evmDaiSolm.executionEnv) = ⟨0⟩ := by
                          have htmp :=
                            endThawVatCodeSize_zero_accountMapEquiv
                              hStateCall.accountMap hvatCodeDebt
                          simpa [evmDaiSolm, evmSolm, initState] using htmp
                      have hdebtBlock :
                          ExecBlock config
                            { contract := contract,
                              locals := endThawStoreDeadlineWord out deadlineSolm }
                            evmDaiSolm
                            (checkedExternalCallStmts (.storage vatRef) "debt"
                              (.intLit 0) [] "vatDebt") .reverted := by
                          simpa [deadlineSolm, whenSolm, waitSolm] using
                          endThawCheckedDebtNoCode evmDaiSolm out deadlineSolm
                            hvatCodeDebtSolm
                      have htail :
                          ExecBlock config
                            { contract := contract, locals := endThawStoreVatDai out }
                            evmDaiSolm
                            ([ .require (.binary .eq (.var "vatDai") (.intLit 0)),
                              .internalCall "add" [.storage whenRef, .storage waitRef]
                                "deadline",
                              .require (.binary .ge nowT (.var "deadline")) ] ++
                            checkedExternalCallStmts (.storage vatRef) "debt"
                              (.intLit 0) [] "vatDebt" ++
                            checkedExternalCallStmts (.storage cureRef) "tell"
                              (.intLit 0) [] "cureTell" (perm := false) ++
                            [ .internalCall "sub" [.var "vatDebt", .var "cureTell"]
                                "debtNew",
                              .assign .storage debtRef (.var "debtNew") ])
                            .reverted := by
                          simpa [whenSolm, waitSolm, deadlineSolm] using
                          endThawReadyTailRevertsAtDebt evmDaiSolm out hdai
                            hfitSolm hreadySolm hdebtBlock
                      have hbody :
                          ExecTransitionBody config contract evmSolm (∅ : Store)
                            thawTransition.body .reverted := by
                          simpa [evmSolm, evmDaiSolm] using
                          endThawBodyReverts_daiOkTailReverted
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                            (σ₀ := σ₀) (A := A) (I := I) (g := g)
                            (fDai :=
                              { contract := contract, locals := endThawStoreVatDai out })
                            (evmDai := evmDaiSolm)
                            hwv hliveSolm hdebtSolm
                            (by simpa [evmSolm, evmDaiSolm] using hdaiBlock) htail
                      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                    · have hvatCodeDebtNE :
                        Reasoning.Theory.extCodeSizeWord σ'
                          (endThawVatWord σ' I) ≠ ⟨0⟩ := hvatCodeDebt
                      have hvatCodeDebtSolmNE :
                          Reasoning.Theory.extCodeSizeWord evmDaiSolm.accountMap
                            (endThawVatWord evmDaiSolm.accountMap
                              evmDaiSolm.executionEnv) ≠ ⟨0⟩ := by
                          have htmp :=
                            endThawVatCodeSize_ne_accountMapEquiv
                              hStateCall.accountMap hvatCodeDebtNE
                          simpa [evmDaiSolm, evmSolm, initState] using htmp
                      obtain ⟨gasDebt, _, _, rd5031⟩ :=
                        endThawX_debtCallReady hmemDai hreadDai
                          hvatCodeDebtNE rd4956
                      obtain ⟨cADebt, σDebt, zDebt, debtOut, AinDebt,
                          callGasDebt, _, _, hΘDebt, rd5032, hdebtOutSize⟩ :=
                        endThawX_debtPostCall rd5031 hdepthLt
                      rcases hΘDebt with ⟨gDebt'', ADebt, hΘDebtEq⟩
                      let evmDebtEvm :=
                        { evmDaiEvm with
                          accountMap := σDebt
                          substate := ADebt
                          createdAccounts := cADebt }
                      obtain ⟨σDebtSolm, ADebtSolm, hcallDebtSolmRaw,
                          hStateDebtRaw⟩ :=
                        endThawDebtCallMadeBridge
                          (evmE := evmDaiEvm) (evmS := evmDaiSolm)
                          (cA' := cADebt) (σ' := σDebt) (A' := ADebt)
                          (Ain := AinDebt) (z := zDebt) (out := debtOut)
                          (g'' := gDebt'') (callGas := callGasDebt)
                          (mem := endThawDaiPostCallMem σ_evm I out)
                          hmemDai hdepthNeDai
                          (by simpa [evmDaiEvm, initState, hperm] using hΘDebtEq)
                          hStateCall
                          (by simp [evmDaiEvm, evmDaiSolm, evmSolm, initState])
                          (by simp [evmDaiEvm, evmDaiSolm, evmSolm, initState])
                          (by simp [evmDaiEvm, evmDaiSolm, evmSolm, initState])
                      let evmDebtSolm :=
                        { evmDaiSolm with
                          accountMap := σDebtSolm
                          substate := ADebtSolm
                          createdAccounts := cADebt }
                      have hcallDebtSolm :
                          typedCallViaEVM config evmDaiSolm
                            (EVM.address (endThawVatAddr evmDaiSolm.accountMap
                              evmDaiSolm.executionEnv)) "debt" 0 []
                            (zDebt, evmDebtSolm, debtOut) true := by
                          simpa [evmDebtSolm] using hcallDebtSolmRaw
                      have hStateDebt :
                          EVMStateEquiv evmDebtEvm evmDebtSolm := by
                        simpa [evmDebtEvm, evmDebtSolm] using hStateDebtRaw
                      cases zDebt
                      · have hrev :=
                          endThawX_debtCallFailed (by simpa using rd5032) hdebtOutSize
                        have hdebtBlock :
                            ExecBlock config
                              { contract := contract,
                                locals := endThawStoreDeadlineWord out deadlineSolm }
                              evmDaiSolm
                              (checkedExternalCallStmts (.storage vatRef) "debt"
                                (.intLit 0) [] "vatDebt") .reverted := by
                            simpa [deadlineSolm] using
                            endThawCheckedDebtFailure
                              (evm := evmDaiSolm) (evm' := evmDebtSolm)
                              (out := out) (debtOut := debtOut)
                              (deadline := deadlineSolm)
                              hvatCodeDebtSolmNE
                              (by simpa using hcallDebtSolm)
                        have htail :
                            ExecBlock config
                              { contract := contract, locals := endThawStoreVatDai out }
                              evmDaiSolm
                              ([ .require (.binary .eq (.var "vatDai") (.intLit 0)),
                                .internalCall "add" [.storage whenRef, .storage waitRef]
                                  "deadline",
                                .require (.binary .ge nowT (.var "deadline")) ] ++
                              checkedExternalCallStmts (.storage vatRef) "debt"
                                (.intLit 0) [] "vatDebt" ++
                              checkedExternalCallStmts (.storage cureRef) "tell"
                                (.intLit 0) [] "cureTell" (perm := false) ++
                              [ .internalCall "sub" [.var "vatDebt", .var "cureTell"]
                                  "debtNew",
                                .assign .storage debtRef (.var "debtNew") ])
                              .reverted := by
                            simpa [whenSolm, waitSolm, deadlineSolm] using
                            endThawReadyTailRevertsAtDebt evmDaiSolm out hdai
                              hfitSolm hreadySolm hdebtBlock
                        have hbody :
                            ExecTransitionBody config contract evmSolm (∅ : Store)
                              thawTransition.body .reverted := by
                            simpa [evmSolm, evmDaiSolm] using
                            endThawBodyReverts_daiOkTailReverted
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                              (σ₀ := σ₀) (A := A) (I := I) (g := g)
                              (fDai :=
                                { contract := contract, locals := endThawStoreVatDai out })
                              (evmDai := evmDaiSolm)
                              hwv hliveSolm hdebtSolm
                              (by simpa [evmSolm, evmDaiSolm] using hdaiBlock) htail
                        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                      · obtain ⟨_, _, rd5050⟩ :=
                          endThawX_debtCallSucceeded (by simpa using rd5032)
                        by_cases hshortDebt : debtOut.size < 32
                        · have hrev :=
                            endThawX_debtReturnDecodeShort hmemDai hreadDai rd5050
                              hshortDebt hdebtOutSize
                          have hdebtBlock :
                              ExecBlock config
                                { contract := contract,
                                  locals := endThawStoreDeadlineWord out deadlineSolm }
                                evmDaiSolm
                                (checkedExternalCallStmts (.storage vatRef) "debt"
                                  (.intLit 0) [] "vatDebt") .reverted := by
                              simpa [deadlineSolm] using
                              endThawCheckedDebtDecodeRevert
                                (evm := evmDaiSolm) (evm' := evmDebtSolm)
                                (out := out) (debtOut := debtOut)
                                (deadline := deadlineSolm)
                                hvatCodeDebtSolmNE
                                (by simpa using hcallDebtSolm) hshortDebt
                          have htail :
                              ExecBlock config
                                { contract := contract,
                                  locals := endThawStoreVatDai out }
                                evmDaiSolm
                                ([ .require (.binary .eq (.var "vatDai") (.intLit 0)),
                                  .internalCall "add" [.storage whenRef, .storage waitRef]
                                    "deadline",
                                  .require (.binary .ge nowT (.var "deadline")) ] ++
                                checkedExternalCallStmts (.storage vatRef) "debt"
                                  (.intLit 0) [] "vatDebt" ++
                                checkedExternalCallStmts (.storage cureRef) "tell"
                                  (.intLit 0) [] "cureTell" (perm := false) ++
                                [ .internalCall "sub" [.var "vatDebt", .var "cureTell"]
                                    "debtNew",
                                  .assign .storage debtRef (.var "debtNew") ])
                                .reverted := by
                              simpa [whenSolm, waitSolm, deadlineSolm] using
                              endThawReadyTailRevertsAtDebt evmDaiSolm out hdai
                                hfitSolm hreadySolm hdebtBlock
                          have hbody :
                              ExecTransitionBody config contract evmSolm (∅ : Store)
                                thawTransition.body .reverted := by
                              simpa [evmSolm, evmDaiSolm] using
                              endThawBodyReverts_daiOkTailReverted
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                                (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                (fDai :=
                                  { contract := contract, locals := endThawStoreVatDai out })
                                (evmDai := evmDaiSolm)
                                hwv hliveSolm hdebtSolm
                                (by simpa [evmSolm, evmDaiSolm] using hdaiBlock) htail
                          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                        · have hloDebt : 32 ≤ debtOut.size := by omega
                          obtain ⟨_, _, rd5073⟩ :=
                            endThawX_debtReturnDecodeOk hmemDai hreadDai rd5050
                              hloDebt hdebtOutSize
                          have hdebtBlock :
                              ExecBlock config
                                { contract := contract,
                                  locals := endThawStoreDeadlineWord out deadlineSolm }
                                evmDaiSolm
                                (checkedExternalCallStmts (.storage vatRef) "debt"
                                  (.intLit 0) [] "vatDebt")
                                (.ok
                                  { contract := contract,
                                    locals := endThawStoreVatDebt out debtOut deadlineSolm }
                                  evmDebtSolm) := by
                              simpa [deadlineSolm] using
                              endThawCheckedDebtSuccess
                                (evm := evmDaiSolm) (evm' := evmDebtSolm)
                                (out := out) (debtOut := debtOut)
                                (deadline := deadlineSolm)
                                hvatCodeDebtSolmNE
                                (by simpa using hcallDebtSolm) hloDebt
                          by_cases hcureCode :
                              Reasoning.Theory.extCodeSizeWord σDebt
                                (endThawCureWord σDebt I) = ⟨0⟩
                          · have hrev :=
                              endThawX_tellNoCode hmemDai hreadDai hdebtOutSize
                                hcureCode rd5073
                            have hcureCodeSolm :
                                Reasoning.Theory.extCodeSizeWord
                                  evmDebtSolm.accountMap
                                  (endThawCureWord evmDebtSolm.accountMap
                                    evmDebtSolm.executionEnv) = ⟨0⟩ := by
                                have htmp :=
                                  endThawCureCodeSize_zero_accountMapEquiv
                                    hStateDebt.accountMap hcureCode
                                simpa [evmDebtEvm, evmDebtSolm, evmDaiEvm, evmDaiSolm,
                                  evmSolm, initState] using htmp
                            have htellBlock :
                                ExecBlock config
                                  { contract := contract,
                                    locals :=
                                      endThawStoreVatDebt out debtOut deadlineSolm }
                                  evmDebtSolm
                                  (checkedExternalCallStmts (.storage cureRef) "tell"
                                    (.intLit 0) [] "cureTell" (perm := false))
                                  .reverted := by
                                simpa [deadlineSolm] using
                                endThawCheckedTellNoCode evmDebtSolm out debtOut
                                  deadlineSolm hcureCodeSolm
                            have htellTail :
                                ExecBlock config
                                  { contract := contract,
                                    locals :=
                                      endThawStoreVatDebt out debtOut deadlineSolm }
                                  evmDebtSolm
                                  (checkedExternalCallStmts (.storage cureRef) "tell"
                                    (.intLit 0) [] "cureTell" (perm := false) ++
                                  [ .internalCall "sub"
                                      [.var "vatDebt", .var "cureTell"] "debtNew",
                                    .assign .storage debtRef (.var "debtNew") ])
                                  .reverted := by
                                exact execBlock_append_term
                                  (s2 :=
                                    [ .internalCall "sub"
                                        [.var "vatDebt", .var "cureTell"] "debtNew",
                                      .assign .storage debtRef (.var "debtNew") ])
                                  htellBlock (by intro f' e' h; cases h)
                            have htail :
                                ExecBlock config
                                  { contract := contract,
                                    locals := endThawStoreVatDai out }
                                  evmDaiSolm
                                  ([ .require (.binary .eq (.var "vatDai") (.intLit 0)),
                                    .internalCall "add"
                                      [.storage whenRef, .storage waitRef] "deadline",
                                    .require (.binary .ge nowT (.var "deadline")) ] ++
                                  checkedExternalCallStmts (.storage vatRef) "debt"
                                    (.intLit 0) [] "vatDebt" ++
                                  checkedExternalCallStmts (.storage cureRef) "tell"
                                    (.intLit 0) [] "cureTell" (perm := false) ++
                                  [ .internalCall "sub"
                                      [.var "vatDebt", .var "cureTell"] "debtNew",
                                    .assign .storage debtRef (.var "debtNew") ])
                                  .reverted := by
                                simpa [whenSolm, waitSolm, deadlineSolm] using
                                endThawReadyTailRevertsAfterDebt evmDaiSolm
                                  evmDebtSolm out debtOut hdai hfitSolm hreadySolm
                                  hdebtBlock htellTail
                            have hbody :
                                ExecTransitionBody config contract evmSolm (∅ : Store)
                                  thawTransition.body .reverted := by
                                simpa [evmSolm, evmDaiSolm] using
                                endThawBodyReverts_daiOkTailReverted
                                  (cA := cA) (gh := gh) (bl := bl)
                                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                  (g := g)
                                  (fDai :=
                                    { contract := contract, locals := endThawStoreVatDai out })
                                  (evmDai := evmDaiSolm)
                                  hwv hliveSolm hdebtSolm
                                  (by simpa [evmSolm, evmDaiSolm] using hdaiBlock) htail
                            exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                          · have hcureCodeNE :
                              Reasoning.Theory.extCodeSizeWord σDebt
                                (endThawCureWord σDebt I) ≠ ⟨0⟩ := hcureCode
                            have hcureCodeSolmNE :
                                Reasoning.Theory.extCodeSizeWord
                                  evmDebtSolm.accountMap
                                  (endThawCureWord evmDebtSolm.accountMap
                                    evmDebtSolm.executionEnv) ≠ ⟨0⟩ := by
                                have htmp :=
                                  endThawCureCodeSize_ne_accountMapEquiv
                                    hStateDebt.accountMap hcureCodeNE
                                simpa [evmDebtEvm, evmDebtSolm, evmDaiEvm, evmDaiSolm,
                                  evmSolm, initState] using htmp
                            obtain ⟨gasTell, _, _, rd5144⟩ :=
                              endThawX_tellCallReady hmemDai hreadDai hdebtOutSize
                                hcureCodeNE rd5073
                            obtain ⟨cATell, σTell, zTell, tellOut, AinTell,
                                callGasTell, _, _, hΘTell, rd5145, htellOutSize⟩ :=
                              endThawX_tellPostStaticcall rd5144 hdepthLt
                            rcases hΘTell with ⟨gTell'', ATell, hΘTellEq⟩
                            let evmTellEvm :=
                              { evmDebtEvm with
                                accountMap := σTell
                                substate := ATell
                                createdAccounts := cATell }
                            have hpostDebtSize :
                                (endThawNoArgPostCallMem endThawDebtSelectorWord
                                  (endThawDaiPostCallMem σ_evm I out) debtOut).size =
                                  164 :=
                              endThawNoArgPostCallMem_size hmemDai hdebtOutSize
                            obtain ⟨σTellSolm, ATellSolm, hcallTellSolmRaw,
                                hStateTellRaw⟩ :=
                              endThawTellCallMadeBridge
                                (evmE := evmDebtEvm) (evmS := evmDebtSolm)
                                (cA' := cATell) (σ' := σTell) (A' := ATell)
                                (Ain := AinTell) (z := zTell) (out := tellOut)
                                (g'' := gTell'') (callGas := callGasTell)
                                (mem :=
                                  endThawNoArgPostCallMem endThawDebtSelectorWord
                                    (endThawDaiPostCallMem σ_evm I out) debtOut)
                                hpostDebtSize
                                (by simpa [evmDebtEvm, evmDaiEvm, initState]
                                  using hdepthNeDai)
                                (by simpa [evmDebtEvm, evmDaiEvm, initState]
                                  using hΘTellEq)
                                hStateDebt
                                (by simp [evmDebtEvm, evmDebtSolm, evmDaiEvm,
                                  evmDaiSolm, evmSolm, initState])
                                (by simp [evmDebtEvm, evmDebtSolm, evmDaiEvm,
                                  evmDaiSolm, evmSolm, initState])
                                (by simp [evmDebtEvm, evmDebtSolm, evmDaiEvm,
                                  evmDaiSolm, evmSolm, initState])
                            let evmTellSolm :=
                              { evmDebtSolm with
                                accountMap := σTellSolm
                                substate := ATellSolm
                                createdAccounts := cATell }
                            have hcallTellSolm :
                                typedCallViaEVM config evmDebtSolm
                                  (EVM.address (endThawCureAddr
                                    evmDebtSolm.accountMap
                                    evmDebtSolm.executionEnv)) "tell" 0 []
                                  (zTell, evmTellSolm, tellOut) false := by
                                simpa [evmTellSolm] using hcallTellSolmRaw
                            have hStateTell :
                                EVMStateEquiv evmTellEvm evmTellSolm := by
                              simpa [evmTellEvm, evmTellSolm] using hStateTellRaw
                            cases zTell
                            · have hrev :=
                                endThawX_tellCallFailed (by simpa using rd5145) htellOutSize
                              have htellBlock :
                                  ExecBlock config
                                    { contract := contract,
                                      locals :=
                                        endThawStoreVatDebt out debtOut deadlineSolm }
                                    evmDebtSolm
                                    (checkedExternalCallStmts (.storage cureRef) "tell"
                                      (.intLit 0) [] "cureTell" (perm := false))
                                    .reverted := by
                                  simpa [deadlineSolm] using
                                  endThawCheckedTellFailure
                                    (evm := evmDebtSolm) (evm' := evmTellSolm)
                                    (out := out) (debtOut := debtOut)
                                    (tellOut := tellOut) (deadline := deadlineSolm)
                                    hcureCodeSolmNE
                                    (by simpa using hcallTellSolm)
                              have htellTail :
                                  ExecBlock config
                                    { contract := contract,
                                      locals :=
                                        endThawStoreVatDebt out debtOut deadlineSolm }
                                    evmDebtSolm
                                    (checkedExternalCallStmts (.storage cureRef) "tell"
                                      (.intLit 0) [] "cureTell" (perm := false) ++
                                    [ .internalCall "sub"
                                        [.var "vatDebt", .var "cureTell"] "debtNew",
                                      .assign .storage debtRef (.var "debtNew") ])
                                    .reverted := by
                                  exact execBlock_append_term
                                    (s2 :=
                                      [ .internalCall "sub"
                                          [.var "vatDebt", .var "cureTell"] "debtNew",
                                        .assign .storage debtRef (.var "debtNew") ])
                                    htellBlock (by intro f' e' h; cases h)
                              have htail :
                                  ExecBlock config
                                    { contract := contract,
                                      locals := endThawStoreVatDai out }
                                    evmDaiSolm
                                    ([ .require (.binary .eq (.var "vatDai") (.intLit 0)),
                                      .internalCall "add"
                                        [.storage whenRef, .storage waitRef] "deadline",
                                      .require (.binary .ge nowT (.var "deadline")) ] ++
                                    checkedExternalCallStmts (.storage vatRef) "debt"
                                      (.intLit 0) [] "vatDebt" ++
                                    checkedExternalCallStmts (.storage cureRef) "tell"
                                      (.intLit 0) [] "cureTell" (perm := false) ++
                                    [ .internalCall "sub"
                                        [.var "vatDebt", .var "cureTell"] "debtNew",
                                      .assign .storage debtRef (.var "debtNew") ])
                                    .reverted := by
                                  simpa [whenSolm, waitSolm, deadlineSolm] using
                                  endThawReadyTailRevertsAfterDebt evmDaiSolm
                                    evmDebtSolm out debtOut hdai hfitSolm hreadySolm
                                    hdebtBlock htellTail
                              have hbody :
                                  ExecTransitionBody config contract evmSolm (∅ : Store)
                                    thawTransition.body .reverted := by
                                  simpa [evmSolm, evmDaiSolm] using
                                  endThawBodyReverts_daiOkTailReverted
                                    (cA := cA) (gh := gh) (bl := bl)
                                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                    (g := g)
                                    (fDai :=
                                      { contract := contract, locals := endThawStoreVatDai out })
                                    (evmDai := evmDaiSolm)
                                    hwv hliveSolm hdebtSolm
                                    (by simpa [evmSolm, evmDaiSolm] using hdaiBlock) htail
                              exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                            · obtain ⟨_, _, rd5163⟩ :=
                                endThawX_tellCallSucceeded (by simpa using rd5145)
                              by_cases hshortTell : tellOut.size < 32
                              · have hpostDebtRead64 :
                                    (endThawNoArgPostCallMem endThawDebtSelectorWord
                                      (endThawDaiPostCallMem σ_evm I out) debtOut).readWithPadding
                                        64 32 =
                                      UInt256.toByteArray ⟨128⟩ :=
                                  endThawNoArgPostCallMem_read64 hmemDai hreadDai
                                    hdebtOutSize
                                have hrev :=
                                  endThawX_tellReturnDecodeShort hpostDebtSize
                                    hpostDebtRead64 rd5163 hshortTell htellOutSize
                                have htellBlock :
                                    ExecBlock config
                                      { contract := contract,
                                        locals :=
                                          endThawStoreVatDebt out debtOut deadlineSolm }
                                      evmDebtSolm
                                      (checkedExternalCallStmts (.storage cureRef) "tell"
                                        (.intLit 0) [] "cureTell" (perm := false))
                                      .reverted := by
                                    simpa [deadlineSolm] using
                                    endThawCheckedTellDecodeRevert
                                      (evm := evmDebtSolm) (evm' := evmTellSolm)
                                      (out := out) (debtOut := debtOut)
                                      (tellOut := tellOut) (deadline := deadlineSolm)
                                      hcureCodeSolmNE
                                      (by simpa using hcallTellSolm) hshortTell
                                have htellTail :
                                    ExecBlock config
                                      { contract := contract,
                                        locals :=
                                          endThawStoreVatDebt out debtOut deadlineSolm }
                                      evmDebtSolm
                                      (checkedExternalCallStmts (.storage cureRef) "tell"
                                        (.intLit 0) [] "cureTell" (perm := false) ++
                                      [ .internalCall "sub"
                                          [.var "vatDebt", .var "cureTell"] "debtNew",
                                        .assign .storage debtRef (.var "debtNew") ])
                                      .reverted := by
                                    exact execBlock_append_term
                                      (s2 :=
                                        [ .internalCall "sub"
                                            [.var "vatDebt", .var "cureTell"] "debtNew",
                                          .assign .storage debtRef (.var "debtNew") ])
                                      htellBlock (by intro f' e' h; cases h)
                                have htail :
                                    ExecBlock config
                                      { contract := contract,
                                        locals := endThawStoreVatDai out }
                                      evmDaiSolm
                                      ([ .require (.binary .eq (.var "vatDai") (.intLit 0)),
                                        .internalCall "add"
                                          [.storage whenRef, .storage waitRef] "deadline",
                                        .require (.binary .ge nowT (.var "deadline")) ] ++
                                      checkedExternalCallStmts (.storage vatRef) "debt"
                                        (.intLit 0) [] "vatDebt" ++
                                      checkedExternalCallStmts (.storage cureRef) "tell"
                                        (.intLit 0) [] "cureTell" (perm := false) ++
                                      [ .internalCall "sub"
                                          [.var "vatDebt", .var "cureTell"] "debtNew",
                                        .assign .storage debtRef (.var "debtNew") ])
                                      .reverted := by
                                    simpa [whenSolm, waitSolm, deadlineSolm] using
                                    endThawReadyTailRevertsAfterDebt evmDaiSolm
                                      evmDebtSolm out debtOut hdai hfitSolm hreadySolm
                                      hdebtBlock htellTail
                                have hbody :
                                    ExecTransitionBody config contract evmSolm (∅ : Store)
                                      thawTransition.body .reverted := by
                                    simpa [evmSolm, evmDaiSolm] using
                                    endThawBodyReverts_daiOkTailReverted
                                      (cA := cA) (gh := gh) (bl := bl)
                                      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                      (g := g)
                                      (fDai :=
                                        { contract := contract, locals := endThawStoreVatDai out })
                                      (evmDai := evmDaiSolm)
                                      hwv hliveSolm hdebtSolm
                                      (by simpa [evmSolm, evmDaiSolm] using hdaiBlock) htail
                                exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                              · have hloTell : 32 ≤ tellOut.size := by omega
                                have hpostDebtRead64 :
                                    (endThawNoArgPostCallMem endThawDebtSelectorWord
                                      (endThawDaiPostCallMem σ_evm I out) debtOut).readWithPadding
                                        64 32 =
                                      UInt256.toByteArray ⟨128⟩ :=
                                  endThawNoArgPostCallMem_read64 hmemDai hreadDai
                                    hdebtOutSize
                                obtain ⟨_, _, rd5186⟩ :=
                                  endThawX_tellReturnDecodeOk hpostDebtSize
                                    hpostDebtRead64 rd5163 hloTell htellOutSize
                                have htellBlock :
                                    ExecBlock config
                                      { contract := contract,
                                        locals :=
                                          endThawStoreVatDebt out debtOut deadlineSolm }
                                      evmDebtSolm
                                      (checkedExternalCallStmts (.storage cureRef) "tell"
                                        (.intLit 0) [] "cureTell" (perm := false))
                                      (.ok
                                        { contract := contract,
                                          locals :=
                                            endThawStoreCureTell out debtOut tellOut
                                              deadlineSolm }
                                        evmTellSolm) := by
                                    simpa [deadlineSolm] using
                                    endThawCheckedTellSuccess
                                      (evm := evmDebtSolm) (evm' := evmTellSolm)
                                      (out := out) (debtOut := debtOut)
                                      (tellOut := tellOut) (deadline := deadlineSolm)
                                      hcureCodeSolmNE
                                      (by simpa using hcallTellSolm) hloTell
                                by_cases hsub :
                                    (endThawReturnWord tellOut).toNat ≤
                                      (endThawReturnWord debtOut).toNat
                                · let debtNew :=
                                    UInt256.sub (endThawReturnWord debtOut)
                                      (endThawReturnWord tellOut)
                                  obtain ⟨_, _, rd5190⟩ :=
                                    endThawX_subSuccess hsub rd5186
                                  have hpostTellSize :
                                      (endThawNoArgPostCallMem endThawTellSelectorWord
                                        (endThawNoArgPostCallMem endThawDebtSelectorWord
                                          (endThawDaiPostCallMem σ_evm I out) debtOut)
                                        tellOut).size = 164 :=
                                    endThawNoArgPostCallMem_size hpostDebtSize htellOutSize
                                  have hpostTellRead64 :
                                      (endThawNoArgPostCallMem endThawTellSelectorWord
                                        (endThawNoArgPostCallMem endThawDebtSelectorWord
                                          (endThawDaiPostCallMem σ_evm I out) debtOut)
                                        tellOut).readWithPadding 64 32 =
                                        UInt256.toByteArray ⟨128⟩ :=
                                    endThawNoArgPostCallMem_read64 hpostDebtSize
                                      hpostDebtRead64 htellOutSize
                                  have hret :=
                                    endThawX_debtStoreLogReturn
                                      (g := Sat256.ofUInt256 g) hperm hpostTellSize
                                      hpostTellRead64 (by simpa [debtNew] using rd5190)
                                  have htail :
                                      ExecBlock config
                                        { contract := contract,
                                          locals := endThawStoreVatDai out }
                                        evmDaiSolm
                                        ([ .require (.binary .eq (.var "vatDai") (.intLit 0)),
                                          .internalCall "add"
                                            [.storage whenRef, .storage waitRef]
                                            "deadline",
                                          .require (.binary .ge nowT (.var "deadline")) ] ++
                                        checkedExternalCallStmts (.storage vatRef) "debt"
                                          (.intLit 0) [] "vatDebt" ++
                                        checkedExternalCallStmts (.storage cureRef) "tell"
                                          (.intLit 0) [] "cureTell" (perm := false) ++
                                        [ .internalCall "sub"
                                            [.var "vatDebt", .var "cureTell"] "debtNew",
                                          .assign .storage debtRef (.var "debtNew") ])
                                        (.ok
                                          { contract := contract,
                                            locals := endThawStoreDebtNew out debtOut tellOut
                                              deadlineSolm debtNew }
                                          (endThawPostState evmTellSolm debtNew)) := by
                                      simpa [whenSolm, waitSolm, deadlineSolm, debtNew] using
                                      endThawReadyTailReturnsAfterDebt evmDaiSolm
                                        evmDebtSolm evmTellSolm out debtOut tellOut hdai
                                        hfitSolm hreadySolm hsub hdebtBlock htellBlock
                                  have hbody :
                                      ExecTransitionBody config contract evmSolm (∅ : Store)
                                        thawTransition.body
                                        (.returned
                                          { contract := contract,
                                            locals := endThawStoreDebtNew out debtOut tellOut
                                              deadlineSolm debtNew }
                                          (endThawPostState evmTellSolm debtNew) none) := by
                                      simpa [evmSolm, evmDaiSolm] using
                                      endThawBodyReturns_daiOkTail
                                        (cA := cA) (gh := gh) (bl := bl)
                                        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                        (g := g)
                                        (fDai :=
                                          { contract := contract, locals := endThawStoreVatDai out })
                                        (fPost :=
                                          { contract := contract,
                                            locals := endThawStoreDebtNew out debtOut
                                              tellOut deadlineSolm debtNew })
                                        (evmDai := evmDaiSolm)
                                        (evmPost := endThawPostState evmTellSolm debtNew)
                                        hwv hliveSolm hdebtSolm
                                        (by simpa [evmSolm, evmDaiSolm] using hdaiBlock) htail
                                  have hStatePost :
                                      EVMStateEquiv (endThawPostState evmTellEvm debtNew)
                                        (endThawPostState evmTellSolm debtNew) := by
                                      simpa [endThawPostState] using
                                      hStateTell.storageStore_codeOwner ⟨11⟩
                                        (rfl : debtNew = debtNew)
                                  exact hret.reEquivExecutionGenEVMStateEquiv
                                    (evm'_evm := endThawPostState evmTellEvm debtNew)
                                    (evm'_solm := endThawPostState evmTellSolm debtNew)
                                    hcode hdispatch hdecode hbody
                                    (by
                                      simp [evmTellEvm, evmDebtEvm, evmDaiEvm,
                                        endThawPostState, initState,
                                        storageStore_createdAccounts])
                                    (by
                                      simpa [evmTellEvm, evmDebtEvm, evmDaiEvm,
                                        endThawPostState, initState,
                                        storageStore_accountMap] using
                                        accountMapEquiv.refl
                                          (sstoreAccountMap I.codeOwner σTell
                                            ⟨11⟩ debtNew))
                                    hStatePost
                                    (by
                                      simpa [thawTransition] using
                                        (returnEquiv.fallthrough
                                          (o := ByteArray.empty) (r := none)
                                          (t := []) (dvs := []) rfl
                                          (by decide +native) (by decide +native)))
                                · have hlt :
                                      (endThawReturnWord debtOut).toNat <
                                        (endThawReturnWord tellOut).toNat := by
                                      omega
                                  have hrev := endThawX_subUnderflow hlt rd5186
                                  have hsubTail :
                                      ExecBlock config
                                        { contract := contract,
                                          locals :=
                                            endThawStoreCureTell out debtOut tellOut
                                              deadlineSolm }
                                        evmTellSolm
                                        [ .internalCall "sub"
                                            [.var "vatDebt", .var "cureTell"] "debtNew",
                                          .assign .storage debtRef (.var "debtNew") ]
                                        .reverted := by
                                      simpa [deadlineSolm] using
                                      endThawTailSubUnderflow evmTellSolm out debtOut
                                        tellOut deadlineSolm hlt
                                  have htellTail :
                                      ExecBlock config
                                        { contract := contract,
                                          locals :=
                                            endThawStoreVatDebt out debtOut deadlineSolm }
                                        evmDebtSolm
                                        (checkedExternalCallStmts (.storage cureRef) "tell"
                                          (.intLit 0) [] "cureTell" (perm := false) ++
                                        [ .internalCall "sub"
                                            [.var "vatDebt", .var "cureTell"] "debtNew",
                                          .assign .storage debtRef (.var "debtNew") ])
                                        .reverted := by
                                      exact
                                       execBlock_append
                                          (s2 :=
                                            [ .internalCall "sub"
                                                [.var "vatDebt", .var "cureTell"] "debtNew",
                                              .assign .storage debtRef (.var "debtNew") ])
                                          htellBlock hsubTail
                                  have htail :
                                      ExecBlock config
                                        { contract := contract,
                                          locals := endThawStoreVatDai out }
                                        evmDaiSolm
                                        ([ .require (.binary .eq (.var "vatDai") (.intLit 0)),
                                          .internalCall "add"
                                            [.storage whenRef, .storage waitRef]
                                            "deadline",
                                          .require (.binary .ge nowT (.var "deadline")) ] ++
                                        checkedExternalCallStmts (.storage vatRef) "debt"
                                          (.intLit 0) [] "vatDebt" ++
                                        checkedExternalCallStmts (.storage cureRef) "tell"
                                          (.intLit 0) [] "cureTell" (perm := false) ++
                                        [ .internalCall "sub"
                                            [.var "vatDebt", .var "cureTell"] "debtNew",
                                          .assign .storage debtRef (.var "debtNew") ])
                                        .reverted := by
                                      simpa [whenSolm, waitSolm, deadlineSolm] using
                                      endThawReadyTailRevertsAfterDebt evmDaiSolm
                                        evmDebtSolm out debtOut hdai hfitSolm hreadySolm
                                        hdebtBlock htellTail
                                  have hbody :
                                      ExecTransitionBody config contract evmSolm (∅ : Store)
                                        thawTransition.body .reverted := by
                                      simpa [evmSolm, evmDaiSolm] using
                                      endThawBodyReverts_daiOkTailReverted
                                        (cA := cA) (gh := gh) (bl := bl)
                                        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                        (g := g)
                                        (fDai :=
                                          { contract := contract, locals := endThawStoreVatDai out })
                                        (evmDai := evmDaiSolm)
                                        hwv hliveSolm hdebtSolm
                                        (by simpa [evmSolm, evmDaiSolm] using hdaiBlock) htail
                                  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                  · have hwaitEvm :
                        (endThawTimestampWord I).toNat < (endThawDeadlineWord σ' I).toNat := by
                        omega
                    have hfitSolm :
                        (Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner
                            ⟨9⟩).toNat +
                            (Solm.EVM.storageLoad evmDaiSolm
                              evmDaiSolm.executionEnv.codeOwner ⟨10⟩).toNat <
                          UInt256.size := by
                        rw [← hwhenCouple, ← hwaitCouple]
                        exact hfitDeadline
                    have hwaitSolm :
                        (endThawTimestampWord evmDaiSolm.executionEnv).toNat <
                          (Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner
                              ⟨9⟩ +
                            Solm.EVM.storageLoad evmDaiSolm
                              evmDaiSolm.executionEnv.codeOwner ⟨10⟩).toNat := by
                        simpa [evmDaiSolm, evmSolm, initState, endThawDeadlineWord,
                          hwhenCouple, hwaitCouple] using hwaitEvm
                    have hbody :
                        ExecTransitionBody config contract evmSolm (∅ : Store)
                          thawTransition.body .reverted := by
                        simpa [evmSolm, evmDaiSolm] using
                          endThawBodyReverts_waitNotFinished
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                            (A := A) (I := I) (g := g) (evmDai := evmDaiSolm)
                            (out := out) hwv hliveSolm hdebtSolm hvatCodeSolmNE
                            (by simpa [evmSolm, evmDaiSolm] using hcallSolm) hlo hdai
                            hfitSolm hwaitSolm
                    exact
                      (endThawX_deadlineNotFinished hwaitEvm
                        (endThawDaiPostCallMem_size σ_evm I out hout)
                        (endThawDaiPostCallMem_read64 σ_evm I out hout) rd4880).reEquivExecutionRevert
                        hcode hdispatch hdecode hbody
              · have hbody :
                    ExecTransitionBody config contract evmSolm (∅ : Store) thawTransition.body
                      .reverted := by
                      simpa [evmSolm, evmDaiSolm] using
                        endThawBodyReverts_daiNonzero
                          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                          (A := A) (I := I) (g := g) (evmDai := evmDaiSolm) (out := out)
                          hwv hliveSolm hdebtSolm hvatCodeSolmNE
                          (by simpa [evmSolm, evmDaiSolm] using hcallSolm) hlo hdai
                exact
                  (endThawX_daiNonzero hdai hout rd4794).reEquivExecutionRevert
                    hcode hdispatch hdecode hbody
        · rw [not_lt] at hdepthLt
          have hdepthEq : I.depth = 1024 :=
            Fin.ext (by have := I.depth.isLt; omega)
          obtain ⟨_, _, rd4753⟩ :=
            endThawX_daiStaticcallDepthLimit (g := g) hdaiReady hdepthEq
          let A_dai :=
            (evmSolm.addAccessedAccount (EVM.address (endThawVatAddr σ_solm I))).substate
          have hcallSolm :
              typedCallViaEVM config evmSolm
                (EVM.address (endThawVatAddr σ_solm I)) "dai" 0
                [.address (endThawVowAddr σ_solm I)]
                (false, { evmSolm with substate := A_dai }, ByteArray.empty) false := by
              simpa [evmSolm, A_dai] using
              (callNotMade_depthLimit (cfg := config) (evm := evmSolm)
                (tgt := EVM.address (endThawVatAddr σ_solm I)) (name := "dai")
                (args := [.address (endThawVowAddr σ_solm I)])
                (callPerm := false)
                (endThawDaiEncode_eq σ_solm I solcFreePtrMem_size)
                (by simpa [evmSolm, initState] using hdepthEq))
          have hbody :
              ExecTransitionBody config contract evmSolm (∅ : Store) thawTransition.body
                .reverted := by
              simpa [evmSolm] using
              endThawBodyReverts_daiCallFailed
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                (A := A) (I := I) (g := g)
                (evmDai := { evmSolm with substate := A_dai })
                (out := ByteArray.empty) hwv hliveSolm hdebtSolm hvatCodeSolmNE hcallSolm
          exact (endThawX_daiCallFailed (g := g) rd4753 (by simp [UInt256.size]))
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hdebtSolm : endThawDebtWord σ_solm I ≠ ⟨0⟩ := by
        intro hbad
        exact hdebt (by rw [hdebtCouple, hbad])
      have hbody :
          ExecTransitionBody config contract evmSolm (∅ : Store) thawTransition.body .reverted := by
        simpa [evmSolm] using
          endThawBodyReverts_debtNonzero
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hliveSolm hdebtSolm
      exact (endThawX_debtNonzero (g := Sat256.ofUInt256 g) hlive hdebt hbodyReach)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hliveSolm : endThawLiveWord σ_solm I ≠ ⟨0⟩ := by
      intro hbad
      exact hlive (by rw [hliveCouple, hbad])
    have hbody :
        ExecTransitionBody config contract evmSolm (∅ : Store) thawTransition.body .reverted := by
      simpa [evmSolm] using
        endThawBodyReverts_liveNonzero
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hwv hliveSolm
    exact (endThawX_liveNonzero (g := Sat256.ofUInt256 g) hlive hbodyReach)
      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.End
