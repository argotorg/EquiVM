import Benchmarks.Dss.End.Trusted
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.End

set_option maxRecDepth 2000000

attribute [local simp]
  wardsSelectorBytes vatSelectorBytes catSelectorBytes dogSelectorBytes vowSelectorBytes
  potSelectorBytes spotSelectorBytes cureSelectorBytes liveSelectorBytes whenSelectorBytes
  waitSelectorBytes debtSelectorBytes tagSelectorBytes gapSelectorBytes ArtSelectorBytes
  fixSelectorBytes bagSelectorBytes outSelectorBytes relySelectorBytes denySelectorBytes
  fileAddressSelectorBytes fileUintSelectorBytes cageSelectorBytes cageIlkSelectorBytes
  snipSelectorBytes skipSelectorBytes skimSelectorBytes freeSelectorBytes thawSelectorBytes
  flowSelectorBytes packSelectorBytes cashSelectorBytes

abbrev freeIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev freeIlkValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (freeIlkWord I))

abbrev freeStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "ilk" (freeIlkValue I)

def freeLiveWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord ⟨8⟩ σ I

def freeVatWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord ⟨1⟩ σ I

def freeVatMaskedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (freeVatWord σ I) solcAddrMask

def freeVowWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord ⟨4⟩ σ I

def freeVowMaskedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (freeVowWord σ I) solcAddrMask

abbrev freeSourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev freeUrnsSelectorWord : UInt256 :=
  ⟨0x2424be5c⟩

abbrev freeUrnsSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨0x09092f97⟩ ⟨226⟩

abbrev freeUrnsOutPtr : UInt256 := ⟨128⟩
abbrev freeUrnsInSize : UInt256 := ⟨68⟩
abbrev freeUrnsOutSize : UInt256 := ⟨64⟩
abbrev freeUrnsEndPtr : UInt256 := ⟨196⟩
abbrev freeInt256LimitWord : UInt256 := UInt256.shiftLeft ⟨1⟩ ⟨255⟩
abbrev freeGrabSelectorWord : UInt256 := ⟨0x7bab3f40⟩
abbrev freeGrabSelectorShifted : UInt256 := UInt256.shiftLeft ⟨0x01eeacfd⟩ ⟨230⟩
abbrev freeGrabOutPtr : UInt256 := ⟨128⟩
abbrev freeGrabInSize : UInt256 := ⟨196⟩
abbrev freeGrabOutSize : UInt256 := ⟨0⟩
abbrev freeGrabEndPtr : UInt256 := ⟨324⟩

noncomputable def freeUrnsSelectorMem (mem : ByteArray) : ByteArray :=
  freeUrnsSelectorShifted.toByteArray.write 0 mem freeUrnsOutPtr.toNat 32

noncomputable def freeUrnsIlkMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (freeIlkWord I).toByteArray.write 0 (freeUrnsSelectorMem mem) 132 32

noncomputable def freeUrnsCalldataMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (freeSourceWord I).toByteArray.write 0 (freeUrnsIlkMem I mem) 164 32

noncomputable def freeUrnsPostCallMem (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  out.write 0 (freeUrnsCalldataMem I solcFreePtrMem) freeUrnsOutPtr.toNat
    (min freeUrnsOutSize (UInt256.ofNat out.size)).toNat

noncomputable def freeUrnsInkWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

noncomputable def freeUrnsArtWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))

noncomputable def freeGrabDinkWord (out : ByteArray) : UInt256 :=
  UInt256.sub ⟨0⟩ (freeUrnsInkWord out)

noncomputable def freeGrabSelectorMem (mem : ByteArray) : ByteArray :=
  freeGrabSelectorShifted.toByteArray.write 0 mem freeGrabOutPtr.toNat 32

noncomputable def freeGrabIlkMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (freeIlkWord I).toByteArray.write 0 (freeGrabSelectorMem mem) 132 32

noncomputable def freeGrabUsrMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (freeSourceWord I).toByteArray.write 0 (freeGrabIlkMem I mem) 164 32

noncomputable def freeGrabVMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (freeSourceWord I).toByteArray.write 0 (freeGrabUsrMem I mem) 196 32

noncomputable def freeGrabWMem (σ : AccountMap) (I : ExecutionEnv) (mem : ByteArray) :
    ByteArray :=
  (freeVowMaskedWord σ I).toByteArray.write 0 (freeGrabVMem I mem) 228 32

noncomputable def freeGrabDinkMem (σ : AccountMap) (I : ExecutionEnv) (urnOut : ByteArray)
    (mem : ByteArray) : ByteArray :=
  (freeGrabDinkWord urnOut).toByteArray.write 0 (freeGrabWMem σ I mem) 260 32

noncomputable def freeGrabCalldataMem (σ : AccountMap) (I : ExecutionEnv) (urnOut : ByteArray)
    (mem : ByteArray) : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0 (freeGrabDinkMem σ I urnOut mem) 292 32

noncomputable def freeGrabPostCallMem (σ : AccountMap) (I : ExecutionEnv)
    (urnOut out : ByteArray) : ByteArray :=
  out.write 0 (freeGrabCalldataMem σ I urnOut (freeUrnsPostCallMem I urnOut))
    freeGrabOutPtr.toNat (min freeGrabOutSize (UInt256.ofNat out.size)).toNat

noncomputable def freeGrabLogMem (σ : AccountMap) (I : ExecutionEnv)
    (urnOut out : ByteArray) : ByteArray :=
  (freeUrnsInkWord urnOut).toByteArray.write 0 (freeGrabPostCallMem σ I urnOut out) 128 32

noncomputable abbrev freeUrnsReturnValues (out : ByteArray) : List Value :=
  [.int (Int.ofNat (freeUrnsInkWord out).toNat), .int (Int.ofNat (freeUrnsArtWord out).toNat)]

noncomputable abbrev freeUrnsLocals (I : ExecutionEnv) (out : ByteArray) : Store :=
  (freeStore I).insert "vatUrn" (collapseReturns (freeUrnsReturnValues out))

noncomputable abbrev freeUrnsInkLocals (I : ExecutionEnv) (out : ByteArray) : Store :=
  (freeUrnsLocals I out).insert "ink" (.int (Int.ofNat (freeUrnsInkWord out).toNat))

noncomputable abbrev freeUrnsArtLocals (I : ExecutionEnv) (out : ByteArray) : Store :=
  (freeUrnsInkLocals I out).insert "art" (.int (Int.ofNat (freeUrnsArtWord out).toNat))

theorem freeUrnsSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (freeUrnsSelectorMem mem).size = 160 := by
  unfold freeUrnsSelectorMem freeUrnsOutPtr
  exact toByteArray_write32_size_of_ge mem freeUrnsSelectorShifted 128 96 160 hmem
    (by native_decide) (by native_decide) (by native_decide)

theorem freeUrnsIlkMem_size (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 96) :
    (freeUrnsIlkMem I mem).size = 164 := by
  unfold freeUrnsIlkMem
  exact toByteArray_write32_size_of_le (freeUrnsSelectorMem mem) (freeIlkWord I) 132
    160 164 (freeUrnsSelectorMem_size hmem)
    (by rw [freeUrnsSelectorMem_size hmem]; native_decide) (by native_decide)

theorem freeUrnsCalldataMem_size (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 96) :
    (freeUrnsCalldataMem I mem).size = 196 := by
  unfold freeUrnsCalldataMem
  exact toByteArray_write32_size_of_le (freeUrnsIlkMem I mem) (freeSourceWord I) 164
    164 196 (freeUrnsIlkMem_size I hmem)
    (by rw [freeUrnsIlkMem_size I hmem]) (by native_decide)

theorem freeUrnsPostCallMem_size_gt64 (I : ExecutionEnv) (out : ByteArray)
    (hshort : out.size < 64) (hout : out.size < UInt256.size) :
    64 < (freeUrnsPostCallMem I out).size := by
  have hmin :
      (min freeUrnsOutSize (UInt256.ofNat out.size)).toNat = out.size := by
    exact umin_ofNat_right_toNat_of_lt (c := 64) (n := out.size) (by decide) hshort hout
  unfold freeUrnsPostCallMem
  rw [hmin]
  by_cases hzero : out.size = 0
  · rw [hzero, byteArray_write_len_zero, freeUrnsCalldataMem_size I solcFreePtrMem_size]
    omega
  · change 64 < (out.write 0 (freeUrnsCalldataMem I solcFreePtrMem) 128 out.size).size
    rw [write_eq_gen out (freeUrnsCalldataMem I solcFreePtrMem) 128 out.size hzero
      le_rfl (by rw [freeUrnsCalldataMem_size I solcFreePtrMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      freeUrnsCalldataMem_size I solcFreePtrMem_size]
    omega

theorem freeUrnsSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (freeUrnsSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold freeUrnsSelectorMem freeUrnsOutPtr
  change (freeUrnsSelectorShifted.toByteArray.write 0 mem 128 32).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [toByteArray_write_read_below_of_gap freeUrnsSelectorShifted mem 128 64
    (by rw [hmem]) (by omega) (by rw [hmem]; native_decide), hread64]

theorem freeUrnsIlkMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (freeUrnsIlkMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold freeUrnsIlkMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [freeUrnsSelectorMem_size hmem]; omega) (by omega),
    freeUrnsSelectorMem_read64 hmem hread64]

theorem freeUrnsCalldataMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (freeUrnsCalldataMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold freeUrnsCalldataMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [freeUrnsIlkMem_size I hmem]) (by omega),
    freeUrnsIlkMem_read64 I hmem hread64]

theorem freeUrnsPostCallMem_read64 (I : ExecutionEnv) (out : ByteArray)
    (hshort : out.size < 64) (hout : out.size < UInt256.size) :
    (freeUrnsPostCallMem I out).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  have hmin :
      (min freeUrnsOutSize (UInt256.ofNat out.size)).toNat = out.size := by
    exact umin_ofNat_right_toNat_of_lt (c := 64) (n := out.size) (by decide) hshort hout
  unfold freeUrnsPostCallMem
  rw [hmin]
  by_cases hzero : out.size = 0
  · rw [hzero, byteArray_write_len_zero]
    exact freeUrnsCalldataMem_read64 I solcFreePtrMem_size solcFreePtrMem_read64
  · change (out.write 0 (freeUrnsCalldataMem I solcFreePtrMem) 128 out.size).readWithPadding
      64 32 = UInt256.toByteArray ⟨128⟩
    rw [write_read_below_gen_extend out (freeUrnsCalldataMem I solcFreePtrMem) 128 out.size
      64 hzero le_rfl
      (by rw [freeUrnsCalldataMem_size I solcFreePtrMem_size]; omega) (by omega)]
    exact freeUrnsCalldataMem_read64 I solcFreePtrMem_size solcFreePtrMem_read64

theorem freeUrnsPostCallMem_mload64 (I : ExecutionEnv) (out : ByteArray)
    (hshort : out.size < 64) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (freeUrnsPostCallMem I out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((freeUrnsPostCallMem I out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by
      have hgt := freeUrnsPostCallMem_size_gt64 I out hshort hout
      omega)
    (by decide)
    (freeUrnsPostCallMem_read64 I out hshort hout)

theorem freeUrnsPostCallMem_size_long (I : ExecutionEnv) (out : ByteArray)
    (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (freeUrnsPostCallMem I out).size = 196 := by
  have hmin :
      (min freeUrnsOutSize (UInt256.ofNat out.size)).toNat = 64 := by
    exact umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlong hout
  unfold freeUrnsPostCallMem
  rw [hmin]
  change (out.write 0 (freeUrnsCalldataMem I solcFreePtrMem) 128 64).size = 196
  rw [write_eq_gen out (freeUrnsCalldataMem I solcFreePtrMem) 128 64
    (by omega) (by omega)
    (by rw [freeUrnsCalldataMem_size I solcFreePtrMem_size]; omega)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    freeUrnsCalldataMem_size I solcFreePtrMem_size]
  omega

theorem freeUrnsPostCallMem_read64_long (I : ExecutionEnv) (out : ByteArray)
    (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (freeUrnsPostCallMem I out).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  have hmin :
      (min freeUrnsOutSize (UInt256.ofNat out.size)).toNat = 64 := by
    exact umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlong hout
  unfold freeUrnsPostCallMem
  rw [hmin]
  change (out.write 0 (freeUrnsCalldataMem I solcFreePtrMem) 128 64).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [write_read_below_gen_extend out (freeUrnsCalldataMem I solcFreePtrMem)
    128 64 64 (by omega) (by omega)
    (by rw [freeUrnsCalldataMem_size I solcFreePtrMem_size]; omega) (by omega)]
  exact freeUrnsCalldataMem_read64 I solcFreePtrMem_size solcFreePtrMem_read64

theorem freeUrnsPostCallMem_mload64_long (I : ExecutionEnv) (out : ByteArray)
    (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (freeUrnsPostCallMem I out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((freeUrnsPostCallMem I out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [freeUrnsPostCallMem_size_long I out hlong hout]; decide)
    (by decide)
    (freeUrnsPostCallMem_read64_long I out hlong hout)

theorem freeGrabSelectorMem_size {mem : ByteArray} (hmem : mem.size = 196) :
    (freeGrabSelectorMem mem).size = 196 := by
  unfold freeGrabSelectorMem freeGrabOutPtr
  exact toByteArray_write32_size_of_le mem freeGrabSelectorShifted 128 196 196 hmem
    (by rw [hmem]; omega) (by native_decide)

theorem freeGrabIlkMem_size (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 196) :
    (freeGrabIlkMem I mem).size = 196 := by
  unfold freeGrabIlkMem
  exact toByteArray_write32_size_of_le (freeGrabSelectorMem mem) (freeIlkWord I) 132
    196 196 (freeGrabSelectorMem_size hmem)
    (by rw [freeGrabSelectorMem_size hmem]; omega) (by native_decide)

theorem freeGrabUsrMem_size (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 196) :
    (freeGrabUsrMem I mem).size = 196 := by
  unfold freeGrabUsrMem
  exact toByteArray_write32_size_of_le (freeGrabIlkMem I mem) (freeSourceWord I) 164
    196 196 (freeGrabIlkMem_size I hmem)
    (by rw [freeGrabIlkMem_size I hmem]; omega) (by native_decide)

theorem freeGrabVMem_size (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 196) :
    (freeGrabVMem I mem).size = 228 := by
  unfold freeGrabVMem
  exact toByteArray_write32_size_of_le (freeGrabUsrMem I mem) (freeSourceWord I) 196
    196 228 (freeGrabUsrMem_size I hmem)
    (by rw [freeGrabUsrMem_size I hmem]) (by native_decide)

theorem freeGrabWMem_size (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (freeGrabWMem σ I mem).size = 260 := by
  unfold freeGrabWMem
  exact toByteArray_write32_size_of_le (freeGrabVMem I mem) (freeVowMaskedWord σ I) 228
    228 260 (freeGrabVMem_size I hmem)
    (by rw [freeGrabVMem_size I hmem]) (by native_decide)

theorem freeGrabDinkMem_size (σ : AccountMap) (I : ExecutionEnv) (urnOut : ByteArray)
    {mem : ByteArray} (hmem : mem.size = 196) :
    (freeGrabDinkMem σ I urnOut mem).size = 292 := by
  unfold freeGrabDinkMem
  exact toByteArray_write32_size_of_le (freeGrabWMem σ I mem) (freeGrabDinkWord urnOut) 260
    260 292 (freeGrabWMem_size σ I hmem)
    (by rw [freeGrabWMem_size σ I hmem]) (by native_decide)

theorem freeGrabCalldataMem_size (σ : AccountMap) (I : ExecutionEnv) (urnOut : ByteArray)
    {mem : ByteArray} (hmem : mem.size = 196) :
    (freeGrabCalldataMem σ I urnOut mem).size = 324 := by
  unfold freeGrabCalldataMem
  exact toByteArray_write32_size_of_le (freeGrabDinkMem σ I urnOut mem) (⟨0⟩ : UInt256) 292
    292 324 (freeGrabDinkMem_size σ I urnOut hmem)
    (by rw [freeGrabDinkMem_size σ I urnOut hmem]) (by native_decide)

theorem freeGrabSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (freeGrabSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold freeGrabSelectorMem freeGrabOutPtr
  change (freeGrabSelectorShifted.toByteArray.write 0 mem 128 32).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [toByteArray_write_read_below_of_gap freeGrabSelectorShifted mem 128 64
    (by rw [hmem]; omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem freeGrabIlkMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (freeGrabIlkMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold freeGrabIlkMem
  rw [toByteArray_write_read_below_of_gap (freeIlkWord I) (freeGrabSelectorMem mem) 132 64
    (by rw [freeGrabSelectorMem_size hmem]; omega) (by omega)
    (by rw [freeGrabSelectorMem_size hmem]; exact lt_usize _ (by norm_num))]
  exact freeGrabSelectorMem_read64 hmem hread64

theorem freeGrabUsrMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (freeGrabUsrMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold freeGrabUsrMem
  rw [toByteArray_write_read_below_of_gap (freeSourceWord I) (freeGrabIlkMem I mem) 164 64
    (by rw [freeGrabIlkMem_size I hmem]; omega) (by omega)
    (by rw [freeGrabIlkMem_size I hmem]; exact lt_usize _ (by norm_num))]
  exact freeGrabIlkMem_read64 I hmem hread64

theorem freeGrabVMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (freeGrabVMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold freeGrabVMem
  rw [toByteArray_write_read_below_of_gap (freeSourceWord I) (freeGrabUsrMem I mem) 196 64
    (by rw [freeGrabUsrMem_size I hmem]; omega) (by omega)
    (by rw [freeGrabUsrMem_size I hmem]; exact lt_usize _ (by norm_num))]
  exact freeGrabUsrMem_read64 I hmem hread64

theorem freeGrabWMem_read64 (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (freeGrabWMem σ I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold freeGrabWMem
  rw [toByteArray_write_read_below_of_gap (freeVowMaskedWord σ I) (freeGrabVMem I mem) 228 64
    (by rw [freeGrabVMem_size I hmem]; omega) (by omega)
    (by rw [freeGrabVMem_size I hmem]; exact lt_usize _ (by norm_num))]
  exact freeGrabVMem_read64 I hmem hread64

theorem freeGrabDinkMem_read64 (σ : AccountMap) (I : ExecutionEnv) (urnOut : ByteArray)
    {mem : ByteArray} (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (freeGrabDinkMem σ I urnOut mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold freeGrabDinkMem
  rw [toByteArray_write_read_below_of_gap (freeGrabDinkWord urnOut) (freeGrabWMem σ I mem)
    260 64 (by rw [freeGrabWMem_size σ I hmem]; omega) (by omega)
    (by rw [freeGrabWMem_size σ I hmem]; exact lt_usize _ (by norm_num))]
  exact freeGrabWMem_read64 σ I hmem hread64

theorem freeGrabCalldataMem_read64 (σ : AccountMap) (I : ExecutionEnv) (urnOut : ByteArray)
    {mem : ByteArray} (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (freeGrabCalldataMem σ I urnOut mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold freeGrabCalldataMem
  rw [toByteArray_write_read_below_of_gap (⟨0⟩ : UInt256) (freeGrabDinkMem σ I urnOut mem)
    292 64 (by rw [freeGrabDinkMem_size σ I urnOut hmem]; omega) (by omega)
    (by rw [freeGrabDinkMem_size σ I urnOut hmem]; exact lt_usize _ (by norm_num))]
  exact freeGrabDinkMem_read64 σ I urnOut hmem hread64

theorem freeGrabPostCallMem_size (σ : AccountMap) (I : ExecutionEnv)
    (urnOut out : ByteArray) (hlong : 64 ≤ urnOut.size) (hurnOut : urnOut.size < UInt256.size) :
    (freeGrabPostCallMem σ I urnOut out).size = 324 := by
  have hmin :
      (min freeGrabOutSize (UInt256.ofNat out.size)).toNat = 0 := by
    unfold freeGrabOutSize
    rw [← u256_ofNat_toNat (UInt256.ofNat out.size)]
    exact umin_ofNat_right_toNat_of_ge (by norm_num [UInt256.size]) (Nat.zero_le _)
      (UInt256.ofNat out.size).val.isLt
  unfold freeGrabPostCallMem
  rw [hmin, byteArray_write_len_zero]
  exact freeGrabCalldataMem_size σ I urnOut
    (freeUrnsPostCallMem_size_long I urnOut hlong hurnOut)

theorem freeGrabPostCallMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (urnOut out : ByteArray) (hlong : 64 ≤ urnOut.size) (hurnOut : urnOut.size < UInt256.size) :
    (freeGrabPostCallMem σ I urnOut out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hmin :
      (min freeGrabOutSize (UInt256.ofNat out.size)).toNat = 0 := by
    unfold freeGrabOutSize
    rw [← u256_ofNat_toNat (UInt256.ofNat out.size)]
    exact umin_ofNat_right_toNat_of_ge (by norm_num [UInt256.size]) (Nat.zero_le _)
      (UInt256.ofNat out.size).val.isLt
  unfold freeGrabPostCallMem
  rw [hmin, byteArray_write_len_zero]
  exact freeGrabCalldataMem_read64 σ I urnOut
    (freeUrnsPostCallMem_size_long I urnOut hlong hurnOut)
    (freeUrnsPostCallMem_read64_long I urnOut hlong hurnOut)

theorem freeGrabLogMem_size (σ : AccountMap) (I : ExecutionEnv)
    (urnOut out : ByteArray) (hlong : 64 ≤ urnOut.size) (hurnOut : urnOut.size < UInt256.size) :
    (freeGrabLogMem σ I urnOut out).size = 324 := by
  unfold freeGrabLogMem
  exact toByteArray_write32_size_of_le (freeGrabPostCallMem σ I urnOut out)
    (freeUrnsInkWord urnOut) 128 324 324
    (freeGrabPostCallMem_size σ I urnOut out hlong hurnOut)
    (by rw [freeGrabPostCallMem_size σ I urnOut out hlong hurnOut]; native_decide)
    (by native_decide)

theorem freeGrabLogMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (urnOut out : ByteArray) (hlong : 64 ≤ urnOut.size) (hurnOut : urnOut.size < UInt256.size) :
    (freeGrabLogMem σ I urnOut out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold freeGrabLogMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [freeGrabPostCallMem_size σ I urnOut out hlong hurnOut]; native_decide)
    (by native_decide)]
  exact freeGrabPostCallMem_read64 σ I urnOut out hlong hurnOut

theorem freeGrabCalldataMem_read128_4 (σ : AccountMap) (I : ExecutionEnv)
    (urnOut : ByteArray) {mem : ByteArray} (hmem : mem.size = 196) :
    (freeGrabCalldataMem σ I urnOut mem).readWithPadding 128 4 = grabSelector := by
  have hSelectorSize := freeGrabSelectorMem_size hmem
  have hIlkSize := freeGrabIlkMem_size I hmem
  have hUsrSize := freeGrabUsrMem_size I hmem
  have hVSize := freeGrabVMem_size I hmem
  have hWSize := freeGrabWMem_size σ I hmem
  have hDinkSize := freeGrabDinkMem_size σ I urnOut hmem
  unfold freeGrabCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (⟨0⟩ : UInt256)
      (freeGrabDinkMem σ I urnOut mem) 292 128 4
      (by rw [hDinkSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hDinkSize]; native_decide)]
  unfold freeGrabDinkMem
  rw [toByteArray_write_read_below_len_of_gap (freeGrabDinkWord urnOut)
      (freeGrabWMem σ I mem) 260 128 4
      (by rw [hWSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hWSize]; native_decide)]
  unfold freeGrabWMem
  rw [toByteArray_write_read_below_len_of_gap (freeVowMaskedWord σ I)
      (freeGrabVMem I mem) 228 128 4
      (by rw [hVSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hVSize]; native_decide)]
  unfold freeGrabVMem
  rw [toByteArray_write_read_below_len_of_gap (freeSourceWord I)
      (freeGrabUsrMem I mem) 196 128 4
      (by rw [hUsrSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hUsrSize]; native_decide)]
  unfold freeGrabUsrMem
  rw [toByteArray_write_read_below_len_of_gap (freeSourceWord I)
      (freeGrabIlkMem I mem) 164 128 4
      (by rw [hIlkSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hIlkSize]; native_decide)]
  unfold freeGrabIlkMem
  rw [toByteArray_write_read_below_len_of_gap (freeIlkWord I)
      (freeGrabSelectorMem mem) 132 128 4
      (by rw [hSelectorSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hSelectorSize]; native_decide)]
  unfold freeGrabSelectorMem freeGrabOutPtr
  change (freeGrabSelectorShifted.toByteArray.write 0 mem 128 32).readWithPadding 128 4 =
    grabSelector
  rw [toByteArray_write_read_window_of_gap freeGrabSelectorShifted mem 128 0 4
      (by omega) (by omega) (by omega) (by rw [hmem]; native_decide)]
  native_decide

theorem freeGrabCalldataMem_read132_32 (σ : AccountMap) (I : ExecutionEnv)
    (urnOut : ByteArray) {mem : ByteArray} (hmem : mem.size = 196) :
    (freeGrabCalldataMem σ I urnOut mem).readWithPadding 132 32 =
      (freeIlkWord I).toByteArray := by
  have hIlkSize := freeGrabIlkMem_size I hmem
  have hUsrSize := freeGrabUsrMem_size I hmem
  have hVSize := freeGrabVMem_size I hmem
  have hWSize := freeGrabWMem_size σ I hmem
  have hDinkSize := freeGrabDinkMem_size σ I urnOut hmem
  unfold freeGrabCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (⟨0⟩ : UInt256)
      (freeGrabDinkMem σ I urnOut mem) 292 132 32
      (by rw [hDinkSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hDinkSize]; native_decide)]
  unfold freeGrabDinkMem
  rw [toByteArray_write_read_below_len_of_gap (freeGrabDinkWord urnOut)
      (freeGrabWMem σ I mem) 260 132 32
      (by rw [hWSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hWSize]; native_decide)]
  unfold freeGrabWMem
  rw [toByteArray_write_read_below_len_of_gap (freeVowMaskedWord σ I)
      (freeGrabVMem I mem) 228 132 32
      (by rw [hVSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hVSize]; native_decide)]
  unfold freeGrabVMem
  rw [toByteArray_write_read_below_len_of_gap (freeSourceWord I)
      (freeGrabUsrMem I mem) 196 132 32
      (by rw [hUsrSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hUsrSize]; native_decide)]
  unfold freeGrabUsrMem
  rw [toByteArray_write_read_below_len_of_gap (freeSourceWord I)
      (freeGrabIlkMem I mem) 164 132 32
      (by rw [hIlkSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hIlkSize]; native_decide)]
  unfold freeGrabIlkMem
  rw [toByteArray_write_read_back_of_gap (freeIlkWord I) (freeGrabSelectorMem mem) 132
      (by rw [freeGrabSelectorMem_size hmem]; native_decide)]

theorem freeGrabCalldataMem_read164_32 (σ : AccountMap) (I : ExecutionEnv)
    (urnOut : ByteArray) {mem : ByteArray} (hmem : mem.size = 196) :
    (freeGrabCalldataMem σ I urnOut mem).readWithPadding 164 32 =
      (freeSourceWord I).toByteArray := by
  have hUsrSize := freeGrabUsrMem_size I hmem
  have hVSize := freeGrabVMem_size I hmem
  have hWSize := freeGrabWMem_size σ I hmem
  have hDinkSize := freeGrabDinkMem_size σ I urnOut hmem
  unfold freeGrabCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (⟨0⟩ : UInt256)
      (freeGrabDinkMem σ I urnOut mem) 292 164 32
      (by rw [hDinkSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hDinkSize]; native_decide)]
  unfold freeGrabDinkMem
  rw [toByteArray_write_read_below_len_of_gap (freeGrabDinkWord urnOut)
      (freeGrabWMem σ I mem) 260 164 32
      (by rw [hWSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hWSize]; native_decide)]
  unfold freeGrabWMem
  rw [toByteArray_write_read_below_len_of_gap (freeVowMaskedWord σ I)
      (freeGrabVMem I mem) 228 164 32
      (by rw [hVSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hVSize]; native_decide)]
  unfold freeGrabVMem
  rw [toByteArray_write_read_below_len_of_gap (freeSourceWord I)
      (freeGrabUsrMem I mem) 196 164 32
      (by rw [hUsrSize]) (by omega) (by omega) (by omega)
      (by rw [hUsrSize]; native_decide)]
  unfold freeGrabUsrMem
  rw [toByteArray_write_read_back_of_gap (freeSourceWord I) (freeGrabIlkMem I mem) 164
      (by rw [freeGrabIlkMem_size I hmem]; native_decide)]

theorem freeGrabCalldataMem_read196_32 (σ : AccountMap) (I : ExecutionEnv)
    (urnOut : ByteArray) {mem : ByteArray} (hmem : mem.size = 196) :
    (freeGrabCalldataMem σ I urnOut mem).readWithPadding 196 32 =
      (freeSourceWord I).toByteArray := by
  have hVSize := freeGrabVMem_size I hmem
  have hWSize := freeGrabWMem_size σ I hmem
  have hDinkSize := freeGrabDinkMem_size σ I urnOut hmem
  unfold freeGrabCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (⟨0⟩ : UInt256)
      (freeGrabDinkMem σ I urnOut mem) 292 196 32
      (by rw [hDinkSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hDinkSize]; native_decide)]
  unfold freeGrabDinkMem
  rw [toByteArray_write_read_below_len_of_gap (freeGrabDinkWord urnOut)
      (freeGrabWMem σ I mem) 260 196 32
      (by rw [hWSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hWSize]; native_decide)]
  unfold freeGrabWMem
  rw [toByteArray_write_read_below_len_of_gap (freeVowMaskedWord σ I)
      (freeGrabVMem I mem) 228 196 32
      (by rw [hVSize]) (by omega) (by omega) (by omega)
      (by rw [hVSize]; native_decide)]
  unfold freeGrabVMem
  rw [toByteArray_write_read_back_of_gap (freeSourceWord I) (freeGrabUsrMem I mem) 196
      (by rw [freeGrabUsrMem_size I hmem]; native_decide)]

theorem freeGrabCalldataMem_read228_32 (σ : AccountMap) (I : ExecutionEnv)
    (urnOut : ByteArray) {mem : ByteArray} (hmem : mem.size = 196) :
    (freeGrabCalldataMem σ I urnOut mem).readWithPadding 228 32 =
      (freeVowMaskedWord σ I).toByteArray := by
  have hWSize := freeGrabWMem_size σ I hmem
  have hDinkSize := freeGrabDinkMem_size σ I urnOut hmem
  unfold freeGrabCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (⟨0⟩ : UInt256)
      (freeGrabDinkMem σ I urnOut mem) 292 228 32
      (by rw [hDinkSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hDinkSize]; native_decide)]
  unfold freeGrabDinkMem
  rw [toByteArray_write_read_below_len_of_gap (freeGrabDinkWord urnOut)
      (freeGrabWMem σ I mem) 260 228 32
      (by rw [hWSize]) (by omega) (by omega) (by omega)
      (by rw [hWSize]; native_decide)]
  unfold freeGrabWMem
  rw [toByteArray_write_read_back_of_gap (freeVowMaskedWord σ I) (freeGrabVMem I mem) 228
      (by rw [freeGrabVMem_size I hmem]; native_decide)]

theorem freeGrabCalldataMem_read260_32 (σ : AccountMap) (I : ExecutionEnv)
    (urnOut : ByteArray) {mem : ByteArray} (hmem : mem.size = 196) :
    (freeGrabCalldataMem σ I urnOut mem).readWithPadding 260 32 =
      (freeGrabDinkWord urnOut).toByteArray := by
  have hDinkSize := freeGrabDinkMem_size σ I urnOut hmem
  unfold freeGrabCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (⟨0⟩ : UInt256)
      (freeGrabDinkMem σ I urnOut mem) 292 260 32
      (by rw [hDinkSize]) (by omega) (by omega) (by omega)
      (by rw [hDinkSize]; native_decide)]
  unfold freeGrabDinkMem
  rw [toByteArray_write_read_back_of_gap (freeGrabDinkWord urnOut) (freeGrabWMem σ I mem)
      260 (by rw [freeGrabWMem_size σ I hmem]; native_decide)]

theorem freeGrabCalldataMem_read292_32 (σ : AccountMap) (I : ExecutionEnv)
    (urnOut : ByteArray) {mem : ByteArray} (hmem : mem.size = 196) :
    (freeGrabCalldataMem σ I urnOut mem).readWithPadding 292 32 =
      (⟨0⟩ : UInt256).toByteArray := by
  unfold freeGrabCalldataMem
  rw [toByteArray_write_read_back_of_gap (⟨0⟩ : UInt256) (freeGrabDinkMem σ I urnOut mem)
      292 (by rw [freeGrabDinkMem_size σ I urnOut hmem]; native_decide)]

theorem freeGrabCalldataMem_read128_196 (σ : AccountMap) (I : ExecutionEnv)
    (urnOut : ByteArray) {mem : ByteArray} (hmem : mem.size = 196) :
    (freeGrabCalldataMem σ I urnOut mem).readWithPadding 128 196 =
      grabSelector ++ (freeIlkWord I).toByteArray ++ (freeSourceWord I).toByteArray ++
        (freeSourceWord I).toByteArray ++ (freeVowMaskedWord σ I).toByteArray ++
        (freeGrabDinkWord urnOut).toByteArray ++ (⟨0⟩ : UInt256).toByteArray := by
  have hsize : (freeGrabCalldataMem σ I urnOut mem).size = 324 :=
    freeGrabCalldataMem_size σ I urnOut hmem
  rw [show 196 = 4 + 192 from rfl,
    byteArray_readWithPadding_split (freeGrabCalldataMem σ I urnOut mem) 128 4 192
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 192 = 32 + 160 from rfl,
    byteArray_readWithPadding_split (freeGrabCalldataMem σ I urnOut mem) 132 32 160
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 160 = 32 + 128 from rfl,
    byteArray_readWithPadding_split (freeGrabCalldataMem σ I urnOut mem) 164 32 128
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 128 = 32 + 96 from rfl,
    byteArray_readWithPadding_split (freeGrabCalldataMem σ I urnOut mem) 196 32 96
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split (freeGrabCalldataMem σ I urnOut mem) 228 32 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (freeGrabCalldataMem σ I urnOut mem) 260 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [freeGrabCalldataMem_read128_4 σ I urnOut hmem,
    freeGrabCalldataMem_read132_32 σ I urnOut hmem,
    freeGrabCalldataMem_read164_32 σ I urnOut hmem,
    freeGrabCalldataMem_read196_32 σ I urnOut hmem,
    freeGrabCalldataMem_read228_32 σ I urnOut hmem,
    freeGrabCalldataMem_read260_32 σ I urnOut hmem,
    freeGrabCalldataMem_read292_32 σ I urnOut hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem freeWordOfIntSubToUInt256 (x y : UInt256) :
    EVM.wordOfInt ((x.toNat : Int) - (y.toNat : Int)) = UInt256.sub x y := by
  by_cases hle : y.toNat ≤ x.toNat
  · have hnonneg : 0 ≤ (x.toNat : Int) - (y.toNat : Int) := by omega
    rw [wordOfInt_nonneg _ hnonneg]
    apply u256_inj
    have htoNat : ((x.toNat : Int) - (y.toNat : Int)).toNat = x.toNat - y.toNat := by
      omega
    rw [usub_toNat (a := x) (b := y) hle]
    simp [EVM.word, EVM.uintN, htoNat]
    exact Nat.mod_eq_of_lt (by exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.val.isLt)
  · have hlt : x.toNat < y.toNat := Nat.lt_of_not_ge hle
    rw [EVM.wordOfInt]
    have hwordMod : EVM.wordModulus = UInt256.size := by native_decide
    have hneg : (x.toNat : Int) - (y.toNat : Int) < 0 := by omega
    rw [if_pos hneg]
    have hnatAbs :
        Int.natAbs ((x.toNat : Int) - (y.toNat : Int)) = y.toNat - x.toNat := by
      omega
    have hdiffMod :
        (y.toNat - x.toNat) % EVM.wordModulus = y.toNat - x.toNat := by
      apply Nat.mod_eq_of_lt
      rw [hwordMod]
      have hy : y.toNat < UInt256.size := y.val.isLt
      omega
    have hdiffNe : y.toNat - x.toNat ≠ 0 := by omega
    rw [hnatAbs, hdiffMod, if_neg hdiffNe]
    apply u256_inj
    rw [usub_toNat_underflow (a := x) (b := y) hlt]
    have hword :
        EVM.wordModulus - (y.toNat - x.toNat) =
          UInt256.size + x.toNat - y.toNat := by
      rw [hwordMod]
      omega
    simp [EVM.word, EVM.uintN, hword, show EVM.twoPow 256 = UInt256.size from by native_decide]
    exact Nat.mod_eq_of_lt (by
      have hy : y.toNat < UInt256.size := y.val.isLt
      omega)

theorem freeAddressArgEncoding (a : AccountAddress) :
    ABI.encodeABIValue? (.elem .address) (.address a) =
      some (EVM.Word.toBytesBE (UInt256.ofNat a.val)) := by
  simp [ABI.encodeABIValue?, ABI.encodeABIWord?]
  rw [show EVM.word (↑a : ℕ) = UInt256.ofNat (↑a : ℕ) from rfl]

theorem freeInt256ZeroArgEncoding :
    ABI.encodeABIValue? (.elem (.int int256Int)) (.int 0) =
      some (EVM.Word.toBytesBE (⟨0⟩ : UInt256)) := by
  native_decide

theorem freeInt256NegInkArgEncoding (out : ByteArray)
    (hink : (freeUrnsInkWord out).toNat ≤ freeInt256LimitWord.toNat) :
    ABI.encodeABIValue? (.elem (.int int256Int))
      (.int (-(Int.ofNat (freeUrnsInkWord out).toNat))) =
      some (EVM.Word.toBytesBE (freeGrabDinkWord out)) := by
  have hword :
      EVM.wordOfInt (-(Int.ofNat (freeUrnsInkWord out).toNat)) =
        freeGrabDinkWord out := by
    simpa [freeGrabDinkWord] using
      freeWordOfIntSubToUInt256 (⟨0⟩ : UInt256) (freeUrnsInkWord out)
  have hlimit : freeInt256LimitWord.toNat = EVM.twoPow 255 := by
    native_decide
  have hlePow : (freeUrnsInkWord out).toNat ≤ EVM.twoPow 255 := by
    rw [← hlimit]
    exact hink
  have hcond :
      (freeUrnsInkWord out).toNat ≤ EVM.twoPow 255 ∧
        -↑(freeUrnsInkWord out).toNat < (↑(EVM.twoPow 255) : Int) := by
    constructor
    · exact hlePow
    · have hpos : 0 < EVM.twoPow 255 := by native_decide
      omega
  simp [int256Int, ABI.encodeABIValue?, ABI.encodeABIWord?]
  rw [if_pos hcond]
  simp only [Option.bind]
  apply congrArg some
  change EVM.Word.toBytesBE (EVM.wordOfInt (-(Int.ofNat (freeUrnsInkWord out).toNat))) =
    EVM.Word.toBytesBE (freeGrabDinkWord out)
  rw [hword]

theorem freeVowAddressWord (σ : AccountMap) (I : ExecutionEnv) :
    EVM.word ↑(AccountAddress.ofUInt256 (freeVowMaskedWord σ I)) =
      freeVowMaskedWord σ I := by
  have hcanon : (freeVowMaskedWord σ I).toNat < EVM.addressModulus := by
    simpa [freeVowMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (freeVowWord σ I)
  have hcanonVal : ↑(freeVowMaskedWord σ I).val < EVM.addressModulus := by
    simpa [UInt256.toNat] using hcanon
  apply u256_inj
  simp only [EVM.word, EVM.uintN, UInt256.toNat, AccountAddress.ofUInt256, Fin.ofNat]
  rw [show AccountAddress.size = EVM.addressModulus from by decide]
  rw [Nat.mod_eq_of_lt hcanonVal]
  rw [Nat.mod_eq_of_lt hcanonVal]
  rw [Nat.mod_eq_of_lt (by exact (freeVowMaskedWord σ I).val.isLt)]

theorem freeGrabEncodeWords (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray)
    (hink : (freeUrnsInkWord out).toNat ≤ freeInt256LimitWord.toNat) :
    config.externalABI.encode? "grab"
      [freeIlkValue I, .address I.source, .address I.source,
        .address (AccountAddress.ofUInt256 (freeVowMaskedWord σ I)),
        .int (-(Int.ofNat (freeUrnsInkWord out).toNat)), .int 0] =
      some (grabSelector ++ (freeIlkWord I).toByteArray ++ (freeSourceWord I).toByteArray ++
        (freeSourceWord I).toByteArray ++ (freeVowMaskedWord σ I).toByteArray ++
        (freeGrabDinkWord out).toByteArray ++ (⟨0⟩ : UInt256).toByteArray) := by
  have hIlk : ABI.encodeABIValue? bytes32 (freeIlkValue I) =
      some (EVM.Word.toBytesBE (freeIlkWord I)) := by
    have hlen : (EVM.Word.toBytesBE (freeIlkWord I)).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size (freeIlkWord I)
    simp [ABI.encodeABIValue?, hlen, zeroBytes, freeIlkValue, bytes32, bytes32Width]
  have hIlk' : ABI.encodeABIValue? (.elem (.bytes bytes32Width)) (freeIlkValue I) =
      some (EVM.Word.toBytesBE (freeIlkWord I)) := by
    simpa [bytes32] using hIlk
  have hsource : ABI.encodeABIValue? (.elem .address) (.address I.source) =
      some (EVM.Word.toBytesBE (freeSourceWord I)) := by
    simp [ABI.encodeABIValue?, ABI.encodeABIWord?, freeSourceWord]
    rw [show EVM.word (↑I.source : ℕ) = UInt256.ofNat (↑I.source : ℕ) from rfl]
  have hvow : ABI.encodeABIValue? (.elem .address)
      (.address (AccountAddress.ofUInt256 (freeVowMaskedWord σ I))) =
      some (EVM.Word.toBytesBE (freeVowMaskedWord σ I)) := by
    simp [ABI.encodeABIValue?, ABI.encodeABIWord?, freeVowAddressWord σ I]
  have hdink := freeInt256NegInkArgEncoding out hink
  have hdink' : ABI.encodeABIValue? (.elem (.int int256Int))
      (.int (-↑(freeUrnsInkWord out).toNat)) =
      some (EVM.Word.toBytesBE (freeGrabDinkWord out)) := by
    simpa using hdink
  have hzero := freeInt256ZeroArgEncoding
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    ABI.encodeABIValuesFrom?, hIlk', hsource, hvow, hzero, addr, bytes32, int256]
  rw [hdink']
  simp only [Option.bind]
  apply congrArg some
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc, word_toBytesBE_toByteArray_eq_toByteArray]

theorem freeGrabEncode_eq (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray)
    (hink : (freeUrnsInkWord out).toNat ≤ freeInt256LimitWord.toNat)
    {mem : ByteArray} (hmem : mem.size = 196) :
    config.externalABI.encode? "grab"
      [freeIlkValue I, .address I.source, .address I.source,
        .address (AccountAddress.ofUInt256 (freeVowMaskedWord σ I)),
        .int (-(Int.ofNat (freeUrnsInkWord out).toNat)), .int 0] =
      some ((freeGrabCalldataMem σ I out mem).readWithPadding
        freeGrabOutPtr.toNat freeGrabInSize.toNat) := by
  rw [show freeGrabOutPtr.toNat = 128 by native_decide,
    show freeGrabInSize.toNat = 196 by native_decide]
  rw [freeGrabCalldataMem_read128_196 σ I out hmem]
  exact freeGrabEncodeWords σ I out hink

theorem freeEVMAddress_ofNat_toNat_eq_ofUInt256 (w : UInt256) :
    EVM.address (↑(AccountAddress.ofNat w.toNat) : ℕ) = AccountAddress.ofUInt256 w := by
  apply Fin.ext
  simp [EVM.address, EVM.uintN, AccountAddress.ofNat, AccountAddress.ofUInt256,
    UInt256.toNat]
  rw [show AccountAddress.size = EVM.twoPow 160 from by decide]
  rw [Nat.mod_mod]

private theorem freeAccountMapExtensionalEq_of_accountMapEquiv {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) : accountMapExtensionalEq σ τ := by
  intro addr
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ] at hστ ⊢
  exact ⟨hστ.1, hστ.2.1, hστ.2.2.1, hστ.2.2.2.1, hστ.2.2.2.2⟩

private theorem freeAccountMapEquiv_of_accountMapExtensionalEq {σ τ : AccountMap}
    (hστ : accountMapExtensionalEq σ τ) : accountMapEquiv σ τ := by
  intro addr
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ] at hστ ⊢
  exact ⟨hστ.1, hστ.2.1, hστ.2.2.1, hστ.2.2.2.1, hστ.2.2.2.2⟩

theorem freeTypedCallViaEVM_accountMapEquiv_noSubstate {cfg : Config}
    {evm_evm evm_solm evm'_evm : EVM.State}
    {tgt : EVM.Address} {name : Ident} {value : ℤ} {args : List Value} {z : Bool}
    {out : ByteArray} {callPerm : Bool}
    (hcall : typedCallViaEVM cfg evm_evm tgt name value args (z, evm'_evm, out) callPerm)
    (hAccounts : accountMapEquiv evm_evm.accountMap evm_solm.accountMap)
    (hOriginalAccounts : evm_evm.σ₀ = evm_solm.σ₀)
    (hCreated : evm_solm.createdAccounts = evm_evm.createdAccounts)
    (hGenesis : evm_solm.genesisBlockHeader = evm_evm.genesisBlockHeader)
    (hBlocks : evm_solm.blocks = evm_evm.blocks)
    (hEnv : evm_solm.executionEnv = evm_evm.executionEnv) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM cfg evm_solm tgt name value args
        (z,
          { evm_solm with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := evm'_evm.createdAccounts },
          out) callPerm ∧
      accountMapEquiv evm'_evm.accountMap σ'_solm := by
  obtain ⟨calldata, hdecode, hcall⟩ := hcall
  have h_ext_eq : accountMapExtensionalEq evm_evm.accountMap evm_solm.accountMap :=
    freeAccountMapExtensionalEq_of_accountMapEquiv hAccounts
  cases hcall with
  | callMade hvalue hTheta hevm' hvalue' hdepth =>
    obtain ⟨callGas, A_in, hTheta⟩ := hTheta
    rename_i valueWord cA' σ' g' A'
    generalize htheta_solm :
      Ethereum.EVM.Θ evm_solm.executionEnv.blobVersionedHashes evm_solm.createdAccounts
        evm_solm.genesisBlockHeader evm_solm.blocks evm_solm.accountMap evm_solm.σ₀ A_in
        evm_solm.executionEnv.codeOwner evm_solm.executionEnv.sender tgt
        (toExecute evm_solm.accountMap tgt) callGas
        (UInt256.ofNat evm_solm.executionEnv.gasPrice) valueWord valueWord calldata
        (evm_solm.executionEnv.depth + 1) evm_solm.executionEnv.header
        callPerm = thetaRes
    have hcode_equiv :
        toExecute evm_evm.accountMap tgt = toExecute evm_solm.accountMap tgt :=
      accountMapExtensionalEq_toExecute h_ext_eq tgt
    have htheta_solm' :
        Ethereum.EVM.Θ evm_evm.executionEnv.blobVersionedHashes evm_evm.createdAccounts
          evm_evm.genesisBlockHeader evm_evm.blocks evm_solm.accountMap evm_evm.σ₀ A_in
          evm_evm.executionEnv.codeOwner evm_evm.executionEnv.sender tgt
          (toExecute evm_evm.accountMap tgt) callGas
          (UInt256.ofNat evm_evm.executionEnv.gasPrice) valueWord valueWord calldata
          (evm_evm.executionEnv.depth + 1) evm_evm.executionEnv.header
          callPerm =
          (thetaRes.1, thetaRes.2.1, thetaRes.2.2.1, thetaRes.2.2.2.1,
            thetaRes.2.2.2.2.1, thetaRes.2.2.2.2.2) := by
      rw [← htheta_solm]
      rw [hCreated, ← hOriginalAccounts, hGenesis, hBlocks, hEnv, hcode_equiv]
    let a1 : AccountAddress := ⟨0, by simp [AccountAddress.size]⟩
    have hTheta_rel :=
      (accountMap_extensionality_of_Theta_and_Lambda
      (blobVersionedHashes := evm_evm.executionEnv.blobVersionedHashes)
      (createdAccounts := evm_evm.createdAccounts)
      (genesisBlockHeader := evm_evm.genesisBlockHeader)
      (blocks := evm_evm.blocks)
      (σ₁ := evm_evm.accountMap)
      (σ₂ := evm_solm.accountMap)
      (σ₀ := evm_evm.σ₀)
      (A := A_in)
      (s := evm_evm.executionEnv.codeOwner)
      (o := evm_evm.executionEnv.sender)
      (r := tgt)
      (g := callGas)
      (p := UInt256.ofNat evm_evm.executionEnv.gasPrice)
      (v := valueWord)
      (v' := valueWord)
      (d := calldata)
      (i := ByteArray.empty)
      (ζ := none)
      (H := evm_evm.executionEnv.header)
      (w := callPerm)
      a1 a1
      (toExecute evm_evm.accountMap tgt)
      cA' thetaRes.1
      σ' thetaRes.2.1
      g' thetaRes.2.2.1
      A' thetaRes.2.2.2.1
      z  thetaRes.2.2.2.2.1
      out thetaRes.2.2.2.2.2
      (evm_evm.executionEnv.depth + 1)
      h_ext_eq).1 hTheta.symm htheta_solm'
    have hCreated' : evm'_evm.createdAccounts = thetaRes.1 := by
      simp [hevm', hTheta_rel.1]
    have hTheta_s :
        (evm'_evm.createdAccounts, thetaRes.2.1, thetaRes.2.2.1, thetaRes.2.2.2.1, z, out) =
          Ethereum.EVM.Θ evm_solm.executionEnv.blobVersionedHashes evm_solm.createdAccounts
            evm_solm.genesisBlockHeader evm_solm.blocks evm_solm.accountMap evm_solm.σ₀ A_in
            evm_solm.executionEnv.codeOwner evm_solm.executionEnv.sender tgt
            (toExecute evm_solm.accountMap tgt) callGas
            (UInt256.ofNat evm_solm.executionEnv.gasPrice) valueWord valueWord calldata
            (evm_solm.executionEnv.depth + 1) evm_solm.executionEnv.header
            callPerm := by
      rw [hTheta_rel.2.2.2.1, hTheta_rel.2.2.2.2.1]
      rw [hCreated']
      exact htheta_solm.symm
    use thetaRes.2.1
    use thetaRes.2.2.2.1
    constructor
    · refine ⟨calldata, hdecode, ?_⟩
      exact callViaEVM.callMade (perm := callPerm) hvalue
        ⟨callGas, A_in, hTheta_s⟩ rfl (by
        rw [hEnv]
        rw [← accountMapExtensionalEq_balanceOf h_ext_eq evm_evm.executionEnv.codeOwner]
        exact hvalue') (by
        rw [hEnv]
        exact hdepth)
    · have hσext : accountMapExtensionalEq σ' thetaRes.2.1 := hTheta_rel.2.2.2.2.2
      simpa [hevm'] using freeAccountMapEquiv_of_accountMapExtensionalEq hσext
  | callNotMade hsubstate hevm' hvalue =>
    let A' := (State.addAccessedAccount evm_solm tgt).substate
    use evm_solm.accountMap
    use A'
    constructor
    · refine ⟨calldata, hdecode, ?_⟩
      apply callViaEVM.callNotMade (perm := callPerm)
      · rfl
      · simp [A', hCreated, hevm']
      · rw [hEnv]
        rw [← accountMapExtensionalEq_balanceOf h_ext_eq evm_evm.executionEnv.codeOwner]
        exact hvalue
    · simpa [hevm'] using hAccounts

theorem freeUrnsPostCallMem_read128_long (I : ExecutionEnv) (out : ByteArray)
    (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (freeUrnsPostCallMem I out).readWithPadding 128 32 = out.extract 0 32 := by
  have hmin :
      (min freeUrnsOutSize (UInt256.ofNat out.size)).toNat = 64 := by
    exact umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlong hout
  unfold freeUrnsPostCallMem
  rw [hmin]
  change (out.write 0 (freeUrnsCalldataMem I solcFreePtrMem) 128 64).readWithPadding 128 32 =
    out.extract 0 32
  rw [write_eq_gen out (freeUrnsCalldataMem I solcFreePtrMem) 128 64
    (by omega) (by omega)
    (by rw [freeUrnsCalldataMem_size I solcFreePtrMem_size]; omega)]
  have hprefix : ((freeUrnsCalldataMem I solcFreePtrMem).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, freeUrnsCalldataMem_size I solcFreePtrMem_size]
    omega
  have hsrc : (out.extract 0 64).size = 64 := by
    rw [ByteArray.size_extract]
    omega
  have hheadSize :
      ((freeUrnsCalldataMem I solcFreePtrMem).extract 0 128 ++ out.extract 0 64).size = 192 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  have hreadIn :
      128 + 32 ≤
        (((freeUrnsCalldataMem I solcFreePtrMem).extract 0 128 ++ out.extract 0 64) ++
          (freeUrnsCalldataMem I solcFreePtrMem).extract (128 + 64)
            (freeUrnsCalldataMem I solcFreePtrMem).size).size := by
    rw [ByteArray.size_append, hheadSize]
    omega
  rw [readWithPadding_eq_extract _ 128 hreadIn]
  rw [extract_append_left _ _ 128 160 (by rw [hheadSize]; omega)]
  rw [extract_append_right_window _ _ 128 160 (by rw [hprefix]), hprefix]
  rw [show 128 - 128 = 0 by omega, show 160 - 128 = 32 by omega]
  rw [extract_extract_BA]
  norm_num

theorem freeUrnsPostCallMem_mload128_long (I : ExecutionEnv) (out : ByteArray)
    (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (freeUrnsPostCallMem I out).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((freeUrnsPostCallMem I out).readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
      freeUrnsInkWord out := by
  unfold freeUrnsInkWord
  rw [if_neg]
  · change UInt256.ofNat
      (fromByteArrayBigEndian ((freeUrnsPostCallMem I out).readWithPadding 128 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
    rw [freeUrnsPostCallMem_read128_long I out hlong hout]
  · exact not_or.mpr
      ⟨by rw [freeUrnsPostCallMem_size_long I out hlong hout]; decide, by native_decide⟩

theorem freeUrnsPostCallMem_read160_long (I : ExecutionEnv) (out : ByteArray)
    (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (freeUrnsPostCallMem I out).readWithPadding 160 32 = out.extract 32 64 := by
  have hmin :
      (min freeUrnsOutSize (UInt256.ofNat out.size)).toNat = 64 := by
    exact umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlong hout
  unfold freeUrnsPostCallMem
  rw [hmin]
  change (out.write 0 (freeUrnsCalldataMem I solcFreePtrMem) 128 64).readWithPadding 160 32 =
    out.extract 32 64
  rw [write_eq_gen out (freeUrnsCalldataMem I solcFreePtrMem) 128 64
    (by omega) (by omega)
    (by rw [freeUrnsCalldataMem_size I solcFreePtrMem_size]; omega)]
  have hprefix : ((freeUrnsCalldataMem I solcFreePtrMem).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, freeUrnsCalldataMem_size I solcFreePtrMem_size]
    omega
  have hsrc : (out.extract 0 64).size = 64 := by
    rw [ByteArray.size_extract]
    omega
  have hmemSize :
      ((freeUrnsCalldataMem I solcFreePtrMem).extract 0 128 ++ out.extract 0 64).size = 192 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  have hreadIn :
      160 + 32 ≤
        (((freeUrnsCalldataMem I solcFreePtrMem).extract 0 128 ++ out.extract 0 64) ++
          (freeUrnsCalldataMem I solcFreePtrMem).extract (128 + 64)
            (freeUrnsCalldataMem I solcFreePtrMem).size).size := by
    rw [ByteArray.size_append, hmemSize]
    omega
  rw [readWithPadding_eq_extract _ 160 hreadIn]
  rw [extract_append_left _ _ 160 192 (by rw [hmemSize])]
  rw [extract_append_right_window _ _ 160 192 (by rw [hprefix]; omega), hprefix]
  rw [show 160 - 128 = 32 by omega, show 192 - 128 = 64 by omega]
  rw [extract_extract_BA]
  norm_num

theorem freeUrnsPostCallMem_mload160_long (I : ExecutionEnv) (out : ByteArray)
    (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨160⟩ : UInt256).toNat ≥ (freeUrnsPostCallMem I out).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((freeUrnsPostCallMem I out).readWithPadding (⟨160⟩ : UInt256).toNat 32))) =
      freeUrnsArtWord out := by
  unfold freeUrnsArtWord
  rw [if_neg]
  · change UInt256.ofNat
      (fromByteArrayBigEndian ((freeUrnsPostCallMem I out).readWithPadding 160 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))
    rw [freeUrnsPostCallMem_read160_long I out hlong hout]
  · exact not_or.mpr
      ⟨by rw [freeUrnsPostCallMem_size_long I out hlong hout]; decide, by native_decide⟩

theorem solcErrorStringMem0_size_of_size196 {mem : ByteArray} (hmem : mem.size = 196) :
    (solcErrorStringMem0 mem).size = 196 := by
  unfold solcErrorStringMem0
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  simp [ByteArray.size_append, ByteArray.size_extract, hmem]

theorem solcErrorStringMem1_size_of_size196 {mem : ByteArray} (hmem : mem.size = 196) :
    (solcErrorStringMem1 mem).size = 196 := by
  unfold solcErrorStringMem1
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem0_size_of_size196 hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract, solcErrorStringMem0_size_of_size196 hmem]

theorem solcErrorStringMem2_size_of_size196 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (solcErrorStringMem2 len mem).size = 196 := by
  unfold solcErrorStringMem2
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem1_size_of_size196 hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract, solcErrorStringMem1_size_of_size196 hmem]

theorem solcErrorStringMem3_size_of_size196 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (solcErrorStringMem3 len word mem).size = 228 := by
  unfold solcErrorStringMem3
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem2_size_of_size196 len hmem])]
  simp [ByteArray.size_append, ByteArray.size_extract, solcErrorStringMem2_size_of_size196 len hmem]

theorem solcErrorStringMem3_read64_of_size196 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [solcErrorStringMem2_size_of_size196 len hmem]; omega) (by omega)
      (by rw [solcErrorStringMem2_size_of_size196 len hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [solcErrorStringMem1_size_of_size196 hmem]; omega) (by omega)
      (by rw [solcErrorStringMem1_size_of_size196 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [solcErrorStringMem0_size_of_size196 hmem]; omega) (by omega)
      (by rw [solcErrorStringMem0_size_of_size196 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem solcErrorStringMem3_mload64_of_size196 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [solcErrorStringMem3_size_of_size196 len word hmem]; decide)
    (by decide) (solcErrorStringMem3_read64_of_size196 len word hmem hread64)

theorem freeUrnsCalldataMem_read128_4 (I : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (freeUrnsCalldataMem I mem).readWithPadding 128 4 = urnsSelector := by
  have hSelectorSize := freeUrnsSelectorMem_size hmem
  have hIlkSize := freeUrnsIlkMem_size I hmem
  unfold freeUrnsCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (freeSourceWord I)
      (freeUrnsIlkMem I mem) 164 128 4
      (by rw [hIlkSize]; omega) (by native_decide) (by omega) (by omega)
      (by rw [hIlkSize]; native_decide)]
  unfold freeUrnsIlkMem
  rw [toByteArray_write_read_below_len_of_gap (freeIlkWord I)
      (freeUrnsSelectorMem mem) 132 128 4
      (by rw [hSelectorSize]; omega)
      (by omega) (by omega) (by omega)
      (by rw [hSelectorSize]; native_decide)]
  unfold freeUrnsSelectorMem
  change (freeUrnsSelectorShifted.toByteArray.write 0 mem 128 32).readWithPadding 128 4 =
    urnsSelector
  rw [toByteArray_write_read_window_of_gap freeUrnsSelectorShifted mem 128 0 4
      (by omega) (by omega) (by omega)
      (by rw [hmem]; native_decide)]
  native_decide

theorem freeUrnsCalldataMem_read132_32 (I : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (freeUrnsCalldataMem I mem).readWithPadding 132 32 =
      (freeIlkWord I).toByteArray := by
  have hIlkSize := freeUrnsIlkMem_size I hmem
  unfold freeUrnsCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (freeSourceWord I)
      (freeUrnsIlkMem I mem) 164 132 32
      (by rw [hIlkSize]) (by omega) (by omega) (by omega)
      (by rw [hIlkSize]; native_decide)]
  unfold freeUrnsIlkMem
  rw [toByteArray_write_read_back_of_gap (freeIlkWord I) (freeUrnsSelectorMem mem) 132
      (by rw [freeUrnsSelectorMem_size hmem]; native_decide)]

theorem freeUrnsCalldataMem_read164_32 (I : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (freeUrnsCalldataMem I mem).readWithPadding 164 32 =
      (freeSourceWord I).toByteArray := by
  unfold freeUrnsCalldataMem
  rw [toByteArray_write_read_back_of_gap (freeSourceWord I) (freeUrnsIlkMem I mem) 164
      (by rw [freeUrnsIlkMem_size I hmem]; native_decide)]

theorem freeUrnsCalldataMem_read128_68 (I : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (freeUrnsCalldataMem I mem).readWithPadding 128 68 =
      urnsSelector ++ (freeIlkWord I).toByteArray ++ (freeSourceWord I).toByteArray := by
  have hsize : (freeUrnsCalldataMem I mem).size = 196 :=
    freeUrnsCalldataMem_size I hmem
  rw [show 68 = 4 + 64 from rfl,
    byteArray_readWithPadding_split (freeUrnsCalldataMem I mem) 128 4 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (freeUrnsCalldataMem I mem) 132 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [freeUrnsCalldataMem_read128_4 I hmem, freeUrnsCalldataMem_read132_32 I hmem,
    freeUrnsCalldataMem_read164_32 I hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem freeUrnsEncodeWords (I : ExecutionEnv) :
    config.externalABI.encode? "urns" [freeIlkValue I, .address I.source] =
      some (urnsSelector ++ (freeIlkWord I).toByteArray ++ (freeSourceWord I).toByteArray) := by
  have hIlk : ABI.encodeABIValue? bytes32 (freeIlkValue I) =
      some (EVM.Word.toBytesBE (freeIlkWord I)) := by
    have hlen : (EVM.Word.toBytesBE (freeIlkWord I)).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size (freeIlkWord I)
    simp [ABI.encodeABIValue?, hlen, zeroBytes, freeIlkValue, bytes32, bytes32Width]
  have hIlk' : ABI.encodeABIValue? (.elem (.bytes bytes32Width)) (freeIlkValue I) =
      some (EVM.Word.toBytesBE (freeIlkWord I)) := by
    simpa [bytes32] using hIlk
  have hsource : ABI.encodeABIValue? (.elem .address) (.address I.source) =
      some (EVM.Word.toBytesBE (freeSourceWord I)) := by
    simp [ABI.encodeABIValue?, ABI.encodeABIWord?, freeSourceWord]
    rw [show EVM.word (↑I.source : ℕ) = UInt256.ofNat (↑I.source : ℕ) from rfl]
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    ABI.encodeABIValuesFrom?, hIlk', hsource, addr, bytes32]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc, word_toBytesBE_toByteArray_eq_toByteArray]

theorem freeUrnsEncode_eq (I : ExecutionEnv) :
    config.externalABI.encode? "urns" [freeIlkValue I, .address I.source] =
      some ((freeUrnsCalldataMem I solcFreePtrMem).readWithPadding
        freeUrnsOutPtr.toNat freeUrnsInSize.toNat) := by
  rw [show freeUrnsOutPtr.toNat = 128 by native_decide,
    show freeUrnsInSize.toNat = 68 by native_decide]
  rw [freeUrnsCalldataMem_read128_68 I solcFreePtrMem_size]
  exact freeUrnsEncodeWords I

theorem freeEvmAddress_ofNat_toNat_eq_ofUInt256 (w : UInt256) :
    EVM.address (↑(AccountAddress.ofNat w.toNat) : ℕ) = AccountAddress.ofUInt256 w := by
  apply Fin.ext
  simp [EVM.address, EVM.uintN, AccountAddress.ofNat, AccountAddress.ofUInt256,
    UInt256.toNat]
  rw [show AccountAddress.size = EVM.twoPow 160 from by decide]
  rw [Nat.mod_mod]

theorem endDecode_free_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (freeTransition.params.map Param.name)
      (transitionSignature freeTransition).paramTypes I.calldata = some (freeStore I) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk"] [bytes32] I.calldata =
    some (freeStore I)
  simpa [freeStore, freeIlkValue, freeIlkWord] using
    endDecodeCalldata_legacyBytes32_ok (cd := I.calldata) (x := "ilk") hsz36

theorem endDecode_free_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (freeTransition.params.map Param.name)
      (transitionSignature freeTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk"] [bytes32] I.calldata = none
  simpa using endDecodeCalldata_legacyBytes32_none_short (cd := I.calldata) (x := "ilk")
    hsz4 hshort

theorem endDispatchFreeLocal {I : ExecutionEnv} (hsel : selIs I (endSelBytes 27)) :
    dispatchMsg contract I.calldata = some freeTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 27 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some freeTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

set_option maxHeartbeats 5000000 in
theorem endReachFreeBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (endSelBytes 27)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1025⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : endSelWord I = ⟨0xc83062c6⟩ :=
    endSelWord_eq_of_beq I hsz 0xc8 0x30 0x62 0xc6 ⟨0xc83062c6⟩
      (by native_decide) (by simpa [endSelBytes] using hsel)
  obtain ⟨_, _, h32⟩ :=
    endReachRootSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have hroot : UInt256.gt (armSelNat endBytecode (⟨32⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h43 := RD.selectorSplitNotTakenAuto h32
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    hroot (by simp)
  have h43gt : UInt256.gt (armSelNat endBytecode (⟨43⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h162 := RD.selectorSplitTakenAuto h43
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    h43gt (by jump_dest) (by simp)
  have h163 := h162.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have h163gt :
      UInt256.gt (armSelNat endBytecode (⟨163⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h174 := by
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
      selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h163
        (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
        h163gt (by simp)
  have h174eq0 : UInt256.eq (armSelNat endBytecode (⟨174⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h185eq0 : UInt256.eq (armSelNat endBytecode (⟨185⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have hfree :
      UInt256.eq (armSelNat endBytecode (⟨196⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h1025 := h174
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      h174eq0 (by simp)
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      h185eq0 (by simp)
    |>.selectorArmTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      hfree (by jump_dest) (by simp)
  exact ⟨_, _, h1025⟩

theorem endFreeX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1025⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7690⟩
        [freeIlkWord I, ⟨562⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := endBytecode) (sel := sel) (entry := ⟨1025⟩) (ret := ⟨562⟩)
    (decoded := ⟨1047⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneBytes32ExternalJump
    (code := endBytecode) (decoded := ⟨1047⟩) (ret := ⟨562⟩) (routine := ⟨7690⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [freeIlkWord] using hroutine⟩

theorem endFreeX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1025⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel)
    (entry := ⟨1025⟩) (ret := ⟨562⟩) (decoded := ⟨1047⟩)
    (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem evalStorageRef_free_live (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := freeStore I } evm liveRef =
      .ok ({ base := "live", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind]

theorem evalExpr_free_live_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := freeStore I } evm
      (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := freeStore I } evm (.storage liveRef) =
        .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat)) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := freeStore I })
      (slot := liveRef)
      (er := ({ base := "live", steps := [] } : EvaledStorageRef))
      (t := .int uint256Int)
      (loc := wordLoc ⟨8⟩)
      (value := .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat))
      (hbase := by simp [freeStore, liveRef])
      (her := evalStorageRef_free_live evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        exact endStorageLocLoad_uint256 evm ⟨8⟩)]
  have hne :
      (Value.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ==
        Value.int 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro hbad
    rw [Value.int.injEq] at hbad
    exact hlive (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?, hne]

theorem evalExpr_free_live_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := freeStore I } evm
      (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := freeStore I } evm (.storage liveRef) =
        .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat)) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := freeStore I })
      (slot := liveRef)
      (er := ({ base := "live", steps := [] } : EvaledStorageRef))
      (t := .int uint256Int)
      (loc := wordLoc ⟨8⟩)
      (value := .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat))
      (hbase := by simp [freeStore, liveRef])
      (her := evalStorageRef_free_live evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        exact endStorageLocLoad_uint256 evm ⟨8⟩)]
  simp only [evalExpr?, hstorage, hlive, EvalResult.bind, bind, pure, evalBinaryOp?]
  native_decide

theorem evalExpr_freeVatStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "vat" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  rw [evalExpr_storage_scalar (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨1⟩)]
  · exact congrArg EvalResult.ok (endStorageLocLoad_address_offset0 _ ⟨1⟩)
  · exact hbase
  · simp [vatRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, addrSt]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw]

theorem evalExpr_freeVatCodeGuard_false {evm : EVM.State} {locals : Store}
    {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address target))
    (hcode :
      (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem evalExpr_freeVatCodeGuard_true {evm : EVM.State} {locals : Store}
    {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address target))
    (hcode :
      (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat ≠
        0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat]
  exact Nat.pos_of_ne_zero hcode

theorem evalExprs_freeUrnsArgs {cA gh bl σ σ₀ A I} {g : UInt256} :
    evalExprs? config { contract := contract, locals := freeStore I }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) [.var "ilk", sender] =
      .ok [freeIlkValue I, .address I.source] := by
  simp [evalExprs?, evalExpr?, sender, envValue, freeStore, freeIlkValue, EvalResult.ofOption,
    EvalResult.bind, bind, pure, initState]

theorem evalExpr_freeVowStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "vow" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vowRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask).toNat)) := by
  rw [evalExpr_storage_scalar (er := ({ base := "vow", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨4⟩)]
  · exact congrArg EvalResult.ok (endStorageLocLoad_address_offset0 _ ⟨4⟩)
  · exact hbase
  · simp [vowRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, addrSt]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw]

theorem freeUrnsDecode_none_short {out : ByteArray} (hshort : out.size < 64) :
    config.externalABI.decode? "urns" out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  change ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [uint256, uint256] out = none
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [uint256, uint256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [uint256, uint256]) (bytes := out.toList) (cursor := 0)
    (total := 32 * [uint256, uint256].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  by_cases hfirst : 32 ≤ out.size
  · have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, hlen]
      omega
    have hscalar0 : decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
        some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 0).take 32)).toNat), 0 + 32) := by
      simpa [uint256, uint256Int] using
        decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
          (bytes := out.toList) (start := 0) htake0
    rw [hscalar0]
    have htake32n : ¬ ((out.toList.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, hlen]
      omega
    have hscalar1 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 = none := by
      simpa [uint256, uint256Int] using
        decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
          (bytes := out.toList) (start := 32) htake32n
    rw [hscalar1]
    rfl
  · have htake0n : ¬ ((out.toList.drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, hlen]
      omega
    have hscalar0 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 = none := by
      simpa [uint256, uint256Int] using
        decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
          (bytes := out.toList) (start := 0) htake0n
    rw [hscalar0]
    rfl

theorem freeUrnsBytesToWord0_eq (out : ByteArray) (hlong : 64 ≤ out.size) :
    ABI.bytesToWord ((out.toList.drop 0).take 32) = freeUrnsInkWord out := by
  rw [decode_word_at_eq_any out 0 (by omega), uInt256OfByteArray_eq]
  unfold freeUrnsInkWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.readBytes 0 32), readBytes_at_toList_any out 0 (by omega)]
  rw [byteArray_toList_eq (out.extract 0 32)]
  simp [ByteArray.data_extract, Array.toList_extract]

theorem freeUrnsBytesToWord32_eq (out : ByteArray) (hlong : 64 ≤ out.size) :
    ABI.bytesToWord ((out.toList.drop 32).take 32) = freeUrnsArtWord out := by
  rw [decode_word_at_eq_any out 32 (by omega), uInt256OfByteArray_eq]
  unfold freeUrnsArtWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.readBytes 32 32), readBytes_at_toList_any out 32 (by omega)]
  rw [byteArray_toList_eq (out.extract 32 64)]
  simp [ByteArray.data_extract, Array.toList_extract]

theorem freeUrnsDecode_ok {out : ByteArray} (hlong : 64 ≤ out.size) :
    config.externalABI.decode? "urns" out =
      some [.int (Int.ofNat (freeUrnsInkWord out).toNat),
        .int (Int.ofNat (freeUrnsArtWord out).toNat)] := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  change ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [uint256, uint256] out =
    some [.int (Int.ofNat (freeUrnsInkWord out).toNat),
      .int (Int.ofNat (freeUrnsArtWord out).toNat)]
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [uint256, uint256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [uint256, uint256]) (bytes := out.toList) (cursor := 0)
    (total := 32 * [uint256, uint256].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have htake32 : ((out.toList.drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have hscalar0 : decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
      some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 0).take 32)).toNat), 0 + 32) := by
    simpa [uint256, uint256Int] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 0) htake0
  have hscalar1 : decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
      some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 32).take 32)).toNat), 32 + 32) := by
    simpa [uint256, uint256Int] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 32) htake32
  rw [hscalar0, hscalar1]
  rw [freeUrnsBytesToWord0_eq out hlong, freeUrnsBytesToWord32_eq out hlong]
  rfl

theorem evalExpr_freeUrnsInk {evm : EVM.State} {I : ExecutionEnv} {out : ByteArray} :
    evalExpr? config { contract := contract, locals := freeUrnsLocals I out } evm
      (.tupleGet (.var "vatUrn") 0) =
        .ok (.int (Int.ofNat (freeUrnsInkWord out).toNat)) := by
  simp [evalExpr?, EvalResult.bind, bind, EvalResult.ofOption, freeUrnsLocals, collapseReturns,
    tupleGetValue?]

theorem evalExpr_freeUrnsArt {evm : EVM.State} {I : ExecutionEnv} {out : ByteArray} :
    evalExpr? config { contract := contract, locals := freeUrnsLocals I out } evm
      (.tupleGet (.var "vatUrn") 1) =
        .ok (.int (Int.ofNat (freeUrnsArtWord out).toNat)) := by
  simp [evalExpr?, EvalResult.bind, bind, EvalResult.ofOption, freeUrnsLocals, collapseReturns,
    tupleGetValue?]

theorem freeUrnsInkLocals_vatUrn_get (I : ExecutionEnv) (out : ByteArray) :
    (freeUrnsInkLocals I out).get? "vatUrn" =
      some (collapseReturns (freeUrnsReturnValues out)) := by
  unfold freeUrnsInkLocals freeUrnsLocals
  simp [Std.HashMap.get?, Std.HashMap.insert, Std.DHashMap.Const.get?_insert,
    Std.DHashMap.Const.get?_insert_self]

theorem evalExpr_freeUrnsArt_afterInk {evm : EVM.State} {I : ExecutionEnv} {out : ByteArray} :
    evalExpr? config { contract := contract, locals := freeUrnsInkLocals I out } evm
      (.tupleGet (.var "vatUrn") 1) =
        .ok (.int (Int.ofNat (freeUrnsArtWord out).toNat)) := by
  simp only [evalExpr?, EvalResult.bind, bind, EvalResult.ofOption]
  rw [show (freeUrnsInkLocals I out).get? "vatUrn" =
      some (collapseReturns (freeUrnsReturnValues out)) from
    freeUrnsInkLocals_vatUrn_get I out]
  simp [collapseReturns, tupleGetValue?]

theorem evalExpr_freeArtZero_false {evm : EVM.State} {I : ExecutionEnv} {out : ByteArray}
    (hart : freeUrnsArtWord out ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := freeUrnsArtLocals I out } evm
      (.binary .eq (.var "art") (.intLit 0)) = .ok (.bool false) := by
  have hartNat : (freeUrnsArtWord out).toNat ≠ 0 := by
    intro hzero
    exact hart (uint256_toNat_eq_zero hzero)
  simp [evalExpr?, EvalResult.bind, bind, EvalResult.ofOption, evalBinaryOp?,
    freeUrnsArtLocals, hartNat]

theorem evalExpr_freeArtZero_true {evm : EVM.State} {I : ExecutionEnv} {out : ByteArray}
    (hart : freeUrnsArtWord out = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := freeUrnsArtLocals I out } evm
      (.binary .eq (.var "art") (.intLit 0)) = .ok (.bool true) := by
  have hartNat : (freeUrnsArtWord out).toNat = 0 := by
    rw [hart]
    rfl
  simp [evalExpr?, EvalResult.bind, bind, EvalResult.ofOption, evalBinaryOp?,
    freeUrnsArtLocals, hartNat]

theorem freeUrnsArtLocals_ink_get (I : ExecutionEnv) (out : ByteArray) :
    (freeUrnsArtLocals I out).get? "ink" =
      some (.int (Int.ofNat (freeUrnsInkWord out).toNat)) := by
  unfold freeUrnsArtLocals freeUrnsInkLocals
  simp [Std.HashMap.get?, Std.HashMap.insert, Std.DHashMap.Const.get?_insert,
    Std.DHashMap.Const.get?_insert_self]

theorem freeUrnsArtLocals_ilk_get (I : ExecutionEnv) (out : ByteArray) :
    (freeUrnsArtLocals I out).get? "ilk" = some (freeIlkValue I) := by
  unfold freeUrnsArtLocals freeUrnsInkLocals freeUrnsLocals freeStore
  rw [store_get_ne, store_get_ne, store_get_ne, store_get_self]
  · native_decide
  · native_decide
  · native_decide

theorem evalExpr_freeNegInk {evm : EVM.State} {I : ExecutionEnv} {out : ByteArray} :
    evalExpr? config { contract := contract, locals := freeUrnsArtLocals I out } evm
      (.unary .neg (asInt256 (.var "ink"))) =
      .ok (.int (-(Int.ofNat (freeUrnsInkWord out).toNat))) := by
  simp only [asInt256, evalExpr?, EvalResult.bind, bind, EvalResult.ofOption]
  rw [freeUrnsArtLocals_ink_get]
  simp [castValue?, evalUnaryOp?, int256St]

set_option maxHeartbeats 1000000 in
theorem evalExprs_freeGrabArgs {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {A' : Substate} (out : ByteArray) :
    evalExprs? config { contract := contract, locals := freeUrnsArtLocals I out }
      { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ, substate := A', createdAccounts := cA' }
      [.var "ilk", sender, sender, vowAddr, .unary .neg (asInt256 (.var "ink")), .intLit 0] =
      .ok [freeIlkValue I, .address I.source, .address I.source,
        .address (AccountAddress.ofUInt256 (freeVowMaskedWord σ I)),
        .int (-(Int.ofNat (freeUrnsInkWord out).toNat)), .int 0] := by
  have hvow : evalExpr? config { contract := contract, locals := freeUrnsArtLocals I out }
      { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ, substate := A', createdAccounts := cA' } vowAddr =
      .ok (.address (AccountAddress.ofUInt256 (freeVowMaskedWord σ I))) := by
    simpa [vowAddr, freeVowMaskedWord, freeVowWord, endSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount, u256_land_comm,
      accountAddress_ofUInt256_eq_ofNat_toNat] using
      evalExpr_freeVowStorage
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ, substate := A', createdAccounts := cA' }
        (locals := freeUrnsArtLocals I out) (by simp [freeUrnsArtLocals, freeUrnsInkLocals,
          freeUrnsLocals, freeStore])
  have hneg :
      evalExpr? config { contract := contract, locals := freeUrnsArtLocals I out }
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ, substate := A', createdAccounts := cA' }
        (.unary .neg (asInt256 (.var "ink"))) =
        .ok (.int (-(Int.ofNat (freeUrnsInkWord out).toNat))) :=
    evalExpr_freeNegInk
  simp only [evalExprs?, EvalResult.bind, bind, pure]
  rw [hneg, hvow]
  simp [evalExpr?, sender, envValue, freeStore, freeIlkValue, EvalResult.ofOption, initState]
  simpa [freeIlkValue] using congrArg Option.get! (freeUrnsArtLocals_ilk_get I out)

theorem evalExpr_freeInkLe_true {evm : EVM.State} {I : ExecutionEnv} {out : ByteArray}
    (hink : (freeUrnsInkWord out).toNat ≤ freeInt256LimitWord.toNat) :
    evalExpr? config { contract := contract, locals := freeUrnsArtLocals I out } evm
      (.binary .le (.var "ink") (.intLit int256Limit)) = .ok (.bool true) := by
  have hinkInt : ((freeUrnsInkWord out).toNat : Int) ≤ int256Limit := by
    have hlimit : freeInt256LimitWord.toNat = Int.toNat int256Limit := by
      native_decide
    have hnonneg : 0 ≤ int256Limit := by native_decide
    rw [hlimit] at hink
    omega
  simp only [evalExpr?, EvalResult.bind, bind, EvalResult.ofOption]
  rw [show (freeUrnsArtLocals I out).get? "ink" =
      some (.int (Int.ofNat (freeUrnsInkWord out).toNat)) from
    freeUrnsArtLocals_ink_get I out]
  simp [evalBinaryOp?, hinkInt]

theorem evalExpr_freeInkLe_false {evm : EVM.State} {I : ExecutionEnv} {out : ByteArray}
    (hink : ¬ (freeUrnsInkWord out).toNat ≤ freeInt256LimitWord.toNat) :
    evalExpr? config { contract := contract, locals := freeUrnsArtLocals I out } evm
      (.binary .le (.var "ink") (.intLit int256Limit)) = .ok (.bool false) := by
  have hinkInt : ¬ ((freeUrnsInkWord out).toNat : Int) ≤ int256Limit := by
    intro hle
    apply hink
    have hlimit : freeInt256LimitWord.toNat = Int.toNat int256Limit := by
      native_decide
    have hnonneg : 0 ≤ int256Limit := by native_decide
    rw [hlimit]
    omega
  simp only [evalExpr?, EvalResult.bind, bind, EvalResult.ofOption]
  rw [show (freeUrnsArtLocals I out).get? "ink" =
      some (.int (Int.ofNat (freeUrnsInkWord out).toNat)) from
    freeUrnsArtLocals_ink_get I out]
  simp [evalBinaryOp?, hinkInt]

theorem endFreeSourceBodyLiveReverts {cA gh bl σ σ₀ A I g}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : freeLiveWord σ I ≠ ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (freeStore I) freeTransition.body .reverted := by
  intro evm0
  have hliveEval :
      evalExpr? config { contract := contract, locals := freeStore I } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool false) := by
    simpa [freeLiveWord, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_free_live_zero_false evm0 I
        (by simpa [freeLiveWord, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount]
          using hlive)
  have hblock :
      ExecBlock config { contract := contract, locals := freeStore I } evm0
        freeTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    exact ExecBlock.consRevert (ExecStmt.requireFalse hliveEval)
  simpa [ExecTransitionBody, evm0, freeTransition, nonpayable, checkedExternalCallStmts] using
    ExecFuncBody.execBlockRevert hblock

theorem endFreeSourceBodyVatNoCodeReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : freeLiveWord σ I = ⟨0⟩)
    (hvatNoCode :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (freeVatMaskedWord σ I) = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (freeStore I) freeTransition.body .reverted := by
  intro evm0
  have hliveEval :
      evalExpr? config { contract := contract, locals := freeStore I } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [freeLiveWord, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_free_live_zero_true evm0 I
        (by simpa [freeLiveWord, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount]
          using hlive)
  have hvat :
      evalExpr? config { contract := contract, locals := freeStore I } evm0 (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)) := by
    simpa [freeVatMaskedWord, freeVatWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, u256_land_comm] using
      evalExpr_freeVatStorage (evm := evm0) (locals := freeStore I) (by simp [freeStore])
  have hvatNoCodeNat :
      (UInt256.ofNat
        ((evm0.lookupAccount (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    have hnat := congrArg UInt256.toNat hvatNoCode
    simp [Reasoning.Theory.uniswapExtCodeSizeWord, evm0, initState, State.lookupAccount,
      accountAddress_ofUInt256_eq_ofNat_toNat] at hnat ⊢
    cases hfind : σ.find? (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)
    · native_decide
    · simp [hfind, Option.option, Function.comp] at hnat ⊢
      exact hnat
  have hguard :
      evalExpr? config { contract := contract, locals := freeStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_freeVatCodeGuard_false hvat hvatNoCodeNat
  refine ExecFuncBody.execBlockRevert ?_
  simpa [freeTransition, nonpayable, checkedExternalCallStmts] using
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
      simp [evm0, initState]; exact hwv))) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hliveEval) <|
        ExecBlock.consRevert (ExecStmt.requireFalse hguard)

theorem endFreeSourceBodyUrnsCallFailure {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmUrns : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : freeLiveWord σ I = ⟨0⟩)
    (hvatCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)).option 0
          (fun acc => acc.code.size))).toNat ≠ 0)
    (hcallUrns :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)) "urns" 0
        [freeIlkValue I, .address I.source] (false, evmUrns, out) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (freeStore I) freeTransition.body .reverted := by
  intro evm0
  have hliveEval :
      evalExpr? config { contract := contract, locals := freeStore I } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [freeLiveWord, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_free_live_zero_true evm0 I
        (by simpa [freeLiveWord, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount]
          using hlive)
  have hvat :
      evalExpr? config { contract := contract, locals := freeStore I } evm0 (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)) := by
    simpa [freeVatMaskedWord, freeVatWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, u256_land_comm] using
      evalExpr_freeVatStorage (evm := evm0) (locals := freeStore I) (by simp [freeStore])
  have hguard :
      evalExpr? config { contract := contract, locals := freeStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_freeVatCodeGuard_true hvat hvatCode
  have hargsUrns := evalExprs_freeUrnsArgs (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hcallStmt :
      ExecStmt config { contract := contract, locals := freeStore I } evm0
        (.externalCall (.storage vatRef) "urns" (.intLit 0) [.var "ilk", sender]
          "vatUrn" (perm := true)) .reverted := by
    exact ExecStmt.externalCallFailure hvat (by simp [evalExpr?, pure]) hargsUrns hcallUrns
  have hblock :
      ExecBlock config { contract := contract, locals := freeStore I } evm0 freeTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveEval) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert hcallStmt
  simpa [ExecTransitionBody, evm0, freeTransition, nonpayable, checkedExternalCallStmts] using
    ExecFuncBody.execBlockRevert hblock

theorem endFreeSourceBodyUrnsDecodeRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmUrns : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : freeLiveWord σ I = ⟨0⟩)
    (hvatCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)).option 0
          (fun acc => acc.code.size))).toNat ≠ 0)
    (hcallUrns :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)) "urns" 0
        [freeIlkValue I, .address I.source] (true, evmUrns, out) true)
    (hdec : config.externalABI.decode? "urns" out = none) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (freeStore I) freeTransition.body .reverted := by
  intro evm0
  have hliveEval :
      evalExpr? config { contract := contract, locals := freeStore I } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [freeLiveWord, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_free_live_zero_true evm0 I
        (by simpa [freeLiveWord, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount]
          using hlive)
  have hvat :
      evalExpr? config { contract := contract, locals := freeStore I } evm0 (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)) := by
    simpa [freeVatMaskedWord, freeVatWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, u256_land_comm] using
      evalExpr_freeVatStorage (evm := evm0) (locals := freeStore I) (by simp [freeStore])
  have hguard :
      evalExpr? config { contract := contract, locals := freeStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_freeVatCodeGuard_true hvat hvatCode
  have hargsUrns := evalExprs_freeUrnsArgs (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hcallStmt :
      ExecStmt config { contract := contract, locals := freeStore I } evm0
        (.externalCall (.storage vatRef) "urns" (.intLit 0) [.var "ilk", sender]
          "vatUrn" (perm := true)) .reverted := by
    exact ExecStmt.externalCallReturnDecodeRevert hvat (by simp [evalExpr?, pure])
      hargsUrns hcallUrns hdec
  have hblock :
      ExecBlock config { contract := contract, locals := freeStore I } evm0 freeTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveEval) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert hcallStmt
  simpa [ExecTransitionBody, evm0, freeTransition, nonpayable, checkedExternalCallStmts] using
    ExecFuncBody.execBlockRevert hblock

theorem endFreeSourceBodyUrnsArtNonzeroReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmUrns : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : freeLiveWord σ I = ⟨0⟩)
    (hvatCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)).option 0
          (fun acc => acc.code.size))).toNat ≠ 0)
    (hcallUrns :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)) "urns" 0
        [freeIlkValue I, .address I.source] (true, evmUrns, out) true)
    (hdec : config.externalABI.decode? "urns" out = some (freeUrnsReturnValues out))
    (hart : freeUrnsArtWord out ≠ ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (freeStore I) freeTransition.body .reverted := by
  intro evm0
  have hliveEval :
      evalExpr? config { contract := contract, locals := freeStore I } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [freeLiveWord, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_free_live_zero_true evm0 I
        (by simpa [freeLiveWord, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount]
          using hlive)
  have hvat :
      evalExpr? config { contract := contract, locals := freeStore I } evm0 (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)) := by
    simpa [freeVatMaskedWord, freeVatWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, u256_land_comm] using
      evalExpr_freeVatStorage (evm := evm0) (locals := freeStore I) (by simp [freeStore])
  have hguard :
      evalExpr? config { contract := contract, locals := freeStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_freeVatCodeGuard_true hvat hvatCode
  have hargsUrns := evalExprs_freeUrnsArgs (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hinkStmt :
      ExecStmt config { contract := contract, locals := freeUrnsLocals I out } evmUrns
        (.letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0))
        (.ok { contract := contract, locals := freeUrnsInkLocals I out } evmUrns) := by
    simpa [freeUrnsInkLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := freeUrnsLocals I out })
        (evm := evmUrns)
        (name := "ink")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatUrn") 0)
        (value := .int (Int.ofNat (freeUrnsInkWord out).toNat))
        evalExpr_freeUrnsInk)
  have hartStmt :
      ExecStmt config { contract := contract, locals := freeUrnsInkLocals I out } evmUrns
        (.letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1))
        (.ok { contract := contract, locals := freeUrnsArtLocals I out } evmUrns) := by
    simpa [freeUrnsArtLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := freeUrnsInkLocals I out })
        (evm := evmUrns)
        (name := "art")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatUrn") 1)
        (value := .int (Int.ofNat (freeUrnsArtWord out).toNat))
        evalExpr_freeUrnsArt_afterInk)
  have hblock :
      ExecBlock config { contract := contract, locals := freeStore I } evm0 freeTransition.body
        .reverted := by
    simp only [freeTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveEval) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsUrns
        hcallUrns hdec) ?_
    refine ExecBlock.consNormal (by simpa [freeUrnsLocals, collapseReturns] using hinkStmt) ?_
    refine ExecBlock.consNormal (by
      simpa [freeUrnsLocals, freeUrnsInkLocals, freeUrnsArtLocals, collapseReturns] using
        hartStmt) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_freeArtZero_false hart))
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endFreeSourceBodyUrnsInkTooLargeReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmUrns : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : freeLiveWord σ I = ⟨0⟩)
    (hvatCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)).option 0
          (fun acc => acc.code.size))).toNat ≠ 0)
    (hcallUrns :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)) "urns" 0
        [freeIlkValue I, .address I.source] (true, evmUrns, out) true)
    (hdec : config.externalABI.decode? "urns" out = some (freeUrnsReturnValues out))
    (hart : freeUrnsArtWord out = ⟨0⟩)
    (hink : ¬ (freeUrnsInkWord out).toNat ≤ freeInt256LimitWord.toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (freeStore I) freeTransition.body .reverted := by
  intro evm0
  have hliveEval :
      evalExpr? config { contract := contract, locals := freeStore I } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [freeLiveWord, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_free_live_zero_true evm0 I
        (by simpa [freeLiveWord, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount]
          using hlive)
  have hvat :
      evalExpr? config { contract := contract, locals := freeStore I } evm0 (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)) := by
    simpa [freeVatMaskedWord, freeVatWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, u256_land_comm] using
      evalExpr_freeVatStorage (evm := evm0) (locals := freeStore I) (by simp [freeStore])
  have hguard :
      evalExpr? config { contract := contract, locals := freeStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_freeVatCodeGuard_true hvat hvatCode
  have hargsUrns := evalExprs_freeUrnsArgs (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hinkStmt :
      ExecStmt config { contract := contract, locals := freeUrnsLocals I out } evmUrns
        (.letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0))
        (.ok { contract := contract, locals := freeUrnsInkLocals I out } evmUrns) := by
    simpa [freeUrnsInkLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := freeUrnsLocals I out })
        (evm := evmUrns)
        (name := "ink")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatUrn") 0)
        (value := .int (Int.ofNat (freeUrnsInkWord out).toNat))
        evalExpr_freeUrnsInk)
  have hartStmt :
      ExecStmt config { contract := contract, locals := freeUrnsInkLocals I out } evmUrns
        (.letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1))
        (.ok { contract := contract, locals := freeUrnsArtLocals I out } evmUrns) := by
    simpa [freeUrnsArtLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := freeUrnsInkLocals I out })
        (evm := evmUrns)
        (name := "art")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatUrn") 1)
        (value := .int (Int.ofNat (freeUrnsArtWord out).toNat))
        evalExpr_freeUrnsArt_afterInk)
  have hblock :
      ExecBlock config { contract := contract, locals := freeStore I } evm0 freeTransition.body
        .reverted := by
    simp only [freeTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveEval) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsUrns
        hcallUrns hdec) ?_
    refine ExecBlock.consNormal (by simpa [freeUrnsLocals, collapseReturns] using hinkStmt) ?_
    refine ExecBlock.consNormal (by
      simpa [freeUrnsLocals, freeUrnsInkLocals, freeUrnsArtLocals, collapseReturns] using
        hartStmt) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_freeArtZero_true hart)) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_freeInkLe_false hink))
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endFreeSourceBodyGrabCallSuccess {cA gh bl σ σUrns σ₀ A I} {g : UInt256}
    {cAUrns : Batteries.RBSet AccountAddress compare} {AUrns : Substate}
    {evmGrab : EVM.State} {out grabOut : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : freeLiveWord σ I = ⟨0⟩)
    (hvatCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)).option 0
          (fun acc => acc.code.size))).toNat ≠ 0)
    (hcallUrns :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)) "urns" 0
        [freeIlkValue I, .address I.source]
        (true,
          { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σUrns, substate := AUrns, createdAccounts := cAUrns },
          out) true)
    (hdec : config.externalABI.decode? "urns" out = some (freeUrnsReturnValues out))
    (hart : freeUrnsArtWord out = ⟨0⟩)
    (hink : (freeUrnsInkWord out).toNat ≤ freeInt256LimitWord.toNat)
    (hvatCodeGrab :
      Reasoning.Theory.uniswapExtCodeSizeWord σUrns (freeVatMaskedWord σUrns I) ≠ ⟨0⟩)
    (hcallGrab :
      typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σUrns, substate := AUrns, createdAccounts := cAUrns }
        (EVM.address (AccountAddress.ofNat (freeVatMaskedWord σUrns I).toNat)) "grab" 0
        [freeIlkValue I, .address I.source, .address I.source,
          .address (AccountAddress.ofUInt256 (freeVowMaskedWord σUrns I)),
          .int (-(Int.ofNat (freeUrnsInkWord out).toNat)), .int 0]
        (true, evmGrab, grabOut) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evmUrns :=
      { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σUrns, substate := AUrns, createdAccounts := cAUrns }
    let localsGrab := (freeUrnsArtLocals I out).insert "_grab" .unit
    ExecTransitionBody config contract evm0 (freeStore I) freeTransition.body
      (.returned { contract := contract, locals := localsGrab } evmGrab none) := by
  intro evm0 evmUrns localsGrab
  have hliveEval :
      evalExpr? config { contract := contract, locals := freeStore I } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [freeLiveWord, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_free_live_zero_true evm0 I
        (by simpa [freeLiveWord, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount]
          using hlive)
  have hvat :
      evalExpr? config { contract := contract, locals := freeStore I } evm0 (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)) := by
    simpa [freeVatMaskedWord, freeVatWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, u256_land_comm] using
      evalExpr_freeVatStorage (evm := evm0) (locals := freeStore I) (by simp [freeStore])
  have hguard :
      evalExpr? config { contract := contract, locals := freeStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_freeVatCodeGuard_true hvat hvatCode
  have hargsUrns := evalExprs_freeUrnsArgs (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hinkStmt :
      ExecStmt config { contract := contract, locals := freeUrnsLocals I out } evmUrns
        (.letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0))
        (.ok { contract := contract, locals := freeUrnsInkLocals I out } evmUrns) := by
    simpa [freeUrnsInkLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := freeUrnsLocals I out })
        (evm := evmUrns)
        (name := "ink")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatUrn") 0)
        (value := .int (Int.ofNat (freeUrnsInkWord out).toNat))
        evalExpr_freeUrnsInk)
  have hartStmt :
      ExecStmt config { contract := contract, locals := freeUrnsInkLocals I out } evmUrns
        (.letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1))
        (.ok { contract := contract, locals := freeUrnsArtLocals I out } evmUrns) := by
    simpa [freeUrnsArtLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := freeUrnsInkLocals I out })
        (evm := evmUrns)
        (name := "art")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatUrn") 1)
        (value := .int (Int.ofNat (freeUrnsArtWord out).toNat))
        evalExpr_freeUrnsArt_afterInk)
  have hvatGrab :
      evalExpr? config { contract := contract, locals := freeUrnsArtLocals I out } evmUrns
        (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (freeVatMaskedWord σUrns I).toNat)) := by
    simpa [freeVatMaskedWord, freeVatWord, endSlotWord, evmUrns, initState,
      Solm.EVM.storageLoad, State.lookupAccount, u256_land_comm] using
      evalExpr_freeVatStorage (evm := evmUrns) (locals := freeUrnsArtLocals I out)
        (by simp [freeUrnsArtLocals, freeUrnsInkLocals, freeUrnsLocals, freeStore])
  have hguardGrab :
      evalExpr? config { contract := contract, locals := freeUrnsArtLocals I out } evmUrns
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    have hcode :
        (UInt256.ofNat ((evmUrns.lookupAccount
          (AccountAddress.ofNat (freeVatMaskedWord σUrns I).toNat)).option 0
          (fun acc => acc.code.size))).toNat ≠ 0 := by
      intro hnat
      apply hvatCodeGrab
      simp [Reasoning.Theory.uniswapExtCodeSizeWord, evmUrns, State.lookupAccount,
        accountAddress_ofUInt256_eq_ofNat_toNat] at hnat ⊢
      cases hfind : σUrns.find? (AccountAddress.ofNat (freeVatMaskedWord σUrns I).toNat)
      · native_decide
      · simp [hfind, Option.option, Function.comp] at hnat ⊢
        exact uint256_toNat_eq_zero hnat
    exact evalExpr_freeVatCodeGuard_true hvatGrab hcode
  have hargsGrab :=
    evalExprs_freeGrabArgs (cA := cA) (gh := gh) (bl := bl) (σ := σUrns) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (cA' := cAUrns) (A' := AUrns) out
  have hdecodeGrab : config.externalABI.decode? "grab" grabOut = some ([] : List Value) := by
    simp [config, externalABI, decodeVoid?]
  have hcallGrabStmt :
      ExecStmt config { contract := contract, locals := freeUrnsArtLocals I out } evmUrns
        (.externalCall (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", sender, sender, vowAddr, .unary .neg (asInt256 (.var "ink")),
            .intLit 0]
          "_grab" (perm := true))
        (.ok { contract := contract, locals := localsGrab } evmGrab) := by
    simpa [localsGrab] using
      ExecStmt.externalCallSuccess hvatGrab (by simp [evalExpr?, pure]) hargsGrab hcallGrab
        hdecodeGrab
  have hblock :
      ExecBlock config { contract := contract, locals := freeStore I } evm0 freeTransition.body
        (.ok { contract := contract, locals := localsGrab } evmGrab) := by
    simp only [freeTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveEval) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsUrns
        hcallUrns hdec) ?_
    refine ExecBlock.consNormal (by simpa [freeUrnsLocals, collapseReturns] using hinkStmt) ?_
    refine ExecBlock.consNormal (by
      simpa [freeUrnsLocals, freeUrnsInkLocals, freeUrnsArtLocals, collapseReturns] using
        hartStmt) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_freeArtZero_true hart)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_freeInkLe_true hink)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardGrab) ?_
    exact ExecBlock.consNormal hcallGrabStmt ExecBlock.nil
  simpa [ExecTransitionBody, evm0, localsGrab] using ExecFuncBody.execBlockOK hblock

theorem endFreeSourceBodyGrabCallFailure {cA gh bl σ σUrns σ₀ A I} {g : UInt256}
    {cAUrns : Batteries.RBSet AccountAddress compare} {AUrns : Substate}
    {evmGrab : EVM.State} {out grabOut : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : freeLiveWord σ I = ⟨0⟩)
    (hvatCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)).option 0
          (fun acc => acc.code.size))).toNat ≠ 0)
    (hcallUrns :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)) "urns" 0
        [freeIlkValue I, .address I.source]
        (true,
          { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σUrns, substate := AUrns, createdAccounts := cAUrns },
          out) true)
    (hdec : config.externalABI.decode? "urns" out = some (freeUrnsReturnValues out))
    (hart : freeUrnsArtWord out = ⟨0⟩)
    (hink : (freeUrnsInkWord out).toNat ≤ freeInt256LimitWord.toNat)
    (hvatCodeGrab :
      Reasoning.Theory.uniswapExtCodeSizeWord σUrns (freeVatMaskedWord σUrns I) ≠ ⟨0⟩)
    (hcallGrab :
      typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σUrns, substate := AUrns, createdAccounts := cAUrns }
        (EVM.address (AccountAddress.ofNat (freeVatMaskedWord σUrns I).toNat)) "grab" 0
        [freeIlkValue I, .address I.source, .address I.source,
          .address (AccountAddress.ofUInt256 (freeVowMaskedWord σUrns I)),
          .int (-(Int.ofNat (freeUrnsInkWord out).toNat)), .int 0]
        (false, evmGrab, grabOut) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evmUrns :=
      { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σUrns, substate := AUrns, createdAccounts := cAUrns }
    ExecTransitionBody config contract evm0 (freeStore I) freeTransition.body .reverted := by
  intro evm0 evmUrns
  have hliveEval :
      evalExpr? config { contract := contract, locals := freeStore I } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [freeLiveWord, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_free_live_zero_true evm0 I
        (by simpa [freeLiveWord, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount]
          using hlive)
  have hvat :
      evalExpr? config { contract := contract, locals := freeStore I } evm0 (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)) := by
    simpa [freeVatMaskedWord, freeVatWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, u256_land_comm] using
      evalExpr_freeVatStorage (evm := evm0) (locals := freeStore I) (by simp [freeStore])
  have hguard :
      evalExpr? config { contract := contract, locals := freeStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_freeVatCodeGuard_true hvat hvatCode
  have hargsUrns := evalExprs_freeUrnsArgs (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hinkStmt :
      ExecStmt config { contract := contract, locals := freeUrnsLocals I out } evmUrns
        (.letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0))
        (.ok { contract := contract, locals := freeUrnsInkLocals I out } evmUrns) := by
    simpa [freeUrnsInkLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := freeUrnsLocals I out })
        (evm := evmUrns)
        (name := "ink")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatUrn") 0)
        (value := .int (Int.ofNat (freeUrnsInkWord out).toNat))
        evalExpr_freeUrnsInk)
  have hartStmt :
      ExecStmt config { contract := contract, locals := freeUrnsInkLocals I out } evmUrns
        (.letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1))
        (.ok { contract := contract, locals := freeUrnsArtLocals I out } evmUrns) := by
    simpa [freeUrnsArtLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := freeUrnsInkLocals I out })
        (evm := evmUrns)
        (name := "art")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatUrn") 1)
        (value := .int (Int.ofNat (freeUrnsArtWord out).toNat))
        evalExpr_freeUrnsArt_afterInk)
  have hvatGrab :
      evalExpr? config { contract := contract, locals := freeUrnsArtLocals I out } evmUrns
        (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (freeVatMaskedWord σUrns I).toNat)) := by
    simpa [freeVatMaskedWord, freeVatWord, endSlotWord, evmUrns, initState,
      Solm.EVM.storageLoad, State.lookupAccount, u256_land_comm] using
      evalExpr_freeVatStorage (evm := evmUrns) (locals := freeUrnsArtLocals I out)
        (by simp [freeUrnsArtLocals, freeUrnsInkLocals, freeUrnsLocals, freeStore])
  have hguardGrab :
      evalExpr? config { contract := contract, locals := freeUrnsArtLocals I out } evmUrns
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    have hcode :
        (UInt256.ofNat ((evmUrns.lookupAccount
          (AccountAddress.ofNat (freeVatMaskedWord σUrns I).toNat)).option 0
          (fun acc => acc.code.size))).toNat ≠ 0 := by
      intro hnat
      apply hvatCodeGrab
      simp [Reasoning.Theory.uniswapExtCodeSizeWord, evmUrns, State.lookupAccount,
        accountAddress_ofUInt256_eq_ofNat_toNat] at hnat ⊢
      cases hfind : σUrns.find? (AccountAddress.ofNat (freeVatMaskedWord σUrns I).toNat)
      · native_decide
      · simp [hfind, Option.option, Function.comp] at hnat ⊢
        exact uint256_toNat_eq_zero hnat
    exact evalExpr_freeVatCodeGuard_true hvatGrab hcode
  have hargsGrab :=
    evalExprs_freeGrabArgs (cA := cA) (gh := gh) (bl := bl) (σ := σUrns) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (cA' := cAUrns) (A' := AUrns) out
  have hcallGrabStmt :
      ExecStmt config { contract := contract, locals := freeUrnsArtLocals I out } evmUrns
        (.externalCall (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", sender, sender, vowAddr, .unary .neg (asInt256 (.var "ink")),
            .intLit 0]
          "_grab" (perm := true))
        .reverted := by
    exact ExecStmt.externalCallFailure hvatGrab (by simp [evalExpr?, pure]) hargsGrab hcallGrab
  have hblock :
      ExecBlock config { contract := contract, locals := freeStore I } evm0 freeTransition.body
        .reverted := by
    simp only [freeTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveEval) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsUrns
        hcallUrns hdec) ?_
    refine ExecBlock.consNormal (by simpa [freeUrnsLocals, collapseReturns] using hinkStmt) ?_
    refine ExecBlock.consNormal (by
      simpa [freeUrnsLocals, freeUrnsInkLocals, freeUrnsArtLocals, collapseReturns] using
        hartStmt) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_freeArtZero_true hart)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_freeInkLe_true hink)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardGrab) ?_
    exact ExecBlock.consRevert hcallGrabStmt
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endFreeSourceBodyGrabNoCodeReverts {cA gh bl σ σUrns σ₀ A I} {g : UInt256}
    {cAUrns : Batteries.RBSet AccountAddress compare} {AUrns : Substate}
    {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : freeLiveWord σ I = ⟨0⟩)
    (hvatCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)).option 0
          (fun acc => acc.code.size))).toNat ≠ 0)
    (hcallUrns :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)) "urns" 0
        [freeIlkValue I, .address I.source]
        (true,
          { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σUrns, substate := AUrns, createdAccounts := cAUrns },
          out) true)
    (hdec : config.externalABI.decode? "urns" out = some (freeUrnsReturnValues out))
    (hart : freeUrnsArtWord out = ⟨0⟩)
    (hink : (freeUrnsInkWord out).toNat ≤ freeInt256LimitWord.toNat)
    (hvatNoCode :
      Reasoning.Theory.uniswapExtCodeSizeWord σUrns (freeVatMaskedWord σUrns I) = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evmUrns :=
      { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σUrns, substate := AUrns, createdAccounts := cAUrns }
    ExecTransitionBody config contract evm0 (freeStore I) freeTransition.body .reverted := by
  intro evm0 evmUrns
  have hliveEval :
      evalExpr? config { contract := contract, locals := freeStore I } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [freeLiveWord, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_free_live_zero_true evm0 I
        (by simpa [freeLiveWord, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount]
          using hlive)
  have hvat :
      evalExpr? config { contract := contract, locals := freeStore I } evm0 (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)) := by
    simpa [freeVatMaskedWord, freeVatWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, u256_land_comm] using
      evalExpr_freeVatStorage (evm := evm0) (locals := freeStore I) (by simp [freeStore])
  have hguard :
      evalExpr? config { contract := contract, locals := freeStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_freeVatCodeGuard_true hvat hvatCode
  have hargsUrns := evalExprs_freeUrnsArgs (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hinkStmt :
      ExecStmt config { contract := contract, locals := freeUrnsLocals I out } evmUrns
        (.letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0))
        (.ok { contract := contract, locals := freeUrnsInkLocals I out } evmUrns) := by
    simpa [freeUrnsInkLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := freeUrnsLocals I out })
        (evm := evmUrns)
        (name := "ink")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatUrn") 0)
        (value := .int (Int.ofNat (freeUrnsInkWord out).toNat))
        evalExpr_freeUrnsInk)
  have hartStmt :
      ExecStmt config { contract := contract, locals := freeUrnsInkLocals I out } evmUrns
        (.letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1))
        (.ok { contract := contract, locals := freeUrnsArtLocals I out } evmUrns) := by
    simpa [freeUrnsArtLocals] using
      (ExecStmt.letDecl
        (cfg := config)
        (solm := { contract := contract, locals := freeUrnsInkLocals I out })
        (evm := evmUrns)
        (name := "art")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatUrn") 1)
        (value := .int (Int.ofNat (freeUrnsArtWord out).toNat))
        evalExpr_freeUrnsArt_afterInk)
  have hvatGrab :
      evalExpr? config { contract := contract, locals := freeUrnsArtLocals I out } evmUrns
        (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (freeVatMaskedWord σUrns I).toNat)) := by
    simpa [freeVatMaskedWord, freeVatWord, endSlotWord, evmUrns, initState,
      Solm.EVM.storageLoad, State.lookupAccount, u256_land_comm] using
      evalExpr_freeVatStorage (evm := evmUrns) (locals := freeUrnsArtLocals I out)
        (by simp [freeUrnsArtLocals, freeUrnsInkLocals, freeUrnsLocals, freeStore])
  have hguardGrab :
      evalExpr? config { contract := contract, locals := freeUrnsArtLocals I out } evmUrns
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_freeVatCodeGuard_false hvatGrab (by
      have hnat := congrArg UInt256.toNat hvatNoCode
      simp [Reasoning.Theory.uniswapExtCodeSizeWord, evmUrns, initState, State.lookupAccount,
        accountAddress_ofUInt256_eq_ofNat_toNat] at hnat ⊢
      cases hfind : σUrns.find? (AccountAddress.ofNat (freeVatMaskedWord σUrns I).toNat)
      · native_decide
      · simp [hfind, Option.option, Function.comp] at hnat ⊢
        exact hnat)
  have hblock :
      ExecBlock config { contract := contract, locals := freeStore I } evm0 freeTransition.body
        .reverted := by
    simp only [freeTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveEval) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsUrns
        hcallUrns hdec) ?_
    refine ExecBlock.consNormal (by simpa [freeUrnsLocals, collapseReturns] using hinkStmt) ?_
    refine ExecBlock.consNormal (by
      simpa [freeUrnsLocals, freeUrnsInkLocals, freeUrnsArtLocals, collapseReturns] using
        hartStmt) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_freeArtZero_true hart)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_freeInkLe_true hink)) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardGrab)
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem RD.endFreeLiveReverts {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : freeLiveWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g s0 ⟨7690⟩
      [freeIlkWord I, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have rd7693pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k7694, C7694, rd7694raw⟩ := rd7693pre.sload (by native_decide) (by evm_ov)
  have rd7694 : RD endBytecode I g s0 ⟨7694⟩
      (freeLiveWord σ I :: freeIlkWord I :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k7694 C7694 := by
    simpa [freeLiveWord, endSlotWord] using rd7694raw
  have rd7695raw := rd7694.iszero (by native_decide) (by evm_ov)
  have rd7695 : RD endBytecode I g s0 ⟨7695⟩
      (⟨0⟩ :: freeIlkWord I :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k7694 + 1) (C7694 + 3) := by
    simpa [isZero_eq_zero_of_ne hlive] using rd7695raw
  have rd7698 := rd7695.pushConst (⟨7760⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd7699 := rd7698.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨7699⟩)
    (len := ⟨14⟩)
    (rawWord := ⟨1408232366394249557190267185493605⟩)
    (shift := ⟨144⟩)
    (word := UInt256.shiftLeft ⟨1408232366394249557190267185493605⟩ ⟨144⟩)
    (op := .PUSH14)
    (width := 14)
    rd7699
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    rfl
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.endFreeLiveOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : freeLiveWord σ I = ⟨0⟩)
    (h : RD endBytecode I g s0 ⟨7690⟩
      [freeIlkWord I, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨7760⟩
      [freeIlkWord I, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd7693pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k7694, C7694, rd7694raw⟩ := rd7693pre.sload (by native_decide) (by evm_ov)
  have rd7694 : RD endBytecode I g s0 ⟨7694⟩
      (freeLiveWord σ I :: freeIlkWord I :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k7694 C7694 := by
    simpa [freeLiveWord, endSlotWord] using rd7694raw
  have rd7695raw := rd7694.iszero (by native_decide) (by evm_ov)
  have rd7695 : RD endBytecode I g s0 ⟨7695⟩
      (⟨1⟩ :: freeIlkWord I :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k7694 + 1) (C7694 + 3) := by
    rw [hlive] at rd7695raw
    simpa using rd7695raw
  have rd7698 := rd7695.pushConst (⟨7760⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd7698.jumpiT (by native_decide) (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem RD.endFreeUrnsExtcodesizeGuard
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨7760⟩
      [freeIlkWord I, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨7831⟩
      (freeVatMaskedWord σ I :: freeVatMaskedWord σ I :: ⟨0⟩ ::
        freeUrnsOutPtr :: freeUrnsInSize :: freeUrnsOutPtr :: freeUrnsOutSize :: freeUrnsEndPtr ::
        freeUrnsSelectorWord :: freeVatMaskedWord σ I :: ⟨0⟩ :: ⟨0⟩ ::
        freeIlkWord I :: ⟨562⟩ :: [sel])
      (freeUrnsCalldataMem I solcFreePtrMem)
      (UInt256.ofNat 7) ByteArray.empty (cA, σ) k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ solcFreePtrMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (solcFreePtrMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [solcFreePtrMem_size]; decide) (by decide) solcFreePtrMem_read64
  have hCallMemSize : (freeUrnsCalldataMem I solcFreePtrMem).size = 196 :=
    freeUrnsCalldataMem_size I solcFreePtrMem_size
  have hCallRead64 :
      (freeUrnsCalldataMem I solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    freeUrnsCalldataMem_read64 I solcFreePtrMem_size solcFreePtrMem_read64
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (freeUrnsCalldataMem I solcFreePtrMem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((freeUrnsCalldataMem I solcFreePtrMem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hCallMemSize]; decide) (by decide) hCallRead64
  have hsourceWord : EVM.Word.ofNat I.source.val = freeSourceWord I := by rfl
  have rd7763 := evm_run rd with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k7764, C7764, rd7764raw⟩ := rd7763.sload (by native_decide) (by evm_ov)
  have rd7764 : RD endBytecode I g s0 ⟨7764⟩
      (freeVatWord σ I :: freeIlkWord I :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k7764 C7764 := by
    simpa [freeVatWord, endSlotWord] using rd7764raw
  have rd7831 := evm_run rd7764 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push4 ⟨0x09092f97⟩ (by native_decide) (by evm_ov),
    push1 ⟨226⟩,
    shl,
    dup2,
    raw mstore 6 (freeUrnsSelectorMem solcFreePtrMem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨4⟩,
    dup2,
    add,
    dup5,
    swap1,
    raw mstore 3 (freeUrnsIlkMem I solcFreePtrMem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    caller,
    push1 ⟨36⟩,
    dup3,
    add,
    raw mstore 3 (freeUrnsCalldataMem I solcFreePtrMem) (UInt256.ofNat 7)
      (by native_decide) mem_cost
      (by
        unfold freeUrnsCalldataMem freeSourceWord
        change (UInt256.ofNat I.source.val).toByteArray.write 0
          (freeUrnsIlkMem I solcFreePtrMem) 164 32 =
          (UInt256.ofNat I.source.val).toByteArray.write 0
            (freeUrnsIlkMem I solcFreePtrMem) 164 32
        rfl)
      (by native_decide) (by evm_ov),
    dup2,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    push1 ⟨0⟩,
    swap4,
    dup5,
    swap4,
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    swap1,
    swap2,
    and,
    swap3,
    raw push4 freeUrnsSelectorWord (by native_decide) (by evm_ov),
    swap3,
    push1 ⟨68⟩,
    dup1,
    dup4,
    add,
    swap4,
    swap3,
    dup3,
    swap1,
    sub,
    add,
    dup2,
    dup8,
    dup8,
    dup1]
  exact ⟨_, _, by
    simpa [freeVatMaskedWord, freeVatWord, endSlotWord, freeUrnsSelectorShifted,
      freeUrnsSelectorWord, freeUrnsSelectorMem, freeUrnsIlkMem, freeUrnsCalldataMem,
      freeUrnsOutPtr, freeUrnsInSize, freeUrnsOutSize, freeUrnsEndPtr, freeSourceWord,
      solcAddrMask, u256_land_comm,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide] using rd7831⟩

theorem RD.endFreeUrnsNoCode
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨7760⟩
      [freeIlkWord I, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (freeVatMaskedWord σ I) = ⟨0⟩) :
    RDrev endBytecode g s0 := by
  obtain ⟨_, _, rd7831⟩ := RD.endFreeUrnsExtcodesizeGuard rd
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨7831⟩) (okPc := ⟨7843⟩)
    rd7831 hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.endFreeUrnsCall
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨7760⟩
      [freeIlkWord I, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (freeVatMaskedWord σ I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g s0 ⟨7846⟩
      (gasWord :: freeVatMaskedWord σ I :: ⟨0⟩ ::
        freeUrnsOutPtr :: freeUrnsInSize :: freeUrnsOutPtr :: freeUrnsOutSize ::
        freeUrnsEndPtr :: freeUrnsSelectorWord :: freeVatMaskedWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: freeIlkWord I :: ⟨562⟩ :: [sel])
      (freeUrnsCalldataMem I solcFreePtrMem)
      (UInt256.ofNat 7) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd7831⟩ := RD.endFreeUrnsExtcodesizeGuard rd
  obtain ⟨gasWord, k', C', rd7846⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨7831⟩) (okPc := ⟨7843⟩)
      rd7831 hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by evm_ov)
  exact ⟨gasWord, k', C', rd7846⟩

theorem RD.endFreeUrnsPostCallRaw
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨7760⟩
      [freeIlkWord I, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (freeVatMaskedWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (k' C' : ℕ),
      RD endBytecode I g s0 ⟨7847⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: freeUrnsEndPtr :: freeUrnsSelectorWord ::
          freeVatMaskedWord σ I :: ⟨0⟩ :: ⟨0⟩ :: freeIlkWord I :: ⟨562⟩ :: [sel])
        (out.write 0 (freeUrnsCalldataMem I solcFreePtrMem) freeUrnsOutPtr.toNat
          (min freeUrnsOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 7) out (cA', σ') k' C'
    ∧ out.size < UInt256.size := by
  obtain ⟨_, _, _, rd7846⟩ := RD.endFreeUrnsCall rd hcodeSize
  obtain ⟨cA', σ', z, out, A_in, callGas, k7847, C7847, hΘ, rd7847raw, houtsz⟩ :=
    RD.call rd7846 (by native_decide) hdepth (by evm_ov)
  obtain ⟨_, _, _⟩ := hΘ
  refine ⟨cA', σ', z, out, k7847, C7847, ?_, houtsz⟩
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
        freeUrnsOutPtr.toNat freeUrnsInSize.toNat)
        freeUrnsOutPtr.toNat freeUrnsOutSize.toNat) = UInt256.ofNat 7 := by
    unfold freeUrnsOutPtr freeUrnsInSize freeUrnsOutSize
    native_decide
  exact haw ▸ rd7847raw

theorem RD.endFreeUrnsPostCall
    {cA gh bl σ σ₀ A I} {g sel : UInt256} {k C : ℕ}
    (rd : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7760⟩
      [freeIlkWord I, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (freeVatMaskedWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD endBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7847⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: freeUrnsEndPtr :: freeUrnsSelectorWord ::
          freeVatMaskedWord σ I :: ⟨0⟩ :: ⟨0⟩ :: freeIlkWord I :: ⟨562⟩ :: [sel])
        (freeUrnsPostCallMem I out) (UInt256.ofNat 7) out (cA', σ') k' C'
    ∧ typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)) "urns" 0
        [freeIlkValue I, .address I.source]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, out) I.perm
    ∧ out.size < UInt256.size := by
  obtain ⟨_, _, _, rd7846⟩ := RD.endFreeUrnsCall rd hcodeSize
  obtain ⟨cA', σ', z, out, A_in, callGas, k7847, C7847, hΘ, rd7847raw, houtsz⟩ :=
    RD.call rd7846 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ'⟩ := hΘ
  refine ⟨cA', σ', z, out, A', k7847, C7847, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
          freeUrnsOutPtr.toNat freeUrnsInSize.toNat)
          freeUrnsOutPtr.toNat freeUrnsOutSize.toNat) = UInt256.ofNat 7 := by
      unfold freeUrnsOutPtr freeUrnsInSize freeUrnsOutSize
      native_decide
    simpa [freeUrnsPostCallMem] using haw ▸ rd7847raw
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := I.perm) (targetWord := freeVatMaskedWord σ I)
      (mem := freeUrnsCalldataMem I solcFreePtrMem) (inOff := freeUrnsOutPtr)
      (inSize := freeUrnsInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      ?_ (freeUrnsEncode_eq I) ?_
    · exact (freeEvmAddress_ofNat_toNat_eq_ofUInt256 (freeVatMaskedWord σ I)).symm
    · simpa [initState] using hΘ'

theorem RD.endFreeUrnsCallFailure
    {cA σ I} {g : Sat256} {s0 : State} {mem o : ByteArray} {aw : UInt256}
    {k C : ℕ} {rest : List UInt256}
    (rd : RD endBytecode I g s0 ⟨7847⟩
      (⟨0⟩ :: rest) mem aw o (cA, σ) k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev endBytecode g s0 := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨7847⟩) (okPc := ⟨7863⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hosz hov

theorem RD.endFreeUrnsCallSuccessToDecode
    {cA σ I} {g : Sat256} {s0 : State} {mem o : ByteArray} {aw : UInt256}
    {k C : ℕ} {R : List UInt256}
    (rd : RD endBytecode I g s0 ⟨7847⟩ (⟨1⟩ :: R) mem aw o (cA, σ) k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD endBytecode I g s0 ⟨7865⟩ R mem aw o (cA, σ) k' C' := by
  exact RD.uniswapCallSuccessGuardOk (pc := ⟨7847⟩) (okPc := ⟨7863⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide) hov

theorem RD.endFreeUrnsReturnDecodeShortReverts
    {cA σStack σCall I} {g : Sat256} {s0 : State} {out : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨7865⟩
      (freeUrnsEndPtr :: freeUrnsSelectorWord :: freeVatMaskedWord σStack I ::
        ⟨0⟩ :: ⟨0⟩ :: freeIlkWord I :: ⟨562⟩ :: [sel])
      (freeUrnsPostCallMem I out) (UInt256.ofNat 7) out (cA, σCall) k C)
    (hshort : out.size < 64) (hout : out.size < UInt256.size) :
    RDrev endBytecode g s0 := by
  have hmload64 := freeUrnsPostCallMem_mload64 I out hshort hout
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨64⟩ : UInt256) = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' out.size hout]
    exact hshort
  have rd7875 := evm_run rd with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd7876raw := RD.lt rd7875 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd7876 := by
    simpa [hlt] using rd7876raw
  have rd7880 := evm_run rd7876 with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨7885⟩ (by native_decide) (by evm_ov)]
  have rd7881 := rd7880.jumpiNT (by native_decide) rfl
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.uniswapPush1Dup1Revert0 (pc := ⟨7881⟩) rd7881
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.endFreeUrnsReturnDecodeOkToArtGuard
    {cA σStack σCall I} {g : Sat256} {s0 : State} {out : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨7865⟩
      (freeUrnsEndPtr :: freeUrnsSelectorWord :: freeVatMaskedWord σStack I ::
        ⟨0⟩ :: ⟨0⟩ :: freeIlkWord I :: ⟨562⟩ :: [sel])
      (freeUrnsPostCallMem I out) (UInt256.ofNat 7) out (cA, σCall) k C)
    (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    ∃ k' C', RD endBytecode I g s0 ⟨7900⟩
      (freeUrnsArtWord out :: freeUrnsInkWord out :: freeIlkWord I :: ⟨562⟩ :: [sel])
      (freeUrnsPostCallMem I out) (UInt256.ofNat 7) out (cA, σCall) k' C' := by
  have hmload64 := freeUrnsPostCallMem_mload64_long I out hlong hout
  have hmload128 := freeUrnsPostCallMem_mload128_long I out hlong hout
  have hmload160 := freeUrnsPostCallMem_mload160_long I out hlong hout
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨64⟩ : UInt256) = ⟨0⟩ := by
    apply ult_zero
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' out.size hout]
    exact hlong
  have rd7875 := evm_run rd with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd7876raw := RD.lt rd7875 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd7876 := by
    simpa [hlt] using rd7876raw
  have rd7880 := evm_run rd7876 with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨7885⟩ (by native_decide) (by evm_ov)]
  have rd7885 := rd7880.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd7893 := evm_run rd7885 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 (freeUrnsInkWord out) (UInt256.ofNat 7) (by native_decide)
      mem_cost hmload128 (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd7894raw := RD.add rd7893 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨k7894, C7894, rd7894⟩ :
      ∃ k7894 C7894, RD endBytecode I g s0 ⟨7894⟩
        (⟨160⟩ :: freeUrnsInkWord out :: ⟨0⟩ :: ⟨0⟩ :: freeIlkWord I :: ⟨562⟩ :: [sel])
        (freeUrnsPostCallMem I out) (UInt256.ofNat 7) out (cA, σCall) k7894 C7894 := by
    exact ⟨_, _, by simpa using rd7894raw⟩
  have rd7900 := evm_run rd7894 with [
    raw mload 0 (freeUrnsArtWord out) (UInt256.ofNat 7) (by native_decide)
      mem_cost hmload160 (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd7900⟩

theorem RD.endFreeUrnsArtZeroToInkGuard
    {cA σ I} {g : Sat256} {s0 : State} {out : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨7900⟩
      (freeUrnsArtWord out :: freeUrnsInkWord out :: freeIlkWord I :: ⟨562⟩ :: [sel])
      (freeUrnsPostCallMem I out) (UInt256.ofNat 7) out (cA, σ) k C)
    (hart : freeUrnsArtWord out = ⟨0⟩) :
    ∃ k' C', RD endBytecode I g s0 ⟨7969⟩
      (freeUrnsArtWord out :: freeUrnsInkWord out :: freeIlkWord I :: ⟨562⟩ :: [sel])
      (freeUrnsPostCallMem I out) (UInt256.ofNat 7) out (cA, σ) k' C' := by
  have rd7902raw := evm_run rd with [
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  have rd7902 := by
    simpa [hart] using rd7902raw
  have rd7905 := evm_run rd7902 with [
    raw push2 ⟨7969⟩ (by native_decide) (by evm_ov)]
  have rd7969 := rd7905.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [hart] using rd7969⟩

set_option maxHeartbeats 1000000 in
theorem RD.solcErrorStringRevertTailMem196 {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 7) rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) hd3
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 7)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 7)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 0 (solcErrorStringMem2 len mem)
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
      (solcErrorStringMem3_mload64_of_size196 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

theorem RD.endFreeUrnsArtNonzeroReverts
    {cA σ I} {g : Sat256} {s0 : State} {out : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨7900⟩
      (freeUrnsArtWord out :: freeUrnsInkWord out :: freeIlkWord I :: ⟨562⟩ :: [sel])
      (freeUrnsPostCallMem I out) (UInt256.ofNat 7) out (cA, σ) k C)
    (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hart : freeUrnsArtWord out ≠ ⟨0⟩) :
    RDrev endBytecode g s0 := by
  have hmem := freeUrnsPostCallMem_size_long I out hlong hout
  have hread64 := freeUrnsPostCallMem_read64_long I out hlong hout
  have rd7902raw := evm_run rd with [
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  have rd7902 := by
    simpa [isZero_eq_zero_of_ne hart] using rd7902raw
  have rd7905 := evm_run rd7902 with [
    raw push2 ⟨7969⟩ (by native_decide) (by evm_ov)]
  have rd7906 := rd7905.jumpiNT (by native_decide) rfl
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.solcErrorStringRevertTailMem196
    (pc := ⟨7906⟩)
    (len := ⟨16⟩)
    (rawWord := ⟨92289916358440441735647045770509906543⟩)
    (shift := ⟨128⟩)
    (word := UInt256.shiftLeft ⟨92289916358440441735647045770509906543⟩ ⟨128⟩)
    (op := .PUSH16)
    (width := 16)
    rd7906
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by rfl)
    hmem
    hread64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.endFreeUrnsInkTooLargeReverts
    {cA σ I} {g : Sat256} {s0 : State} {out : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨7969⟩
      (freeUrnsArtWord out :: freeUrnsInkWord out :: freeIlkWord I :: ⟨562⟩ :: [sel])
      (freeUrnsPostCallMem I out) (UInt256.ofNat 7) out (cA, σ) k C)
    (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hink : ¬ (freeUrnsInkWord out).toNat ≤ freeInt256LimitWord.toNat) :
    RDrev endBytecode g s0 := by
  have hmem := freeUrnsPostCallMem_size_long I out hlong hout
  have hread64 := freeUrnsPostCallMem_read64_long I out hlong hout
  have hgt : UInt256.gt (freeUrnsInkWord out) freeInt256LimitWord = ⟨1⟩ :=
    ugt_one (by omega)
  have rd7975 := evm_run rd with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨255⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rd7977raw := RD.gt rd7975 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd7977 := by
    simpa [freeInt256LimitWord, hgt] using rd7977raw
  have rd7981 := evm_run rd7977 with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨8041⟩ (by native_decide) (by evm_ov)]
  have rd7982 := rd7981.jumpiNT (by native_decide) rfl
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.solcErrorStringRevertTailMem196
    (pc := ⟨7982⟩)
    (len := ⟨12⟩)
    (rawWord := ⟨21487920629507395907578785655⟩)
    (shift := ⟨160⟩)
    (word := UInt256.shiftLeft ⟨21487920629507395907578785655⟩ ⟨160⟩)
    (op := .PUSH12)
    (width := 12)
    rd7982
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by rfl)
    hmem
    hread64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.endFreeUrnsInkOkToGrabPrep
    {cA σ I} {g : Sat256} {s0 : State} {out : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨7969⟩
      (freeUrnsArtWord out :: freeUrnsInkWord out :: freeIlkWord I :: ⟨562⟩ :: [sel])
      (freeUrnsPostCallMem I out) (UInt256.ofNat 7) out (cA, σ) k C)
    (hink : (freeUrnsInkWord out).toNat ≤ freeInt256LimitWord.toNat) :
    ∃ k' C', RD endBytecode I g s0 ⟨8041⟩
      (freeUrnsArtWord out :: freeUrnsInkWord out :: freeIlkWord I :: ⟨562⟩ :: [sel])
      (freeUrnsPostCallMem I out) (UInt256.ofNat 7) out (cA, σ) k' C' := by
  have hgt : UInt256.gt (freeUrnsInkWord out) freeInt256LimitWord = ⟨0⟩ :=
    ugt_zero hink
  have rd7975 := evm_run rd with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨255⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rd7977raw := RD.gt rd7975 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd7977 := by
    simpa [freeInt256LimitWord, hgt] using rd7977raw
  have rd7981 := evm_run rd7977 with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨8041⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, rd7981.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)⟩

theorem RD.endFreeGrabExtcodesizeGuard
    {cA σ I} {g : Sat256} {s0 : State} {urnOut : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨8041⟩
      (freeUrnsArtWord urnOut :: freeUrnsInkWord urnOut :: freeIlkWord I :: ⟨562⟩ :: [sel])
      (freeUrnsPostCallMem I urnOut) (UInt256.ofNat 7) urnOut (cA, σ) k C)
    (hlong : 64 ≤ urnOut.size) (hurnOut : urnOut.size < UInt256.size) :
    ∃ k' C', RD endBytecode I g s0 ⟨8143⟩
      (freeVatMaskedWord σ I :: freeVatMaskedWord σ I :: ⟨0⟩ ::
        freeGrabOutPtr :: freeGrabInSize :: freeGrabOutPtr :: freeGrabOutSize ::
        freeGrabEndPtr :: freeGrabSelectorWord :: freeVatMaskedWord σ I ::
        freeUrnsArtWord urnOut :: freeUrnsInkWord urnOut :: freeIlkWord I :: ⟨562⟩ :: [sel])
      (freeGrabCalldataMem σ I urnOut (freeUrnsPostCallMem I urnOut))
      (UInt256.ofNat 11) urnOut (cA, σ) k' C' := by
  have hbaseMem : (freeUrnsPostCallMem I urnOut).size = 196 :=
    freeUrnsPostCallMem_size_long I urnOut hlong hurnOut
  have hbaseRead64 :
      (freeUrnsPostCallMem I urnOut).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    freeUrnsPostCallMem_read64_long I urnOut hlong hurnOut
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (freeUrnsPostCallMem I urnOut).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((freeUrnsPostCallMem I urnOut).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    freeUrnsPostCallMem_mload64_long I urnOut hlong hurnOut
  have hCallMemSize :
      (freeGrabCalldataMem σ I urnOut (freeUrnsPostCallMem I urnOut)).size = 324 :=
    freeGrabCalldataMem_size σ I urnOut hbaseMem
  have hCallRead64 :
      (freeGrabCalldataMem σ I urnOut (freeUrnsPostCallMem I urnOut)).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    freeGrabCalldataMem_read64 σ I urnOut hbaseMem hbaseRead64
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (freeGrabCalldataMem σ I urnOut (freeUrnsPostCallMem I urnOut)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 11 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((freeGrabCalldataMem σ I urnOut (freeUrnsPostCallMem I urnOut)).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hCallMemSize]; decide) (by decide) hCallRead64
  have hvatCanon : (freeVatMaskedWord σ I).toNat < EVM.addressModulus := by
    simpa [freeVatMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (freeVatWord σ I)
  have hvatMask :
      UInt256.land solcAddrMask (freeVatMaskedWord σ I) = freeVatMaskedWord σ I :=
    solcAddrMask_clean_left hvatCanon
  have hvowCanon : (freeVowMaskedWord σ I).toNat < EVM.addressModulus := by
    simpa [freeVowMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (freeVowWord σ I)
  have hvowMask :
      UInt256.land solcAddrMask (freeVowMaskedWord σ I) = freeVowMaskedWord σ I :=
    solcAddrMask_clean_left hvowCanon
  have rd8044pre := evm_run rd with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k8044, C8044, rd8044raw⟩ := rd8044pre.sload (by native_decide) (by evm_ov)
  have rd8045 : RD endBytecode I g s0 ⟨8045⟩
      (freeVatWord σ I :: freeUrnsArtWord urnOut :: freeUrnsInkWord urnOut ::
        freeIlkWord I :: ⟨562⟩ :: [sel])
      (freeUrnsPostCallMem I urnOut) (UInt256.ofNat 7) urnOut (cA, σ) k8044 C8044 := by
    simpa [freeVatWord, endSlotWord] using rd8044raw
  have rd8048pre := evm_run rd8045 with [
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k8048, C8048, rd8048raw⟩ := rd8048pre.sload (by native_decide) (by evm_ov)
  have rd8049 : RD endBytecode I g s0 ⟨8049⟩
      (freeVowWord σ I :: ⟨4⟩ :: freeVatWord σ I :: freeUrnsArtWord urnOut ::
        freeUrnsInkWord urnOut :: freeIlkWord I :: ⟨562⟩ :: [sel])
      (freeUrnsPostCallMem I urnOut) (UInt256.ofNat 7) urnOut (cA, σ) k8048 C8048 := by
    simpa [freeVowWord, endSlotWord] using rd8048raw
  have rd8143 := evm_run rd8049 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push4 ⟨0x01eeacfd⟩ (by native_decide) (by evm_ov),
    push1 ⟨230⟩,
    shl,
    dup2,
    raw mstore 0 (freeGrabSelectorMem (freeUrnsPostCallMem I urnOut)) (UInt256.ofNat 7)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    swap3,
    dup4,
    add,
    dup8,
    swap1,
    raw mstore 0 (freeGrabIlkMem I (freeUrnsPostCallMem I urnOut)) (UInt256.ofNat 7)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    caller,
    push1 ⟨36⟩,
    dup5,
    add,
    dup2,
    swap1,
    raw mstore 0 (freeGrabUsrMem I (freeUrnsPostCallMem I urnOut)) (UInt256.ofNat 7)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨68⟩,
    dup5,
    add,
    raw mstore 3 (freeGrabVMem I (freeUrnsPostCallMem I urnOut)) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    swap2,
    dup3,
    and,
    push1 ⟨100⟩,
    dup5,
    add,
    raw mstore 3 (freeGrabWMem σ I (freeUrnsPostCallMem I urnOut)) (UInt256.ofNat 9)
      (by native_decide) mem_cost
      (by
        rw [show ({ val := 128 } + { val := 100 } : UInt256).toNat = 228
          from by native_decide]
        simp [freeGrabWMem, freeGrabVMem, freeVowMaskedWord, u256_land_comm,
          show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask from by decide])
      (by native_decide) (by evm_ov),
    push1 ⟨0⟩,
    dup7,
    dup2,
    sub,
    push1 ⟨132⟩,
    dup6,
    add,
    raw mstore 3 (freeGrabDinkMem σ I urnOut (freeUrnsPostCallMem I urnOut))
      (UInt256.ofNat 10) (by native_decide) mem_cost
      (by
        rw [show ({ val := 128 } + { val := 132 } : UInt256).toNat = 260
          from by native_decide]
        rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨164⟩,
    dup5,
    add,
    dup2,
    swap1,
    raw mstore 3 (freeGrabCalldataMem σ I urnOut (freeUrnsPostCallMem I urnOut))
      (UInt256.ofNat 11) (by native_decide) mem_cost
      (by
        rw [show ({ val := 128 } + { val := 164 } : UInt256).toNat = 292
          from by native_decide]
        rfl)
      (by native_decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 11) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    swap2,
    swap1,
    swap4,
    and,
    swap3,
    raw push4 freeGrabSelectorWord (by native_decide) (by evm_ov),
    swap3,
    push1 ⟨196⟩,
    dup1,
    dup3,
    add,
    swap4,
    swap2,
    dup3,
    swap1,
    sub,
    add,
    dup2,
    dup4,
    dup8,
    dup1]
  exact ⟨_, _, by
    simpa [freeVatMaskedWord, freeVatWord, freeVowWord, freeVowMaskedWord,
      endSlotWord, freeGrabSelectorShifted, freeGrabSelectorWord, freeGrabSelectorMem,
      freeGrabIlkMem, freeGrabUsrMem, freeGrabVMem, freeGrabWMem, freeGrabDinkMem,
      freeGrabCalldataMem, freeGrabOutPtr, freeGrabInSize, freeGrabOutSize,
      freeGrabEndPtr, freeGrabDinkWord, solcAddrMask, u256_land_comm, hvatMask, hvowMask,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨196⟩ = freeGrabInSize
        from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨196⟩ = freeGrabEndPtr from by native_decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide] using rd8143⟩

theorem RD.endFreeGrabPostCall
    {cA0 cA gh bl σBase σ σ₀ A0 ACall I} {g sel : UInt256} {urnOut : ByteArray}
    {k C : ℕ}
    (rd : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA0 gh bl σBase σ₀ (Sat256.ofUInt256 g) A0 I) ⟨8041⟩
      (freeUrnsArtWord urnOut :: freeUrnsInkWord urnOut :: freeIlkWord I :: ⟨562⟩ :: [sel])
      (freeUrnsPostCallMem I urnOut) (UInt256.ofNat 7) urnOut (cA, σ) k C)
    (hlong : 64 ≤ urnOut.size) (hurnOut : urnOut.size < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (freeVatMaskedWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hink : (freeUrnsInkWord urnOut).toNat ≤ freeInt256LimitWord.toNat) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD endBytecode I (Sat256.ofUInt256 g)
        (initState cA0 gh bl σBase σ₀ (Sat256.ofUInt256 g) A0 I) ⟨8159⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: freeGrabEndPtr :: freeGrabSelectorWord ::
          freeVatMaskedWord σ I :: freeUrnsArtWord urnOut :: freeUrnsInkWord urnOut ::
          freeIlkWord I :: ⟨562⟩ :: [sel])
        (freeGrabPostCallMem σ I urnOut out) (UInt256.ofNat 11) out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA0 gh bl σBase σ₀ (Sat256.ofUInt256 g) A0 I with
          accountMap := σ, substate := ACall, createdAccounts := cA }
        (EVM.address (AccountAddress.ofNat (freeVatMaskedWord σ I).toNat)) "grab" 0
        [freeIlkValue I, .address I.source, .address I.source,
          .address (AccountAddress.ofUInt256 (freeVowMaskedWord σ I)),
          .int (-(Int.ofNat (freeUrnsInkWord urnOut).toNat)), .int 0]
        (z, { initState cA0 gh bl σBase σ₀ (Sat256.ofUInt256 g) A0 I with
              accountMap := σ', substate := A', createdAccounts := cA' }, out) I.perm
    ∧ out.size < UInt256.size := by
  obtain ⟨_, _, rd8143⟩ := RD.endFreeGrabExtcodesizeGuard rd hlong hurnOut
  obtain ⟨gasWord, k8158, C8158, rd8158⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨8143⟩) (okPc := ⟨8155⟩)
      rd8143 hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by evm_ov)
  obtain ⟨cA', σ', z, out, A_in, callGas, k8159, C8159, hΘgrab, rd8159raw, houtsz⟩ :=
    RD.call rd8158 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘgrab
  refine ⟨cA', σ', z, out, A', k8159, C8159, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 11).toNat
          freeGrabOutPtr.toNat freeGrabInSize.toNat)
          freeGrabOutPtr.toNat freeGrabOutSize.toNat) = UInt256.ofNat 11 := by
      unfold freeGrabOutPtr freeGrabInSize freeGrabOutSize
      native_decide
    simpa [freeGrabPostCallMem] using haw ▸ rd8159raw
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := I.perm) (targetWord := freeVatMaskedWord σ I)
      (mem := freeGrabCalldataMem σ I urnOut (freeUrnsPostCallMem I urnOut))
      (inOff := freeGrabOutPtr) (inSize := freeGrabInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      ?_ (freeGrabEncode_eq σ I urnOut hink
        (freeUrnsPostCallMem_size_long I urnOut hlong hurnOut)) ?_
    · exact (freeEVMAddress_ofNat_toNat_eq_ofUInt256 (freeVatMaskedWord σ I)).symm
    · simpa [initState] using hΘ

theorem RD.endFreeGrabNoCode
    {cA σ I} {g : Sat256} {s0 : State} {urnOut : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨8041⟩
      (freeUrnsArtWord urnOut :: freeUrnsInkWord urnOut :: freeIlkWord I :: ⟨562⟩ :: [sel])
      (freeUrnsPostCallMem I urnOut) (UInt256.ofNat 7) urnOut (cA, σ) k C)
    (hlong : 64 ≤ urnOut.size) (hurnOut : urnOut.size < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (freeVatMaskedWord σ I) = ⟨0⟩) :
    RDrev endBytecode g s0 := by
  obtain ⟨_, _, rd8143⟩ := RD.endFreeGrabExtcodesizeGuard rd hlong hurnOut
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨8143⟩) (okPc := ⟨8155⟩)
    rd8143 hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.endFreeGrabCallFailure
    {cA σStack σCall I} {g : Sat256} {s0 : State} {urnOut out : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨8159⟩
      (⟨0⟩ :: freeGrabEndPtr :: freeGrabSelectorWord :: freeVatMaskedWord σStack I ::
        freeUrnsArtWord urnOut :: freeUrnsInkWord urnOut :: freeIlkWord I :: ⟨562⟩ :: [sel])
      (freeGrabPostCallMem σStack I urnOut out) (UInt256.ofNat 11) out (cA, σCall) k C)
    (houtsz : out.size < UInt256.size) :
    RDrev endBytecode g s0 := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨8159⟩) (okPc := ⟨8175⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) houtsz
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.endFreeGrabCallSuccessReturn
    {cA σStack σCall I} {g : Sat256} {s0 : State} {urnOut out : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨8159⟩
      (⟨1⟩ :: freeGrabEndPtr :: freeGrabSelectorWord :: freeVatMaskedWord σStack I ::
        freeUrnsArtWord urnOut :: freeUrnsInkWord urnOut :: freeIlkWord I :: ⟨562⟩ :: [sel])
      (freeGrabPostCallMem σStack I urnOut out) (UInt256.ofNat 11) out (cA, σCall) k C)
    (hperm : I.perm = true)
    (hlong : 64 ≤ urnOut.size) (hurnOut : urnOut.size < UInt256.size) :
    RDret endBytecode g s0 (cA, σCall) ByteArray.empty := by
  have hpostSize := freeGrabPostCallMem_size σStack I urnOut out hlong hurnOut
  have hpostRead64 := freeGrabPostCallMem_read64 σStack I urnOut out hlong hurnOut
  have hlogSize := freeGrabLogMem_size σStack I urnOut out hlong hurnOut
  have hlogRead64 := freeGrabLogMem_read64 σStack I urnOut out hlong hurnOut
  obtain ⟨k8177, C8177, rd8177⟩ :=
    RD.uniswapCallSuccessGuardOk (pc := ⟨8159⟩) (okPc := ⟨8175⟩) rd
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd8181pre := evm_run rd8177 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have rd8181 := RD.mload 0 ⟨128⟩ (UInt256.ofNat 11) rd8181pre
    (by native_decide) mem_cost
    (mloadFreePtrValue (by rw [hpostSize]; native_decide) (by native_decide) hpostRead64)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd8184pre := evm_run rd8181 with [
    raw dup6 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8184 := RD.mstore 0 (freeGrabLogMem σStack I urnOut out)
    (UInt256.ofNat 11) rd8184pre
    (by native_decide) mem_cost (by rfl) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd8186pre := evm_run rd8184 with [
    raw swap1 (by native_decide) (by evm_ov)]
  have rd8186 := RD.mload 0 ⟨128⟩ (UInt256.ofNat 11) rd8186pre
    (by native_decide) mem_cost
    (mloadFreePtrValue (by rw [hlogSize]; native_decide) (by native_decide) hlogRead64)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd8229pre := evm_run rd8186 with [
    raw caller (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd8226 := rd8229pre.pushConst
    (⟨109656130289137434518609496003275983118662975745057881014998262805362093846744⟩ :
      UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd8233pre := evm_run rd8226 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hlogLen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨32⟩ = ⟨32⟩ := by
    native_decide
  have rd8235 := RD.log3
    (a := ⟨128⟩) (b := ⟨32⟩)
    (c := ⟨109656130289137434518609496003275983118662975745057881014998262805362093846744⟩)
    (d := freeIlkWord I) (e := freeSourceWord I)
    (t := [freeUrnsArtWord urnOut, freeUrnsInkWord urnOut, freeIlkWord I, ⟨562⟩, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 11).toNat (⟨128⟩ : UInt256).toNat
        (⟨32⟩ : UInt256).toNat))
    (by simpa [freeSourceWord, hlogLen] using rd8233pre)
    (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd8238pre := evm_run rd8235 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd562 := RD.jump (a := ⟨562⟩) (t := [sel]) rd8238pre
    (by native_decide) (by jump_dest) (by evm_ov)
  have rd563 := RD.jumpdest (pc := ⟨562⟩) (stk := [sel]) rd562
    (by native_decide) (by evm_ov)
  exact RD.stop rd563 (by native_decide) (by evm_ov)

theorem RD.endFreeUrnsDepthLimitReverts
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨7760⟩
      [freeIlkWord I, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (freeVatMaskedWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    RDrev endBytecode g s0 := by
  obtain ⟨_, _, _, rd7846⟩ := RD.endFreeUrnsCall rd hcodeSize
  obtain ⟨k7847, C7847, rd7847raw⟩ :=
    RD.callDepthLimit rd7846 (by native_decide) hdepth (by simp)
  have hmin : (min freeUrnsOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    unfold freeUrnsOutSize
    rw [← u256_ofNat_toNat (UInt256.ofNat ByteArray.empty.size)]
    exact umin_ofNat_right_toNat_of_ge (by norm_num [UInt256.size]) (Nat.zero_le _)
      (UInt256.ofNat ByteArray.empty.size).val.isLt
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
        freeUrnsOutPtr.toNat freeUrnsInSize.toNat)
        freeUrnsOutPtr.toNat freeUrnsOutSize.toNat) = UInt256.ofNat 7 := by
    unfold freeUrnsOutPtr freeUrnsInSize freeUrnsOutSize
    native_decide
  have rd7847 : RD endBytecode I g s0 ⟨7847⟩
      (⟨0⟩ :: freeUrnsEndPtr :: freeUrnsSelectorWord :: freeVatMaskedWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: freeIlkWord I :: ⟨562⟩ :: [sel])
      (ByteArray.empty.write 0 (freeUrnsCalldataMem I solcFreePtrMem) freeUrnsOutPtr.toNat
        (min freeUrnsOutSize (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat 7) ByteArray.empty (cA, σ) k7847 C7847 := by
    exact haw ▸ rd7847raw
  simpa [hmin, byteArray_write_len_zero] using
    RD.endFreeUrnsCallFailure rd7847 (by native_decide) (by simp)

theorem endFreeBodyCore : endBodyObligation 27 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (endSelBytes 27) rfl hsel
  have hdispatch := endDispatchFreeLocal hsel
  have hreach :=
    endReachFreeBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := endDecode_free_ok (I := I) hsz36
    obtain ⟨_, _, h7690⟩ :=
      endFreeX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach
    by_cases hlive : freeLiveWord σ_evm I = ⟨0⟩
    · obtain ⟨_, _, h7760⟩ := RD.endFreeLiveOk (g := Sat256.ofUInt256 g) hlive h7690
      have hliveSolm : freeLiveWord σ_solm I = ⟨0⟩ := by
        have hword : freeLiveWord σ_evm I = freeLiveWord σ_solm I :=
          accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
        rw [← hword, hlive]
      have hliveEval :
          evalExpr? config
            { contract := contract, locals := freeStore I }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
        simpa [freeLiveWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
          evalExpr_free_live_zero_true
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simpa [freeLiveWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
              using hliveSolm)
      by_cases hvatNoCode :
          Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (freeVatMaskedWord σ_evm I) = ⟨0⟩
      · have hvatMasked :
            freeVatMaskedWord σ_evm I = freeVatMaskedWord σ_solm I := by
          have hvatWord : freeVatWord σ_evm I = freeVatWord σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
          change UInt256.land (freeVatWord σ_evm I) solcAddrMask =
            UInt256.land (freeVatWord σ_solm I) solcAddrMask
          rw [hvatWord]
        have hvatNoCodeSolm :
            Reasoning.Theory.uniswapExtCodeSizeWord σ_solm (freeVatMaskedWord σ_solm I) =
              ⟨0⟩ := by
          have hcodeEq :
              Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (freeVatMaskedWord σ_evm I) =
                Reasoning.Theory.uniswapExtCodeSizeWord σ_solm (freeVatMaskedWord σ_evm I) :=
            uniswapExtCodeSizeWord_accountMapEquiv hAccounts (freeVatMaskedWord σ_evm I)
          rw [← hvatMasked, ← hcodeEq]
          exact hvatNoCode
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (freeStore I)
              freeTransition.body .reverted := by
          exact endFreeSourceBodyVatNoCodeReverts (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hwv hliveSolm hvatNoCodeSolm
        have hrev := RD.endFreeUrnsNoCode (g := Sat256.ofUInt256 g) h7760 hvatNoCode
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hvatMasked :
            freeVatMaskedWord σ_evm I = freeVatMaskedWord σ_solm I := by
          have hvatWord : freeVatWord σ_evm I = freeVatWord σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
          change UInt256.land (freeVatWord σ_evm I) solcAddrMask =
            UInt256.land (freeVatWord σ_solm I) solcAddrMask
          rw [hvatWord]
        have hvatCodeSolm :
            Reasoning.Theory.uniswapExtCodeSizeWord σ_solm (freeVatMaskedWord σ_solm I) ≠
              ⟨0⟩ := by
          intro hzero
          apply hvatNoCode
          rw [← hvatMasked] at hzero
          rw [← uniswapExtCodeSizeWord_accountMapEquiv hAccounts
            (freeVatMaskedWord σ_evm I)] at hzero
          exact hzero
        have hvatCodeNatSolm :
            (UInt256.ofNat
              (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
                (AccountAddress.ofNat (freeVatMaskedWord σ_solm I).toNat)).option 0
                (fun acc => acc.code.size))).toNat ≠ 0 := by
          intro hnat
          apply hvatCodeSolm
          simp [Reasoning.Theory.uniswapExtCodeSizeWord, initState, State.lookupAccount,
            accountAddress_ofUInt256_eq_ofNat_toNat] at hnat ⊢
          cases hfind : σ_solm.find? (AccountAddress.ofNat (freeVatMaskedWord σ_solm I).toNat)
          · native_decide
          · simp [hfind, Option.option, Function.comp] at hnat ⊢
            exact uint256_toNat_eq_zero hnat
        by_cases hdepthMax : I.depth = (1024 : Fin 1025)
        · have hrev :=
            RD.endFreeUrnsDepthLimitReverts
              (g := Sat256.ofUInt256 g) h7760 hvatNoCode hdepthMax
          have hcallUrns :
              typedCallViaEVM config
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (EVM.address (AccountAddress.ofNat (freeVatMaskedWord σ_solm I).toNat))
                "urns" 0 [freeIlkValue I, .address I.source]
                (false,
                  { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                    substate :=
                      ((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).addAccessedAccount
                          (EVM.address
                            (AccountAddress.ofNat (freeVatMaskedWord σ_solm I).toNat))).substate },
                  ByteArray.empty) true := by
            exact callNotMade_depthLimit
              (cfg := config)
              (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (tgt := EVM.address (AccountAddress.ofNat (freeVatMaskedWord σ_solm I).toNat))
              (name := "urns")
              (args := [freeIlkValue I, .address I.source])
              (calldata :=
                (freeUrnsCalldataMem I solcFreePtrMem).readWithPadding
                  freeUrnsOutPtr.toNat freeUrnsInSize.toNat)
              (callPerm := true)
              (freeUrnsEncode_eq I)
              (by simpa [initState] using hdepthMax)
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (freeStore I)
                freeTransition.body .reverted := by
            exact endFreeSourceBodyUrnsCallFailure (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hliveSolm hvatCodeNatSolm hcallUrns
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hdepthLt : I.depth.val < 1024 := by
            have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
            have hne : I.depth.val ≠ 1024 := by
              intro hval
              apply hdepthMax
              apply Fin.ext
              exact hval
            omega
          obtain ⟨cA', σ', z, out, A', kCall, CCall, hcallRD, hcallEvm, houtsz⟩ :=
            RD.endFreeUrnsPostCall
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) h7760 hvatNoCode hdepthLt
          cases z
          · have hrev :=
              RD.endFreeUrnsCallFailure hcallRD houtsz
                (by simp only [List.length_cons, List.length_nil]; omega)
            obtain ⟨σ'_solm, A'_solm, hcallSolm, hStateUrns⟩ :=
              typedCallViaEVM_initState_EVMStateEquiv hcallEvm (by simp [initState])
                hAccounts
            have hcallUrns :
                typedCallViaEVM config
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (EVM.address (AccountAddress.ofNat (freeVatMaskedWord σ_solm I).toNat))
                  "urns" 0 [freeIlkValue I, .address I.source]
                  (false,
                    { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' },
                    out) true := by
              simpa [hvatMasked, hperm] using hcallSolm
            have hbody :
                ExecTransitionBody config contract
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (freeStore I)
                  freeTransition.body .reverted := by
              exact endFreeSourceBodyUrnsCallFailure (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hliveSolm hvatCodeNatSolm hcallUrns
            exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · obtain ⟨_, _, h7865⟩ :=
              RD.endFreeUrnsCallSuccessToDecode hcallRD
                (by simp only [List.length_cons, List.length_nil]; omega)
            obtain ⟨σ'_solm, A'_solm, hcallSolm, hStateUrns⟩ :=
              typedCallViaEVM_initState_EVMStateEquiv hcallEvm (by simp [initState])
                hAccounts
            have hcallUrns :
                typedCallViaEVM config
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (EVM.address (AccountAddress.ofNat (freeVatMaskedWord σ_solm I).toNat))
                  "urns" 0 [freeIlkValue I, .address I.source]
                  (true,
                    { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' },
                    out) true := by
              simpa [hvatMasked, hperm] using hcallSolm
            by_cases houtShort : out.size < 64
            · have hrev := RD.endFreeUrnsReturnDecodeShortReverts h7865 houtShort houtsz
              have hbody :
                  ExecTransitionBody config contract
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (freeStore I)
                    freeTransition.body .reverted := by
                exact endFreeSourceBodyUrnsDecodeRevert (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hwv hliveSolm hvatCodeNatSolm hcallUrns (freeUrnsDecode_none_short houtShort)
              exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have houtLong : 64 ≤ out.size := by omega
              have hdecUrns := freeUrnsDecode_ok (out := out) houtLong
              obtain ⟨_, _, h7900⟩ :=
                RD.endFreeUrnsReturnDecodeOkToArtGuard h7865 houtLong houtsz
              by_cases hart : freeUrnsArtWord out = ⟨0⟩
              · obtain ⟨_, _, h7969⟩ := RD.endFreeUrnsArtZeroToInkGuard h7900 hart
                by_cases hink : (freeUrnsInkWord out).toNat ≤ freeInt256LimitWord.toNat
                · obtain ⟨_, _, h8041⟩ := RD.endFreeUrnsInkOkToGrabPrep h7969 hink
                  have hvatMaskedUrns :
                      freeVatMaskedWord σ' I = freeVatMaskedWord σ'_solm I := by
                    have hvatWord : freeVatWord σ' I = freeVatWord σ'_solm I :=
                      accountMapEquiv_storage_findD hStateUrns.accountMap I.codeOwner ⟨1⟩
                        ⟨0⟩
                    change UInt256.land (freeVatWord σ' I) solcAddrMask =
                      UInt256.land (freeVatWord σ'_solm I) solcAddrMask
                    rw [hvatWord]
                  have hvowMaskedUrns :
                      freeVowMaskedWord σ' I = freeVowMaskedWord σ'_solm I := by
                    have hvowWord : freeVowWord σ' I = freeVowWord σ'_solm I :=
                      accountMapEquiv_storage_findD hStateUrns.accountMap I.codeOwner ⟨4⟩
                        ⟨0⟩
                    change UInt256.land (freeVowWord σ' I) solcAddrMask =
                      UInt256.land (freeVowWord σ'_solm I) solcAddrMask
                    rw [hvowWord]
                  by_cases hgrabNoCode :
                      Reasoning.Theory.uniswapExtCodeSizeWord σ' (freeVatMaskedWord σ' I) =
                        ⟨0⟩
                  · have hrev := RD.endFreeGrabNoCode h8041 houtLong houtsz hgrabNoCode
                    have hgrabNoCodeSolm :
                        Reasoning.Theory.uniswapExtCodeSizeWord σ'_solm
                          (freeVatMaskedWord σ'_solm I) = ⟨0⟩ := by
                      have hcodeEq :
                          Reasoning.Theory.uniswapExtCodeSizeWord σ'
                            (freeVatMaskedWord σ' I) =
                            Reasoning.Theory.uniswapExtCodeSizeWord σ'_solm
                              (freeVatMaskedWord σ' I) :=
                        uniswapExtCodeSizeWord_accountMapEquiv hStateUrns.accountMap
                          (freeVatMaskedWord σ' I)
                      rw [← hvatMaskedUrns, ← hcodeEq]
                      exact hgrabNoCode
                    have hbody :
                        ExecTransitionBody config contract
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          (freeStore I) freeTransition.body .reverted := by
                      exact endFreeSourceBodyGrabNoCodeReverts (cA := cA) (gh := gh)
                        (bl := bl) (σ := σ_solm) (σUrns := σ'_solm) (σ₀ := σ₀)
                        (A := A) (I := I) (g := g) (cAUrns := cA')
                        (AUrns := A'_solm) hwv hliveSolm hvatCodeNatSolm hcallUrns
                        hdecUrns hart hink hgrabNoCodeSolm
                    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                  · obtain ⟨cA'', σ'', zGrab, grabOut, A'', kGrab, CGrab, hgrabRD,
                        hgrabEvm, hgrabOutSz⟩ :=
                      RD.endFreeGrabPostCall
                        (cA0 := cA) (cA := cA') (gh := gh) (bl := bl)
                        (σBase := σ_evm) (σ := σ') (σ₀ := σ₀) (A0 := A)
                        (ACall := A') (I := I) (g := g) (sel := endSelWord I)
                        h8041 houtLong houtsz hgrabNoCode hdepthLt hink
                    let evmUrnsEvm :=
                      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σ', substate := A', createdAccounts := cA' }
                    let evmUrnsSolm :=
                      { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σ'_solm, substate := A'_solm,
                        createdAccounts := cA' }
                    have hgrabCodeSolm :
                        Reasoning.Theory.uniswapExtCodeSizeWord σ'_solm
                          (freeVatMaskedWord σ'_solm I) ≠ ⟨0⟩ := by
                      intro hzero
                      apply hgrabNoCode
                      have hcodeEq :
                          Reasoning.Theory.uniswapExtCodeSizeWord σ'
                            (freeVatMaskedWord σ' I) =
                            Reasoning.Theory.uniswapExtCodeSizeWord σ'_solm
                              (freeVatMaskedWord σ' I) :=
                        uniswapExtCodeSizeWord_accountMapEquiv hStateUrns.accountMap
                          (freeVatMaskedWord σ' I)
                      rw [← hvatMaskedUrns] at hzero
                      rw [hcodeEq]
                      exact hzero
                    obtain ⟨σ''_solm, A''_solm, hgrabSolmRaw, hσ''⟩ :=
                      freeTypedCallViaEVM_accountMapEquiv_noSubstate
                        (evm_solm := evmUrnsSolm) hgrabEvm
                        (by simpa [evmUrnsEvm, evmUrnsSolm] using hStateUrns.accountMap)
                        (by simp [evmUrnsEvm, evmUrnsSolm, initState])
                        (by simp [evmUrnsEvm, evmUrnsSolm])
                        (by simp [evmUrnsEvm, evmUrnsSolm, initState])
                        (by simp [evmUrnsEvm, evmUrnsSolm, initState])
                        (by
                          simpa [evmUrnsEvm, evmUrnsSolm] using
                            (EVMStateEquiv.executionEnv hStateUrns).symm)
                    cases zGrab
                    · have hgrabRD0 : RD endBytecode I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨8159⟩
                          (⟨0⟩ :: freeGrabEndPtr :: freeGrabSelectorWord ::
                            freeVatMaskedWord σ' I :: freeUrnsArtWord out ::
                            freeUrnsInkWord out :: freeIlkWord I :: ⟨562⟩ ::
                            [endSelWord I])
                          (freeGrabPostCallMem σ' I out grabOut) (UInt256.ofNat 11)
                          grabOut (cA'', σ'') kGrab CGrab := by
                        simpa using hgrabRD
                      have hrev := RD.endFreeGrabCallFailure hgrabRD0 hgrabOutSz
                      have hgrabSolm :
                          typedCallViaEVM config evmUrnsSolm
                            (EVM.address
                              (AccountAddress.ofNat (freeVatMaskedWord σ'_solm I).toNat))
                            "grab" 0
                            [freeIlkValue I, .address I.source, .address I.source,
                              .address
                                (AccountAddress.ofUInt256 (freeVowMaskedWord σ'_solm I)),
                              .int (-(Int.ofNat (freeUrnsInkWord out).toNat)), .int 0]
                            (false,
                              { evmUrnsSolm with
                                accountMap := σ''_solm, substate := A''_solm,
                                createdAccounts := cA'' },
                              grabOut) true := by
                        simpa [evmUrnsEvm, evmUrnsSolm, hvatMaskedUrns, hvowMaskedUrns,
                          hperm] using hgrabSolmRaw
                      have hbody :
                          ExecTransitionBody config contract
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                            (freeStore I) freeTransition.body .reverted := by
                        exact endFreeSourceBodyGrabCallFailure (cA := cA) (gh := gh)
                          (bl := bl) (σ := σ_solm) (σUrns := σ'_solm) (σ₀ := σ₀)
                          (A := A) (I := I) (g := g) (cAUrns := cA')
                          (AUrns := A'_solm) hwv hliveSolm hvatCodeNatSolm hcallUrns
                          hdecUrns hart hink hgrabCodeSolm hgrabSolm
                      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                    · have hgrabRD1 : RD endBytecode I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨8159⟩
                          (⟨1⟩ :: freeGrabEndPtr :: freeGrabSelectorWord ::
                            freeVatMaskedWord σ' I :: freeUrnsArtWord out ::
                            freeUrnsInkWord out :: freeIlkWord I :: ⟨562⟩ ::
                            [endSelWord I])
                          (freeGrabPostCallMem σ' I out grabOut) (UInt256.ofNat 11)
                          grabOut (cA'', σ'') kGrab CGrab := by
                        simpa using hgrabRD
                      have hret :=
                        RD.endFreeGrabCallSuccessReturn hgrabRD1 hperm houtLong houtsz
                      have hgrabSolm :
                          typedCallViaEVM config evmUrnsSolm
                            (EVM.address
                              (AccountAddress.ofNat (freeVatMaskedWord σ'_solm I).toNat))
                            "grab" 0
                            [freeIlkValue I, .address I.source, .address I.source,
                              .address
                                (AccountAddress.ofUInt256 (freeVowMaskedWord σ'_solm I)),
                              .int (-(Int.ofNat (freeUrnsInkWord out).toNat)), .int 0]
                            (true,
                              { evmUrnsSolm with
                                accountMap := σ''_solm, substate := A''_solm,
                                createdAccounts := cA'' },
                              grabOut) true := by
                        simpa [evmUrnsEvm, evmUrnsSolm, hvatMaskedUrns, hvowMaskedUrns,
                          hperm] using hgrabSolmRaw
                      let evmGrabEvm :=
                        { evmUrnsEvm with
                          accountMap := σ'', substate := A'',
                          createdAccounts := cA'' }
                      let evmGrabSolm :=
                        { evmUrnsSolm with
                          accountMap := σ''_solm, substate := A''_solm,
                          createdAccounts := cA'' }
                      have hbody :
                          ExecTransitionBody config contract
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                            (freeStore I) freeTransition.body
                            (.returned
                              { contract := contract,
                                locals := (freeUrnsArtLocals I out).insert "_grab" .unit }
                              evmGrabSolm none) := by
                        simpa [evmUrnsSolm, evmGrabSolm] using
                          endFreeSourceBodyGrabCallSuccess (cA := cA) (gh := gh)
                            (bl := bl) (σ := σ_solm) (σUrns := σ'_solm) (σ₀ := σ₀)
                            (A := A) (I := I) (g := g) (cAUrns := cA')
                            (AUrns := A'_solm) (evmGrab := evmGrabSolm)
                            (grabOut := grabOut) hwv hliveSolm hvatCodeNatSolm hcallUrns
                            hdecUrns hart hink hgrabCodeSolm hgrabSolm
                      have hStateFinal : EVMStateEquiv evmGrabEvm evmGrabSolm := by
                        refine ⟨?_, rfl, ?_⟩
                        · simpa [evmGrabEvm, evmGrabSolm, evmUrnsEvm, evmUrnsSolm] using
                            hStateUrns.executionEnv
                        · simpa [evmGrabEvm, evmGrabSolm] using hσ''
                      have hretEquiv :
                          returnEquiv ByteArray.empty none freeTransition.returnType := by
                        change returnEquiv ByteArray.empty none []
                        exact returnEquiv.fallthrough rfl rfl (by native_decide)
                      exact hret.reEquivExecutionGenEVMStateEquiv hcode hdispatch hdecode
                        hbody (by simp [evmGrabEvm])
                        (by simpa [evmGrabEvm] using accountMapEquiv_refl σ'')
                        hStateFinal hretEquiv
                · have hrev := RD.endFreeUrnsInkTooLargeReverts h7969 houtLong houtsz hink
                  have hbody :
                      ExecTransitionBody config contract
                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                        (freeStore I) freeTransition.body .reverted := by
                    exact endFreeSourceBodyUrnsInkTooLargeReverts (cA := cA) (gh := gh)
                      (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                      (g := g) hwv hliveSolm hvatCodeNatSolm hcallUrns hdecUrns hart hink
                  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have hrev := RD.endFreeUrnsArtNonzeroReverts h7900 houtLong houtsz hart
                have hbody :
                    ExecTransitionBody config contract
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                      (freeStore I) freeTransition.body .reverted := by
                  exact endFreeSourceBodyUrnsArtNonzeroReverts (cA := cA) (gh := gh)
                    (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                    (g := g) hwv hliveSolm hvatCodeNatSolm hcallUrns hdecUrns hart
                exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hliveSolm : freeLiveWord σ_solm I ≠ ⟨0⟩ := by
        intro hzero
        apply hlive
        have hword : freeLiveWord σ_evm I = freeLiveWord σ_solm I :=
          accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
        rw [hword, hzero]
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (freeStore I)
            freeTransition.body .reverted := by
        exact endFreeSourceBodyLiveReverts (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hliveSolm
      have hrev := RD.endFreeLiveReverts (g := Sat256.ofUInt256 g) hlive h7690
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hshort : I.calldata.size < 36 := by omega
    have hrev :=
      endFreeX_shortarg (σ := σ_evm) (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach
    exact hrev.reEquivDecodingFailed hcode hdispatch (endDecode_free_none_short hsz4 hshort)

end Benchmarks.Dss.End
