import Benchmarks.Dss.End.PackBody

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

/-! ## `cash(bytes32,uint256)` -/

abbrev cashIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev cashWadWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev cashStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "ilk" (.fixedBytes bytes32Width (EVM.Word.toBytesBE (cashIlkWord I))))
    |>.insert "wad" (.int (Int.ofNat (cashWadWord I).toNat))

abbrev cashIlkValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (cashIlkWord I))

abbrev cashIlkKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (cashIlkWord I))

abbrev cashSourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev cashFluxSelectorWord : UInt256 := ⟨1628552750⟩

abbrev cashFluxSelectorShifted : UInt256 :=
  UInt256.shiftLeft cashFluxSelectorWord ⟨224⟩

abbrev cashFluxOutPtr : UInt256 := ⟨128⟩

abbrev cashFluxInSize : UInt256 := ⟨132⟩

abbrev cashFluxOutSize : UInt256 := ⟨0⟩

abbrev cashFluxEndPtr : UInt256 := ⟨260⟩

noncomputable def cashFluxSelectorMem (mem : ByteArray) : ByteArray :=
  cashFluxSelectorShifted.toByteArray.write 0 mem cashFluxOutPtr.toNat 32

noncomputable def cashFluxIlkMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (cashIlkWord I).toByteArray.write 0 (cashFluxSelectorMem mem) 132 32

noncomputable def cashFluxThisMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (UInt256.ofNat I.codeOwner.val).toByteArray.write 0 (cashFluxIlkMem I mem) 164 32

noncomputable def cashFluxSourceMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (cashSourceWord I).toByteArray.write 0 (cashFluxThisMem I mem) 196 32

def cashFixStorageSlot (I : ExecutionEnv) : UInt256 :=
  fixSlot (cashIlkKey I)

def cashFixWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (cashFixStorageSlot I) σ I

theorem cashFixStorageSlot_eq (I : ExecutionEnv) :
    cashFixStorageSlot I = solcMappingSlot ⟨15⟩ (cashIlkWord I) := by
  unfold cashFixStorageSlot fixSlot mapSlot solcMappingSlot cashIlkKey cashIlkWord
  unfold bytes32Width
  rw [keyValueToWord_fixedBytes32]

def cashVatWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord ⟨1⟩ σ I

abbrev cashVatMaskedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (cashVatWord σ I)

def cashOutStorageSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨17⟩ (cashIlkWord I)) (cashSourceWord I)

def cashOutWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (cashOutStorageSlot I) σ I

def cashBagStorageSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨16⟩ (cashSourceWord I)

def cashBagWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (cashBagStorageSlot I) σ I

abbrev cashRayWord : UInt256 :=
  ⟨1000000000000000000000000000⟩

abbrev cashAmtMulWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.mul (cashWadWord I) (cashFixWord σ I)

abbrev cashAmtWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.div (cashAmtMulWord σ I) cashRayWord

noncomputable def cashFluxCalldataMem (σ : AccountMap) (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  (cashAmtWord σ I).toByteArray.write 0 (cashFluxSourceMem I mem) 228 32

noncomputable def cashFluxPostCallMem (σ : AccountMap) (I : ExecutionEnv)
    (base out : ByteArray) : ByteArray :=
  out.write 0 (cashFluxCalldataMem σ I base) cashFluxOutPtr.toNat
    (min cashFluxOutSize (UInt256.ofNat out.size)).toNat

abbrev cashStoreAmt (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (cashStore I).insert "amt" (.int (Int.ofNat (cashAmtWord σ I).toNat))

abbrev cashStoreAmtOutNew (σ : AccountMap) (I : ExecutionEnv) (outNew : UInt256) : Store :=
  (cashStoreAmt σ I).insert "outNew" (.int (Int.ofNat outNew.toNat))

theorem cashStoreAmt_get_wad (σ : AccountMap) (I : ExecutionEnv) :
    (cashStoreAmt σ I).get? "wad" = some (.int (Int.ofNat (cashWadWord I).toNat)) := by
  unfold cashStoreAmt cashStore
  rw [store_get_ne]
  · simp
  · native_decide

theorem cashStoreAmt_get_ilk (σ : AccountMap) (I : ExecutionEnv) :
    (cashStoreAmt σ I).get? "ilk" = some (cashIlkValue I) := by
  unfold cashStoreAmt cashStore cashIlkValue
  rw [store_get_ne]
  · rw [store_get_ne]
    · simp
    · native_decide
  · native_decide

theorem cashStoreAmt_get_amt (σ : AccountMap) (I : ExecutionEnv) :
    (cashStoreAmt σ I).get? "amt" = some (.int (Int.ofNat (cashAmtWord σ I).toNat)) := by
  unfold cashStoreAmt
  simp

theorem cashStoreAmtOutNew_get_outNew (σ : AccountMap) (I : ExecutionEnv) (outNew : UInt256) :
    (cashStoreAmtOutNew σ I outNew).get? "outNew" =
      some (.int (Int.ofNat outNew.toNat)) := by
  unfold cashStoreAmtOutNew
  simp

theorem cashFluxSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (cashFluxSelectorMem mem).size = 160 := by
  unfold cashFluxSelectorMem cashFluxOutPtr
  exact toByteArray_write32_size_of_ge mem cashFluxSelectorShifted 128 96 160 hmem
    (by native_decide) (by native_decide) (by native_decide)

theorem cashFluxIlkMem_size (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 96) :
    (cashFluxIlkMem I mem).size = 164 := by
  unfold cashFluxIlkMem
  exact toByteArray_write32_size_of_le (cashFluxSelectorMem mem) (cashIlkWord I) 132
    160 164 (cashFluxSelectorMem_size hmem)
    (by rw [cashFluxSelectorMem_size hmem]; native_decide) (by native_decide)

theorem cashFluxThisMem_size (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 96) :
    (cashFluxThisMem I mem).size = 196 := by
  unfold cashFluxThisMem
  exact toByteArray_write32_size_of_le (cashFluxIlkMem I mem)
    (UInt256.ofNat I.codeOwner.val) 164 164 196 (cashFluxIlkMem_size I hmem)
    (by rw [cashFluxIlkMem_size I hmem]) (by native_decide)

theorem cashFluxSourceMem_size (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 96) :
    (cashFluxSourceMem I mem).size = 228 := by
  unfold cashFluxSourceMem
  exact toByteArray_write32_size_of_le (cashFluxThisMem I mem) (cashSourceWord I) 196
    196 228 (cashFluxThisMem_size I hmem)
    (by rw [cashFluxThisMem_size I hmem]) (by native_decide)

theorem cashFluxCalldataMem_size (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (cashFluxCalldataMem σ I mem).size = 260 := by
  unfold cashFluxCalldataMem
  exact toByteArray_write32_size_of_le (cashFluxSourceMem I mem) (cashAmtWord σ I) 228
    228 260 (cashFluxSourceMem_size I hmem)
    (by rw [cashFluxSourceMem_size I hmem]) (by native_decide)

theorem cashFluxSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (cashFluxSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold cashFluxSelectorMem cashFluxOutPtr
  change (cashFluxSelectorShifted.toByteArray.write 0 mem 128 32).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [toByteArray_write_read_below_of_gap cashFluxSelectorShifted mem 128 64
    (by rw [hmem]) (by omega) (by rw [hmem]; native_decide), hread64]

theorem cashFluxIlkMem_read64 (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (cashFluxIlkMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold cashFluxIlkMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [cashFluxSelectorMem_size hmem]; omega) (by omega),
    cashFluxSelectorMem_read64 hmem hread64]

theorem cashFluxThisMem_read64 (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (cashFluxThisMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold cashFluxThisMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [cashFluxIlkMem_size I hmem]) (by omega),
    cashFluxIlkMem_read64 I hmem hread64]

theorem cashFluxSourceMem_read64 (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (cashFluxSourceMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold cashFluxSourceMem
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
    (by rw [cashFluxThisMem_size I hmem]) (by omega),
    cashFluxThisMem_read64 I hmem hread64]

theorem cashFluxCalldataMem_read64 (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (cashFluxCalldataMem σ I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold cashFluxCalldataMem
  rw [write32_read_below _ _ 228 64 (by rw [toByteArray_size])
    (by rw [cashFluxSourceMem_size I hmem]) (by omega),
    cashFluxSourceMem_read64 I hmem hread64]

theorem cashFluxCalldataMem_read128_4 (σ : AccountMap) (I : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (cashFluxCalldataMem σ I mem).readWithPadding 128 4 = fluxSelector := by
  have hSourceSize := cashFluxSourceMem_size I hmem
  unfold cashFluxCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (cashAmtWord σ I)
      (cashFluxSourceMem I mem) 228 128 4
      (by rw [hSourceSize]; omega)
      (by omega) (by omega) (by omega)
      (by rw [hSourceSize]; native_decide)]
  have hThisSize := cashFluxThisMem_size I hmem
  unfold cashFluxSourceMem
  rw [toByteArray_write_read_below_len_of_gap (cashSourceWord I)
      (cashFluxThisMem I mem) 196 128 4
      (by rw [hThisSize]; omega)
      (by omega) (by omega) (by omega)
      (by rw [hThisSize]; native_decide)]
  have hIlkSize := cashFluxIlkMem_size I hmem
  unfold cashFluxThisMem
  rw [toByteArray_write_read_below_len_of_gap (UInt256.ofNat I.codeOwner.val)
      (cashFluxIlkMem I mem) 164 128 4
      (by rw [hIlkSize]; omega)
      (by omega) (by omega) (by omega)
      (by rw [hIlkSize]; native_decide)]
  have hSelectorSize := cashFluxSelectorMem_size hmem
  unfold cashFluxIlkMem
  rw [toByteArray_write_read_below_len_of_gap (cashIlkWord I)
      (cashFluxSelectorMem mem) 132 128 4
      (by rw [hSelectorSize]; omega)
      (by omega) (by omega) (by omega)
      (by rw [hSelectorSize]; native_decide)]
  unfold cashFluxSelectorMem
  change (cashFluxSelectorShifted.toByteArray.write 0 mem 128 32).readWithPadding 128 4 =
    fluxSelector
  rw [toByteArray_write_read_window_of_gap cashFluxSelectorShifted mem 128 0 4
      (by omega) (by omega) (by omega)
      (by rw [hmem]; native_decide)]
  native_decide

theorem cashFluxCalldataMem_read132_32 (σ : AccountMap) (I : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (cashFluxCalldataMem σ I mem).readWithPadding 132 32 =
      (cashIlkWord I).toByteArray := by
  have hSourceSize := cashFluxSourceMem_size I hmem
  unfold cashFluxCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (cashAmtWord σ I)
      (cashFluxSourceMem I mem) 228 132 32
      (by rw [hSourceSize]; omega)
      (by omega) (by omega) (by omega)
      (by rw [hSourceSize]; native_decide)]
  have hThisSize := cashFluxThisMem_size I hmem
  unfold cashFluxSourceMem
  rw [toByteArray_write_read_below_len_of_gap (cashSourceWord I)
      (cashFluxThisMem I mem) 196 132 32
      (by rw [hThisSize]; omega)
      (by omega) (by omega) (by omega)
      (by rw [hThisSize]; native_decide)]
  have hIlkSize := cashFluxIlkMem_size I hmem
  unfold cashFluxThisMem
  rw [toByteArray_write_read_below_len_of_gap (UInt256.ofNat I.codeOwner.val)
      (cashFluxIlkMem I mem) 164 132 32
      (by rw [hIlkSize])
      (by omega) (by omega) (by omega)
      (by rw [hIlkSize]; native_decide)]
  unfold cashFluxIlkMem
  rw [toByteArray_write_read_back_of_gap (cashIlkWord I) (cashFluxSelectorMem mem) 132
      (by rw [cashFluxSelectorMem_size hmem]; native_decide)]

theorem cashFluxCalldataMem_read164_32 (σ : AccountMap) (I : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (cashFluxCalldataMem σ I mem).readWithPadding 164 32 =
      (UInt256.ofNat I.codeOwner.val).toByteArray := by
  have hSourceSize := cashFluxSourceMem_size I hmem
  unfold cashFluxCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (cashAmtWord σ I)
      (cashFluxSourceMem I mem) 228 164 32
      (by rw [hSourceSize]; omega)
      (by omega) (by omega) (by omega)
      (by rw [hSourceSize]; native_decide)]
  have hThisSize := cashFluxThisMem_size I hmem
  unfold cashFluxSourceMem
  rw [toByteArray_write_read_below_len_of_gap (cashSourceWord I)
      (cashFluxThisMem I mem) 196 164 32
      (by rw [hThisSize])
      (by omega) (by omega) (by omega)
      (by rw [hThisSize]; native_decide)]
  unfold cashFluxThisMem
  rw [toByteArray_write_read_back_of_gap (UInt256.ofNat I.codeOwner.val)
      (cashFluxIlkMem I mem) 164
      (by rw [cashFluxIlkMem_size I hmem]; native_decide)]

theorem cashFluxCalldataMem_read196_32 (σ : AccountMap) (I : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (cashFluxCalldataMem σ I mem).readWithPadding 196 32 =
      (cashSourceWord I).toByteArray := by
  have hSourceSize := cashFluxSourceMem_size I hmem
  unfold cashFluxCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (cashAmtWord σ I)
      (cashFluxSourceMem I mem) 228 196 32
      (by rw [hSourceSize])
      (by omega) (by omega) (by omega)
      (by rw [hSourceSize]; native_decide)]
  unfold cashFluxSourceMem
  rw [toByteArray_write_read_back_of_gap (cashSourceWord I) (cashFluxThisMem I mem) 196
      (by rw [cashFluxThisMem_size I hmem]; native_decide)]

theorem cashFluxCalldataMem_read228_32 (σ : AccountMap) (I : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (cashFluxCalldataMem σ I mem).readWithPadding 228 32 =
      (cashAmtWord σ I).toByteArray := by
  unfold cashFluxCalldataMem
  rw [toByteArray_write_read_back_of_gap (cashAmtWord σ I) (cashFluxSourceMem I mem) 228
      (by rw [cashFluxSourceMem_size I hmem]; native_decide)]

theorem cashFluxCalldataMem_read128_132 (σ : AccountMap) (I : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (cashFluxCalldataMem σ I mem).readWithPadding 128 132 =
      fluxSelector ++ (cashIlkWord I).toByteArray ++
        (UInt256.ofNat I.codeOwner.val).toByteArray ++
        (cashSourceWord I).toByteArray ++ (cashAmtWord σ I).toByteArray := by
  have hsize : (cashFluxCalldataMem σ I mem).size = 260 :=
    cashFluxCalldataMem_size σ I hmem
  rw [show 132 = 4 + 128 from rfl,
    byteArray_readWithPadding_split (cashFluxCalldataMem σ I mem) 128 4 128
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 128 = 32 + 96 from rfl,
    byteArray_readWithPadding_split (cashFluxCalldataMem σ I mem) 132 32 96
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split (cashFluxCalldataMem σ I mem) 164 32 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (cashFluxCalldataMem σ I mem) 196 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [cashFluxCalldataMem_read128_4 σ I hmem,
    cashFluxCalldataMem_read132_32 σ I hmem,
    cashFluxCalldataMem_read164_32 σ I hmem,
    cashFluxCalldataMem_read196_32 σ I hmem,
    cashFluxCalldataMem_read228_32 σ I hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem cashFluxEncodeWords (σ : AccountMap) (I : ExecutionEnv) :
    config.externalABI.encode? "flux"
      [cashIlkValue I, .address I.codeOwner, .address I.source,
        .int (Int.ofNat (cashAmtWord σ I).toNat)] =
      some (fluxSelector ++ (cashIlkWord I).toByteArray ++
        (UInt256.ofNat I.codeOwner.val).toByteArray ++
        (cashSourceWord I).toByteArray ++ (cashAmtWord σ I).toByteArray) := by
  have hIlk : ABI.encodeABIValue? bytes32 (cashIlkValue I) =
      some (EVM.Word.toBytesBE (cashIlkWord I)) := by
    have hlen : (EVM.Word.toBytesBE (cashIlkWord I)).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size (cashIlkWord I)
    simp [ABI.encodeABIValue?, hlen, zeroBytes, cashIlkValue, bytes32, bytes32Width]
  have hIlk' : ABI.encodeABIValue? (.elem (.bytes bytes32Width)) (cashIlkValue I) =
      some (EVM.Word.toBytesBE (cashIlkWord I)) := by
    simpa [bytes32] using hIlk
  have hthis : ABI.encodeABIValue? (.elem .address) (.address I.codeOwner) =
      some (EVM.Word.toBytesBE (UInt256.ofNat I.codeOwner.val)) := by
    exact packAddressArgEncoding I.codeOwner
  have hsource : ABI.encodeABIValue? (.elem .address) (.address I.source) =
      some (EVM.Word.toBytesBE (cashSourceWord I)) := by
    simpa [cashSourceWord] using packAddressArgEncoding I.source
  have hamt : ABI.encodeABIValue? (.elem (.int uint256Int))
      (.int ↑(cashAmtWord σ I).toNat) =
      some (EVM.Word.toBytesBE (cashAmtWord σ I)) := by
    simpa [Int.ofNat_eq_natCast] using packUint256ArgEncoding (cashAmtWord σ I)
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    ABI.encodeABIValuesFrom?, hIlk', hthis, hsource, bytes32, addr, uint256]
  rw [hamt]
  simp only [Option.bind]
  apply congrArg some
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc, word_toBytesBE_toByteArray_eq_toByteArray]

theorem cashFluxEncode_eq (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    config.externalABI.encode? "flux"
      [cashIlkValue I, .address I.codeOwner, .address I.source,
        .int (Int.ofNat (cashAmtWord σ I).toNat)] =
      some ((cashFluxCalldataMem σ I mem).readWithPadding
        cashFluxOutPtr.toNat cashFluxInSize.toNat) := by
  rw [show cashFluxOutPtr.toNat = 128 by native_decide,
    show cashFluxInSize.toNat = 132 by native_decide]
  rw [cashFluxCalldataMem_read128_132 σ I hmem]
  exact cashFluxEncodeWords σ I

theorem cashFluxPostCallMem_size (σ : AccountMap) (I : ExecutionEnv) {base : ByteArray}
    (out : ByteArray) (hbase : base.size = 96) :
    (cashFluxPostCallMem σ I base out).size = 260 := by
  have hmin : (min cashFluxOutSize (UInt256.ofNat out.size)).toNat = 0 := by
    unfold cashFluxOutSize
    rw [← u256_ofNat_toNat (UInt256.ofNat out.size)]
    exact umin_ofNat_right_toNat_of_ge (by norm_num [UInt256.size]) (Nat.zero_le _)
      (UInt256.ofNat out.size).val.isLt
  unfold cashFluxPostCallMem
  rw [hmin, byteArray_write_len_zero]
  exact cashFluxCalldataMem_size σ I hbase

theorem cashFluxPostCallMem_read64 (σ : AccountMap) (I : ExecutionEnv) {base : ByteArray}
    (out : ByteArray) (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (cashFluxPostCallMem σ I base out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hmin : (min cashFluxOutSize (UInt256.ofNat out.size)).toNat = 0 := by
    unfold cashFluxOutSize
    rw [← u256_ofNat_toNat (UInt256.ofNat out.size)]
    exact umin_ofNat_right_toNat_of_ge (by norm_num [UInt256.size]) (Nat.zero_le _)
      (UInt256.ofNat out.size).val.isLt
  unfold cashFluxPostCallMem
  rw [hmin, byteArray_write_len_zero]
  exact cashFluxCalldataMem_read64 σ I hbase hread64

noncomputable def cashOutHashMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  twoWordHashMem (cashSourceWord I) (solcMappingSlot ⟨17⟩ (cashIlkWord I))
    (twoWordHashMem (cashIlkWord I) ⟨17⟩ mem)

noncomputable def cashBagHashMem (_I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  wordAt32Mem ⟨16⟩ mem

noncomputable def cashOutRestoredMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (solcMappingSlot ⟨17⟩ (cashIlkWord I)).toByteArray.write 0
    (cashBagHashMem I (cashOutHashMem I mem)) 32 32

theorem cash_wordAt0Mem_size_of_ge32 {mem : ByteArray} (word : UInt256)
    (hmem : 32 ≤ mem.size) :
    (wordAt0Mem word mem).size = mem.size := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem cash_wordAt32Mem_size_of_ge64 {mem : ByteArray} (word : UInt256)
    (hmem : 64 ≤ mem.size) :
    (wordAt32Mem word mem).size = mem.size := by
  unfold wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem cash_twoWordHashMem_size_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  unfold twoWordHashMem
  rw [cash_wordAt32Mem_size_of_ge64 slot (by
    rw [cash_wordAt0Mem_size_of_ge32 key (by omega)]
    exact hmem)]
  exact cash_wordAt0Mem_size_of_ge32 key (by omega)

theorem cash_twoWordHashMem_read0_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 = UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
    (by rw [cash_wordAt0Mem_size_of_ge32 key (by omega)]; omega) (by omega)]
  exact wordAt0Mem_read0 key mem

theorem cash_twoWordHashMem_read32_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 = UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [cash_wordAt0Mem_size_of_ge32 key (by omega)]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

theorem cash_twoWordHashMem_read64_of_ge96 {mem : ByteArray} (key slot : UInt256)
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [cash_wordAt0Mem_size_of_ge32 key (by omega)]; omega) (by omega)
      (by rw [cash_wordAt0Mem_size_of_ge32 key (by omega)]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega) (by omega)
      (by omega)]
  exact hread64

theorem cash_twoWordHashMem_read0_64_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [cash_twoWordHashMem_size_of_ge64 key slot hmem]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [cash_twoWordHashMem_size_of_ge64 key slot hmem]; omega),
      cash_twoWordHashMem_read0_of_ge64 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [cash_twoWordHashMem_size_of_ge64 key slot hmem]; omega),
      cash_twoWordHashMem_read32_of_ge64 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem cash_twoWordHashMem_solcMappingSlot_of_ge64 (baseSlot key : UInt256)
    {mem : ByteArray} (hmem : 64 ≤ mem.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [cash_twoWordHashMem_read0_64_of_ge64 key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

theorem cashOutHashMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (cashOutHashMem I mem).size = 260 := by
  unfold cashOutHashMem
  rw [cash_twoWordHashMem_size_of_ge64, cash_twoWordHashMem_size_of_ge64]
  · exact hmem
  · rw [hmem]
    omega
  · rw [cash_twoWordHashMem_size_of_ge64 (cashIlkWord I) ⟨17⟩ (by rw [hmem]; omega),
      hmem]
    omega

theorem cashOutHashMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (cashOutHashMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold cashOutHashMem
  apply cash_twoWordHashMem_read64_of_ge96
  · rw [cash_twoWordHashMem_size_of_ge64 (cashIlkWord I) ⟨17⟩ (by rw [hmem]; omega),
      hmem]
    omega
  · exact cash_twoWordHashMem_read64_of_ge96 (cashIlkWord I) ⟨17⟩
      (by rw [hmem]; omega) hread64

theorem cashBagHashMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (cashBagHashMem I mem).size = 260 := by
  unfold cashBagHashMem
  rw [cash_wordAt32Mem_size_of_ge64 ⟨16⟩ (by rw [hmem]; omega)]
  exact hmem

theorem cashBagHashMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (cashBagHashMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold cashBagHashMem
  unfold wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; omega)]
  exact hread64

theorem cashOutHashMem_read0 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (cashOutHashMem I mem).readWithPadding 0 32 = UInt256.toByteArray (cashSourceWord I) := by
  unfold cashOutHashMem
  apply cash_twoWordHashMem_read0_of_ge64
  rw [cash_twoWordHashMem_size_of_ge64 (cashIlkWord I) ⟨17⟩ (by rw [hmem]; omega),
    hmem]
  omega

theorem cashBagHashMemOfOut_read0_64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (cashBagHashMem I (cashOutHashMem I mem)).readWithPadding 0 64 =
      UInt256.toByteArray (cashSourceWord I) ++ UInt256.toByteArray (⟨16⟩ : UInt256) := by
  have houtSize : (cashOutHashMem I mem).size = 260 := cashOutHashMem_size I hmem
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [cashBagHashMem_size I houtSize]; omega)]
  have hleft :
      (cashBagHashMem I (cashOutHashMem I mem)).extract 0 32 =
        UInt256.toByteArray (cashSourceWord I) := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [cashBagHashMem_size I houtSize]; omega)]
    unfold cashBagHashMem wordAt32Mem
    rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [houtSize]; omega) (by omega)]
    exact cashOutHashMem_read0 I hmem
  have hright :
      (cashBagHashMem I (cashOutHashMem I mem)).extract 32 64 =
        UInt256.toByteArray (⟨16⟩ : UInt256) := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [cashBagHashMem_size I houtSize]; omega)]
    unfold cashBagHashMem wordAt32Mem
    rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [houtSize]; omega)]
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (⟨16⟩ : UInt256)).size ≤ 32
      rw [toByteArray_size])
  rw [show (cashBagHashMem I (cashOutHashMem I mem)).extract 0 64 =
      (cashBagHashMem I (cashOutHashMem I mem)).extract 0 32 ++
        (cashBagHashMem I (cashOutHashMem I mem)).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem cashOutRestoredMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (cashOutRestoredMem I mem).size = 260 := by
  unfold cashOutRestoredMem
  exact toByteArray_write32_size_of_le (cashBagHashMem I (cashOutHashMem I mem))
    (solcMappingSlot ⟨17⟩ (cashIlkWord I)) 32 260 260
    (cashBagHashMem_size I (cashOutHashMem_size I hmem))
    (by rw [cashBagHashMem_size I (cashOutHashMem_size I hmem)]; native_decide)
    (by native_decide)

theorem cashOutRestoredMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (cashOutRestoredMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold cashOutRestoredMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [cashBagHashMem_size I (cashOutHashMem_size I hmem)]; omega) (by omega)
      (by rw [cashBagHashMem_size I (cashOutHashMem_size I hmem)]; omega)]
  exact cashBagHashMem_read64 I (cashOutHashMem_size I hmem)
    (cashOutHashMem_read64 I hmem hread64)

noncomputable def cashLogMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (cashWadWord I).toByteArray.write 0 mem 128 32

theorem cashLogMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (cashLogMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold cashLogMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [hmem]; omega) (by omega)]
  exact hread64

theorem cash_solcErrorStringMem0_size_of_size260 {mem : ByteArray}
    (hmem : mem.size = 260) :
    (solcErrorStringMem0 mem).size = 260 := by
  unfold solcErrorStringMem0
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  simp [ByteArray.size_append, ByteArray.size_extract, hmem]

theorem cash_solcErrorStringMem1_size_of_size260 {mem : ByteArray}
    (hmem : mem.size = 260) :
    (solcErrorStringMem1 mem).size = 260 := by
  unfold solcErrorStringMem1
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [cash_solcErrorStringMem0_size_of_size260 hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract,
    cash_solcErrorStringMem0_size_of_size260 hmem]

theorem cash_solcErrorStringMem2_size_of_size260 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (solcErrorStringMem2 len mem).size = 260 := by
  unfold solcErrorStringMem2
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [cash_solcErrorStringMem1_size_of_size260 hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract,
    cash_solcErrorStringMem1_size_of_size260 hmem]

theorem cash_solcErrorStringMem3_size_of_size260 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (solcErrorStringMem3 len word mem).size = 260 := by
  unfold solcErrorStringMem3
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [cash_solcErrorStringMem2_size_of_size260 len hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract,
    cash_solcErrorStringMem2_size_of_size260 len hmem]

theorem cash_solcErrorStringMem3_read64_of_size260 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [cash_solcErrorStringMem2_size_of_size260 len hmem]; omega) (by omega)
      (by rw [cash_solcErrorStringMem2_size_of_size260 len hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [cash_solcErrorStringMem1_size_of_size260 hmem]; omega) (by omega)
      (by rw [cash_solcErrorStringMem1_size_of_size260 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [cash_solcErrorStringMem0_size_of_size260 hmem]; omega) (by omega)
      (by rw [cash_solcErrorStringMem0_size_of_size260 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem cash_solcErrorStringMem3_mload64_of_size260 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue (by rw [cash_solcErrorStringMem3_size_of_size260 len word hmem]; decide)
    (by decide) (cash_solcErrorStringMem3_read64_of_size260 len word hmem hread64)

set_option maxHeartbeats 1000000 in
theorem RD.cashErrorStringRevertTailPush32Aw9 {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc len word : UInt256}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 9) rdata acc k C)
    (hwf : solcErrorStringRevertTailPush32Wf code pc len word)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hd68, hdDup3, hdAdd,
      hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3, hdSub, hd100,
      hdAdd2, hdSwap4, hdRev⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) hd3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 9)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 9)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 0 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 9) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdWord := rdPrefix.pushConst word
    (width := 32) (op := .PUSH32) (by decide) hd27
    (by simp only [List.length_cons]; omega)
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 0 (solcErrorStringMem3 len word mem)
      (UInt256.ofNat 9) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) hdMload
      mem_cost
      (cash_solcErrorStringMem3_mload64_of_size260 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

theorem evalExpr_cashVatStorage (evm : EVM.State) {locals : Store}
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

theorem evalExpr_cashVatCodeGuard_true {evm : EVM.State} {locals : Store}
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

theorem evalExpr_cashVatCodeGuard_false {evm : EVM.State} {locals : Store}
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

theorem evalExpr_cashFixStorage {evm : EVM.State} {locals : Store}
    (hbaseAbsent : "fix" ∉ locals)
    (hget : locals["ilk"]? = some (cashIlkValue evm.executionEnv)) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (fixRef (.var "ilk"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (cashFixStorageSlot evm.executionEnv)).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := fixRef (.var "ilk"))
    (er := ({ base := "fix", steps := [.mindex (cashIlkKey evm.executionEnv)] } :
      EvaledStorageRef))
    (t := .int uint256Int)
    (loc := wordLoc (cashFixStorageSlot evm.executionEnv))
    (value := .int (Int.ofNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (cashFixStorageSlot evm.executionEnv)).toNat))
    (hbase := by simpa [fixRef] using hbaseAbsent)
    (her := by
      have hlen :
          (EVM.Word.toBytesBE (cashIlkWord evm.executionEnv)).length = bytes32Width.val + 1 := by
        simpa [bytes32Width] using word_toBytesBE_toByteArray_size (cashIlkWord evm.executionEnv)
      simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, fixRef, cashIlkValue,
        cashIlkKey, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, valueToKey?,
        hget, hlen])
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, cashIlkKey, uint256St])
    (hloc := by rfl)
    (hload := by
      simpa [wordLoc, uint256Loc, uint256Int] using
        storageLocLoad_uint256 evm (cashFixStorageSlot evm.executionEnv))]

theorem evalExpr_cashOutStorage {evm : EVM.State} {locals : Store}
    (hbaseAbsent : "out" ∉ locals)
    (hget : locals["ilk"]? = some (cashIlkValue evm.executionEnv)) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (outRef (.var "ilk") sender)) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (cashOutStorageSlot evm.executionEnv)).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := outRef (.var "ilk") sender)
    (er := ({ base := "out", steps := [.mindex (cashIlkKey evm.executionEnv),
      .mindex (.address evm.executionEnv.source)] } : EvaledStorageRef))
    (t := .int uint256Int)
    (loc := wordLoc (cashOutStorageSlot evm.executionEnv))
    (value := .int (Int.ofNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (cashOutStorageSlot evm.executionEnv)).toNat))
    (hbase := by simpa [outRef] using hbaseAbsent)
    (her := by
      have hlen :
          (EVM.Word.toBytesBE (cashIlkWord evm.executionEnv)).length = bytes32Width.val + 1 := by
        simpa [bytes32Width] using word_toBytesBE_toByteArray_size (cashIlkWord evm.executionEnv)
      simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, outRef, sender,
        cashIlkValue, cashIlkKey, envValue, valueToKey?, EvalResult.bind, EvalResult.ofOption,
        bind, pure, evalExpr?, hget, hlen])
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, cashIlkKey, uint256St])
    (hloc := by
      funext x
      change storageLayoutRaw
          { base := "out", steps := [.mindex (cashIlkKey evm.executionEnv),
            .mindex (.address evm.executionEnv.source)] } x =
        some (wordLoc (cashOutStorageSlot evm.executionEnv))
      simp [storageLayoutRaw, cashOutStorageSlot]
      unfold outSlot outIlkSlot mapSlot solcMappingSlot cashIlkKey cashIlkWord
      unfold cashSourceWord bytes32Width
      rw [keyValueToWord_fixedBytes32, keyValueToWord_address])
    (hload := by
      simpa [wordLoc, uint256Loc, uint256Int] using
        storageLocLoad_uint256 evm (cashOutStorageSlot evm.executionEnv))]

theorem evalExpr_cashBagStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "bag" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage (bagRef sender)) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (cashBagStorageSlot evm.executionEnv)).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := bagRef sender)
    (er := ({ base := "bag", steps := [.mindex (.address evm.executionEnv.source)] } :
      EvaledStorageRef))
    (t := .int uint256Int)
    (loc := wordLoc (cashBagStorageSlot evm.executionEnv))
    (value := .int (Int.ofNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (cashBagStorageSlot evm.executionEnv)).toNat))
    (hbase := hbase)
    (her := by
      simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bagRef, sender,
        envValue, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?])
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext x
      change storageLayoutRaw
          { base := "bag", steps := [.mindex (.address evm.executionEnv.source)] } x =
        some (wordLoc (cashBagStorageSlot evm.executionEnv))
      simp [storageLayoutRaw, bagSlot, mapSlot, cashBagStorageSlot, solcMappingSlot,
        cashSourceWord, keyValueToWord_address])
    (hload := by
      simpa [wordLoc, uint256Loc, uint256Int] using
        storageLocLoad_uint256 evm (cashBagStorageSlot evm.executionEnv))]

theorem assign_cashOutStorage (evm : EVM.State) {locals : Store}
    (outNew : UInt256)
    (hbaseAbsent : "out" ∉ locals)
    (hget : locals["ilk"]? = some (cashIlkValue evm.executionEnv)) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (outRef (.var "ilk") sender) (.int (Int.ofNat outNew.toNat)) =
        .ok ({ contract := contract, locals := locals },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (cashOutStorageSlot evm.executionEnv) outNew) := by
  exact assignStorageRef_storage_scalar
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (cashOutStorageSlot evm.executionEnv) outNew)
    (slot := outRef (.var "ilk") sender)
    (er := ({ base := "out", steps := [.mindex (cashIlkKey evm.executionEnv),
      .mindex (.address evm.executionEnv.source)] } : EvaledStorageRef))
    (ty := StorageType.elem (.int uint256Int))
    (loc := wordLoc (cashOutStorageSlot evm.executionEnv))
    (n := Int.ofNat outNew.toNat)
    (by simpa [outRef] using hbaseAbsent)
    (by
      have hlen :
          (EVM.Word.toBytesBE (cashIlkWord evm.executionEnv)).length = bytes32Width.val + 1 := by
        simpa [bytes32Width] using word_toBytesBE_toByteArray_size (cashIlkWord evm.executionEnv)
      simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, outRef, sender,
        cashIlkValue, cashIlkKey, envValue, valueToKey?, EvalResult.bind, EvalResult.ofOption,
        bind, pure, evalExpr?, hget, hlen])
    (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, cashIlkKey, uint256St])
    (by
      funext x
      change storageLayoutRaw
          { base := "out", steps := [.mindex (cashIlkKey evm.executionEnv),
            .mindex (.address evm.executionEnv.source)] } x =
        some (wordLoc (cashOutStorageSlot evm.executionEnv))
      simp [storageLayoutRaw, cashOutStorageSlot]
      unfold outSlot outIlkSlot mapSlot solcMappingSlot cashIlkKey cashIlkWord
      unfold cashSourceWord bytes32Width
      rw [keyValueToWord_fixedBytes32, keyValueToWord_address])
    (storageLocStore_uint256 evm (cashOutStorageSlot evm.executionEnv) outNew)

theorem cashMulLocalsZ_get_y (x y z : UInt256) :
    (packAddLocalsZ x y z).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  unfold packAddLocalsZ
  rw [store_get_ne]
  · exact packAddLocals_get_y x y
  · native_decide

theorem cash_mul_div_right_cancel {x y : UInt256}
    (hfit : x.toNat * y.toNat < UInt256.size) (hy : y ≠ ⟨0⟩) :
    UInt256.div (UInt256.mul x y) y = x := by
  apply u256_inj
  rw [udiv_toNat, u256_mul_toNat, Nat.mod_eq_of_lt hfit]
  have hyNat : y.toNat ≠ 0 := by
    intro hzero
    exact hy (uint256_toNat_eq_zero hzero)
  rw [Nat.mul_comm x.toNat y.toNat]
  exact Nat.mul_div_right _ (Nat.pos_of_ne_zero hyNat)

theorem evalExpr_cash_mul_ok {evm : EVM.State} {x y prod : UInt256}
    (hprod : prod = UInt256.mul x y)
    (hfit : x.toNat * y.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := packAddLocals x y } evm
      (u256 (.binary .mul (.var "x") (.var "y"))) =
        .ok (.int (Int.ofNat prod.toNat)) := by
  have hx :
      evalExpr? config { contract := contract, locals := packAddLocals x y } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa using evalExpr_packVarUInt256 (evm := evm) (locals := packAddLocals x y)
      (name := "x") (value := x) (packAddLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := packAddLocals x y } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa using evalExpr_packVarUInt256 (evm := evm) (locals := packAddLocals x y)
      (name := "y") (value := y) (packAddLocals_get_y x y)
  have hlt : ¬ Int.ofNat (x.toNat * y.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hword : prod.toNat = x.toNat * y.toNat := by
    rw [hprod, u256_mul_toNat, Nat.mod_eq_of_lt hfit]
  simp [u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem cashMulFunctionBodyReturnsNonzero (evm : EVM.State) {x y prod : UInt256}
    (hprod : prod = UInt256.mul x y)
    (hfit : x.toNat * y.toNat < UInt256.size)
    (hy : y ≠ ⟨0⟩) :
    ExecFuncBody config { contract := contract, locals := packAddLocals x y } evm
      mulFunction.body
      (.returned { contract := contract, locals := packAddLocalsZ x y prod } evm
        (some [.int (Int.ofNat prod.toNat)])) := by
  let locals := packAddLocals x y
  let localsZ := packAddLocalsZ x y prod
  have hMul :
      evalExpr? config { contract := contract, locals := locals } evm
        (u256 (.binary .mul (.var "x") (.var "y"))) =
          .ok (.int (Int.ofNat prod.toNat)) := by
    simpa [locals] using evalExpr_cash_mul_ok (evm := evm) hprod hfit
  have hxZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [localsZ] using evalExpr_packVarUInt256 (evm := evm) (locals := localsZ)
      (name := "x") (value := x) (packAddLocalsZ_get_x x y prod)
  have hyZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [localsZ] using evalExpr_packVarUInt256 (evm := evm) (locals := localsZ)
      (name := "y") (value := y) (cashMulLocalsZ_get_y x y prod)
  have hzZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat prod.toNat)) := by
    simpa [localsZ] using evalExpr_packVarUInt256 (evm := evm) (locals := localsZ)
      (name := "z") (value := prod) (packAddLocalsZ_get_z x y prod)
  have hZeroLit :
      evalExpr? config { contract := contract, locals := localsZ } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hReq :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .or
          (.binary .eq (.var "y") (.intLit 0))
          (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x"))) =
        .ok (.bool true) := by
    have hyEqZero :
        evalExpr? config { contract := contract, locals := localsZ } evm
          (.binary .eq (.var "y") (.intLit 0)) = .ok (.bool false) := by
      apply evalExpr_packEqInt_false hyZ hZeroLit
      intro hbad
      exact hy (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
    have hdivWord : UInt256.div prod y = x := by
      rw [hprod]
      exact cash_mul_div_right_cancel hfit hy
    have hDiv :
        evalExpr? config { contract := contract, locals := localsZ } evm
          (.binary .div (.var "z") (.var "y")) =
            .ok (.int (Int.ofNat x.toNat)) := by
      have h := evalExpr_packDivUInt256_ok (evm := evm) (locals := localsZ)
        (x := .var "z") (y := .var "y") (a := prod) (b := y)
        (q := UInt256.div prod y) hzZ hyZ hy rfl
      simpa [hdivWord] using h
    have hRight :
        evalExpr? config { contract := contract, locals := localsZ } evm
          (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x")) =
            .ok (.bool true) := by
      exact evalExpr_packEqInt_true hDiv hxZ rfl
    exact evalExpr_packOr_false_right hyEqZero hRight
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm mulFunction.body
        (.returned { contract := contract, locals := localsZ } evm
          (some [.int (Int.ofNat prod.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hMul) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzZ))
  simpa [mulFunction, locals, localsZ] using ExecFuncBody.execBlockRet hblock

theorem evalExpr_cash_mul_overflow {evm : EVM.State} {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    evalExpr? config { contract := contract, locals := packAddLocals x y } evm
      (u256 (.binary .mul (.var "x") (.var "y"))) = .revert := by
  have hx :
      evalExpr? config { contract := contract, locals := packAddLocals x y } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa using evalExpr_packVarUInt256 (evm := evm) (locals := packAddLocals x y)
      (name := "x") (value := x) (packAddLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := packAddLocals x y } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa using evalExpr_packVarUInt256 (evm := evm) (locals := packAddLocals x y)
      (name := "y") (value := y) (packAddLocals_get_y x y)
  have hge :
      Int.ofNat x.toNat * Int.ofNat y.toNat ≥ 2 ^ (256 : Nat) := by
    have hgeNat : 2 ^ (256 : Nat) ≤ x.toNat * y.toNat := by
      simpa [UInt256.size] using hover
    have hgeInt :
        (2 ^ (256 : Nat) : Int) ≤ (x.toNat * y.toNat : Int) := by
      exact_mod_cast hgeNat
    simpa [Nat.cast_mul, Nat.cast_pow] using hgeInt
  have hcond :
      (decide (Int.ofNat x.toNat * Int.ofNat y.toNat < 0) ||
        decide (Int.ofNat x.toNat * Int.ofNat y.toNat ≥ 2 ^ (256 : Nat))) = true := by
    rw [Bool.or_eq_true]
    exact Or.inr (decide_eq_true hge)
  unfold u256
  simp only [evalExpr?, hx, hy, EvalResult.bind, bind, pure,
    evalBinaryOp?, uint256Int]
  rw [hcond]
  rfl

theorem cashMulFunctionBodyReverts (evm : EVM.State) {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    ExecFuncBody config { contract := contract, locals := packAddLocals x y } evm
      mulFunction.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consRevert <|
      ExecStmt.letDeclRevert (evalExpr_cash_mul_overflow (evm := evm) hover)

abbrev cashRmulLocalsM (x y m : UInt256) : Store :=
  (packAddLocals x y).insert "m" (.int (Int.ofNat m.toNat))

theorem cashRmulLocalsM_get_x (x y m : UInt256) :
    (cashRmulLocalsM x y m).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  unfold cashRmulLocalsM
  rw [store_get_ne]
  · exact packAddLocals_get_x x y
  · native_decide

theorem cashRmulLocalsM_get_m (x y m : UInt256) :
    (cashRmulLocalsM x y m).get? "m" = some (.int (Int.ofNat m.toNat)) := by
  unfold cashRmulLocalsM
  simp

theorem cashRmulFunctionBodyReturnsNonzero (evm : EVM.State) {x y prod amt : UInt256}
    (hprod : prod = UInt256.mul x y)
    (hfit : x.toNat * y.toNat < UInt256.size)
    (hy : y ≠ ⟨0⟩)
    (hamt : amt = UInt256.div prod cashRayWord) :
    ExecFuncBody config { contract := contract, locals := packAddLocals x y } evm
      rmulFunction.body
      (.returned { contract := contract, locals := cashRmulLocalsM x y prod } evm
        (some [.int (Int.ofNat amt.toNat)])) := by
  let locals := packAddLocals x y
  let localsM := cashRmulLocalsM x y prod
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_packVarUInt256 (evm := evm) (locals := locals)
      (name := "x") (value := x) (packAddLocals_get_x x y)
  have hyExpr :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using evalExpr_packVarUInt256 (evm := evm) (locals := locals)
      (name := "y") (value := y) (packAddLocals_get_y x y)
  have hargsMul :
      evalExprs? config { contract := contract, locals := locals } evm [.var "x", .var "y"] =
        .ok [Value.int (Int.ofNat x.toNat), Value.int (Int.ofNat y.toNat)] := by
    simp [evalExprs?, hx, hyExpr, EvalResult.bind, bind, pure]
  have hlookupMul : lookupCallable? contract "mul" = some mulFunction.toCallable := by
    simp [lookupCallable?, lookupFunction?, contract, functions, addFunction, subFunction,
      mulFunction]
  have hbindMul :
      bindParams? mulFunction.params [Value.int (Int.ofNat x.toNat), Value.int (Int.ofNat y.toNat)] =
        some (packAddLocals x y) := by
    simp [mulFunction, packAddLocals, bindParams?]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "mul" [.var "x", .var "y"] "m")
        (.ok { contract := contract, locals := localsM } evm) := by
    have hbody := cashMulFunctionBodyReturnsNonzero evm hprod hfit hy
    simpa [locals, localsM, cashRmulLocalsM, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals })
        (evm := evm) (calleeEvm := evm) (name := "mul") (retVar := "m")
        (args := [.var "x", .var "y"])
        (argVals := [Value.int (Int.ofNat x.toNat), Value.int (Int.ofNat y.toNat)])
        (callee := mulFunction) (locals := packAddLocals x y)
        (calleeSolm := { contract := contract, locals := packAddLocalsZ x y prod })
        (value := some [.int (Int.ofNat prod.toNat)]) hargsMul hlookupMul hbindMul hbody)
  have hm :
      evalExpr? config { contract := contract, locals := localsM } evm (.var "m") =
        .ok (.int (Int.ofNat prod.toNat)) := by
    simpa [localsM] using evalExpr_packVarUInt256 (evm := evm) (locals := localsM)
      (name := "m") (value := prod) (cashRmulLocalsM_get_m x y prod)
  have hray :
      evalExpr? config { contract := contract, locals := localsM } evm (.intLit RAY) =
        .ok (.int (Int.ofNat cashRayWord.toNat)) := by
    have hrayNat : cashRayWord.toNat = 1000000000000000000000000000 := by
      native_decide
    simp [evalExpr?, pure, RAY, cashRayWord, hrayNat]
  have hDiv :
      evalExpr? config { contract := contract, locals := localsM } evm
        (.binary .div (.var "m") (.intLit RAY)) =
          .ok (.int (Int.ofNat amt.toNat)) := by
    have h := evalExpr_packDivUInt256_ok (evm := evm) (locals := localsM)
      (x := .var "m") (y := .intLit RAY) (a := prod) (b := cashRayWord)
      (q := UInt256.div prod cashRayWord) hm hray
      (by native_decide : cashRayWord ≠ ⟨0⟩) rfl
    simpa [hamt] using h
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm rmulFunction.body
        (.returned { contract := contract, locals := localsM } evm
          (some [.int (Int.ofNat amt.toNat)])) := by
    refine ExecBlock.consNormal hmulStmt ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hDiv))
  simpa [rmulFunction, locals, localsM] using ExecFuncBody.execBlockRet hblock

theorem cashRmulFunctionBodyReverts (evm : EVM.State) {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    ExecFuncBody config { contract := contract, locals := packAddLocals x y } evm
      rmulFunction.body .reverted := by
  let locals := packAddLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_packVarUInt256 (evm := evm) (locals := locals)
      (name := "x") (value := x) (packAddLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using evalExpr_packVarUInt256 (evm := evm) (locals := locals)
      (name := "y") (value := y) (packAddLocals_get_y x y)
  have hargsMul :
      evalExprs? config { contract := contract, locals := locals } evm [.var "x", .var "y"] =
        .ok [Value.int (Int.ofNat x.toNat), Value.int (Int.ofNat y.toNat)] := by
    simp [evalExprs?, hx, hy, EvalResult.bind, bind, pure]
  have hlookupMul : lookupCallable? contract "mul" = some mulFunction.toCallable := by
    simp [lookupCallable?, lookupFunction?, contract, functions, addFunction, subFunction,
      mulFunction]
  have hbindMul :
      bindParams? mulFunction.params [Value.int (Int.ofNat x.toNat), Value.int (Int.ofNat y.toNat)] =
        some (packAddLocals x y) := by
    simp [mulFunction, packAddLocals, bindParams?]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "mul" [.var "x", .var "y"] "m") .reverted := by
    exact internalCallFunctionRevert hargsMul hlookupMul hbindMul
      (cashMulFunctionBodyReverts evm hover)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [rmulFunction, locals] using ExecBlock.consRevert hmulStmt

theorem endCashSourceBodyFixZeroReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hfix : cashFixWord σ I = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (cashStore I) cashTransition.body .reverted := by
  intro evm0
  have hfixStorage :
      evalExpr? config { contract := contract, locals := cashStore I } evm0
        (.storage (fixRef (.var "ilk"))) =
        .ok (.int (Int.ofNat (cashFixWord σ I).toNat)) := by
    simpa [cashFixWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_cashFixStorage (evm := evm0) (locals := cashStore I)
        (by simp [cashStore])
        (by
          unfold cashStore cashIlkValue
          rw [Std.HashMap.getElem?_insert]
          rw [if_neg (by native_decide : ¬(("wad" == "ilk") = true))]
          rw [Std.HashMap.getElem?_insert]
          have henv : evm0.executionEnv = I := by simp [evm0, initState]
          rw [henv]
          simp)
  have hzero :
      evalExpr? config { contract := contract, locals := cashStore I } evm0 (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hguard :
      evalExpr? config { contract := contract, locals := cashStore I } evm0
        (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) := by
    simp only [evalExpr?, hfixStorage, hzero, EvalResult.bind, bind, evalBinaryOp?]
    rw [hfix]
    native_decide
  have hblock :
      ExecBlock config { contract := contract, locals := cashStore I } evm0 cashTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  simpa [ExecTransitionBody, evm0, cashTransition, nonpayable, checkedExternalCallStmts] using
    ExecFuncBody.execBlockRevert hblock

set_option maxHeartbeats 1000000 in
theorem endCashRmulStmtOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hmul : (cashWadWord I).toNat * (cashFixWord σ I).toNat < UInt256.size)
    (hfix : cashFixWord σ I ≠ ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecStmt config { contract := contract, locals := cashStore I } evm0
      (.internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt")
      (.ok { contract := contract, locals := cashStoreAmt σ I } evm0) := by
  intro evm0
  have hwad :
      evalExpr? config { contract := contract, locals := cashStore I } evm0 (.var "wad") =
        .ok (.int (Int.ofNat (cashWadWord I).toNat)) := by
    exact evalExpr_packVarUInt256 (evm := evm0) (locals := cashStore I)
      (name := "wad") (value := cashWadWord I) (by simp [cashStore])
  have hfixStorage :
      evalExpr? config { contract := contract, locals := cashStore I } evm0
        (.storage (fixRef (.var "ilk"))) =
        .ok (.int (Int.ofNat (cashFixWord σ I).toNat)) := by
    simpa [cashFixWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_cashFixStorage (evm := evm0) (locals := cashStore I)
        (by simp [cashStore])
        (by
          unfold cashStore cashIlkValue
          rw [Std.HashMap.getElem?_insert]
          rw [if_neg (by native_decide : ¬(("wad" == "ilk") = true))]
          rw [Std.HashMap.getElem?_insert]
          have henv : evm0.executionEnv = I := by simp [evm0, initState]
          rw [henv]
          simp)
  have hargs :
      evalExprs? config { contract := contract, locals := cashStore I } evm0
        [.var "wad", .storage (fixRef (.var "ilk"))] =
        .ok [Value.int (Int.ofNat (cashWadWord I).toNat),
          Value.int (Int.ofNat (cashFixWord σ I).toNat)] := by
    simp only [evalExprs?, hwad, hfixStorage, EvalResult.bind, bind, pure]
  have hlookup : lookupCallable? contract "rmul" = some rmulFunction.toCallable := by
    simp [lookupCallable?, lookupFunction?, contract, functions, addFunction, subFunction,
      mulFunction, minFunction, rmulFunction]
  have hbind :
      bindParams? rmulFunction.params
        [Value.int (Int.ofNat (cashWadWord I).toNat),
          Value.int (Int.ofNat (cashFixWord σ I).toNat)] =
        some (packAddLocals (cashWadWord I) (cashFixWord σ I)) := by
    simp [rmulFunction, packAddLocals, bindParams?]
  have hbody := cashRmulFunctionBodyReturnsNonzero evm0
    (x := cashWadWord I) (y := cashFixWord σ I)
    (prod := cashAmtMulWord σ I) (amt := cashAmtWord σ I)
    (by rfl) hmul hfix (by rfl)
  simpa [cashStoreAmt, cashAmtWord, cashAmtMulWord, cashRmulLocalsM,
    resumeAfterInternalCall] using
    (internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := cashStore I })
      (evm := evm0) (calleeEvm := evm0) (name := "rmul") (retVar := "amt")
      (args := [.var "wad", .storage (fixRef (.var "ilk"))])
      (argVals := [Value.int (Int.ofNat (cashWadWord I).toNat),
        Value.int (Int.ofNat (cashFixWord σ I).toNat)])
      (callee := rmulFunction) (locals := packAddLocals (cashWadWord I) (cashFixWord σ I))
      (calleeSolm :=
        { contract := contract,
          locals := cashRmulLocalsM (cashWadWord I) (cashFixWord σ I) (cashAmtMulWord σ I) })
      (value := some [.int (Int.ofNat (cashAmtWord σ I).toNat)]) hargs hlookup hbind hbody)

theorem evalExprs_cashFluxArgs {cA gh bl σ σ₀ A I} {g : UInt256} :
    evalExprs? config { contract := contract, locals := cashStoreAmt σ I }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      [.var "ilk", thisAddr, sender, .var "amt"] =
      .ok [cashIlkValue I, .address I.codeOwner, .address I.source,
        .int (Int.ofNat (cashAmtWord σ I).toNat)] := by
  simp only [evalExprs?, evalExpr?, thisAddr, sender, envValue, initState,
    EvalResult.bind, bind, pure, EvalResult.ofOption]
  rw [cashStoreAmt_get_ilk, cashStoreAmt_get_amt]

set_option maxHeartbeats 2000000 in
theorem endCashSourceBodyCallSuccess {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmFlux : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hfix : cashFixWord σ I ≠ ⟨0⟩)
    (hmul : (cashWadWord I).toNat * (cashFixWord σ I).toNat < UInt256.size)
    (hvatCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat (cashVatMaskedWord σ I).toNat)).option 0
          (fun acc => acc.code.size))).toNat ≠ 0)
    (hcallFlux :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (cashVatMaskedWord σ I).toNat)) "flux" 0
        [cashIlkValue I, .address I.codeOwner, .address I.source,
          .int (Int.ofNat (cashAmtWord σ I).toNat)]
        (true, evmFlux, out) true)
    (hfit :
      (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
        (cashOutStorageSlot evmFlux.executionEnv)).toNat + (cashWadWord I).toNat <
          UInt256.size) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let outOld := Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
      (cashOutStorageSlot evmFlux.executionEnv)
    let outNew := outOld + cashWadWord I
    let localsFlux := (cashStoreAmt σ I).insert "_flux" .unit
    let finalFrame : Frame :=
      { contract := contract,
        locals := localsFlux.insert "outNew" (.int (Int.ofNat outNew.toNat)) }
    let evmStored :=
      Solm.EVM.storageStore evmFlux evmFlux.executionEnv.codeOwner
        (cashOutStorageSlot evmFlux.executionEnv) outNew
    (hguard :
      evalExpr? config finalFrame evmStored
        (.binary .le (.storage (outRef (.var "ilk") sender)) (.storage (bagRef sender))) =
          .ok (.bool true)) →
    ExecTransitionBody config contract evm0 (cashStore I) cashTransition.body
      (.returned finalFrame evmStored none) := by
  intro evm0 outOld outNew localsFlux finalFrame evmStored hguard
  have hfixStorage :
      evalExpr? config { contract := contract, locals := cashStore I } evm0
        (.storage (fixRef (.var "ilk"))) =
        .ok (.int (Int.ofNat (cashFixWord σ I).toNat)) := by
    simpa [cashFixWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_cashFixStorage (evm := evm0) (locals := cashStore I)
        (by simp [cashStore])
        (by
          unfold cashStore cashIlkValue
          rw [Std.HashMap.getElem?_insert]
          rw [if_neg (by native_decide : ¬(("wad" == "ilk") = true))]
          rw [Std.HashMap.getElem?_insert]
          have henv : evm0.executionEnv = I := by simp [evm0, initState]
          rw [henv]
          simp)
  have hzero :
      evalExpr? config { contract := contract, locals := cashStore I } evm0 (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hguardFix :
      evalExpr? config { contract := contract, locals := cashStore I } evm0
        (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) := by
    have hne : (Value.int (Int.ofNat (cashFixWord σ I).toNat) == Value.int 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro hbad
      rw [Value.int.injEq] at hbad
      exact hfix (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
    simp only [evalExpr?, hfixStorage, hzero, EvalResult.bind, bind, evalBinaryOp?, hne,
      Bool.not_false]
  have hrmulStmt :
      ExecStmt config { contract := contract, locals := cashStore I } evm0
        (.internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt")
        (.ok { contract := contract, locals := cashStoreAmt σ I } evm0) := by
    simpa [evm0] using
      endCashRmulStmtOk (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hmul hfix
  have hvat :
      evalExpr? config { contract := contract, locals := cashStoreAmt σ I } evm0
        (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (cashVatMaskedWord σ I).toNat)) := by
    simpa [cashVatMaskedWord, cashVatWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, u256_land_comm] using
      evalExpr_cashVatStorage (evm := evm0) (locals := cashStoreAmt σ I)
        (by simp [cashStoreAmt, cashStore])
  have hvatGuard :
      evalExpr? config { contract := contract, locals := cashStoreAmt σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_cashVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargsFlux := evalExprs_cashFluxArgs (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hdecodeFlux : config.externalABI.decode? "flux" out = some ([] : List Value) := by
    simp [config, externalABI, decodeVoid?]
  have hcallStmt :
      ExecStmt config { contract := contract, locals := cashStoreAmt σ I } evm0
        (.externalCall (.storage vatRef) "flux" (.intLit 0)
          [.var "ilk", thisAddr, sender, .var "amt"] "_flux" (perm := true))
        (.ok { contract := contract, locals := localsFlux } evmFlux) := by
    simpa [localsFlux] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsFlux hcallFlux
        hdecodeFlux
  have henvFlux : evmFlux.executionEnv = I := by
    simpa [evm0, initState] using typedCallViaEVM_executionEnv_eq hcallFlux
  have hout :
      evalExpr? config { contract := contract, locals := localsFlux } evmFlux
        (.storage (outRef (.var "ilk") sender)) =
        .ok (.int (Int.ofNat outOld.toNat)) := by
    simpa [outOld] using
      evalExpr_cashOutStorage (evm := evmFlux) (locals := localsFlux)
        (by simp [localsFlux, cashStoreAmt, cashStore])
        (by
          rw [henvFlux]
          unfold localsFlux
          rw [Std.HashMap.getElem?_insert]
          rw [if_neg (by native_decide : ¬(("_flux" == "ilk") = true))]
          exact cashStoreAmt_get_ilk σ I)
  have hwad :
      evalExpr? config { contract := contract, locals := localsFlux } evmFlux (.var "wad") =
        .ok (.int (Int.ofNat (cashWadWord I).toNat)) := by
    have hget :
        localsFlux.get? "wad" = some (.int (Int.ofNat (cashWadWord I).toNat)) := by
      unfold localsFlux
      rw [store_get_ne]
      · exact cashStoreAmt_get_wad σ I
      · native_decide
    exact evalExpr_packVarUInt256 (evm := evmFlux) (locals := localsFlux)
      (name := "wad") (value := cashWadWord I) hget
  have hargsAdd :
      evalExprs? config { contract := contract, locals := localsFlux } evmFlux
        [.storage (outRef (.var "ilk") sender), .var "wad"] =
        .ok [Value.int (Int.ofNat outOld.toNat),
          Value.int (Int.ofNat (cashWadWord I).toNat)] := by
    simp [evalExprs?, hout, hwad, EvalResult.bind, bind, pure]
  have hlookupAdd : lookupCallable? contract "add" = some addFunction.toCallable := by
    simp [lookupCallable?, lookupFunction?, contract, functions, addFunction, subFunction,
      mulFunction]
  have hbindAdd :
      bindParams? addFunction.params
        [Value.int (Int.ofNat outOld.toNat), Value.int (Int.ofNat (cashWadWord I).toNat)] =
        some (packAddLocals outOld (cashWadWord I)) := by
    simp [addFunction, packAddLocals, bindParams?]
  have haddStmt :
      ExecStmt config { contract := contract, locals := localsFlux } evmFlux
        (.internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew")
        (.ok finalFrame evmFlux) := by
    have hbody := packAddFunctionBodyReturns evmFlux (x := outOld) (y := cashWadWord I)
      (sum := outNew) (by simp [outNew]) hfit
    change ExecStmt config { contract := contract, locals := localsFlux } evmFlux
      (.internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew")
      (.ok (resumeAfterInternalCall { contract := contract, locals := localsFlux } "outNew"
        (some [.int (Int.ofNat outNew.toNat)])) evmFlux)
    exact
      internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := localsFlux })
        (evm := evmFlux) (calleeEvm := evmFlux) (name := "add") (retVar := "outNew")
        (args := [.storage (outRef (.var "ilk") sender), .var "wad"])
        (argVals := [Value.int (Int.ofNat outOld.toNat),
          Value.int (Int.ofNat (cashWadWord I).toNat)])
        (callee := addFunction) (locals := packAddLocals outOld (cashWadWord I))
        (value := some [.int (Int.ofNat outNew.toNat)]) hargsAdd hlookupAdd hbindAdd hbody
  have houtNewExpr :
      evalExpr? config finalFrame evmFlux (.var "outNew") =
        .ok (.int (Int.ofNat outNew.toNat)) := by
    have hget :
        finalFrame.locals.get? "outNew" = some (.int (Int.ofNat outNew.toNat)) := by
      change (localsFlux.insert "outNew" (.int (Int.ofNat outNew.toNat))).get? "outNew" =
        some (.int (Int.ofNat outNew.toNat))
      exact store_get_self localsFlux "outNew" (.int (Int.ofNat outNew.toNat))
    simpa [finalFrame] using
      evalExpr_packVarUInt256 (evm := evmFlux) (locals := finalFrame.locals)
        (name := "outNew") (value := outNew) hget
  have hassign :
      assignStorageRef? config finalFrame evmFlux
        .storage (outRef (.var "ilk") sender) (.int (Int.ofNat outNew.toNat)) =
        .ok (finalFrame, evmStored) := by
    simpa [finalFrame, evmStored] using
      assign_cashOutStorage evmFlux outNew
        (by simp [localsFlux, cashStoreAmt, cashStore])
        (by
          rw [henvFlux]
          change (localsFlux.insert "outNew" (.int (Int.ofNat outNew.toNat))).get? "ilk" =
            some (cashIlkValue I)
          rw [store_get_ne]
          · unfold localsFlux
            rw [store_get_ne]
            · exact cashStoreAmt_get_ilk σ I
            · native_decide
          · native_decide)
  have hassignStmt :
      ExecStmt config finalFrame evmFlux
        (.assign .storage (outRef (.var "ilk") sender) (.var "outNew"))
        (.ok finalFrame evmStored) :=
    ExecStmt.assign houtNewExpr hassign
  have hblock :
      ExecBlock config { contract := contract, locals := cashStore I } evm0 cashTransition.body
        (.ok finalFrame evmStored) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardFix) ?_
    refine ExecBlock.consNormal hrmulStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
    refine ExecBlock.consNormal hcallStmt ?_
    refine ExecBlock.consNormal haddStmt ?_
    refine ExecBlock.consNormal hassignStmt ?_
    exact ExecBlock.consNormal (ExecStmt.requireTrue hguard) ExecBlock.nil
  simpa [ExecTransitionBody, evm0, cashTransition, nonpayable, checkedExternalCallStmts,
    localsFlux, outOld, outNew, finalFrame, evmStored] using ExecFuncBody.execBlockOK hblock

set_option maxHeartbeats 2000000 in
theorem endCashSourceBodyCallSuccessBagInsufficientReverts {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmFlux : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hfix : cashFixWord σ I ≠ ⟨0⟩)
    (hmul : (cashWadWord I).toNat * (cashFixWord σ I).toNat < UInt256.size)
    (hvatCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat (cashVatMaskedWord σ I).toNat)).option 0
          (fun acc => acc.code.size))).toNat ≠ 0)
    (hcallFlux :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (cashVatMaskedWord σ I).toNat)) "flux" 0
        [cashIlkValue I, .address I.codeOwner, .address I.source,
          .int (Int.ofNat (cashAmtWord σ I).toNat)]
        (true, evmFlux, out) true)
    (hfit :
      (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
        (cashOutStorageSlot evmFlux.executionEnv)).toNat + (cashWadWord I).toNat <
          UInt256.size) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let outOld := Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
      (cashOutStorageSlot evmFlux.executionEnv)
    let outNew := outOld + cashWadWord I
    let localsFlux := (cashStoreAmt σ I).insert "_flux" .unit
    let finalFrame : Frame :=
      { contract := contract,
        locals := localsFlux.insert "outNew" (.int (Int.ofNat outNew.toNat)) }
    let evmStored :=
      Solm.EVM.storageStore evmFlux evmFlux.executionEnv.codeOwner
        (cashOutStorageSlot evmFlux.executionEnv) outNew
    (hguard :
      evalExpr? config finalFrame evmStored
        (.binary .le (.storage (outRef (.var "ilk") sender)) (.storage (bagRef sender))) =
          .ok (.bool false)) →
    ExecTransitionBody config contract evm0 (cashStore I) cashTransition.body .reverted := by
  intro evm0 outOld outNew localsFlux finalFrame evmStored hguard
  have hfixStorage :
      evalExpr? config { contract := contract, locals := cashStore I } evm0
        (.storage (fixRef (.var "ilk"))) =
        .ok (.int (Int.ofNat (cashFixWord σ I).toNat)) := by
    simpa [cashFixWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_cashFixStorage (evm := evm0) (locals := cashStore I)
        (by simp [cashStore])
        (by
          unfold cashStore cashIlkValue
          rw [Std.HashMap.getElem?_insert]
          rw [if_neg (by native_decide : ¬(("wad" == "ilk") = true))]
          rw [Std.HashMap.getElem?_insert]
          have henv : evm0.executionEnv = I := by simp [evm0, initState]
          rw [henv]
          simp)
  have hzero :
      evalExpr? config { contract := contract, locals := cashStore I } evm0 (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hguardFix :
      evalExpr? config { contract := contract, locals := cashStore I } evm0
        (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) := by
    have hne : (Value.int (Int.ofNat (cashFixWord σ I).toNat) == Value.int 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro hbad
      rw [Value.int.injEq] at hbad
      exact hfix (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
    simp only [evalExpr?, hfixStorage, hzero, EvalResult.bind, bind, evalBinaryOp?, hne,
      Bool.not_false]
  have hrmulStmt :
      ExecStmt config { contract := contract, locals := cashStore I } evm0
        (.internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt")
        (.ok { contract := contract, locals := cashStoreAmt σ I } evm0) := by
    simpa [evm0] using
      endCashRmulStmtOk (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hmul hfix
  have hvat :
      evalExpr? config { contract := contract, locals := cashStoreAmt σ I } evm0
        (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (cashVatMaskedWord σ I).toNat)) := by
    simpa [cashVatMaskedWord, cashVatWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, u256_land_comm] using
      evalExpr_cashVatStorage (evm := evm0) (locals := cashStoreAmt σ I)
        (by simp [cashStoreAmt, cashStore])
  have hvatGuard :
      evalExpr? config { contract := contract, locals := cashStoreAmt σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_cashVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargsFlux := evalExprs_cashFluxArgs (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hdecodeFlux : config.externalABI.decode? "flux" out = some ([] : List Value) := by
    simp [config, externalABI, decodeVoid?]
  have hcallStmt :
      ExecStmt config { contract := contract, locals := cashStoreAmt σ I } evm0
        (.externalCall (.storage vatRef) "flux" (.intLit 0)
          [.var "ilk", thisAddr, sender, .var "amt"] "_flux" (perm := true))
        (.ok { contract := contract, locals := localsFlux } evmFlux) := by
    simpa [localsFlux] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsFlux hcallFlux
        hdecodeFlux
  have henvFlux : evmFlux.executionEnv = I := by
    simpa [evm0, initState] using typedCallViaEVM_executionEnv_eq hcallFlux
  have hout :
      evalExpr? config { contract := contract, locals := localsFlux } evmFlux
        (.storage (outRef (.var "ilk") sender)) =
        .ok (.int (Int.ofNat outOld.toNat)) := by
    simpa [outOld] using
      evalExpr_cashOutStorage (evm := evmFlux) (locals := localsFlux)
        (by simp [localsFlux, cashStoreAmt, cashStore])
        (by
          rw [henvFlux]
          unfold localsFlux
          rw [Std.HashMap.getElem?_insert]
          rw [if_neg (by native_decide : ¬(("_flux" == "ilk") = true))]
          exact cashStoreAmt_get_ilk σ I)
  have hwad :
      evalExpr? config { contract := contract, locals := localsFlux } evmFlux (.var "wad") =
        .ok (.int (Int.ofNat (cashWadWord I).toNat)) := by
    have hget :
        localsFlux.get? "wad" = some (.int (Int.ofNat (cashWadWord I).toNat)) := by
      unfold localsFlux
      rw [store_get_ne]
      · exact cashStoreAmt_get_wad σ I
      · native_decide
    exact evalExpr_packVarUInt256 (evm := evmFlux) (locals := localsFlux)
      (name := "wad") (value := cashWadWord I) hget
  have hargsAdd :
      evalExprs? config { contract := contract, locals := localsFlux } evmFlux
        [.storage (outRef (.var "ilk") sender), .var "wad"] =
        .ok [Value.int (Int.ofNat outOld.toNat),
          Value.int (Int.ofNat (cashWadWord I).toNat)] := by
    simp [evalExprs?, hout, hwad, EvalResult.bind, bind, pure]
  have hlookupAdd : lookupCallable? contract "add" = some addFunction.toCallable := by
    simp [lookupCallable?, lookupFunction?, contract, functions, addFunction, subFunction,
      mulFunction]
  have hbindAdd :
      bindParams? addFunction.params
        [Value.int (Int.ofNat outOld.toNat), Value.int (Int.ofNat (cashWadWord I).toNat)] =
        some (packAddLocals outOld (cashWadWord I)) := by
    simp [addFunction, packAddLocals, bindParams?]
  have haddStmt :
      ExecStmt config { contract := contract, locals := localsFlux } evmFlux
        (.internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew")
        (.ok finalFrame evmFlux) := by
    have hbody := packAddFunctionBodyReturns evmFlux (x := outOld) (y := cashWadWord I)
      (sum := outNew) (by simp [outNew]) hfit
    change ExecStmt config { contract := contract, locals := localsFlux } evmFlux
      (.internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew")
      (.ok (resumeAfterInternalCall { contract := contract, locals := localsFlux } "outNew"
        (some [.int (Int.ofNat outNew.toNat)])) evmFlux)
    exact
      internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := localsFlux })
        (evm := evmFlux) (calleeEvm := evmFlux) (name := "add") (retVar := "outNew")
        (args := [.storage (outRef (.var "ilk") sender), .var "wad"])
        (argVals := [Value.int (Int.ofNat outOld.toNat),
          Value.int (Int.ofNat (cashWadWord I).toNat)])
        (callee := addFunction) (locals := packAddLocals outOld (cashWadWord I))
        (value := some [.int (Int.ofNat outNew.toNat)]) hargsAdd hlookupAdd hbindAdd hbody
  have houtNewExpr :
      evalExpr? config finalFrame evmFlux (.var "outNew") =
        .ok (.int (Int.ofNat outNew.toNat)) := by
    have hget :
        finalFrame.locals.get? "outNew" = some (.int (Int.ofNat outNew.toNat)) := by
      change (localsFlux.insert "outNew" (.int (Int.ofNat outNew.toNat))).get? "outNew" =
        some (.int (Int.ofNat outNew.toNat))
      exact store_get_self localsFlux "outNew" (.int (Int.ofNat outNew.toNat))
    simpa [finalFrame] using
      evalExpr_packVarUInt256 (evm := evmFlux) (locals := finalFrame.locals)
        (name := "outNew") (value := outNew) hget
  have hassign :
      assignStorageRef? config finalFrame evmFlux
        .storage (outRef (.var "ilk") sender) (.int (Int.ofNat outNew.toNat)) =
        .ok (finalFrame, evmStored) := by
    simpa [finalFrame, evmStored] using
      assign_cashOutStorage evmFlux outNew
        (by simp [localsFlux, cashStoreAmt, cashStore])
        (by
          rw [henvFlux]
          change (localsFlux.insert "outNew" (.int (Int.ofNat outNew.toNat))).get? "ilk" =
            some (cashIlkValue I)
          rw [store_get_ne]
          · unfold localsFlux
            rw [store_get_ne]
            · exact cashStoreAmt_get_ilk σ I
            · native_decide
          · native_decide)
  have hassignStmt :
      ExecStmt config finalFrame evmFlux
        (.assign .storage (outRef (.var "ilk") sender) (.var "outNew"))
        (.ok finalFrame evmStored) :=
    ExecStmt.assign houtNewExpr hassign
  have hblock :
      ExecBlock config { contract := contract, locals := cashStore I } evm0 cashTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardFix) ?_
    refine ExecBlock.consNormal hrmulStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
    refine ExecBlock.consNormal hcallStmt ?_
    refine ExecBlock.consNormal haddStmt ?_
    refine ExecBlock.consNormal hassignStmt ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  simpa [ExecTransitionBody, evm0, cashTransition, nonpayable, checkedExternalCallStmts,
    localsFlux, outOld, outNew, finalFrame, evmStored] using ExecFuncBody.execBlockRevert hblock

theorem endCashSourceBodyNoCodeReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hfix : cashFixWord σ I ≠ ⟨0⟩)
    (hmul : (cashWadWord I).toNat * (cashFixWord σ I).toNat < UInt256.size)
    (hvatNoCode :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (cashVatMaskedWord σ I) = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (cashStore I) cashTransition.body .reverted := by
  intro evm0
  have hfixStorage :
      evalExpr? config { contract := contract, locals := cashStore I } evm0
        (.storage (fixRef (.var "ilk"))) =
        .ok (.int (Int.ofNat (cashFixWord σ I).toNat)) := by
    simpa [cashFixWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_cashFixStorage (evm := evm0) (locals := cashStore I)
        (by simp [cashStore])
        (by
          unfold cashStore cashIlkValue
          rw [Std.HashMap.getElem?_insert]
          rw [if_neg (by native_decide : ¬(("wad" == "ilk") = true))]
          rw [Std.HashMap.getElem?_insert]
          have henv : evm0.executionEnv = I := by simp [evm0, initState]
          rw [henv]
          simp)
  have hzero :
      evalExpr? config { contract := contract, locals := cashStore I } evm0 (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hguardFix :
      evalExpr? config { contract := contract, locals := cashStore I } evm0
        (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) := by
    have hne : (Value.int (Int.ofNat (cashFixWord σ I).toNat) == Value.int 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro hbad
      rw [Value.int.injEq] at hbad
      exact hfix (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
    simp only [evalExpr?, hfixStorage, hzero, EvalResult.bind, bind, evalBinaryOp?, hne,
      Bool.not_false]
  have hrmulStmt :
      ExecStmt config { contract := contract, locals := cashStore I } evm0
        (.internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt")
        (.ok { contract := contract, locals := cashStoreAmt σ I } evm0) := by
    simpa [evm0] using
      endCashRmulStmtOk (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hmul hfix
  have hvat :
      evalExpr? config { contract := contract, locals := cashStoreAmt σ I } evm0
        (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (cashVatMaskedWord σ I).toNat)) := by
    simpa [cashVatMaskedWord, cashVatWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, u256_land_comm] using
      evalExpr_cashVatStorage (evm := evm0) (locals := cashStoreAmt σ I)
        (by simp [cashStoreAmt, cashStore])
  have hvatNoCodeNat :
      (UInt256.ofNat
        ((evm0.lookupAccount (AccountAddress.ofNat (cashVatMaskedWord σ I).toNat)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    have hnat := congrArg UInt256.toNat hvatNoCode
    simp [Reasoning.Theory.uniswapExtCodeSizeWord, evm0, initState, State.lookupAccount,
      accountAddress_ofUInt256_eq_ofNat_toNat] at hnat ⊢
    cases hfind : σ.find? (AccountAddress.ofNat (cashVatMaskedWord σ I).toNat)
    · native_decide
    · simp [hfind, Option.option, Function.comp] at hnat ⊢
      exact hnat
  have hvatGuard :
      evalExpr? config { contract := contract, locals := cashStoreAmt σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_cashVatCodeGuard_false hvat hvatNoCodeNat
  refine ExecFuncBody.execBlockRevert ?_
  simpa [cashTransition, nonpayable, checkedExternalCallStmts] using
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
      simp [evm0, initState]; exact hwv))) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hguardFix) <|
        ExecBlock.consNormal hrmulStmt <|
          ExecBlock.consRevert (ExecStmt.requireFalse hvatGuard)

theorem endCashSourceBodyCallFailure {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmFlux : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hfix : cashFixWord σ I ≠ ⟨0⟩)
    (hmul : (cashWadWord I).toNat * (cashFixWord σ I).toNat < UInt256.size)
    (hvatCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat (cashVatMaskedWord σ I).toNat)).option 0
          (fun acc => acc.code.size))).toNat ≠ 0)
    (hcallFlux :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (cashVatMaskedWord σ I).toNat)) "flux" 0
        [cashIlkValue I, .address I.codeOwner, .address I.source,
          .int (Int.ofNat (cashAmtWord σ I).toNat)]
        (false, evmFlux, out) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (cashStore I) cashTransition.body .reverted := by
  intro evm0
  have hfixStorage :
      evalExpr? config { contract := contract, locals := cashStore I } evm0
        (.storage (fixRef (.var "ilk"))) =
        .ok (.int (Int.ofNat (cashFixWord σ I).toNat)) := by
    simpa [cashFixWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_cashFixStorage (evm := evm0) (locals := cashStore I)
        (by simp [cashStore])
        (by
          unfold cashStore cashIlkValue
          rw [Std.HashMap.getElem?_insert]
          rw [if_neg (by native_decide : ¬(("wad" == "ilk") = true))]
          rw [Std.HashMap.getElem?_insert]
          have henv : evm0.executionEnv = I := by simp [evm0, initState]
          rw [henv]
          simp)
  have hzero :
      evalExpr? config { contract := contract, locals := cashStore I } evm0 (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hguardFix :
      evalExpr? config { contract := contract, locals := cashStore I } evm0
        (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) := by
    have hne : (Value.int (Int.ofNat (cashFixWord σ I).toNat) == Value.int 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro hbad
      rw [Value.int.injEq] at hbad
      exact hfix (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
    simp only [evalExpr?, hfixStorage, hzero, EvalResult.bind, bind, evalBinaryOp?, hne,
      Bool.not_false]
  have hrmulStmt :
      ExecStmt config { contract := contract, locals := cashStore I } evm0
        (.internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt")
        (.ok { contract := contract, locals := cashStoreAmt σ I } evm0) := by
    simpa [evm0] using
      endCashRmulStmtOk (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hmul hfix
  have hvat :
      evalExpr? config { contract := contract, locals := cashStoreAmt σ I } evm0
        (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (cashVatMaskedWord σ I).toNat)) := by
    simpa [cashVatMaskedWord, cashVatWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, u256_land_comm] using
      evalExpr_cashVatStorage (evm := evm0) (locals := cashStoreAmt σ I)
        (by simp [cashStoreAmt, cashStore])
  have hvatGuard :
      evalExpr? config { contract := contract, locals := cashStoreAmt σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_cashVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargsFlux := evalExprs_cashFluxArgs (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hcallStmt :
      ExecStmt config { contract := contract, locals := cashStoreAmt σ I } evm0
        (.externalCall (.storage vatRef) "flux" (.intLit 0)
          [.var "ilk", thisAddr, sender, .var "amt"] "_flux" (perm := true))
        .reverted := by
    exact ExecStmt.externalCallFailure hvat (by simp [evalExpr?, pure]) hargsFlux hcallFlux
  have hblock :
      ExecBlock config { contract := contract, locals := cashStore I } evm0 cashTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardFix) ?_
    refine ExecBlock.consNormal hrmulStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
    exact ExecBlock.consRevert hcallStmt
  simpa [ExecTransitionBody, evm0, cashTransition, nonpayable, checkedExternalCallStmts]
    using ExecFuncBody.execBlockRevert hblock

set_option maxHeartbeats 2000000 in
theorem endCashSourceBodyCallSuccessAddOverflow {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmFlux : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hfix : cashFixWord σ I ≠ ⟨0⟩)
    (hmul : (cashWadWord I).toNat * (cashFixWord σ I).toNat < UInt256.size)
    (hvatCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat (cashVatMaskedWord σ I).toNat)).option 0
          (fun acc => acc.code.size))).toNat ≠ 0)
    (hcallFlux :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (cashVatMaskedWord σ I).toNat)) "flux" 0
        [cashIlkValue I, .address I.codeOwner, .address I.source,
          .int (Int.ofNat (cashAmtWord σ I).toNat)]
        (true, evmFlux, out) true)
    (hover :
      UInt256.size ≤
        (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
          (cashOutStorageSlot evmFlux.executionEnv)).toNat + (cashWadWord I).toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (cashStore I) cashTransition.body .reverted := by
  intro evm0
  let outOld := Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
    (cashOutStorageSlot evmFlux.executionEnv)
  let localsFlux := (cashStoreAmt σ I).insert "_flux" .unit
  have hfixStorage :
      evalExpr? config { contract := contract, locals := cashStore I } evm0
        (.storage (fixRef (.var "ilk"))) =
        .ok (.int (Int.ofNat (cashFixWord σ I).toNat)) := by
    simpa [cashFixWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_cashFixStorage (evm := evm0) (locals := cashStore I)
        (by simp [cashStore])
        (by
          unfold cashStore cashIlkValue
          rw [Std.HashMap.getElem?_insert]
          rw [if_neg (by native_decide : ¬(("wad" == "ilk") = true))]
          rw [Std.HashMap.getElem?_insert]
          have henv : evm0.executionEnv = I := by simp [evm0, initState]
          rw [henv]
          simp)
  have hzero :
      evalExpr? config { contract := contract, locals := cashStore I } evm0 (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hguardFix :
      evalExpr? config { contract := contract, locals := cashStore I } evm0
        (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) := by
    have hne : (Value.int (Int.ofNat (cashFixWord σ I).toNat) == Value.int 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro hbad
      rw [Value.int.injEq] at hbad
      exact hfix (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
    simp only [evalExpr?, hfixStorage, hzero, EvalResult.bind, bind, evalBinaryOp?, hne,
      Bool.not_false]
  have hrmulStmt :
      ExecStmt config { contract := contract, locals := cashStore I } evm0
        (.internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt")
        (.ok { contract := contract, locals := cashStoreAmt σ I } evm0) := by
    simpa [evm0] using
      endCashRmulStmtOk (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hmul hfix
  have hvat :
      evalExpr? config { contract := contract, locals := cashStoreAmt σ I } evm0
        (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (cashVatMaskedWord σ I).toNat)) := by
    simpa [cashVatMaskedWord, cashVatWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, u256_land_comm] using
      evalExpr_cashVatStorage (evm := evm0) (locals := cashStoreAmt σ I)
        (by simp [cashStoreAmt, cashStore])
  have hvatGuard :
      evalExpr? config { contract := contract, locals := cashStoreAmt σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_cashVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargsFlux := evalExprs_cashFluxArgs (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hdecodeFlux : config.externalABI.decode? "flux" out = some ([] : List Value) := by
    simp [config, externalABI, decodeVoid?]
  have hcallStmt :
      ExecStmt config { contract := contract, locals := cashStoreAmt σ I } evm0
        (.externalCall (.storage vatRef) "flux" (.intLit 0)
          [.var "ilk", thisAddr, sender, .var "amt"] "_flux" (perm := true))
        (.ok { contract := contract, locals := localsFlux } evmFlux) := by
    simpa [localsFlux] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsFlux hcallFlux
        hdecodeFlux
  have henvFlux : evmFlux.executionEnv = I := by
    simpa [evm0, initState] using typedCallViaEVM_executionEnv_eq hcallFlux
  have hout :
      evalExpr? config { contract := contract, locals := localsFlux } evmFlux
        (.storage (outRef (.var "ilk") sender)) =
        .ok (.int (Int.ofNat outOld.toNat)) := by
    simpa [outOld] using
      evalExpr_cashOutStorage (evm := evmFlux) (locals := localsFlux)
        (by simp [localsFlux, cashStoreAmt, cashStore])
        (by
          rw [henvFlux]
          unfold localsFlux
          rw [Std.HashMap.getElem?_insert]
          rw [if_neg (by native_decide : ¬(("_flux" == "ilk") = true))]
          exact cashStoreAmt_get_ilk σ I)
  have hwad :
      evalExpr? config { contract := contract, locals := localsFlux } evmFlux (.var "wad") =
        .ok (.int (Int.ofNat (cashWadWord I).toNat)) := by
    have hget :
        localsFlux.get? "wad" = some (.int (Int.ofNat (cashWadWord I).toNat)) := by
      unfold localsFlux
      rw [store_get_ne]
      · exact cashStoreAmt_get_wad σ I
      · native_decide
    exact evalExpr_packVarUInt256 (evm := evmFlux) (locals := localsFlux)
      (name := "wad") (value := cashWadWord I) hget
  have hargsAdd :
      evalExprs? config { contract := contract, locals := localsFlux } evmFlux
        [.storage (outRef (.var "ilk") sender), .var "wad"] =
        .ok [Value.int (Int.ofNat outOld.toNat),
          Value.int (Int.ofNat (cashWadWord I).toNat)] := by
    simp [evalExprs?, hout, hwad, EvalResult.bind, bind, pure]
  have hlookupAdd : lookupCallable? contract "add" = some addFunction.toCallable := by
    simp [lookupCallable?, lookupFunction?, contract, functions, addFunction, subFunction,
      mulFunction]
  have hbindAdd :
      bindParams? addFunction.params
        [Value.int (Int.ofNat outOld.toNat), Value.int (Int.ofNat (cashWadWord I).toNat)] =
        some (packAddLocals outOld (cashWadWord I)) := by
    simp [addFunction, packAddLocals, bindParams?]
  have haddStmt :
      ExecStmt config { contract := contract, locals := localsFlux } evmFlux
        (.internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew")
        .reverted := by
    exact internalCallFunctionRevert hargsAdd hlookupAdd hbindAdd
      (packAddFunctionBodyReverts evmFlux (x := outOld) (y := cashWadWord I) hover)
  have hblock :
      ExecBlock config { contract := contract, locals := cashStore I } evm0 cashTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardFix) ?_
    refine ExecBlock.consNormal hrmulStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
    refine ExecBlock.consNormal hcallStmt ?_
    exact ExecBlock.consRevert haddStmt
  simpa [ExecTransitionBody, evm0, cashTransition, nonpayable, checkedExternalCallStmts,
    localsFlux, outOld] using ExecFuncBody.execBlockRevert hblock

theorem endDecode_cash_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (cashTransition.params.map Param.name)
      (transitionSignature cashTransition).paramTypes I.calldata =
        some (cashStore I) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk", "wad"] [bytes32, uint256]
    I.calldata = some (cashStore I)
  simpa [cashStore, cashIlkWord, cashWadWord] using
    endDecodeCalldata_legacyBytes32Uint256_ok (cd := I.calldata) (x := "ilk")
      (y := "wad") hsz68

theorem endDecode_cash_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (cashTransition.params.map Param.name)
      (transitionSignature cashTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk", "wad"] [bytes32, uint256]
    I.calldata = none
  exact endDecodeCalldata_legacyBytes32Uint256_none_short (cd := I.calldata)
    (x := "ilk") (y := "wad") hsz4 hshort

theorem endDispatchCashLocal {I : ExecutionEnv} (hsel : selIs I (endSelBytes 31)) :
    dispatchMsg contract I.calldata = some cashTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 31 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some cashTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

set_option maxHeartbeats 5000000 in
theorem endReachCashBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (endSelBytes 31)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1274⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : endSelWord I = ⟨0xfe8507c6⟩ :=
    endSelWord_eq_of_beq I hsz 0xfe 0x85 0x07 0xc6 ⟨0xfe8507c6⟩
      (by native_decide) (by simpa [endSelBytes] using hsel)
  obtain ⟨_, _, h32⟩ :=
    endReachRootSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have hroot :
      UInt256.gt (armSelNat endBytecode (⟨32⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h43 := RD.selectorSplitNotTakenAuto h32
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    hroot (by simp)
  have h43gt :
      UInt256.gt (armSelNat endBytecode (⟨43⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h54 := by
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
      selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43
        (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
        h43gt (by simp)
  have h54gt :
      UInt256.gt (armSelNat endBytecode (⟨54⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h65 := by
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
      selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h54
        (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
        h54gt (by simp)
  have hcat :
      UInt256.eq (armSelNat endBytecode (⟨65⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have hgap :
      UInt256.eq (armSelNat endBytecode (⟨76⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have htag :
      UInt256.eq (armSelNat endBytecode (⟨87⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have hcash :
      UInt256.eq (armSelNat endBytecode (⟨98⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h1274 := h65
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      hcat (by simp)
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      hgap (by simp)
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      htag (by simp)
    |>.selectorArmTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      hcash (by jump_dest) (by simp)
  exact ⟨_, _, h1274⟩

theorem RD.endCashDecodeToRoutine {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel de : UInt256}
    (h : RD endBytecode I g s0 ⟨1296⟩
      (de :: ⟨4⟩ :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨9609⟩
      [cashWadWord I, cashIlkWord I, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd9609 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw push2 ⟨9609⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa [cashWadWord, cashIlkWord, calldataWord] using rd9609⟩

theorem endCashX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9609⟩
        [cashWadWord I, cashIlkWord I, ⟨562⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := endBytecode) (sel := sel) (entry := ⟨1274⟩) (ret := ⟨562⟩)
    (decoded := ⟨1296⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  exact RD.endCashDecodeToRoutine hdecoded

theorem endCashX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel)
    (entry := ⟨1274⟩) (ret := ⟨562⟩) (decoded := ⟨1296⟩)
    (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem endCashX_fixZero {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hfix : cashFixWord σ I = ⟨0⟩)
    (h : RD endBytecode I g s0 ⟨9609⟩
      [cashWadWord I, cashIlkWord I, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have hslot :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC ((twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem).readWithPadding
              0 64))) =
        cashFixStorageSlot I := by
    rw [twoWordHashMem_solcMappingSlot ⟨15⟩ (cashIlkWord I) solcFreePtrMem_size]
    exact (cashFixStorageSlot_eq I).symm
  have rd9624pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (cashIlkWord I) solcFreePtrMem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by simp [wordAt0Mem])
      (by native_decide) (by evm_ov),
    raw push1 ⟨15⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by
        simp [twoWordHashMem, wordAt32Mem,
          show (⟨32⟩ : UInt256).toNat = 32 from by native_decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd9624hash := rd9624pre.keccak256 0 (cashFixStorageSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨k9625, C9625, rd9625raw⟩ := rd9624hash.sload (by native_decide) (by evm_ov)
  have rd9625 : RD endBytecode I g s0 ⟨9625⟩
      (cashFixWord σ I :: cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k9625 C9625 := by
    simpa [cashFixWord, endSlotWord, cashFixStorageSlot] using rd9625raw
  have rd9628pre := rd9625.push2 ⟨9705⟩ (by native_decide) (by evm_ov)
  rw [hfix] at rd9628pre
  have rd9629 := rd9628pre.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTailPush32
    (pc := ⟨9629⟩)
    (len := ⟨23⟩)
    (word := ⟨31404631181908416848914724429574912633421996829782487769820129510129741594624⟩)
    rd9629
    (by
      unfold solcErrorStringRevertTailPush32Wf
      repeat' first | apply And.intro | native_decide)
    (twoWordHashMem_size_96 (cashIlkWord I) ⟨15⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 (cashIlkWord I) ⟨15⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCashX_toRmul {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hfix : cashFixWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g s0 ⟨9609⟩
      [cashWadWord I, cashIlkWord I, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨10114⟩
      (cashFixWord σ I :: cashWadWord I :: ⟨9758⟩ :: cashSourceWord I ::
        UInt256.ofNat I.codeOwner.val :: cashIlkWord I :: ⟨1628552750⟩ ::
        cashVatMaskedWord σ I :: cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (cashIlkWord I) ⟨15⟩
        (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hslot :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC ((twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem).readWithPadding
              0 64))) =
        cashFixStorageSlot I := by
    rw [twoWordHashMem_solcMappingSlot ⟨15⟩ (cashIlkWord I) solcFreePtrMem_size]
    exact (cashFixStorageSlot_eq I).symm
  have rd9624pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (cashIlkWord I) solcFreePtrMem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by simp [wordAt0Mem])
      (by native_decide) (by evm_ov),
    raw push1 ⟨15⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by
        simp [twoWordHashMem, wordAt32Mem,
          show (⟨32⟩ : UInt256).toNat = 32 from by native_decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd9624hash := rd9624pre.keccak256 0 (cashFixStorageSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨k9625, C9625, rd9625raw⟩ := rd9624hash.sload (by native_decide) (by evm_ov)
  have rd9625 : RD endBytecode I g s0 ⟨9625⟩
      (cashFixWord σ I :: cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k9625 C9625 := by
    simpa [cashFixWord, endSlotWord, cashFixStorageSlot] using rd9625raw
  have rd9628pre := rd9625.push2 ⟨9705⟩ (by native_decide) (by evm_ov)
  have rd9705raw := rd9628pre.jumpiT (by native_decide) hfix (by jump_dest) (by evm_ov)
  have rd9708pre := evm_run (rd9705raw.jumpdest (by native_decide) (by evm_ov)) with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k9709, C9709, rd9709raw⟩ := rd9708pre.sload (by native_decide) (by evm_ov)
  have rd9709 : RD endBytecode I g s0 ⟨9709⟩
      (cashVatWord σ I :: cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k9709 C9709 := by
    simpa [cashVatWord, endSlotWord] using rd9709raw
  have rd9723pre := evm_run rd9709 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (cashIlkWord I)
      (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem)) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by simp [wordAt0Mem])
      (by native_decide) (by evm_ov),
    raw push1 ⟨15⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (twoWordHashMem (cashIlkWord I) ⟨15⟩
      (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by
        simp [twoWordHashMem, wordAt32Mem,
          show (⟨32⟩ : UInt256).toNat = 32 from by native_decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hslot2 :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC ((twoWordHashMem (cashIlkWord I) ⟨15⟩
              (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem)).readWithPadding 0 64))) =
        cashFixStorageSlot I := by
    have hsize : (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem).size = 96 :=
      twoWordHashMem_size_96 (cashIlkWord I) ⟨15⟩ solcFreePtrMem_size
    rw [twoWordHashMem_solcMappingSlot ⟨15⟩ (cashIlkWord I) hsize]
    exact (cashFixStorageSlot_eq I).symm
  have rd9723hash := rd9723pre.keccak256 0 (cashFixStorageSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot2 (by native_decide) (by evm_ov)
  obtain ⟨k9724, C9724, rd9724raw⟩ := rd9723hash.sload (by native_decide) (by evm_ov)
  have rd9724 : RD endBytecode I g s0 ⟨9724⟩
      (cashFixWord σ I :: cashVatWord σ I :: cashWadWord I :: cashIlkWord I ::
        ⟨562⟩ :: [sel])
      (twoWordHashMem (cashIlkWord I) ⟨15⟩
        (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k9724 C9724 := by
    simpa [cashFixWord, endSlotWord, cashFixStorageSlot] using rd9724raw
  have rd9744pre := evm_run rd9724 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push4 ⟨1628552750⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd9745 := RD.uniswapAddress rd9744pre (by native_decide) (by evm_ov)
  have rd9757pre := evm_run rd9745 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨9758⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨10114⟩ (by native_decide) (by evm_ov)]
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  have hvat :
      (cashVatWord σ I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩) =
        cashVatMaskedWord σ I := by
    have hvat0 :
        (cashVatWord σ I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩) =
          (cashVatWord σ I).land solcAddrMask := by
      exact congrArg (fun m : UInt256 => UInt256.land (cashVatWord σ I) m) hmask
    rw [hvat0]
    simpa [cashVatMaskedWord] using u256_land_comm (cashVatWord σ I) solcAddrMask
  rw [hvat] at rd9757pre
  exact ⟨_, _, by
    simpa [cashSourceWord] using
      rd9757pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem endCashX_mulOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} {mem : ByteArray}
    (hmul : (cashWadWord I).toNat * (cashFixWord σ I).toNat < UInt256.size)
    (hfix : cashFixWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g s0 ⟨10170⟩
      (cashFixWord σ I :: cashWadWord I :: ⟨10139⟩ :: cashRayWord :: ⟨0⟩ ::
        cashFixWord σ I :: cashWadWord I :: ⟨9758⟩ :: cashSourceWord I ::
        UInt256.ofNat I.codeOwner.val :: cashIlkWord I :: ⟨1628552750⟩ ::
        cashVatMaskedWord σ I :: cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨10139⟩
      (cashAmtMulWord σ I :: cashRayWord :: ⟨0⟩ ::
        cashFixWord σ I :: cashWadWord I :: ⟨9758⟩ :: cashSourceWord I ::
        UInt256.ofNat I.codeOwner.val :: cashIlkWord I :: ⟨1628552750⟩ ::
        cashVatMaskedWord σ I :: cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd10180pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨10197⟩ (by native_decide) (by evm_ov)]
  rw [isZero_eq_zero_of_ne hfix] at rd10180pre
  have rd10182pre := evm_run
      (rd10180pre.jumpiNT (by native_decide) rfl (by evm_ov)) with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd10192pre := evm_run rd10182pre with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨10194⟩ (by native_decide) (by evm_ov)]
  have rd10194raw :=
    rd10192pre.jumpiT (by native_decide) hfix (by jump_dest) (by evm_ov)
  have rd10197pre := evm_run (rd10194raw.jumpdest (by native_decide) (by evm_ov)) with [
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have hdiv : UInt256.div (cashAmtMulWord σ I) (cashFixWord σ I) = cashWadWord I := by
    simpa [cashAmtMulWord] using
      cash_mul_div_right_cancel (x := cashWadWord I) (y := cashFixWord σ I) hmul hfix
  rw [hdiv, u256_eq_refl] at rd10197pre
  have rd10108 :=
    rd10197pre.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)
  have rd10113pre := evm_run (rd10108.jumpdest (by native_decide) (by evm_ov)) with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [cashAmtMulWord] using
      rd10113pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem endCashX_rmulOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hmul : (cashWadWord I).toNat * (cashFixWord σ I).toNat < UInt256.size)
    (hfix : cashFixWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g s0 ⟨10114⟩
      (cashFixWord σ I :: cashWadWord I :: ⟨9758⟩ :: cashSourceWord I ::
        UInt256.ofNat I.codeOwner.val :: cashIlkWord I :: ⟨1628552750⟩ ::
        cashVatMaskedWord σ I :: cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (cashIlkWord I) ⟨15⟩
        (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨9758⟩
      (cashAmtWord σ I :: cashSourceWord I :: UInt256.ofNat I.codeOwner.val ::
        cashIlkWord I :: ⟨1628552750⟩ :: cashVatMaskedWord σ I ::
        cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (cashIlkWord I) ⟨15⟩
        (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd10138pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov)]
  have rd10130pre := rd10138pre.pushConst cashRayWord
    (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
  have rd10138pre := evm_run rd10130pre with [
    raw push2 ⟨10139⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push2 ⟨10170⟩ (by native_decide) (by evm_ov)]
  have rd10170 := rd10138pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨k10139, C10139, rd10139⟩ :=
    endCashX_mulOk (g := g) (s0 := s0) (hmul := hmul) (hfix := hfix) rd10170
  have rd10145pre := evm_run rd10139 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨10146⟩ (by native_decide) (by evm_ov)]
  have hrayNonzero : cashRayWord ≠ ⟨0⟩ := by native_decide
  have rd10146raw := rd10145pre.jumpiT (by native_decide) hrayNonzero
    (by jump_dest) (by evm_ov)
  have rd10153pre := evm_run (rd10146raw.jumpdest (by native_decide) (by evm_ov)) with [
    raw div (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [cashAmtWord] using
      rd10153pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem RD.endCashFluxExtcodesizeGuard
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨9758⟩
      (cashAmtWord σ I :: cashSourceWord I :: UInt256.ofNat I.codeOwner.val ::
        cashIlkWord I :: cashFluxSelectorWord :: cashVatMaskedWord σ I ::
        cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (cashIlkWord I) ⟨15⟩
        (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨9839⟩
      (cashVatMaskedWord σ I :: cashVatMaskedWord σ I :: ⟨0⟩ ::
        cashFluxOutPtr :: cashFluxInSize :: cashFluxOutPtr :: cashFluxOutSize ::
        cashFluxEndPtr :: cashFluxSelectorWord :: cashVatMaskedWord σ I ::
        cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (cashFluxCalldataMem σ I
        (twoWordHashMem (cashIlkWord I) ⟨15⟩
          (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem)))
      (UInt256.ofNat 9) ByteArray.empty (cA, σ) k' C' := by
  let mem0 := twoWordHashMem (cashIlkWord I) ⟨15⟩
    (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem)
  have hmem0 : mem0.size = 96 := by
    unfold mem0
    exact twoWordHashMem_size_96 (cashIlkWord I) ⟨15⟩
      (twoWordHashMem_size_96 (cashIlkWord I) ⟨15⟩ solcFreePtrMem_size)
  have hread64 :
      mem0.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    unfold mem0
    exact twoWordHashMem_read64 (cashIlkWord I) ⟨15⟩
      (twoWordHashMem_size_96 (cashIlkWord I) ⟨15⟩ solcFreePtrMem_size)
      (twoWordHashMem_read64 (cashIlkWord I) ⟨15⟩ solcFreePtrMem_size
        solcFreePtrMem_read64)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem0.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem0.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem0]; decide) (by decide) hread64
  have hCallMemSize : (cashFluxCalldataMem σ I mem0).size = 260 :=
    cashFluxCalldataMem_size σ I hmem0
  have hCallRead64 :
      (cashFluxCalldataMem σ I mem0).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    cashFluxCalldataMem_read64 σ I hmem0 hread64
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (cashFluxCalldataMem σ I mem0).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((cashFluxCalldataMem σ I mem0).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hCallMemSize]; decide) (by decide) hCallRead64
  have hsourceCanon : (cashSourceWord I).toNat < EVM.addressModulus := by
    change I.source.val % UInt256.size < EVM.addressModulus
    rw [Nat.mod_eq_of_lt (lt_trans I.source.isLt (by native_decide))]
    change (↑I.source : ℕ) < AccountAddress.size
    exact I.source.isLt
  have hsourceMask :
      UInt256.land solcAddrMask (cashSourceWord I) = cashSourceWord I :=
    solcAddrMask_clean_left hsourceCanon
  have hthisCanon : (UInt256.ofNat I.codeOwner.val).toNat < EVM.addressModulus := by
    change I.codeOwner.val % UInt256.size < EVM.addressModulus
    rw [Nat.mod_eq_of_lt (lt_trans I.codeOwner.isLt (by native_decide))]
    change (↑I.codeOwner : ℕ) < AccountAddress.size
    exact I.codeOwner.isLt
  have hthisMask :
      UInt256.land solcAddrMask (UInt256.ofNat I.codeOwner.val) =
        UInt256.ofNat I.codeOwner.val :=
    solcAddrMask_clean_left hthisCanon
  have rd0 : RD endBytecode I g s0 ⟨9758⟩
      (cashAmtWord σ I :: cashSourceWord I :: UInt256.ofNat I.codeOwner.val ::
        cashIlkWord I :: cashFluxSelectorWord :: cashVatMaskedWord σ I ::
        cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      mem0 (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    simpa [mem0] using rd
  have rd9839 := evm_run rd0 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw push4 ⟨4294967295⟩ (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (cashFluxSelectorMem mem0) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 (cashFluxIlkMem I mem0) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 (cashFluxThisMem I mem0) (UInt256.ofNat 7)
      (by native_decide) mem_cost
      (by
        simp [cashFluxThisMem, hthisMask,
          show ({ val := 32 } + ({ val := 4 } + { val := 128 }) : UInt256).toNat = 164
            from by native_decide,
          show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask from by decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 (cashFluxSourceMem I mem0) (UInt256.ofNat 8)
      (by native_decide) mem_cost
      (by
        simp [cashFluxSourceMem, hsourceMask,
          show ({ val := 32 } + ({ val := 32 } + ({ val := 4 } + { val := 128 })) :
            UInt256).toNat = 196 from by native_decide,
          show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask from by decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 (cashFluxCalldataMem σ I mem0) (UInt256.ofNat 9)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [mem0, cashFluxSelectorShifted, cashFluxSelectorWord, cashFluxSelectorMem,
      cashFluxIlkMem, cashFluxThisMem, cashFluxSourceMem, cashFluxCalldataMem,
      cashFluxOutPtr, cashFluxInSize, cashFluxOutSize, cashFluxEndPtr, solcAddrMask,
      u256_land_comm, hsourceMask, hthisMask,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide] using rd9839⟩

theorem RD.endCashFluxCall
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨9758⟩
      (cashAmtWord σ I :: cashSourceWord I :: UInt256.ofNat I.codeOwner.val ::
        cashIlkWord I :: cashFluxSelectorWord :: cashVatMaskedWord σ I ::
        cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (cashIlkWord I) ⟨15⟩
        (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (cashVatMaskedWord σ I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g s0 ⟨9854⟩
      (gasWord :: cashVatMaskedWord σ I :: ⟨0⟩ ::
        cashFluxOutPtr :: cashFluxInSize :: cashFluxOutPtr :: cashFluxOutSize ::
        cashFluxEndPtr :: cashFluxSelectorWord :: cashVatMaskedWord σ I ::
        cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (cashFluxCalldataMem σ I
        (twoWordHashMem (cashIlkWord I) ⟨15⟩
          (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem)))
      (UInt256.ofNat 9) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd9839⟩ := RD.endCashFluxExtcodesizeGuard rd
  obtain ⟨gasWord, k', C', rd9854⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨9839⟩) (okPc := ⟨9851⟩)
      rd9839 hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by evm_ov)
  exact ⟨gasWord, k', C', rd9854⟩

theorem RD.endCashFluxNoCode
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨9758⟩
      (cashAmtWord σ I :: cashSourceWord I :: UInt256.ofNat I.codeOwner.val ::
        cashIlkWord I :: cashFluxSelectorWord :: cashVatMaskedWord σ I ::
        cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (cashIlkWord I) ⟨15⟩
        (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (cashVatMaskedWord σ I) = ⟨0⟩) :
    RDrev endBytecode g s0 := by
  obtain ⟨_, _, rd9839⟩ := RD.endCashFluxExtcodesizeGuard rd
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨9839⟩) (okPc := ⟨9851⟩)
    rd9839 hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

set_option maxHeartbeats 3000000 in
theorem RD.endCashFluxPostCall
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {k C : ℕ}
    (rd : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9758⟩
      (cashAmtWord σ I :: cashSourceWord I :: UInt256.ofNat I.codeOwner.val ::
        cashIlkWord I :: cashFluxSelectorWord :: cashVatMaskedWord σ I ::
        cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (cashIlkWord I) ⟨15⟩
        (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (cashVatMaskedWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD endBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9855⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: cashFluxEndPtr :: cashFluxSelectorWord ::
          cashVatMaskedWord σ I :: cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
        (cashFluxPostCallMem σ I
          (twoWordHashMem (cashIlkWord I) ⟨15⟩
            (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem)) out)
        (UInt256.ofNat 9) out (cA', σ') k' C'
    ∧ typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (cashVatMaskedWord σ I).toNat)) "flux" 0
        [cashIlkValue I, .address I.codeOwner, .address I.source,
          .int (Int.ofNat (cashAmtWord σ I).toNat)]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, out) I.perm
    ∧ out.size < UInt256.size := by
  let mem0 := twoWordHashMem (cashIlkWord I) ⟨15⟩
    (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem)
  have hmem0 : mem0.size = 96 := by
    unfold mem0
    exact twoWordHashMem_size_96 (cashIlkWord I) ⟨15⟩
      (twoWordHashMem_size_96 (cashIlkWord I) ⟨15⟩ solcFreePtrMem_size)
  obtain ⟨_, _, _, rd9854⟩ := RD.endCashFluxCall (by simpa [mem0] using rd) hcodeSize
  obtain ⟨cA', σ', z, out, A_in, callGas, k9855, C9855, hΘcash, rd9855raw, houtsz⟩ :=
    RD.call rd9854 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘcash
  refine ⟨cA', σ', z, out, A', k9855, C9855, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
          cashFluxOutPtr.toNat cashFluxInSize.toNat)
          cashFluxOutPtr.toNat cashFluxOutSize.toNat) = UInt256.ofNat 9 := by
      unfold cashFluxOutPtr cashFluxInSize cashFluxOutSize
      native_decide
    simpa [mem0, cashFluxPostCallMem] using haw ▸ rd9855raw
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := I.perm) (targetWord := cashVatMaskedWord σ I)
      (mem := cashFluxCalldataMem σ I mem0) (inOff := cashFluxOutPtr)
      (inSize := cashFluxInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      ?_ (cashFluxEncode_eq σ I hmem0) ?_
    · exact (evmAddress_ofNat_toNat_eq_ofUInt256 (cashVatMaskedWord σ I)).symm
    · simpa [initState] using hΘ

theorem RD.endCashFluxCallFailure
    {cA σ I} {g : Sat256} {s0 : State} {mem o : ByteArray} {aw : UInt256}
    {k C : ℕ} {rest : List UInt256}
    (rd : RD endBytecode I g s0 ⟨9855⟩
      (⟨0⟩ :: rest) mem aw o (cA, σ) k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev endBytecode g s0 := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨9855⟩) (okPc := ⟨9871⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hosz hov

theorem RD.endCashFluxDepthLimitReverts
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨9758⟩
      (cashAmtWord σ I :: cashSourceWord I :: UInt256.ofNat I.codeOwner.val ::
        cashIlkWord I :: cashFluxSelectorWord :: cashVatMaskedWord σ I ::
        cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (twoWordHashMem (cashIlkWord I) ⟨15⟩
        (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (cashVatMaskedWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    RDrev endBytecode g s0 := by
  let mem0 := twoWordHashMem (cashIlkWord I) ⟨15⟩
    (twoWordHashMem (cashIlkWord I) ⟨15⟩ solcFreePtrMem)
  have hmem0 : mem0.size = 96 := by
    unfold mem0
    exact twoWordHashMem_size_96 (cashIlkWord I) ⟨15⟩
      (twoWordHashMem_size_96 (cashIlkWord I) ⟨15⟩ solcFreePtrMem_size)
  have hread64 :
      mem0.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    unfold mem0
    exact twoWordHashMem_read64 (cashIlkWord I) ⟨15⟩
      (twoWordHashMem_size_96 (cashIlkWord I) ⟨15⟩ solcFreePtrMem_size)
      (twoWordHashMem_read64 (cashIlkWord I) ⟨15⟩ solcFreePtrMem_size
        solcFreePtrMem_read64)
  obtain ⟨_, _, _, rd9854⟩ := RD.endCashFluxCall (by simpa [mem0] using rd) hcodeSize
  obtain ⟨k9855, C9855, rd9855raw⟩ :=
    RD.callDepthLimit rd9854 (by native_decide) hdepth (by simp)
  have hmin : (min cashFluxOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    unfold cashFluxOutSize
    rw [← u256_ofNat_toNat (UInt256.ofNat ByteArray.empty.size)]
    exact umin_ofNat_right_toNat_of_ge (by norm_num [UInt256.size]) (Nat.zero_le _)
      (UInt256.ofNat ByteArray.empty.size).val.isLt
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
        cashFluxOutPtr.toNat cashFluxInSize.toNat)
        cashFluxOutPtr.toNat cashFluxOutSize.toNat) = UInt256.ofNat 9 := by
    unfold cashFluxOutPtr cashFluxInSize cashFluxOutSize
    native_decide
  have rd9855 : RD endBytecode I g s0 ⟨9855⟩
      (⟨0⟩ :: cashFluxEndPtr :: cashFluxSelectorWord :: cashVatMaskedWord σ I ::
        cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (cashFluxPostCallMem σ I mem0 ByteArray.empty) (UInt256.ofNat 9) ByteArray.empty
      (cA, σ) k9855 C9855 := by
    simpa [cashFluxPostCallMem, hmin] using haw ▸ rd9855raw
  exact RD.endCashFluxCallFailure rd9855 (by native_decide) (by simp)

theorem RD.endCashFluxCallSuccessToOut
    {cA σ I} {g : Sat256} {s0 : State} {mem o : ByteArray} {aw : UInt256}
    {k C : ℕ} {d0 d1 d2 : UInt256} {R : List UInt256}
    (rd : RD endBytecode I g s0 ⟨9855⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: R) mem aw o (cA, σ) k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD endBytecode I g s0 ⟨9873⟩
      (d0 :: d1 :: d2 :: R) mem aw o (cA, σ) k' C' := by
  exact RD.uniswapCallSuccessGuardOk (pc := ⟨9855⟩) (okPc := ⟨9871⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simpa only [List.length_cons] using hov)

theorem RD.endCashLoadOutToAdd
    {cA σ I} {g : Sat256} {s0 : State} {mem o : ByteArray}
    {k C : ℕ} {sel vatWord : UInt256}
    (rd : RD endBytecode I g s0 ⟨9873⟩
      (cashFluxEndPtr :: cashFluxSelectorWord :: vatWord ::
        cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) o (cA, σ) k C)
    (hmem : mem.size = 260) :
    ∃ k' C', RD endBytecode I g s0 ⟨10092⟩
      (cashWadWord I :: cashOutWord σ I :: ⟨9911⟩ ::
        cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (cashOutHashMem I mem) (UInt256.ofNat 9) o (cA, σ) k' C' := by
  have hinner :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC ((twoWordHashMem (cashIlkWord I) ⟨17⟩ mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨17⟩ (cashIlkWord I) := by
    exact cash_twoWordHashMem_solcMappingSlot_of_ge64 ⟨17⟩ (cashIlkWord I)
      (by rw [hmem]; omega)
  have hslot :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC ((cashOutHashMem I mem).readWithPadding 0 64))) =
        cashOutStorageSlot I := by
    unfold cashOutHashMem
    rw [cash_twoWordHashMem_solcMappingSlot_of_ge64
      (solcMappingSlot ⟨17⟩ (cashIlkWord I)) (cashSourceWord I)]
    · rfl
    · rw [cash_twoWordHashMem_size_of_ge64 (cashIlkWord I) ⟨17⟩ (by rw [hmem]; omega),
        hmem]
      omega
  have rd9891pre := evm_run rd with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (cashIlkWord I) mem) (UInt256.ofNat 9)
      (by native_decide) mem_cost (by
        simp [wordAt0Mem])
      (by native_decide) (by evm_ov),
    raw push1 ⟨17⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (twoWordHashMem (cashIlkWord I) ⟨17⟩ mem) (UInt256.ofNat 9)
      (by native_decide) mem_cost (by
        simp [twoWordHashMem, wordAt32Mem,
          show (⟨32⟩ : UInt256).toNat = 32 from by native_decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rd9892 := rd9891pre.keccak256 0 (solcMappingSlot ⟨17⟩ (cashIlkWord I))
    (UInt256.ofNat 9) (by native_decide) mem_cost hinner (by native_decide) (by evm_ov)
  have rd9899pre := evm_run rd9892 with [
    raw caller (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw mstore 0
      (wordAt0Mem (cashSourceWord I) (twoWordHashMem (cashIlkWord I) ⟨17⟩ mem))
      (UInt256.ofNat 9) (by native_decide) mem_cost (by
        simp [wordAt0Mem, cashSourceWord])
      (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw mstore 0 (cashOutHashMem I mem) (UInt256.ofNat 9)
      (by native_decide) mem_cost (by
        simp [cashOutHashMem, twoWordHashMem, wordAt32Mem,
          show (⟨32⟩ : UInt256).toNat = 32 from by native_decide])
      (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd9900 := rd9899pre.keccak256 0 (cashOutStorageSlot I)
    (UInt256.ofNat 9) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨k9901, C9901, rd9901raw⟩ := rd9900.sload (by native_decide) (by evm_ov)
  have rd9901 : RD endBytecode I g s0 ⟨9901⟩
      (cashOutWord σ I :: vatWord :: cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (cashOutHashMem I mem) (UInt256.ofNat 9) o (cA, σ) k9901 C9901 := by
    simpa [cashOutWord, endSlotWord, cashOutStorageSlot] using rd9901raw
  have rd10092 := evm_run rd9901 with [
    raw push2 ⟨9911⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨10092⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, rd10092.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem RD.endCashOutAddSuccess
    {cA σ I} {g : Sat256} {s0 : State} {mem o : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨10092⟩
      (cashWadWord I :: cashOutWord σ I :: ⟨9911⟩ ::
        cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) o (cA, σ) k C)
    (hfit : (cashOutWord σ I).toNat + (cashWadWord I).toNat < UInt256.size) :
    ∃ k' C', RD endBytecode I g s0 ⟨9911⟩
      ((cashOutWord σ I + cashWadWord I) ::
        cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) o (cA, σ) k' C' := by
  have haddNat :
      (cashOutWord σ I + cashWadWord I).toNat =
        (cashOutWord σ I).toNat + (cashWadWord I).toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hfit]
  have haddNat' :
      (cashWadWord I + cashOutWord σ I).toNat =
        (cashWadWord I).toNat + (cashOutWord σ I).toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt (by omega)]
  have hlt : UInt256.lt (cashWadWord I + cashOutWord σ I) (cashOutWord σ I) = ⟨0⟩ :=
    ult_zero (by rw [haddNat']; omega)
  have rd10099pre := evm_run rd with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov)]
  rw [hlt] at rd10099pre
  have rd10103pre := evm_run rd10099pre with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have rd10108raw :=
    rd10103pre.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)
  have rd9911 := evm_run (rd10108raw.jumpdest (by native_decide) (by evm_ov)) with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by
    simpa [u256_add_comm (cashWadWord I) (cashOutWord σ I)] using rd9911⟩

theorem RD.endCashOutAddOverflow
    {cA σ I} {g : Sat256} {s0 : State} {mem o : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨10092⟩
      (cashWadWord I :: cashOutWord σ I :: ⟨9911⟩ ::
        cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) o (cA, σ) k C)
    (hover : UInt256.size ≤ (cashOutWord σ I).toNat + (cashWadWord I).toNat) :
    RDrev endBytecode g s0 := by
  have hsum_lt2 :
      (cashOutWord σ I).toNat + (cashWadWord I).toNat < 2 * UInt256.size := by
    have hout : (cashOutWord σ I).toNat < UInt256.size := (cashOutWord σ I).val.isLt
    have hwad : (cashWadWord I).toNat < UInt256.size := (cashWadWord I).val.isLt
    omega
  have hmod :
      ((cashOutWord σ I).toNat + (cashWadWord I).toNat) % UInt256.size =
        (cashOutWord σ I).toNat + (cashWadWord I).toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat :
      (cashOutWord σ I + cashWadWord I).toNat =
        (cashOutWord σ I).toNat + (cashWadWord I).toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt : UInt256.lt (cashOutWord σ I + cashWadWord I) (cashOutWord σ I) = ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hout : (cashOutWord σ I).toNat < UInt256.size := (cashOutWord σ I).val.isLt
    have hwad : (cashWadWord I).toNat < UInt256.size := (cashWadWord I).val.isLt
    omega
  have rd10099pre := evm_run rd with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov)]
  rw [show cashWadWord I + cashOutWord σ I = cashOutWord σ I + cashWadWord I from
    u256_add_comm (cashWadWord I) (cashOutWord σ I)] at rd10099pre
  rw [hlt] at rd10099pre
  have rd10103pre := evm_run rd10099pre with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have rd10104 := rd10103pre.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.uniswapPush1Dup1Revert0 rd10104
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.endCashFluxCallSuccessAddOverflow
    {cA σStack σCall I} {g : Sat256} {s0 : State} {base out : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨9855⟩
      (⟨1⟩ :: cashFluxEndPtr :: cashFluxSelectorWord ::
        cashVatMaskedWord σStack I :: cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (cashFluxPostCallMem σStack I base out) (UInt256.ofNat 9) out
      (cA, σCall) k C)
    (hbase : base.size = 96)
    (hover : UInt256.size ≤ (cashOutWord σCall I).toNat + (cashWadWord I).toNat) :
    RDrev endBytecode g s0 := by
  have hmem := cashFluxPostCallMem_size σStack I out hbase
  obtain ⟨k9873, C9873, rd9873⟩ :=
    RD.endCashFluxCallSuccessToOut rd (by simp)
  obtain ⟨k10092, C10092, rd10092⟩ :=
    RD.endCashLoadOutToAdd rd9873 hmem
  exact RD.endCashOutAddOverflow rd10092 hover

theorem RD.endCashStoreOut
    {cA σ I} {g : Sat256} {s0 : State} {mem o : ByteArray}
    {k C : ℕ} {sel outNew : UInt256}
    (rd : RD endBytecode I g s0 ⟨9911⟩
      (outNew :: cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) o (cA, σ) k C)
    (hperm : I.perm = true)
    (hmem : mem.size = 260) :
    ∃ k' C', RD endBytecode I g s0 ⟨9941⟩
      (solcMappingSlot ⟨17⟩ (cashIlkWord I) :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ ::
        outNew :: cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (cashOutHashMem I mem) (UInt256.ofNat 9) o
      (cA, sstoreAccountMap I.codeOwner σ (cashOutStorageSlot I) outNew) k' C' := by
  have hinner :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC ((twoWordHashMem (cashIlkWord I) ⟨17⟩ mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨17⟩ (cashIlkWord I) := by
    exact cash_twoWordHashMem_solcMappingSlot_of_ge64 ⟨17⟩ (cashIlkWord I)
      (by rw [hmem]; omega)
  have hslot :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC ((cashOutHashMem I mem).readWithPadding 0 64))) =
        cashOutStorageSlot I := by
    unfold cashOutHashMem
    rw [cash_twoWordHashMem_solcMappingSlot_of_ge64
      (solcMappingSlot ⟨17⟩ (cashIlkWord I)) (cashSourceWord I)]
    · rfl
    · rw [cash_twoWordHashMem_size_of_ge64 (cashIlkWord I) ⟨17⟩ (by rw [hmem]; omega),
        hmem]
      omega
  have rd9928pre := evm_run rd with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (cashIlkWord I) mem) (UInt256.ofNat 9)
      (by native_decide) mem_cost (by
        simp [wordAt0Mem])
      (by native_decide) (by evm_ov),
    raw push1 ⟨17⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (twoWordHashMem (cashIlkWord I) ⟨17⟩ mem) (UInt256.ofNat 9)
      (by native_decide) mem_cost (by
        simp [twoWordHashMem, wordAt32Mem,
          show (⟨32⟩ : UInt256).toNat = 32 from by native_decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rd9929 := rd9928pre.keccak256 0 (solcMappingSlot ⟨17⟩ (cashIlkWord I))
    (UInt256.ofNat 9) (by native_decide) mem_cost hinner (by native_decide) (by evm_ov)
  have rd9937pre := evm_run rd9929 with [
    raw caller (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw mstore 0
      (wordAt0Mem (cashSourceWord I) (twoWordHashMem (cashIlkWord I) ⟨17⟩ mem))
      (UInt256.ofNat 9) (by native_decide) mem_cost (by
        simp [wordAt0Mem, cashSourceWord])
      (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw mstore 0 (cashOutHashMem I mem) (UInt256.ofNat 9)
      (by native_decide) mem_cost (by
        simp [cashOutHashMem, twoWordHashMem, wordAt32Mem,
          show (⟨32⟩ : UInt256).toNat = 32 from by native_decide])
      (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rd9938 := rd9937pre.keccak256 0 (cashOutStorageSlot I)
    (UInt256.ofNat 9) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  have rd9940pre := evm_run rd9938 with [
    raw dup6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k9941, C9941, rd9941⟩ := rd9940pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨k9941, C9941, rd9941⟩

theorem RD.endCashBagGuardOk
    {cA σ I} {g : Sat256} {s0 : State} {mem o : ByteArray}
    {k C : ℕ} {sel outNew : UInt256}
    (rd : RD endBytecode I g s0 ⟨9941⟩
      (solcMappingSlot ⟨17⟩ (cashIlkWord I) :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ ::
        outNew :: cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (cashOutHashMem I mem) (UInt256.ofNat 9) o (cA, σ) k C)
    (hmem : mem.size = 260)
    (hguard : UInt256.lt (cashBagWord σ I) outNew = ⟨0⟩) :
    ∃ k' C', RD endBytecode I g s0 ⟨10033⟩
      (cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (cashOutRestoredMem I mem) (UInt256.ofNat 9) o (cA, σ) k' C' := by
  have hbagSlot :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC ((cashBagHashMem I (cashOutHashMem I mem)).readWithPadding 0 64))) =
        cashBagStorageSlot I := by
    rw [cashBagHashMemOfOut_read0_64 I hmem]
    unfold cashBagStorageSlot solcMappingSlot
    exact mappingSlot_single (cashSourceWord I) (⟨16⟩ : UInt256)
  have rd9946pre := evm_run rd with [
    raw push1 ⟨16⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw mstore 0 (cashBagHashMem I (cashOutHashMem I mem)) (UInt256.ofNat 9)
      (by native_decide) mem_cost (by
        simp [cashBagHashMem, cashOutHashMem, twoWordHashMem, wordAt32Mem,
          show (⟨32⟩ : UInt256).toNat = 32 from by native_decide])
      (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  have rd9947 := rd9946pre.keccak256 0 (cashBagStorageSlot I)
    (UInt256.ofNat 9) (by native_decide) mem_cost hbagSlot (by native_decide) (by evm_ov)
  obtain ⟨k9948, C9948, rd9948raw⟩ := rd9947.sload (by native_decide) (by evm_ov)
  have rd9948 : RD endBytecode I g s0 ⟨9948⟩
      (cashBagWord σ I :: ⟨32⟩ :: solcMappingSlot ⟨17⟩ (cashIlkWord I) ::
        outNew :: cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (cashBagHashMem I (cashOutHashMem I mem)) (UInt256.ofNat 9) o
      (cA, σ) k9948 C9948 := by
    simpa [cashBagWord, endSlotWord, cashBagStorageSlot] using rd9948raw
  have rd9951pre := evm_run rd9948 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 (cashOutRestoredMem I mem) (UInt256.ofNat 9)
      (by native_decide) mem_cost (by
        simp [cashOutRestoredMem, cashBagHashMem, cashOutHashMem, twoWordHashMem, wordAt32Mem,
          show (⟨32⟩ : UInt256).toNat = 32 from by native_decide])
      (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov)]
  rw [hguard] at rd9951pre
  have rd9956pre := evm_run rd9951pre with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨10033⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, rd9956pre.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)⟩

theorem RD.endCashBagGuardReverts
    {cA σ I} {g : Sat256} {s0 : State} {mem o : ByteArray}
    {k C : ℕ} {sel outNew : UInt256}
    (rd : RD endBytecode I g s0 ⟨9941⟩
      (solcMappingSlot ⟨17⟩ (cashIlkWord I) :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ ::
        outNew :: cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (cashOutHashMem I mem) (UInt256.ofNat 9) o (cA, σ) k C)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hguard : UInt256.lt (cashBagWord σ I) outNew = ⟨1⟩) :
    RDrev endBytecode g s0 := by
  have hbagSlot :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC ((cashBagHashMem I (cashOutHashMem I mem)).readWithPadding 0 64))) =
        cashBagStorageSlot I := by
    rw [cashBagHashMemOfOut_read0_64 I hmem]
    unfold cashBagStorageSlot solcMappingSlot
    exact mappingSlot_single (cashSourceWord I) (⟨16⟩ : UInt256)
  have rd9946pre := evm_run rd with [
    raw push1 ⟨16⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw mstore 0 (cashBagHashMem I (cashOutHashMem I mem)) (UInt256.ofNat 9)
      (by native_decide) mem_cost (by
        simp [cashBagHashMem, cashOutHashMem, twoWordHashMem, wordAt32Mem,
          show (⟨32⟩ : UInt256).toNat = 32 from by native_decide])
      (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  have rd9947 := rd9946pre.keccak256 0 (cashBagStorageSlot I)
    (UInt256.ofNat 9) (by native_decide) mem_cost hbagSlot (by native_decide) (by evm_ov)
  obtain ⟨k9948, C9948, rd9948raw⟩ := rd9947.sload (by native_decide) (by evm_ov)
  have rd9948 : RD endBytecode I g s0 ⟨9948⟩
      (cashBagWord σ I :: ⟨32⟩ :: solcMappingSlot ⟨17⟩ (cashIlkWord I) ::
        outNew :: cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (cashBagHashMem I (cashOutHashMem I mem)) (UInt256.ofNat 9) o
      (cA, σ) k9948 C9948 := by
    simpa [cashBagWord, endSlotWord, cashBagStorageSlot] using rd9948raw
  have rd9951pre := evm_run rd9948 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 (cashOutRestoredMem I mem) (UInt256.ofNat 9)
      (by native_decide) mem_cost (by
        simp [cashOutRestoredMem, cashBagHashMem, cashOutHashMem, twoWordHashMem, wordAt32Mem,
          show (⟨32⟩ : UInt256).toNat = 32 from by native_decide])
      (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov)]
  rw [hguard] at rd9951pre
  have rd9957pre := evm_run rd9951pre with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨10033⟩ (by native_decide) (by evm_ov)]
  exact RD.cashErrorStringRevertTailPush32Aw9
    (pc := ⟨9957⟩)
    (len := ⟨28⟩)
    (word :=
      ⟨31404631182226403021804016008925091983348064744006520697614593646256157884416⟩)
    (rd9957pre.jumpiNT (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega))
    (by
      unfold solcErrorStringRevertTailPush32Wf
      repeat' first | apply And.intro | native_decide)
    (cashOutRestoredMem_size I hmem)
    (cashOutRestoredMem_read64 I hmem hread64)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.endCashLogAndReturn
    {cA σ I} {g : Sat256} {s0 : State} {mem o : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨10033⟩
      (cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 9) o (cA, σ) k C)
    (hperm : I.perm = true)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDret endBytecode g s0 (cA, σ) ByteArray.empty := by
  have hlogRead64 :
      (cashLogMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
    cashLogMem_read64 I hmem hread64
  have rd10042pre := evm_run rd with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have rd10038 := RD.mload 0 ⟨128⟩ (UInt256.ofNat 9) rd10042pre
    (by native_decide) mem_cost
    (mloadFreePtrValue (by rw [hmem]; native_decide) (by native_decide) hread64)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd10042pre' := evm_run rd10038 with [
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (cashLogMem I mem) (UInt256.ofNat 9)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd10043 := RD.mload 0 ⟨128⟩ (UInt256.ofNat 9) rd10042pre'
    (by native_decide) mem_cost
    (mloadFreePtrValue (by
      unfold cashLogMem
      rw [toByteArray_write32_size_of_le mem (cashWadWord I) 128 260 260 hmem
        (by rw [hmem]; native_decide) (by native_decide)]
      native_decide) (by native_decide) hlogRead64)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd10088pre := evm_run rd10043 with [
    raw caller (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd10080 := rd10088pre.pushConst
    (⟨61762761858481124507418629652158970992922529429700365484370387914003088643017⟩ :
      UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd10088 := evm_run rd10080 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hlogLen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨32⟩ = ⟨32⟩ := by
    native_decide
  have rd10089 := RD.log3
    (a := ⟨128⟩) (b := ⟨32⟩)
    (c := ⟨61762761858481124507418629652158970992922529429700365484370387914003088643017⟩)
    (d := cashIlkWord I) (e := cashSourceWord I)
    (t := [cashWadWord I, cashIlkWord I, ⟨562⟩, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 9).toNat (⟨128⟩ : UInt256).toNat
        (⟨32⟩ : UInt256).toNat))
    (by simpa [cashSourceWord, hlogLen] using rd10088)
    (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd10091pre := evm_run rd10089 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd562 := RD.jump (a := ⟨562⟩) (t := [sel]) rd10091pre
    (by native_decide) (by jump_dest) (by evm_ov)
  have rd563 := RD.jumpdest (pc := ⟨562⟩) (stk := [sel]) rd562
    (by native_decide) (by evm_ov)
  exact RD.stop rd563 (by native_decide) (by evm_ov)

theorem RD.endCashFluxCallSuccessReturn
    {cA σStack σCall I} {g : Sat256} {s0 : State} {base out : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨9855⟩
      (⟨1⟩ :: cashFluxEndPtr :: cashFluxSelectorWord ::
        cashVatMaskedWord σStack I :: cashWadWord I :: cashIlkWord I :: ⟨562⟩ :: [sel])
      (cashFluxPostCallMem σStack I base out) (UInt256.ofNat 9) out
      (cA, σCall) k C)
    (hperm : I.perm = true)
    (hbase : base.size = 96)
    (hbaseRead64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hfit : (cashOutWord σCall I).toNat + (cashWadWord I).toNat < UInt256.size)
    (hguard :
      UInt256.lt
        (cashBagWord
          (sstoreAccountMap I.codeOwner σCall (cashOutStorageSlot I)
            (cashOutWord σCall I + cashWadWord I)) I)
        (cashOutWord σCall I + cashWadWord I) = ⟨0⟩) :
    RDret endBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σCall (cashOutStorageSlot I)
        (cashOutWord σCall I + cashWadWord I))
      ByteArray.empty := by
  have hmem := cashFluxPostCallMem_size σStack I out hbase
  have hread64 := cashFluxPostCallMem_read64 σStack I out hbase hbaseRead64
  obtain ⟨k9873, C9873, rd9873⟩ :=
    RD.endCashFluxCallSuccessToOut rd (by simp)
  obtain ⟨k10092, C10092, rd10092⟩ :=
    RD.endCashLoadOutToAdd rd9873 hmem
  obtain ⟨k9911, C9911, rd9911⟩ :=
    RD.endCashOutAddSuccess rd10092 hfit
  have houtMemSize := cashOutHashMem_size I hmem
  have houtRead64 := cashOutHashMem_read64 I hmem hread64
  obtain ⟨k9941, C9941, rd9941⟩ :=
    RD.endCashStoreOut rd9911 hperm houtMemSize
  obtain ⟨k10033, C10033, rd10033⟩ :=
    RD.endCashBagGuardOk rd9941 houtMemSize hguard
  exact RD.endCashLogAndReturn rd10033 hperm
    (cashOutRestoredMem_size I houtMemSize)
    (cashOutRestoredMem_read64 I houtMemSize houtRead64)

theorem endCashBodyCore : endBodyObligation 31 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  sorry

end Benchmarks.Dss.End
