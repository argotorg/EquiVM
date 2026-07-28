import Benchmarks.Dss.DaiJoin.Mul

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.DaiJoin

/-! ## Shared `join(address,uint256)` calldata words and trace helpers -/

abbrev joinUsrWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev joinUsrMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (joinUsrWord I)

abbrev joinWadWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev joinUsrValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (joinUsrWord I).toNat)

abbrev joinWadValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (joinWadWord I).toNat)

abbrev joinStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "usr" (joinUsrValue I)).insert "wad" (joinWadValue I)

abbrev joinMoveSelectorPlainWord : UInt256 := ⟨0xbb35783b⟩

abbrev joinMoveSelectorShiftedWord : UInt256 :=
  UInt256.shiftLeft joinMoveSelectorPlainWord ⟨224⟩

noncomputable def joinMoveSelectorMem (mem : ByteArray) : ByteArray :=
  joinMoveSelectorShiftedWord.toByteArray.write 0 mem 128 32

noncomputable def joinMoveThisMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (UInt256.ofNat I.codeOwner.val).toByteArray.write 0 (joinMoveSelectorMem mem) 132 32

noncomputable def joinMoveUsrMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (joinUsrMaskedWord I).toByteArray.write 0 (joinMoveThisMem I mem) 164 32

noncomputable def joinMoveCalldataMem (I : ExecutionEnv) (rad : UInt256)
    (mem : ByteArray) : ByteArray :=
  rad.toByteArray.write 0 (joinMoveUsrMem I mem) 196 32

theorem joinMoveSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (joinMoveSelectorMem mem).size = 160 := by
  unfold joinMoveSelectorMem
  exact toByteArray_write32_size_of_ge mem joinMoveSelectorShiftedWord 128 96 160 hmem
    (by omega) (by native_decide) (by omega)

theorem joinMoveThisMem_size (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 96) :
    (joinMoveThisMem I mem).size = 164 := by
  unfold joinMoveThisMem
  exact toByteArray_write32_size_of_le (joinMoveSelectorMem mem)
    (UInt256.ofNat I.codeOwner.val) 132 160 164 (joinMoveSelectorMem_size hmem)
    (by rw [joinMoveSelectorMem_size hmem]; omega) (by omega)

theorem joinMoveUsrMem_size (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 96) :
    (joinMoveUsrMem I mem).size = 196 := by
  unfold joinMoveUsrMem
  exact toByteArray_write32_size_of_le (joinMoveThisMem I mem) (joinUsrMaskedWord I)
    164 164 196 (joinMoveThisMem_size I hmem)
    (by rw [joinMoveThisMem_size I hmem]) (by omega)

theorem joinMoveCalldataMem_size (I : ExecutionEnv) (rad : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (joinMoveCalldataMem I rad mem).size = 228 := by
  unfold joinMoveCalldataMem
  exact toByteArray_write32_size_of_le (joinMoveUsrMem I mem) rad
    196 196 228 (joinMoveUsrMem_size I hmem)
    (by rw [joinMoveUsrMem_size I hmem]) (by omega)

theorem joinMoveSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (joinMoveSelectorMem mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold joinMoveSelectorMem
  rw [toByteArray_write_read_below_of_gap joinMoveSelectorShiftedWord mem 128 64
    (by rw [hmem]) (by omega) (by rw [hmem]; native_decide)]
  exact hread64

theorem joinMoveThisMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (joinMoveThisMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold joinMoveThisMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [joinMoveSelectorMem_size hmem]; omega) (by omega)]
  exact joinMoveSelectorMem_read64 hmem hread64

theorem joinMoveUsrMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (joinMoveUsrMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold joinMoveUsrMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [joinMoveThisMem_size I hmem]) (by norm_num)]
  exact joinMoveThisMem_read64 I hmem hread64

theorem joinMoveCalldataMem_read64 (I : ExecutionEnv) (rad : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (joinMoveCalldataMem I rad mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold joinMoveCalldataMem
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
    (by rw [joinMoveUsrMem_size I hmem]) (by omega)]
  exact joinMoveUsrMem_read64 I hmem hread64

theorem joinMoveCalldataMem_read128_100 (I : ExecutionEnv) (rad : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (joinMoveCalldataMem I rad mem).readWithPadding 128 100 =
      vatMoveSelector ++ (UInt256.ofNat I.codeOwner.val).toByteArray ++
        (joinUsrMaskedWord I).toByteArray ++ rad.toByteArray := by
  let final := joinMoveCalldataMem I rad mem
  have hfinalSize : final.size = 228 := by
    dsimp [final]
    exact joinMoveCalldataMem_size I rad hmem
  have hselectorRead : final.readWithPadding 128 4 = vatMoveSelector := by
    dsimp [final]
    unfold joinMoveCalldataMem
    rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
      (by rw [joinMoveUsrMem_size I hmem]) (by omega)
      (by rw [joinMoveUsrMem_size I hmem]; omega) (by omega) (by norm_num)]
    unfold joinMoveUsrMem
    rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
      (by rw [joinMoveThisMem_size I hmem]) (by omega)
      (by rw [joinMoveThisMem_size I hmem]; omega) (by omega) (by norm_num)]
    unfold joinMoveThisMem
    rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
      (by rw [joinMoveSelectorMem_size hmem]; omega) (by omega)
      (by rw [joinMoveSelectorMem_size hmem]; omega) (by omega) (by norm_num)]
    unfold joinMoveSelectorMem
    rw [toByteArray_write_read_window_of_gap joinMoveSelectorShiftedWord mem 128 0 4
      (by norm_num) (by norm_num) (by norm_num) (by rw [hmem]; native_decide)]
    unfold joinMoveSelectorShiftedWord joinMoveSelectorPlainWord vatMoveSelector selectorBytes
    native_decide
  have hthisRead :
      final.readWithPadding 132 32 = (UInt256.ofNat I.codeOwner.val).toByteArray := by
    dsimp [final]
    unfold joinMoveCalldataMem
    rw [write32_read_below_len _ _ 196 132 32 (by rw [toByteArray_size])
      (by rw [joinMoveUsrMem_size I hmem]) (by omega)
      (by rw [joinMoveUsrMem_size I hmem]; omega) (by omega) (by norm_num)]
    unfold joinMoveUsrMem
    rw [write32_read_below_len _ _ 164 132 32 (by rw [toByteArray_size])
      (by rw [joinMoveThisMem_size I hmem]) (by omega)
      (by rw [joinMoveThisMem_size I hmem]) (by omega) (by norm_num)]
    unfold joinMoveThisMem
    rw [write32_read_prefix_len _ _ 132 32 (by rw [toByteArray_size])
      (by rw [joinMoveSelectorMem_size hmem]; omega) (by omega) (by omega)
      (by norm_num)]
    rw [toByteArray_extract_all]
  have husrRead : final.readWithPadding 164 32 = (joinUsrMaskedWord I).toByteArray := by
    dsimp [final]
    unfold joinMoveCalldataMem
    rw [write32_read_below_len _ _ 196 164 32 (by rw [toByteArray_size])
      (by rw [joinMoveUsrMem_size I hmem]) (by omega)
      (by rw [joinMoveUsrMem_size I hmem]) (by omega) (by norm_num)]
    unfold joinMoveUsrMem
    rw [write32_read_prefix_len _ _ 164 32 (by rw [toByteArray_size])
      (by rw [joinMoveThisMem_size I hmem]) (by omega) (by omega)
      (by norm_num)]
    rw [toByteArray_extract_all]
  have hradRead : final.readWithPadding 196 32 = rad.toByteArray := by
    dsimp [final]
    unfold joinMoveCalldataMem
    rw [write32_read_back _ _ 196 (by rw [toByteArray_size])
      (by rw [joinMoveUsrMem_size I hmem])]
    rw [toByteArray_extract_all]
  rw [readWithPadding_eq_extract' final 128 100 (by norm_num) (by norm_num)
    (by rw [hfinalSize])]
  have hselectorExt : final.extract 128 132 = vatMoveSelector := by
    rw [← readWithPadding_eq_extract' final 128 4 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hselectorRead
  have hthisExt : final.extract 132 164 = (UInt256.ofNat I.codeOwner.val).toByteArray := by
    rw [← readWithPadding_eq_extract' final 132 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hthisRead
  have husrExt : final.extract 164 196 = (joinUsrMaskedWord I).toByteArray := by
    rw [← readWithPadding_eq_extract' final 164 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact husrRead
  have hradExt : final.extract 196 228 = rad.toByteArray := by
    rw [← readWithPadding_eq_extract' final 196 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize])]
    exact hradRead
  have hsplit : final.extract 128 228 =
      final.extract 128 132 ++ final.extract 132 164 ++ final.extract 164 196 ++
        final.extract 196 228 := by
    rw [show final.extract 128 228 = final.extract 128 132 ++ final.extract 132 228 by
      rw [ByteArray.extract_append_extract]; norm_num]
    rw [show final.extract 132 228 = final.extract 132 164 ++ final.extract 164 228 by
      rw [ByteArray.extract_append_extract]; norm_num]
    rw [show final.extract 164 228 = final.extract 164 196 ++ final.extract 196 228 by
      rw [ByteArray.extract_append_extract]; norm_num]
    simp
  rw [hsplit, hselectorExt, hthisExt, husrExt, hradExt]

theorem joinMoveEncode_eq (I : ExecutionEnv) (rad : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    config.externalABI.encode? "move"
        [.address I.codeOwner, .address (AccountAddress.ofUInt256 (joinUsrMaskedWord I)),
          .int (Int.ofNat rad.toNat)] =
      some ((joinMoveCalldataMem I rad mem).readWithPadding 128 100) := by
  rw [joinMoveCalldataMem_read128_100 I rad hmem]
  have hthisLen :
      (EVM.Word.toBytesBE (UInt256.ofNat I.codeOwner.val)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (UInt256.ofNat I.codeOwner.val)
  have husrLen : (EVM.Word.toBytesBE (joinUsrMaskedWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (joinUsrMaskedWord I)
  have hradLt : rad.toNat < EVM.twoPow 256 := by
    simp [UInt256.toNat, UInt256.size, EVM.twoPow]
  have hradWord : EVM.word rad.toNat = rad := by
    simpa [UInt256.ofNat] using u256_ofNat_toNat rad
  have hthisWord : EVM.word I.codeOwner.val = UInt256.ofNat I.codeOwner.val := by
    rfl
  have husrCanon : (joinUsrMaskedWord I).toNat < EVM.addressModulus := by
    rw [joinUsrMaskedWord, u256_land_comm]
    exact solcAddrMask_result_canonical (joinUsrWord I)
  have husrWord :
      EVM.word (AccountAddress.ofNat (joinUsrMaskedWord I).toNat).val =
        joinUsrMaskedWord I := by
    exact Option.some.inj (valueToWord_address_ofNat_canonical (joinUsrMaskedWord I) husrCanon)
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr, uint256, uint256Int,
    vatMoveSelector, selectorBytes, hradLt, hradWord, hthisWord, husrWord,
    accountAddress_ofUInt256_eq_ofNat_toNat, word_toBytesBE_toByteArray_eq_toByteArray,
    ByteArray.append_assoc]

abbrev joinBurnSelectorSeedWord : UInt256 := ⟨0x2770a7eb⟩

abbrev joinBurnSelectorPlainWord : UInt256 := ⟨0x9dc29fac⟩

abbrev joinBurnSelectorShiftedWord : UInt256 :=
  UInt256.shiftLeft joinBurnSelectorSeedWord ⟨226⟩

noncomputable def joinBurnSelectorMem (mem : ByteArray) : ByteArray :=
  joinBurnSelectorShiftedWord.toByteArray.write 0 mem 128 32

noncomputable def joinBurnSenderMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (solcSourceWord I).toByteArray.write 0 (joinBurnSelectorMem mem) 132 32

noncomputable def joinBurnCalldataMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (joinWadWord I).toByteArray.write 0 (joinBurnSenderMem I mem) 164 32

theorem joinBurnSelectorMem_size {mem : ByteArray} (hmem : mem.size = 228) :
    (joinBurnSelectorMem mem).size = 228 := by
  unfold joinBurnSelectorMem
  exact toByteArray_write32_size_of_le mem joinBurnSelectorShiftedWord 128 228 228 hmem
    (by rw [hmem]; omega) (by omega)

theorem joinBurnSenderMem_size (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 228) :
    (joinBurnSenderMem I mem).size = 228 := by
  unfold joinBurnSenderMem
  exact toByteArray_write32_size_of_le (joinBurnSelectorMem mem) (solcSourceWord I)
    132 228 228 (joinBurnSelectorMem_size hmem)
    (by rw [joinBurnSelectorMem_size hmem]; omega) (by omega)

theorem joinBurnCalldataMem_size (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 228) :
    (joinBurnCalldataMem I mem).size = 228 := by
  unfold joinBurnCalldataMem
  exact toByteArray_write32_size_of_le (joinBurnSenderMem I mem) (joinWadWord I)
    164 228 228 (joinBurnSenderMem_size I hmem)
    (by rw [joinBurnSenderMem_size I hmem]; omega) (by omega)

theorem joinBurnSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (joinBurnSelectorMem mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold joinBurnSelectorMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [hmem]; omega) (by norm_num)]
  exact hread64

theorem joinBurnSenderMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (joinBurnSenderMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold joinBurnSenderMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [joinBurnSelectorMem_size hmem]; omega) (by omega)]
  exact joinBurnSelectorMem_read64 hmem hread64

theorem joinBurnCalldataMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (joinBurnCalldataMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold joinBurnCalldataMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [joinBurnSenderMem_size I hmem]; omega) (by omega)]
  exact joinBurnSenderMem_read64 I hmem hread64

abbrev joinEventSignatureWord : UInt256 :=
  ⟨0xb4e09949657f21548b58afe74e7b86cd2295da5ff1598ae1e5faecb1cf19ca95⟩

noncomputable def joinJoinEventMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (joinWadWord I).toByteArray.write 0 mem 128 32

theorem joinJoinEventMem_size (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 228) :
    (joinJoinEventMem I mem).size = 228 := by
  unfold joinJoinEventMem
  exact toByteArray_write32_size_of_le mem (joinWadWord I) 128 228 228 hmem
    (by rw [hmem]; omega) (by omega)

theorem joinJoinEventMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (joinJoinEventMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold joinJoinEventMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [hmem]; omega) (by omega)]
  exact hread64

theorem joinBurnCalldataMem_read128_68 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (joinBurnCalldataMem I mem).readWithPadding 128 68 =
      daiBurnSelector ++ (solcSourceWord I).toByteArray ++ (joinWadWord I).toByteArray := by
  let final := joinBurnCalldataMem I mem
  have hfinalSize : final.size = 228 := by
    dsimp [final]
    exact joinBurnCalldataMem_size I hmem
  have hselectorRead : final.readWithPadding 128 4 = daiBurnSelector := by
    dsimp [final]
    unfold joinBurnCalldataMem
    rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
      (by rw [joinBurnSenderMem_size I hmem]; omega) (by omega)
      (by rw [joinBurnSenderMem_size I hmem]; omega) (by omega) (by omega)]
    unfold joinBurnSenderMem
    rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
      (by rw [joinBurnSelectorMem_size hmem]; omega) (by omega)
      (by rw [joinBurnSelectorMem_size hmem]; omega) (by omega) (by omega)]
    unfold joinBurnSelectorMem
    rw [toByteArray_write_read_window_of_gap joinBurnSelectorShiftedWord mem 128 0 4
      (by norm_num) (by norm_num) (by norm_num) (by rw [hmem]; native_decide)]
    unfold joinBurnSelectorShiftedWord joinBurnSelectorSeedWord daiBurnSelector selectorBytes
    native_decide
  have hsenderRead : final.readWithPadding 132 32 = (solcSourceWord I).toByteArray := by
    dsimp [final]
    unfold joinBurnCalldataMem
    rw [write32_read_below_len _ _ 164 132 32 (by rw [toByteArray_size])
      (by rw [joinBurnSenderMem_size I hmem]; omega) (by omega)
      (by rw [joinBurnSenderMem_size I hmem]; omega) (by omega) (by omega)]
    unfold joinBurnSenderMem
    rw [write32_read_prefix_len _ _ 132 32 (by rw [toByteArray_size])
      (by rw [joinBurnSelectorMem_size hmem]; omega) (by omega) (by omega)
      (by omega)]
    rw [toByteArray_extract_all]
  have hwadRead : final.readWithPadding 164 32 = (joinWadWord I).toByteArray := by
    dsimp [final]
    unfold joinBurnCalldataMem
    rw [write32_read_prefix_len _ _ 164 32 (by rw [toByteArray_size])
      (by rw [joinBurnSenderMem_size I hmem]; omega) (by omega) (by omega)
      (by omega)]
    rw [toByteArray_extract_all]
  rw [readWithPadding_eq_extract' final 128 68 (by norm_num) (by norm_num)
    (by rw [hfinalSize]; omega)]
  have hselectorExt : final.extract 128 132 = daiBurnSelector := by
    rw [← readWithPadding_eq_extract' final 128 4 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hselectorRead
  have hsenderExt : final.extract 132 164 = (solcSourceWord I).toByteArray := by
    rw [← readWithPadding_eq_extract' final 132 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hsenderRead
  have hwadExt : final.extract 164 196 = (joinWadWord I).toByteArray := by
    rw [← readWithPadding_eq_extract' final 164 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hwadRead
  have hsplit : final.extract 128 196 =
      final.extract 128 132 ++ final.extract 132 164 ++ final.extract 164 196 := by
    rw [show final.extract 128 196 = final.extract 128 132 ++ final.extract 132 196 by
      rw [ByteArray.extract_append_extract]; norm_num]
    rw [show final.extract 132 196 = final.extract 132 164 ++ final.extract 164 196 by
      rw [ByteArray.extract_append_extract]; norm_num]
    simp
  rw [hsplit, hselectorExt, hsenderExt, hwadExt]

theorem joinBurnEncode_eq (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 228) :
    config.externalABI.encode? "burn"
        [.address I.source, .int (Int.ofNat (joinWadWord I).toNat)] =
      some ((joinBurnCalldataMem I mem).readWithPadding 128 68) := by
  rw [joinBurnCalldataMem_read128_68 I hmem]
  have hsenderLen : (EVM.Word.toBytesBE (solcSourceWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (solcSourceWord I)
  have hwadLen : (EVM.Word.toBytesBE (joinWadWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (joinWadWord I)
  have hwadLt : (joinWadWord I).toNat < EVM.twoPow 256 := by
    simp [UInt256.toNat, UInt256.size, EVM.twoPow]
  have hwadWord : EVM.word (joinWadWord I).toNat = joinWadWord I := by
    simpa [UInt256.ofNat] using u256_ofNat_toNat (joinWadWord I)
  have hsenderWord : EVM.word I.source.val = solcSourceWord I := by
    rfl
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr, uint256, uint256Int,
    daiBurnSelector, selectorBytes, hwadLt, hwadWord, hsenderWord,
    word_toBytesBE_toByteArray_eq_toByteArray, ByteArray.append_assoc]

theorem daiJoinJoinToMul {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (h : RD daiJoinBytecode I g s0 ⟨449⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiJoinBytecode I g s0 ⟨1678⟩
      [joinWadWord I, daiJoinONEWord, ⟨490⟩, joinUsrMaskedWord I,
        UInt256.ofNat I.codeOwner, joinMoveSelectorPlainWord, daiJoinVatTargetWord σ I,
        joinWadWord I, joinUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hmask :
      UInt256.land (daiJoinSlotWord ⟨1⟩ σ I) solcAddrMask =
        daiJoinVatTargetWord σ I := rfl
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have rd452 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k453, C453, rd453raw⟩ := rd452.sload (by native_decide) (by evm_ov)
  have rd453 : RD daiJoinBytecode I g s0 ⟨453⟩
      (daiJoinSlotWord ⟨1⟩ σ I :: joinWadWord I :: joinUsrMaskedWord I :: ⟨232⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k453 C453 := by
    simpa [daiJoinSlotWord, solcSlotWord] using rd453raw
  have rd467 := evm_run rd453 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push4 joinMoveSelectorPlainWord (by native_decide) (by evm_ov)]
  have rd467Norm : ∃ k C, RD daiJoinBytecode I g s0 ⟨467⟩
      [joinMoveSelectorPlainWord, daiJoinVatTargetWord σ I, joinWadWord I,
        joinUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [daiJoinVatTargetWord, daiJoinAddressReturnWord, hmaskConst, u256_land_comm]
        using rd467⟩
  obtain ⟨_, _, rd467'⟩ := rd467Norm
  have rd468 := RD.address rd467' (by native_decide) (by evm_ov)
  have rd468Norm : ∃ k C, RD daiJoinBytecode I g s0 ⟨468⟩
      [UInt256.ofNat I.codeOwner, joinMoveSelectorPlainWord, daiJoinVatTargetWord σ I,
        joinWadWord I, joinUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd468⟩
  obtain ⟨_, _, rd468'⟩ := rd468Norm
  have rd472 := evm_run rd468' with [
    raw dup5 (by native_decide) (by evm_ov),
    raw push2 ⟨490⟩ (by native_decide) (by evm_ov)]
  have rd472Norm : ∃ k C, RD daiJoinBytecode I g s0 ⟨472⟩
      [⟨490⟩, joinUsrMaskedWord I, UInt256.ofNat I.codeOwner, joinMoveSelectorPlainWord,
        daiJoinVatTargetWord σ I, joinWadWord I, joinUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd472⟩
  obtain ⟨_, _, rd472'⟩ := rd472Norm
  have rd485 := rd472'.pushConst daiJoinONEWord
    (width := 12) (op := .PUSH12) (by native_decide) (by native_decide) (by evm_ov)
  have rd485Norm : ∃ k C, RD daiJoinBytecode I g s0 ⟨485⟩
      [daiJoinONEWord, ⟨490⟩, joinUsrMaskedWord I, UInt256.ofNat I.codeOwner,
        joinMoveSelectorPlainWord, daiJoinVatTargetWord σ I, joinWadWord I,
        joinUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd485⟩
  obtain ⟨_, _, rd485'⟩ := rd485Norm
  have rd486 := evm_run rd485' with [
    raw dup7 (by native_decide) (by evm_ov)]
  have rd486Norm : ∃ k C, RD daiJoinBytecode I g s0 ⟨486⟩
      [joinWadWord I, daiJoinONEWord, ⟨490⟩, joinUsrMaskedWord I,
        UInt256.ofNat I.codeOwner, joinMoveSelectorPlainWord, daiJoinVatTargetWord σ I,
        joinWadWord I, joinUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd486⟩
  obtain ⟨_, _, rd486'⟩ := rd486Norm
  have rd489 := evm_run rd486' with [
    raw push2 ⟨1678⟩ (by native_decide) (by evm_ov)]
  have rd489Norm : ∃ k C, RD daiJoinBytecode I g s0 ⟨489⟩
      [⟨1678⟩, joinWadWord I, daiJoinONEWord, ⟨490⟩, joinUsrMaskedWord I,
        UInt256.ofNat I.codeOwner, joinMoveSelectorPlainWord, daiJoinVatTargetWord σ I,
        joinWadWord I, joinUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd489⟩
  obtain ⟨_, _, rd489'⟩ := rd489Norm
  have rd1678 := RD.jump (a := ⟨1678⟩) rd489' (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, rd1678⟩

theorem daiJoinJoinMulSuccess {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hguard :
      joinWadWord I = ⟨0⟩ ∨
        UInt256.div (daiJoinRadWord (joinWadWord I)) (joinWadWord I) = daiJoinONEWord)
    (h : RD daiJoinBytecode I g s0 ⟨449⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiJoinBytecode I g s0 ⟨490⟩
      [daiJoinRadWord (joinWadWord I), joinUsrMaskedWord I, UInt256.ofNat I.codeOwner,
        joinMoveSelectorPlainWord, daiJoinVatTargetWord σ I, joinWadWord I,
        joinUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd1678⟩ := daiJoinJoinToMul h
  obtain ⟨_, _, rd490⟩ := daiJoinMulRoutine_success
    (code := daiJoinBytecode) (ee := I) (g := g) (s0 := s0)
    (x := daiJoinONEWord) (y := joinWadWord I) (ret := ⟨490⟩)
    (R := [joinUsrMaskedWord I, UInt256.ofNat I.codeOwner, joinMoveSelectorPlainWord,
      daiJoinVatTargetWord σ I, joinWadWord I, joinUsrMaskedWord I, ⟨232⟩, sel])
    rd1678 hguard (by jump_dest) daiJoinMulRoutine_shape (by simp)
  exact ⟨_, _, by simpa [daiJoinRadWord] using rd490⟩

theorem daiJoinJoinToVatMoveExtcodesizeGuard {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel rad : UInt256}
    (h : RD daiJoinBytecode I g s0 ⟨490⟩
      [rad, joinUsrMaskedWord I, UInt256.ofNat I.codeOwner, joinMoveSelectorPlainWord,
        daiJoinVatTargetWord σ I, joinWadWord I, joinUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiJoinBytecode I g s0 ⟨564⟩
      (daiJoinVatTargetWord σ I :: daiJoinVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨100⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: joinMoveSelectorPlainWord ::
        daiJoinVatTargetWord σ I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨232⟩ :: sel :: [])
      (joinMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
      ByteArray.empty (cA, σ) k' C' := by
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hselectorMask :
      UInt256.land (⟨4294967295⟩ : UInt256) joinMoveSelectorPlainWord =
        joinMoveSelectorPlainWord := by
    native_decide
  have hownerCanon : (UInt256.ofNat I.codeOwner.val).toNat < EVM.addressModulus := by
    rw [UInt256.toNat_ofNat_of_lt]
    · rw [show EVM.addressModulus = AccountAddress.size from by decide]
      exact I.codeOwner.isLt
    · exact lt_trans I.codeOwner.isLt (by native_decide)
  have hownerMask :
      UInt256.land solcAddrMask (UInt256.ofNat I.codeOwner.val) =
        UInt256.ofNat I.codeOwner.val :=
    solcAddrMask_clean_left hownerCanon
  have husrCanon : (joinUsrMaskedWord I).toNat < EVM.addressModulus := by
    rw [joinUsrMaskedWord, u256_land_comm]
    exact solcAddrMask_result_canonical (joinUsrWord I)
  have husrMask :
      UInt256.land solcAddrMask (joinUsrMaskedWord I) = joinUsrMaskedWord I :=
    solcAddrMask_clean_left husrCanon
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ solcFreePtrMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (solcFreePtrMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [solcFreePtrMem_size]; decide) (by decide)
      solcFreePtrMem_read64
  have hcallMem : (joinMoveCalldataMem I rad solcFreePtrMem).size = 228 :=
    joinMoveCalldataMem_size I rad solcFreePtrMem_size
  have hcallRead64 :
      (joinMoveCalldataMem I rad solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    joinMoveCalldataMem_read64 I rad solcFreePtrMem_size solcFreePtrMem_read64
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (joinMoveCalldataMem I rad solcFreePtrMem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((joinMoveCalldataMem I rad solcFreePtrMem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  have rd564 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    dup5,
    push4 ⟨4294967295⟩,
    and,
    push1 ⟨224⟩,
    shl,
    dup2,
    raw mstore 6 (joinMoveSelectorMem solcFreePtrMem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨4⟩,
    add,
    dup1,
    dup5,
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    and,
    dup2,
    raw mstore 3 (joinMoveThisMem I solcFreePtrMem) (UInt256.ofNat 6)
      (by native_decide) mem_cost
      (by
        simpa [joinMoveThisMem, hmaskConst]
          using congrArg
            (fun w => w.toByteArray.write 0 (joinMoveSelectorMem solcFreePtrMem) 132 32)
            hownerMask)
      (by decide) (by evm_ov),
    push1 ⟨32⟩,
    add,
    dup4,
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    and,
    dup2,
    raw mstore 3 (joinMoveUsrMem I solcFreePtrMem) (UInt256.ofNat 7)
      (by native_decide) mem_cost
      (by
        simpa [joinMoveUsrMem, hmaskConst]
          using congrArg
            (fun w => w.toByteArray.write 0 (joinMoveThisMem I solcFreePtrMem) 164 32)
            husrMask)
      (by decide) (by evm_ov),
    push1 ⟨32⟩,
    add,
    dup3,
    dup2,
    raw mstore 3 (joinMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩,
    add,
    swap4,
    pop,
    pop,
    pop,
    pop,
    push1 ⟨0⟩,
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    dup1,
    dup4,
    sub,
    dup2,
    push1 ⟨0⟩,
    dup8,
    dup1]
  have hpc :
      ((⟨490⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 5 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = (⟨564⟩ : UInt256) := by
    native_decide
  exact ⟨_, _, by
    simpa [joinMoveSelectorMem, joinMoveSelectorShiftedWord, joinMoveThisMem,
      joinMoveUsrMem, joinMoveCalldataMem, hmaskConst, hselectorMask, hownerMask,
      husrMask, hpc] using rd564⟩

theorem daiJoinJoinVatMoveNoCode {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel rad : UInt256}
    (h : RD daiJoinBytecode I g s0 ⟨490⟩
      [rad, joinUsrMaskedWord I, UInt256.ofNat I.codeOwner, joinMoveSelectorPlainWord,
        daiJoinVatTargetWord σ I, joinWadWord I, joinUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (daiJoinVatTargetWord σ I) = ⟨0⟩) :
    RDrev daiJoinBytecode g s0 := by
  obtain ⟨_, _, rd564⟩ := daiJoinJoinToVatMoveExtcodesizeGuard h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨564⟩) (okPc := ⟨576⟩) rd564
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem daiJoinJoinVatMoveCallReady {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel rad : UInt256}
    (h : RD daiJoinBytecode I g s0 ⟨490⟩
      [rad, joinUsrMaskedWord I, UInt256.ofNat I.codeOwner, joinMoveSelectorPlainWord,
        daiJoinVatTargetWord σ I, joinWadWord I, joinUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (daiJoinVatTargetWord σ I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD daiJoinBytecode I g s0 ⟨579⟩
      (gasWord :: daiJoinVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: joinMoveSelectorPlainWord ::
        daiJoinVatTargetWord σ I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨232⟩ :: sel :: [])
      (joinMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd564⟩ := daiJoinJoinToVatMoveExtcodesizeGuard h
  obtain ⟨gasWord, k', C', rd579⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨564⟩) (okPc := ⟨576⟩) rd564
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd579⟩

theorem daiJoinJoinVatMovePostCall {cA gh bl σ σ₀ A I} {g sel rad gasWord : UInt256}
    {k C : ℕ}
    (rd579 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨579⟩
      (gasWord :: daiJoinVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: joinMoveSelectorPlainWord ::
        daiJoinVatTargetWord σ I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨232⟩ :: sel :: [])
      (joinMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
      ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl σ σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ I))
          (toExecute σ (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((joinMoveCalldataMem I rad solcFreePtrMem).readWithPadding 128 100)
          (I.depth + 1) I.header I.perm)
      ∧ RD daiJoinBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨580⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: joinMoveSelectorPlainWord ::
            daiJoinVatTargetWord σ I :: joinWadWord I :: joinUsrMaskedWord I ::
            ⟨232⟩ :: sel :: [])
          (joinMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
          out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA', σ', z, out, Ain, callGas, k', C', hΘ, rd580raw, hout⟩ :=
    RD.call rd579 (by native_decide) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
      native_decide
    have hmin :
        (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
      exact umin_ofNat_right_toNat_of_ge (c := 0) (n := out.size)
        (by native_decide) (Nat.zero_le _) hout
    simpa [byteArray_write_len_zero, hmin, haw] using rd580raw

theorem daiJoinJoinVatMoveCallDepthLimit {cA gh bl σ σ₀ A I}
    {g sel rad gasWord : UInt256} {k C : ℕ}
    (rd579 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨579⟩
      (gasWord :: daiJoinVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: joinMoveSelectorPlainWord ::
        daiJoinVatTargetWord σ I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨232⟩ :: sel :: [])
      (joinMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
      ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨580⟩
      (⟨0⟩ :: ⟨228⟩ :: joinMoveSelectorPlainWord :: daiJoinVatTargetWord σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (joinMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', C', rd580raw⟩ :=
    RD.callDepthLimit rd579 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
    native_decide
  have hmin :
      (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  simpa [byteArray_write_len_zero, hmin, haw] using rd580raw

theorem daiJoinJoinVatMoveCallFailed {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (rd580 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨580⟩
      (⟨0⟩ :: ⟨228⟩ :: joinMoveSelectorPlainWord :: daiJoinVatTargetWord σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev daiJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨580⟩) (okPc := ⟨596⟩) rd580
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp)

theorem daiJoinJoinVatMoveCallSucceeded {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (rd580 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨580⟩
      (⟨1⟩ :: ⟨228⟩ :: joinMoveSelectorPlainWord :: daiJoinVatTargetWord σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata acc k C) :
    ∃ k' C', RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨598⟩
      (⟨228⟩ :: joinMoveSelectorPlainWord :: daiJoinVatTargetWord σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨580⟩) (okPc := ⟨596⟩) rd580
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem daiJoinJoinVatMoveToDaiBurnExtcodesizeGuard
    {cA gh bl σ σ₀ σ' A I} {g sel rad : UInt256}
    {rdata : ByteArray} {cA' : Batteries.RBSet AccountAddress compare}
    {k C : ℕ}
    (rd598 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨598⟩
      (⟨228⟩ :: joinMoveSelectorPlainWord :: daiJoinVatTargetWord σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (joinMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
      rdata (cA', σ') k C) :
    ∃ k' C', RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨671⟩
      (daiJoinDaiTargetWord σ' I :: daiJoinDaiTargetWord σ' I :: ⟨0⟩ ::
        ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨196⟩ ::
        joinBurnSelectorPlainWord :: daiJoinDaiTargetWord σ' I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (joinBurnCalldataMem I (joinMoveCalldataMem I rad solcFreePtrMem))
      (UInt256.ofNat 8) rdata (cA', σ') k' C' := by
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hburnSelector :
      UInt256.shiftLeft joinBurnSelectorSeedWord ⟨226⟩ =
        UInt256.shiftLeft joinBurnSelectorPlainWord ⟨224⟩ := by
    native_decide
  have hmoveMem : (joinMoveCalldataMem I rad solcFreePtrMem).size = 228 :=
    joinMoveCalldataMem_size I rad solcFreePtrMem_size
  have hmoveRead64 :
      (joinMoveCalldataMem I rad solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    joinMoveCalldataMem_read64 I rad solcFreePtrMem_size solcFreePtrMem_read64
  have hmload64Move :
      (if (⟨64⟩ : UInt256).toNat ≥ (joinMoveCalldataMem I rad solcFreePtrMem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((joinMoveCalldataMem I rad solcFreePtrMem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmoveMem]; decide) (by decide) hmoveRead64
  have hburnMem :
      (joinBurnCalldataMem I (joinMoveCalldataMem I rad solcFreePtrMem)).size = 228 :=
    joinBurnCalldataMem_size I hmoveMem
  have hburnRead64 :
      (joinBurnCalldataMem I (joinMoveCalldataMem I rad solcFreePtrMem)).readWithPadding
          64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    joinBurnCalldataMem_read64 I hmoveMem hmoveRead64
  have hmload64Burn :
      (if (⟨64⟩ : UInt256).toNat ≥
            (joinBurnCalldataMem I (joinMoveCalldataMem I rad solcFreePtrMem)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((joinBurnCalldataMem I (joinMoveCalldataMem I rad solcFreePtrMem)).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hburnMem]; decide) (by decide) hburnRead64
  have rd599 := RD.pop rd598 (by native_decide) (by evm_ov)
  have rd601p := evm_run rd599 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k601, C601, rd601raw⟩ := rd601p.sload (by native_decide) (by evm_ov)
  have rd602 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨602⟩
      (daiJoinSlotWord ⟨2⟩ σ' I :: joinMoveSelectorPlainWord ::
        daiJoinVatTargetWord σ I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨232⟩ :: sel :: [])
      (joinMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
      rdata (cA', σ') k601 C601 := by
    simpa [daiJoinSlotWord, solcSlotWord] using rd601raw
  have rd671 := evm_run rd602 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Move (by decide) (by evm_ov),
    raw push4 joinBurnSelectorSeedWord (by native_decide) (by evm_ov),
    raw push1 ⟨226⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (joinBurnSelectorMem (joinMoveCalldataMem I rad solcFreePtrMem))
      (UInt256.ofNat 8) (by native_decide) mem_cost
      (by rfl)
      (by decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 (joinBurnSenderMem I (joinMoveCalldataMem I rad solcFreePtrMem))
      (UInt256.ofNat 8) (by native_decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 (joinBurnCalldataMem I (joinMoveCalldataMem I rad solcFreePtrMem))
      (UInt256.ofNat 8) (by native_decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Burn (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push4 joinBurnSelectorPlainWord (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have hpc :
      ((⟨602⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 5 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 5 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = (⟨671⟩ : UInt256) := by
    native_decide
  exact ⟨_, _, by
    simpa [daiJoinDaiTargetWord, daiJoinAddressReturnWord, hmaskConst, hburnSelector,
      joinBurnSelectorShiftedWord, joinBurnSelectorSeedWord, joinBurnSelectorPlainWord,
      joinBurnSelectorMem, joinBurnSenderMem, joinBurnCalldataMem, u256_land_comm, hpc]
      using rd671⟩

theorem daiJoinJoinDaiBurnNoCode
    {cA gh bl σ σ₀ σ' A I} {g sel rad : UInt256}
    {rdata : ByteArray} {cA' : Batteries.RBSet AccountAddress compare}
    {k C : ℕ}
    (rd598 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨598⟩
      (⟨228⟩ :: joinMoveSelectorPlainWord :: daiJoinVatTargetWord σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (joinMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
      rdata (cA', σ') k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (daiJoinDaiTargetWord σ' I) = ⟨0⟩) :
    RDrev daiJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd671⟩ := daiJoinJoinVatMoveToDaiBurnExtcodesizeGuard rd598
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨671⟩) (okPc := ⟨683⟩) rd671
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem daiJoinJoinDaiBurnCallReady
    {cA gh bl σ σ₀ σ' A I} {g sel rad : UInt256}
    {rdata : ByteArray} {cA' : Batteries.RBSet AccountAddress compare}
    {k C : ℕ}
    (rd598 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨598⟩
      (⟨228⟩ :: joinMoveSelectorPlainWord :: daiJoinVatTargetWord σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (joinMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
      rdata (cA', σ') k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (daiJoinDaiTargetWord σ' I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨686⟩
      (gasWord :: daiJoinDaiTargetWord σ' I :: ⟨0⟩ :: ⟨128⟩ :: ⟨68⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨196⟩ :: joinBurnSelectorPlainWord ::
        daiJoinDaiTargetWord σ' I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨232⟩ :: sel :: [])
      (joinBurnCalldataMem I (joinMoveCalldataMem I rad solcFreePtrMem))
      (UInt256.ofNat 8) rdata (cA', σ') k' C' := by
  obtain ⟨_, _, rd671⟩ := daiJoinJoinVatMoveToDaiBurnExtcodesizeGuard rd598
  obtain ⟨gasWord, k', C', rd686⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨671⟩) (okPc := ⟨683⟩) rd671
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd686⟩

theorem daiJoinJoinDaiBurnPostCall
    {cA cA' gh bl σ σ₀ σ' A I} {g sel rad gasWord : UInt256}
    {rdata : ByteArray} {k C : ℕ}
    (rd686 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨686⟩
      (gasWord :: daiJoinDaiTargetWord σ' I :: ⟨0⟩ :: ⟨128⟩ :: ⟨68⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨196⟩ :: joinBurnSelectorPlainWord ::
        daiJoinDaiTargetWord σ' I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨232⟩ :: sel :: [])
      (joinBurnCalldataMem I (joinMoveCalldataMem I rad solcFreePtrMem))
      (UInt256.ofNat 8) rdata (cA', σ') k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', z, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl σ' σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I))
          (toExecute σ' (AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((joinBurnCalldataMem I (joinMoveCalldataMem I rad solcFreePtrMem)).readWithPadding
            128 68)
          (I.depth + 1) I.header I.perm)
      ∧ RD daiJoinBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨687⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨196⟩ :: joinBurnSelectorPlainWord ::
            daiJoinDaiTargetWord σ' I :: joinWadWord I :: joinUsrMaskedWord I ::
            ⟨232⟩ :: sel :: [])
          (joinBurnCalldataMem I (joinMoveCalldataMem I rad solcFreePtrMem))
          (UInt256.ofNat 8) out (cA'', σ'') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA'', σ'', z, out, Ain, callGas, k', C', hΘ, rd687raw, hout⟩ :=
    RD.call rd686 (by native_decide) hdepth (by evm_ov)
  refine ⟨cA'', σ'', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
      native_decide
    have hmin :
        (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
      exact umin_ofNat_right_toNat_of_ge (c := 0) (n := out.size)
        (by native_decide) (Nat.zero_le _) hout
    simpa [byteArray_write_len_zero, hmin, haw] using rd687raw

theorem daiJoinJoinDaiBurnCallDepthLimit
    {cA cA' gh bl σ σ₀ σ' A I} {g sel rad gasWord : UInt256}
    {rdata : ByteArray} {k C : ℕ}
    (rd686 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨686⟩
      (gasWord :: daiJoinDaiTargetWord σ' I :: ⟨0⟩ :: ⟨128⟩ :: ⟨68⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨196⟩ :: joinBurnSelectorPlainWord ::
        daiJoinDaiTargetWord σ' I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨232⟩ :: sel :: [])
      (joinBurnCalldataMem I (joinMoveCalldataMem I rad solcFreePtrMem))
      (UInt256.ofNat 8) rdata (cA', σ') k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨687⟩
      (⟨0⟩ :: ⟨196⟩ :: joinBurnSelectorPlainWord :: daiJoinDaiTargetWord σ' I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (joinBurnCalldataMem I (joinMoveCalldataMem I rad solcFreePtrMem))
      (UInt256.ofNat 8) ByteArray.empty (cA', σ') k' C' := by
  obtain ⟨k', C', rd687raw⟩ :=
    RD.callDepthLimit rd686 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
    native_decide
  have hmin :
      (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  simpa [byteArray_write_len_zero, hmin, haw] using rd687raw

theorem daiJoinJoinDaiBurnCallFailed
    {cA gh bl σ σ₀ σd A I} {g sel : UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (rd687 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨687⟩
      (⟨0⟩ :: ⟨196⟩ :: joinBurnSelectorPlainWord :: daiJoinDaiTargetWord σd I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev daiJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨687⟩) (okPc := ⟨703⟩) rd687
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp)

theorem daiJoinJoinDaiBurnCallSucceeded
    {cA gh bl σ σ₀ σd A I} {g sel : UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (rd687 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨687⟩
      (⟨1⟩ :: ⟨196⟩ :: joinBurnSelectorPlainWord :: daiJoinDaiTargetWord σd I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata acc k C) :
    ∃ k' C', RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨705⟩
      (⟨196⟩ :: joinBurnSelectorPlainWord :: daiJoinDaiTargetWord σd I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨687⟩) (okPc := ⟨703⟩) rd687
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem daiJoinJoinDaiBurnSuccessTail
    {cA gh bl σ σ₀ σd A I} {g sel : UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hperm : I.perm = true)
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd705 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨705⟩
      (⟨196⟩ :: joinBurnSelectorPlainWord :: daiJoinDaiTargetWord σd I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata acc k C) :
    RDret daiJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) acc ByteArray.empty := by
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have husrCanon : (joinUsrMaskedWord I).toNat < EVM.addressModulus := by
    rw [joinUsrMaskedWord, u256_land_comm]
    exact solcAddrMask_result_canonical (joinUsrWord I)
  have husrMask :
      UInt256.land solcAddrMask (joinUsrMaskedWord I) = joinUsrMaskedWord I :=
    solcAddrMask_clean_left husrCanon
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have heventMem : (joinJoinEventMem I mem).size = 228 :=
    joinJoinEventMem_size I hmem
  have heventRead64 :
      (joinJoinEventMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
    joinJoinEventMem_read64 I hmem hread64
  have hmload64Event :
      (if (⟨64⟩ : UInt256).toNat ≥ (joinJoinEventMem I mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((joinJoinEventMem I mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [heventMem]; decide) (by decide) heventRead64
  have rd727 := evm_run rd705 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (joinJoinEventMem I mem) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Event (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have hpc727 :
      ((⟨705⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = (⟨727⟩ : UInt256) := by
    native_decide
  have rd727Norm : ∃ k' C', RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨727⟩
      (⟨128⟩ :: ⟨128⟩ :: joinBurnSelectorPlainWord :: joinUsrMaskedWord I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (joinJoinEventMem I mem) (UInt256.ofNat 8) rdata acc k' C' := by
    exact ⟨_, _, by
      simpa [joinJoinEventMem, hmaskConst, husrMask, hpc727, u256_land_comm]
        using rd727⟩
  obtain ⟨_, _, rd727'⟩ := rd727Norm
  have rd760 := rd727'.pushConst joinEventSignatureWord
    (width := 32) (op := .PUSH32) (by native_decide) (by native_decide) (by evm_ov)
  have rd770pre := evm_run rd760 with [
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hpc770 :
      ((⟨760⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) = (⟨770⟩ : UInt256) := by
    native_decide
  have rd770Norm : ∃ k' C', RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨770⟩
      (⟨128⟩ :: ⟨32⟩ :: joinEventSignatureWord :: joinUsrMaskedWord I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (joinJoinEventMem I mem) (UInt256.ofNat 8) rdata acc k' C' := by
    exact ⟨_, _, by
      simpa [joinEventSignatureWord, hpc770] using rd770pre⟩
  obtain ⟨_, _, rd770⟩ := rd770Norm
  have rd771 := RD.log2
    (a := ⟨128⟩) (b := ⟨32⟩) (c := joinEventSignatureWord)
    (d := joinUsrMaskedWord I)
    (t := [joinWadWord I, joinUsrMaskedWord I, ⟨232⟩, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 8).toNat (⟨128⟩ : UInt256).toNat
        (⟨32⟩ : UInt256).toNat))
    rd770 (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd772 := RD.pop (a := joinWadWord I)
    (t := [joinUsrMaskedWord I, ⟨232⟩, sel]) rd771
    (by native_decide) (by evm_ov)
  have rd773 := RD.pop (a := joinUsrMaskedWord I) (t := [⟨232⟩, sel]) rd772
    (by native_decide) (by evm_ov)
  have rd232 := RD.jump (a := ⟨232⟩) (t := [sel]) rd773
    (by native_decide) (by jump_dest) (by evm_ov)
  have rd232' := RD.jumpdest (pc := ⟨232⟩) (stk := [sel]) rd232
    (by native_decide) (by evm_ov)
  simpa using RD.stop rd232' (by native_decide) (by evm_ov)

theorem daiJoinJoinMulReverts {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hwad : joinWadWord I ≠ ⟨0⟩)
    (hguard :
      UInt256.div (daiJoinRadWord (joinWadWord I)) (joinWadWord I) ≠ daiJoinONEWord)
    (h : RD daiJoinBytecode I g s0 ⟨449⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiJoinBytecode g s0 := by
  obtain ⟨_, _, rd1678⟩ := daiJoinJoinToMul h
  exact daiJoinMulRoutine_revert
    (code := daiJoinBytecode) (ee := I) (g := g) (s0 := s0)
    (x := daiJoinONEWord) (y := joinWadWord I) (ret := ⟨490⟩)
    (R := [joinUsrMaskedWord I, UInt256.ofNat I.codeOwner, joinMoveSelectorPlainWord,
      daiJoinVatTargetWord σ I, joinWadWord I, joinUsrMaskedWord I, ⟨232⟩, sel])
    rd1678 hwad hguard daiJoinMulRoutine_revert_shape (by simp)

end Benchmarks.Dss.DaiJoin
