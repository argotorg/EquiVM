import Benchmarks.Dss.Flipper.Yank
import Benchmarks.Dss.Flipper.BidDelete

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## Remaining external-call helpers for `yank(uint256)` -/

theorem yankVatFluxSelectorWord_prefix :
    (UInt256.toByteArray yankVatFluxSelectorWord).extract 0 4 = vatFluxSelector := by
  native_decide

theorem yankVatFluxCallMem_read128_4 (σmem σ : AccountMap) (I : ExecutionEnv) :
    (yankVatFluxCallMem σmem σ I).readWithPadding 128 4 = vatFluxSelector := by
  rw [yankVatFluxCallMem_eq_cascade]
  rw [writeCascade_read_window_of_head (yankVatHashMem σmem I) 128 0 4
    yankVatFluxSelectorWord
    [(132, flipperSlotWord ⟨3⟩ σ I),
     (164, EVM.word I.codeOwner.val),
     (196, solcSourceWord I),
     (228, bidLotWord (yankId I) σ I)]
    (by rw [yankVatHashMem_size]; native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)
    (by norm_num) (by norm_num) (by norm_num)]
  exact yankVatFluxSelectorWord_prefix

theorem yankVatFluxCallMem_read132 (σmem σ : AccountMap) (I : ExecutionEnv) :
    (yankVatFluxCallMem σmem σ I).readWithPadding 132 32 =
      UInt256.toByteArray (flipperSlotWord ⟨3⟩ σ I) := by
  rw [yankVatFluxCallMem_eq_cascade, writeCascade_cons]
  have hbase :
      (writeWord (yankVatHashMem σmem I) 128 yankVatFluxSelectorWord).size = 164 := by
    rw [writeWord_size]
    · rw [yankVatHashMem_size]; native_decide
    · rw [yankVatHashMem_size]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord (yankVatHashMem σmem I) 128 yankVatFluxSelectorWord)
    (base := 164) (off := 132) (word := flipperSlotWord ⟨3⟩ σ I)
    (rest := [(164, EVM.word I.codeOwner.val),
      (196, solcSourceWord I),
      (228, bidLotWord (yankId I) σ I)])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem yankVatFluxCallMem_read164 (σmem σ : AccountMap) (I : ExecutionEnv) :
    (yankVatFluxCallMem σmem σ I).readWithPadding 164 32 =
      UInt256.toByteArray (EVM.word I.codeOwner.val) := by
  rw [yankVatFluxCallMem_eq_cascade, writeCascade_cons, writeCascade_cons]
  let mem1 := writeWord (yankVatHashMem σmem I) 128 yankVatFluxSelectorWord
  have hmem1 : mem1.size = 164 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [yankVatHashMem_size]; native_decide
    · rw [yankVatHashMem_size]; native_decide
  have hbase :
      (writeWord mem1 132 (flipperSlotWord ⟨3⟩ σ I)).size = 164 := by
    rw [writeWord_size]
    · rw [hmem1]; native_decide
    · rw [hmem1]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem1 132 (flipperSlotWord ⟨3⟩ σ I))
    (base := 164) (off := 164) (word := EVM.word I.codeOwner.val)
    (rest := [(196, solcSourceWord I),
      (228, bidLotWord (yankId I) σ I)])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem yankVatFluxCallMem_read196 (σmem σ : AccountMap) (I : ExecutionEnv) :
    (yankVatFluxCallMem σmem σ I).readWithPadding 196 32 =
      UInt256.toByteArray (solcSourceWord I) := by
  rw [yankVatFluxCallMem_eq_cascade, writeCascade_cons, writeCascade_cons,
    writeCascade_cons]
  let mem1 := writeWord (yankVatHashMem σmem I) 128 yankVatFluxSelectorWord
  let mem2 := writeWord mem1 132 (flipperSlotWord ⟨3⟩ σ I)
  have hmem1 : mem1.size = 164 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [yankVatHashMem_size]; native_decide
    · rw [yankVatHashMem_size]; native_decide
  have hmem2 : mem2.size = 164 := by
    dsimp [mem2]
    rw [writeWord_size]
    · rw [hmem1]; native_decide
    · rw [hmem1]; native_decide
  have hbase : (writeWord mem2 164 (EVM.word I.codeOwner.val)).size = 196 := by
    rw [writeWord_size]
    · rw [hmem2]; native_decide
    · rw [hmem2]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem2 164 (EVM.word I.codeOwner.val))
    (base := 196) (off := 196) (word := solcSourceWord I)
    (rest := [(228, bidLotWord (yankId I) σ I)])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem yankVatFluxCallMem_read228 (σmem σ : AccountMap) (I : ExecutionEnv) :
    (yankVatFluxCallMem σmem σ I).readWithPadding 228 32 =
      UInt256.toByteArray (bidLotWord (yankId I) σ I) := by
  rw [yankVatFluxCallMem_eq_cascade, writeCascade_cons, writeCascade_cons,
    writeCascade_cons, writeCascade_cons]
  let mem1 := writeWord (yankVatHashMem σmem I) 128 yankVatFluxSelectorWord
  let mem2 := writeWord mem1 132 (flipperSlotWord ⟨3⟩ σ I)
  let mem3 := writeWord mem2 164 (EVM.word I.codeOwner.val)
  have hmem1 : mem1.size = 164 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [yankVatHashMem_size]; native_decide
    · rw [yankVatHashMem_size]; native_decide
  have hmem2 : mem2.size = 164 := by
    dsimp [mem2]
    rw [writeWord_size]
    · rw [hmem1]; native_decide
    · rw [hmem1]; native_decide
  have hmem3 : mem3.size = 196 := by
    dsimp [mem3]
    rw [writeWord_size]
    · rw [hmem2]; native_decide
    · rw [hmem2]; native_decide
  have hbase : (writeWord mem3 196 (solcSourceWord I)).size = 228 := by
    rw [writeWord_size]
    · rw [hmem3]; native_decide
    · rw [hmem3]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem3 196 (solcSourceWord I))
    (base := 228) (off := 228) (word := bidLotWord (yankId I) σ I)
    (rest := [])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites])

theorem yankVatFluxCallMem_read (σmem σ : AccountMap) (I : ExecutionEnv) :
    (yankVatFluxCallMem σmem σ I).readWithPadding 128 132 =
      vatFluxSelector ++
      UInt256.toByteArray (flipperSlotWord ⟨3⟩ σ I) ++
      UInt256.toByteArray (EVM.word I.codeOwner.val) ++
      UInt256.toByteArray (solcSourceWord I) ++
      UInt256.toByteArray (bidLotWord (yankId I) σ I) := by
  rw [byteArray_readWithPadding_split (yankVatFluxCallMem σmem σ I) 128 4 128
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [yankVatFluxCallMem_size])]
  rw [yankVatFluxCallMem_read128_4]
  rw [byteArray_readWithPadding_split (yankVatFluxCallMem σmem σ I) 132 32 96
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [yankVatFluxCallMem_size])]
  rw [yankVatFluxCallMem_read132]
  rw [byteArray_readWithPadding_split (yankVatFluxCallMem σmem σ I) 164 32 64
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [yankVatFluxCallMem_size])]
  rw [yankVatFluxCallMem_read164]
  rw [byteArray_readWithPadding_split (yankVatFluxCallMem σmem σ I) 196 32 32
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [yankVatFluxCallMem_size])]
  rw [yankVatFluxCallMem_read196, yankVatFluxCallMem_read228]
  simp [ByteArray.append_assoc]

theorem yankEncodeABIValue_bytes32_word (w : UInt256) :
    encodeABIValue? bytes32 (.fixedBytes bytes32Width (EVM.Word.toBytesBE w)) =
      some (UInt256.toByteArray w).toList := by
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    simpa [toByteArray_eq_toBytesBE] using word_toBytesBE_toByteArray_size w
  have hz : zeroBytes 0 = [] := by native_decide
  simp [bytes32, bytes32Width, encodeABIValue?, hlen, hz,
    toByteArray_eq_toBytesBE, byteArray_toList_eq]

theorem yankEncodeABIValue_this_address (I : ExecutionEnv) :
    encodeABIValue? addr (.address I.codeOwner) =
      some (UInt256.toByteArray (EVM.word I.codeOwner.val)).toList := by
  have hword : EVM.word I.codeOwner.val = EVM.word I.codeOwner.val := rfl
  simp [addr, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat,
    EVM.addressModulus, hword, toByteArray_eq_toBytesBE, byteArray_toList_eq]

theorem yankEncodeABIValue_source_address (I : ExecutionEnv) :
    encodeABIValue? addr (.address I.source) =
      some (UInt256.toByteArray (solcSourceWord I)).toList := by
  have hword : EVM.word I.source.val = solcSourceWord I := rfl
  simp [addr, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, EVM.addressModulus,
    hword, toByteArray_eq_toBytesBE, byteArray_toList_eq]

theorem yankVatFluxCallMem_encode (σmem σ : AccountMap) (I : ExecutionEnv) :
    config.externalABI.encode? "flux"
      [.fixedBytes bytes32Width (EVM.Word.toBytesBE (flipperSlotWord ⟨3⟩ σ I)),
        .address I.codeOwner,
        .address I.source,
        .int (Int.ofNat (bidLotWord (yankId I) σ I).toNat)] =
        some ((yankVatFluxCallMem σmem σ I).readWithPadding 128 132) := by
  rw [yankVatFluxCallMem_read]
  unfold config externalABI
  simp only [if_true]
  unfold ABI.encodeCallWithSelector?
  have hpayload :
      encodeABIValues? [bytes32, addr, addr, uint256]
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (flipperSlotWord ⟨3⟩ σ I)),
          .address I.codeOwner,
          .address I.source,
          .int (Int.ofNat (bidLotWord (yankId I) σ I).toNat)] =
          some (UInt256.toByteArray (flipperSlotWord ⟨3⟩ σ I) ++
            UInt256.toByteArray (EVM.word I.codeOwner.val) ++
            UInt256.toByteArray (solcSourceWord I) ++
            UInt256.toByteArray (bidLotWord (yankId I) σ I)).toList := by
    unfold encodeABIValues?
    rw [show abiTupleHeadSize? [bytes32, addr, addr, uint256] = some 128 by native_decide]
    simp only [encodeABIValuesFrom?, Option.bind, bind]
    rw [yankEncodeABIValue_bytes32_word, yankEncodeABIValue_this_address,
      yankEncodeABIValue_source_address, yankEncodeABIValue_uint256_word]
    simp [show isDynamicABIType bytes32 = false by native_decide,
      show isDynamicABIType addr = false by native_decide,
      show isDynamicABIType uint256 = false by native_decide,
      ByteArray.append_assoc, byteArray_toList_eq]
  rw [hpayload]
  apply congrArg some
  apply ByteArray.ext
  simp [vatFluxSelector, byteArray_toList_eq, ByteArray.append_assoc]

abbrev yankVatMoveSelectorWord : UInt256 :=
  UInt256.shiftLeft (⟨3140843579⟩ : UInt256) ⟨224⟩

theorem yankVatMoveSelectorWord_prefix :
    (UInt256.toByteArray yankVatMoveSelectorWord).extract 0 4 = moveSelector := by
  native_decide

noncomputable abbrev yankMoveHashMem (σmem σflux : AccountMap) (I : ExecutionEnv)
    (id : UInt256) : ByteArray :=
  writeCascade (yankVatFluxCallMem σmem σflux I) [(0, id), (32, ⟨1⟩)]

theorem yankMoveHashMem_size (σmem σflux : AccountMap) (I : ExecutionEnv)
    (id : UInt256) :
    (yankMoveHashMem σmem σflux I id).size = 260 := by
  unfold yankMoveHashMem
  exact writeCascade_size_of_base (yankVatFluxCallMem σmem σflux I)
    [(0, id), (32, (⟨1⟩ : UInt256))]
    (yankVatFluxCallMem_size σmem σflux I)
    (by simp [WriteGapsOk])
    (by norm_num [writeCascadeSize])

theorem yankMoveHashMem_read64 (σmem σflux : AccountMap) (I : ExecutionEnv)
    (id : UInt256) :
    (yankMoveHashMem σmem σflux I id).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold yankMoveHashMem
  rw [writeCascade_read_preserved_of_base (yankVatFluxCallMem σmem σflux I)
    [(0, id), (32, (⟨1⟩ : UInt256))]
    (yankVatFluxCallMem_size σmem σflux I)
    (by simp [WindowDisjointFromWrites] <;> native_decide)]
  exact yankVatFluxCallMem_read64 σmem σflux I

theorem yankMoveHashMem_read0 (σmem σflux : AccountMap) (I : ExecutionEnv)
    (id : UInt256) :
    (yankMoveHashMem σmem σflux I id).readWithPadding 0 32 = UInt256.toByteArray id := by
  unfold yankMoveHashMem
  exact writeCascade_read_word_of_head_of_base
    (yankVatFluxCallMem σmem σflux I) (base := 260) (off := 0) (word := id)
    (rest := [(32, (⟨1⟩ : UInt256))])
    (yankVatFluxCallMem_size σmem σflux I)
    (by native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem yankMoveHashMem_read32 (σmem σflux : AccountMap) (I : ExecutionEnv)
    (id : UInt256) :
    (yankMoveHashMem σmem σflux I id).readWithPadding 32 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold yankMoveHashMem
  rw [writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord (yankVatFluxCallMem σmem σflux I) 0 id) (base := 260) (off := 32)
    (word := (⟨1⟩ : UInt256)) (rest := [])
    (by
      rw [writeWord_size]
      · rw [yankVatFluxCallMem_size]; native_decide
      · rw [yankVatFluxCallMem_size]; native_decide)
    (by native_decide)
    (by simp [WindowDisjointFromWrites])

theorem yankMoveHashMem_read0_64 (σmem σflux : AccountMap) (I : ExecutionEnv)
    (id : UInt256) :
    (yankMoveHashMem σmem σflux I id).readWithPadding 0 64 =
      UInt256.toByteArray id ++ UInt256.toByteArray (⟨1⟩ : UInt256) := by
  rw [byteArray_readWithPadding_split (yankMoveHashMem σmem σflux I id) 0 32 32
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [yankMoveHashMem_size]; omega)]
  rw [yankMoveHashMem_read0, yankMoveHashMem_read32]

theorem yankMoveHashMem_solcMappingSlot (σmem σflux : AccountMap) (I : ExecutionEnv)
    (id : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((yankMoveHashMem σmem σflux I id).readWithPadding 0 64))) =
      solcMappingSlot ⟨1⟩ id := by
  rw [yankMoveHashMem_read0_64]
  unfold solcMappingSlot
  exact mappingSlot_single id ⟨1⟩

noncomputable abbrev yankVatMoveCallMem (σmem σflux σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  writeCascade (yankMoveHashMem σmem σflux I (yankId I))
    [(128, yankVatMoveSelectorWord),
     (132, solcSourceWord I),
     (164, bidGuyWord (yankId I) σ I),
     (196, bidBidWord (yankId I) σ I)]

theorem yankVatMoveCallMem_size (σmem σflux σ : AccountMap) (I : ExecutionEnv) :
    (yankVatMoveCallMem σmem σflux σ I).size = 260 := by
  unfold yankVatMoveCallMem
  exact writeCascade_size_of_base (yankMoveHashMem σmem σflux I (yankId I))
    [(128, yankVatMoveSelectorWord),
     (132, solcSourceWord I),
     (164, bidGuyWord (yankId I) σ I),
     (196, bidBidWord (yankId I) σ I)]
    (yankMoveHashMem_size σmem σflux I (yankId I))
    (by simp [WriteGapsOk] <;> native_decide)
    (by norm_num [writeCascadeSize])

theorem yankVatMoveCallMem_read64 (σmem σflux σ : AccountMap) (I : ExecutionEnv) :
    (yankVatMoveCallMem σmem σflux σ I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold yankVatMoveCallMem
  rw [writeCascade_read_preserved_of_base (yankMoveHashMem σmem σflux I (yankId I))
    [(128, yankVatMoveSelectorWord),
     (132, solcSourceWord I),
     (164, bidGuyWord (yankId I) σ I),
     (196, bidBidWord (yankId I) σ I)]
    (yankMoveHashMem_size σmem σflux I (yankId I))
    (by simp [WindowDisjointFromWrites] <;> native_decide)]
  exact yankMoveHashMem_read64 σmem σflux I (yankId I)

theorem yankVatMoveCallMem_read128_4 (σmem σflux σ : AccountMap) (I : ExecutionEnv) :
    (yankVatMoveCallMem σmem σflux σ I).readWithPadding 128 4 = moveSelector := by
  unfold yankVatMoveCallMem
  rw [writeCascade_read_window_of_head (yankMoveHashMem σmem σflux I (yankId I)) 128 0 4
    yankVatMoveSelectorWord
    [(132, solcSourceWord I),
     (164, bidGuyWord (yankId I) σ I),
     (196, bidBidWord (yankId I) σ I)]
    (by rw [yankMoveHashMem_size]; native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)
    (by norm_num) (by norm_num) (by norm_num)]
  exact yankVatMoveSelectorWord_prefix

theorem yankVatMoveCallMem_read132 (σmem σflux σ : AccountMap) (I : ExecutionEnv) :
    (yankVatMoveCallMem σmem σflux σ I).readWithPadding 132 32 =
      UInt256.toByteArray (solcSourceWord I) := by
  unfold yankVatMoveCallMem
  rw [writeCascade_cons]
  have hbase :
      (writeWord (yankMoveHashMem σmem σflux I (yankId I)) 128
        yankVatMoveSelectorWord).size =
        260 := by
    rw [writeWord_size]
    · rw [yankMoveHashMem_size]; native_decide
    · rw [yankMoveHashMem_size]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord (yankMoveHashMem σmem σflux I (yankId I)) 128 yankVatMoveSelectorWord)
    (base := 260) (off := 132) (word := solcSourceWord I)
    (rest := [(164, bidGuyWord (yankId I) σ I),
      (196, bidBidWord (yankId I) σ I)])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem yankVatMoveCallMem_read164 (σmem σflux σ : AccountMap) (I : ExecutionEnv) :
    (yankVatMoveCallMem σmem σflux σ I).readWithPadding 164 32 =
      UInt256.toByteArray (bidGuyWord (yankId I) σ I) := by
  unfold yankVatMoveCallMem
  rw [writeCascade_cons, writeCascade_cons]
  let mem1 := writeWord (yankMoveHashMem σmem σflux I (yankId I)) 128
    yankVatMoveSelectorWord
  have hmem1 : mem1.size = 260 := by
    have hhash :
        (writeWord (writeWord (yankVatFluxCallMem σmem σflux I) 0 (yankId I)) 32
            (⟨1⟩ : UInt256)).size = 260 := by
      simpa [yankMoveHashMem] using yankMoveHashMem_size σmem σflux I (yankId I)
    dsimp [mem1]
    rw [writeWord_size]
    · rw [hhash]; native_decide
    · rw [hhash]; native_decide
  have hbase : (writeWord mem1 132 (solcSourceWord I)).size = 260 := by
    rw [writeWord_size]
    · rw [hmem1]; native_decide
    · rw [hmem1]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem1 132 (solcSourceWord I))
    (base := 260) (off := 164) (word := bidGuyWord (yankId I) σ I)
    (rest := [(196, bidBidWord (yankId I) σ I)])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem yankVatMoveCallMem_read196 (σmem σflux σ : AccountMap) (I : ExecutionEnv) :
    (yankVatMoveCallMem σmem σflux σ I).readWithPadding 196 32 =
      UInt256.toByteArray (bidBidWord (yankId I) σ I) := by
  unfold yankVatMoveCallMem
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons]
  let mem1 := writeWord (yankMoveHashMem σmem σflux I (yankId I)) 128
    yankVatMoveSelectorWord
  let mem2 := writeWord mem1 132 (solcSourceWord I)
  have hmem1 : mem1.size = 260 := by
    have hhash :
        (writeWord (writeWord (yankVatFluxCallMem σmem σflux I) 0 (yankId I)) 32
            (⟨1⟩ : UInt256)).size = 260 := by
      simpa [yankMoveHashMem] using yankMoveHashMem_size σmem σflux I (yankId I)
    dsimp [mem1]
    rw [writeWord_size]
    · rw [hhash]; native_decide
    · rw [hhash]; native_decide
  have hmem2 : mem2.size = 260 := by
    dsimp [mem2]
    rw [writeWord_size]
    · rw [hmem1]; native_decide
    · rw [hmem1]; native_decide
  have hbase : (writeWord mem2 164 (bidGuyWord (yankId I) σ I)).size = 260 := by
    rw [writeWord_size]
    · rw [hmem2]; native_decide
    · rw [hmem2]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem2 164 (bidGuyWord (yankId I) σ I))
    (base := 260) (off := 196) (word := bidBidWord (yankId I) σ I)
    (rest := [])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites])

theorem yankVatMoveCallMem_read (σmem σflux σ : AccountMap) (I : ExecutionEnv) :
    (yankVatMoveCallMem σmem σflux σ I).readWithPadding 128 100 =
      moveSelector ++
      UInt256.toByteArray (solcSourceWord I) ++
      UInt256.toByteArray (bidGuyWord (yankId I) σ I) ++
      UInt256.toByteArray (bidBidWord (yankId I) σ I) := by
  rw [byteArray_readWithPadding_split (yankVatMoveCallMem σmem σflux σ I) 128 4 96
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [yankVatMoveCallMem_size]; omega)]
  rw [yankVatMoveCallMem_read128_4]
  rw [byteArray_readWithPadding_split (yankVatMoveCallMem σmem σflux σ I) 132 32 64
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [yankVatMoveCallMem_size]; omega)]
  rw [yankVatMoveCallMem_read132]
  rw [byteArray_readWithPadding_split (yankVatMoveCallMem σmem σflux σ I) 164 32 32
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [yankVatMoveCallMem_size]; omega)]
  rw [yankVatMoveCallMem_read164, yankVatMoveCallMem_read196]
  simp [ByteArray.append_assoc]

theorem yankEncodeABIValue_address_word (w : UInt256) :
    encodeABIValue? addr
        (.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)) =
      some (UInt256.toByteArray (UInt256.land w solcAddrMask)).toList := by
  have hcanon := solcAddrMask_result_canonical w
  have haddrMod : (UInt256.land w solcAddrMask).toNat % AccountAddress.size =
      (UInt256.land w solcAddrMask).toNat := by
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
  have hword : EVM.word (UInt256.land w solcAddrMask).toNat =
      UInt256.land w solcAddrMask := u256_ofNat_toNat _
  simp [addr, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, haddrMod, hword,
    toByteArray_eq_toBytesBE, byteArray_toList_eq]

theorem yankVatMoveCallMem_encode (σmem σflux σ : AccountMap) (I : ExecutionEnv) :
    config.externalABI.encode? "move"
      [.address I.source,
        .address (AccountAddress.ofNat (bidGuyWord (yankId I) σ I).toNat),
        .int (Int.ofNat (bidBidWord (yankId I) σ I).toNat)] =
        some ((yankVatMoveCallMem σmem σflux σ I).readWithPadding 128 100) := by
  rw [yankVatMoveCallMem_read]
  unfold config externalABI
  simp only [if_true]
  unfold ABI.encodeCallWithSelector?
  have hguy :
      encodeABIValue? addr
          (.address (AccountAddress.ofNat (bidGuyWord (yankId I) σ I).toNat)) =
        some (UInt256.toByteArray (bidGuyWord (yankId I) σ I)).toList := by
    simpa [bidGuyWord, flipperAddressReturnWord] using
      yankEncodeABIValue_address_word (flipperSlotWord (bidPackedSlotOfWord (yankId I)) σ I)
  have hpayload :
      encodeABIValues? [addr, addr, uint256]
        [.address I.source,
          .address (AccountAddress.ofNat (bidGuyWord (yankId I) σ I).toNat),
          .int (Int.ofNat (bidBidWord (yankId I) σ I).toNat)] =
          some (UInt256.toByteArray (solcSourceWord I) ++
            UInt256.toByteArray (bidGuyWord (yankId I) σ I) ++
            UInt256.toByteArray (bidBidWord (yankId I) σ I)).toList := by
    unfold encodeABIValues?
    rw [show abiTupleHeadSize? [addr, addr, uint256] = some 96 by native_decide]
    simp only [encodeABIValuesFrom?, Option.bind, bind]
    rw [yankEncodeABIValue_source_address, hguy, yankEncodeABIValue_uint256_word]
    simp [show isDynamicABIType addr = false by native_decide,
      show isDynamicABIType uint256 = false by native_decide,
      ByteArray.append_assoc, byteArray_toList_eq]
  rw [hpayload]
  apply congrArg some
  apply ByteArray.ext
  simp [moveSelector, byteArray_toList_eq, ByteArray.append_assoc]

theorem evalExpr_bidBid_of_get_id_evm {evm : EVM.State} {locals : Store}
    {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (bidsF (.var "id") "bid")) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidBaseOfWord id)).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint256Int)
    (loc := wordLoc (bidBaseOfWord id))
    (hbase := hbids)
    (her := evalStorageRef_bidField_of_get_id (evm := evm) (locals := locals)
      (id := id) (field := "bid") hid)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract, storageDecls,
        BidStructTy, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        bidEvaledRefOfWord, bidSlotOfWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  exact congrArg EvalResult.ok (flipperStorageLocLoad_uint256 evm (bidBaseOfWord id))

abbrev yankMoveArgValsOf (evm : EVM.State) (id : UInt256) : List Value :=
  [.address evm.executionEnv.source,
    .address
      (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidPackedSlotOfWord id))
          solcAddrMask).toNat),
    .int (Int.ofNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidBaseOfWord id)).toNat)]

theorem evalExprs_yankMoveArgs_ofLocals {evm : EVM.State} {locals : Store} {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExprs? config { contract := contract, locals := locals } evm
      [sender, .storage (bidsF (.var "id") "guy"),
        .storage (bidsF (.var "id") "bid")] =
        .ok (yankMoveArgValsOf evm id) := by
  have hguy := evalExpr_bidGuy_of_get_id_evm (evm := evm)
    (locals := locals) (id := id) hid hbids
  have hbid := evalExpr_bidBid_of_get_id_evm (evm := evm)
    (locals := locals) (id := id) hid hbids
  simp only [evalExprs?, evalExpr?, envValue, sender, hguy, hbid, yankMoveArgValsOf,
    EvalResult.bind, bind, pure]

theorem yankLocalsAfterFlux_get_id (I : ExecutionEnv) :
    (((yankLocals I).insert "_clawRet" (collapseReturns [])).insert "_fluxRet"
      (collapseReturns [])).get? "id" = some (.int (Int.ofNat (yankId I).toNat)) := by
  rw [store_get_ne _ _ (by decide)]
  exact yankLocalsAfterClaw_get_id I

theorem yankLocalsAfterFlux_get_bids (I : ExecutionEnv) :
    (((yankLocals I).insert "_clawRet" (collapseReturns [])).insert "_fluxRet"
      (collapseReturns [])).get? "bids" = none := by
  rw [store_get_ne _ _ (by decide)]
  exact yankLocalsAfterClaw_get_bids I

theorem yankLocalsAfterFlux_get_vat (I : ExecutionEnv) :
    (((yankLocals I).insert "_clawRet" (collapseReturns [])).insert "_fluxRet"
      (collapseReturns [])).get? "vat" = none := by
  rw [store_get_ne _ _ (by decide)]
  exact yankLocalsAfterClaw_get_vat I

theorem yankLocalsAfterCalls_get_id (I : ExecutionEnv) :
    ((((yankLocals I).insert "_clawRet" (collapseReturns [])).insert "_fluxRet"
      (collapseReturns [])).insert "_moveRet" (collapseReturns [])).get? "id" =
        some (.int (Int.ofNat (yankId I).toNat)) := by
  rw [store_get_ne _ _ (by decide)]
  exact yankLocalsAfterFlux_get_id I

theorem yankLocalsAfterCalls_get_bids (I : ExecutionEnv) :
    ((((yankLocals I).insert "_clawRet" (collapseReturns [])).insert "_fluxRet"
      (collapseReturns [])).insert "_moveRet" (collapseReturns [])).get? "bids" = none := by
  rw [store_get_ne _ _ (by decide)]
  exact yankLocalsAfterFlux_get_bids I

theorem flipperYankX_toVatCall {cA σmem σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out : ByteArray} {ret sel selector target : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨1365⟩
      (selector :: target :: yankId I :: ret :: sel :: [])
      (yankCatCallMem σmem I) (UInt256.ofNat 6) out (cA, σ) k C) :
    ∃ gasWord k' C', RD flipperBytecode I g s0 ⟨1481⟩
      (gasWord :: flipperVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ :: ⟨132⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: ⟨1628552750⟩ ::
        flipperVatTargetWord σ I :: yankId I :: ret :: sel :: [])
      (yankVatFluxCallMem σmem σ I) (UInt256.ofNat 9) out (cA, σ) k' C' := by
  obtain ⟨_, _, rd1466⟩ := flipperYankX_toVatExtcodesizeGuard h
  obtain ⟨gasWord, k1481, C1481, rd1481⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1466⟩) (okPc := ⟨1478⟩) rd1466
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k1481, C1481, by simpa using rd1481⟩

theorem flipperYankX_vatPostCall
    {cA0 gh bl σbase σ₀ A I} {g : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σmem σ : AccountMap} {Acur : Substate}
    {k C : ℕ} {out0 : ByteArray} {ret sel selector target : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (h : RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨1365⟩
      (selector :: target :: yankId I :: ret :: sel :: [])
      (yankCatCallMem σmem I) (UInt256.ofNat 6) out0 (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨1482⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: ⟨1628552750⟩ ::
          flipperVatTargetWord σ I :: yankId I :: ret :: sel :: [])
        (yankVatFluxCallMem σmem σ I) (UInt256.ofNat 9) out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        ({ initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ, substate := Acur, createdAccounts := cA })
        (EVM.address (flipperVatAddress σ I)) "flux" 0
        (yankFluxArgValsOf
          ({ initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ, substate := Acur, createdAccounts := cA })
          (yankId I))
        (z,
          { { initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ, substate := Acur, createdAccounts := cA } with
            accountMap := σ', substate := A', createdAccounts := cA' },
          out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd1481⟩ := flipperYankX_toVatCall hcodeSize h
  obtain ⟨cA', σ', z, out, A_in, callGas, k1482, C1482, hΘpack, rd1482raw,
      houtsz⟩ :=
    RD.call rd1481 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k1482, C1482, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
          (⟨128⟩ : UInt256).toNat (⟨132⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 9 := by
      native_decide
    have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
      rfl
    have rd1482 : RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨1482⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: ⟨1628552750⟩ ::
          flipperVatTargetWord σ I :: yankId I :: ret :: sel :: [])
        (out.write 0 (yankVatFluxCallMem σmem σ I) 128
          (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 9) out (cA', σ') k1482 C1482 :=
      haw ▸ rd1482raw
    rw [hmin, byteArray_write_len_zero] at rd1482
    exact rd1482
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := flipperVatTargetWord σ I)
      (mem := yankVatFluxCallMem σmem σ I) (inOff := ⟨128⟩) (inSize := ⟨132⟩)
      (fun hdepthEq => by
        have hEq : I.depth = (1024 : Fin 1025) := by
          simpa [initState] using hdepthEq
        exact absurd hdepth (by rw [hEq]; decide))
      (flipperVatEvmAddress_eq_target_of_accountMapEquiv (accountMapEquiv.refl σ))
      ?_ ?_
    · simpa [yankFluxArgValsOf, initState, flipperSlotWord, solcSlotWord,
        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        bidLotWord, bidSlotOfWord, bidBaseOfWord] using
        yankVatFluxCallMem_encode σmem σ I
    · simpa [initState, hperm] using hΘ

theorem flipperYankSourceBodyVatCallFailure {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCat evmVat : EVM.State} {outCat outVat : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (hguy : bidGuyWord (yankId I) σ I ≠ ⟨0⟩)
    (hbidLt :
      (bidBidWord (yankId I) σ I).toNat < (bidTabWord (yankId I) σ I).toNat)
    (hcatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperCatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallCat :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperCatAddress σ I)) "claw" 0
        (yankClawArgVals (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
        (true, evmCat, outCat) true)
    (hvatCode :
      0 <
        (UInt256.ofNat
          ((evmCat.lookupAccount (flipperVatAddress evmCat.accountMap evmCat.executionEnv)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM config evmCat
        (EVM.address (flipperVatAddress evmCat.accountMap evmCat.executionEnv)) "flux" 0
        (yankFluxArgValsOf evmCat (yankId I)) (false, evmVat, outVat) true) :
    let locals := yankLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let locals1 := (yankLocals I).insert "_clawRet" (collapseReturns [])
    ExecTransitionBody config contract evm0 locals yankTransition.body .reverted := by
  intro locals evm0 locals1
  have hauthGuard := flipperAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, yankLocals]) hauth
  have hguyGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
          .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_yankGuyNeZero_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hguy
  have hbidGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .lt (.storage (bidsF (.var "id") "bid"))
          (.storage (bidsF (.var "id") "tab"))) = .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_yankBidLtTab_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hbidLt
  have hcat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage catRef) =
        .ok (.address (flipperCatAddress evm0.accountMap evm0.executionEnv)) := by
    exact evalExpr_flipperStorageCatOfLocals (by simpa [locals] using yankLocals_get_cat I)
  have hguardCat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage catRef)) (.intLit 0)) = .ok (.bool true) := by
    simpa [evm0, initState, flipperCatAddress] using
      evalExpr_flipperCatCodeGuard_true_ofLocals (evm := evm0) (locals := locals) hcat
        hcatCode
  have hargsCat :
      evalExprs? config { contract := contract, locals := locals } evm0
        [.storage (bidsF (.var "id") "tab")] = .ok (yankClawArgVals evm0) := by
    simpa [locals] using evalExprs_yankClawArgs (evm := evm0)
  have hcallCat' :
      typedCallViaEVM config evm0
        (EVM.address (flipperCatAddress evm0.accountMap evm0.executionEnv)) "claw" 0
        (yankClawArgVals evm0) (true, evmCat, outCat) true := by
    simpa [evm0, initState, flipperCatAddress] using hcallCat
  have hdecCat : config.externalABI.decode? "claw" outCat = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hcatBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage catRef) "claw" (.intLit 0)
          [.storage (bidsF (.var "id") "tab")] "_clawRet")
        (.ok { contract := contract, locals := locals1 } evmCat) := by
    simpa [checkedExternalCallStmts, locals1, locals] using
      checkedExternalCallSuccess (cfg := config) (C := contract) (evm := evm0)
        (evm' := evmCat) (locals := locals) (receiver := .storage catRef)
        (retVar := "_clawRet") (name := "claw")
        (target := flipperCatAddress evm0.accountMap evm0.executionEnv) (sendVal := 0)
        (args := [.storage (bidsF (.var "id") "tab")])
        (argVals := yankClawArgVals evm0) (out := outCat) (perm := true) (value := [])
        hguardCat hcat hargsCat hcallCat' hdecCat
  have hvat : evalExpr? config { contract := contract, locals := locals1 } evmCat
      (.storage vatRef) =
        .ok (.address (flipperVatAddress evmCat.accountMap evmCat.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals
      (by simpa [locals1] using yankLocalsAfterClaw_get_vat I)
  have hguardVat :
      evalExpr? config { contract := contract, locals := locals1 } evmCat
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_flipperVatCodeGuard_true_ofLocals hvat hvatCode
  have hargsVat :
      evalExprs? config { contract := contract, locals := locals1 } evmCat
        [.storage ilkRef, thisAddr, sender, .storage (bidsF (.var "id") "lot")] =
        .ok (yankFluxArgValsOf evmCat (yankId I)) := by
    exact evalExprs_yankFluxArgs_ofLocals
      (by simpa [locals1] using yankLocalsAfterClaw_get_id I)
      (by simpa [locals1] using yankLocalsAfterClaw_get_bids I)
      (by simpa [locals1] using yankLocalsAfterClaw_get_ilk I)
  have hvatBlock :
      ExecBlock config { contract := contract, locals := locals1 } evmCat
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, sender, .storage (bidsF (.var "id") "lot")]
          "_fluxRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallFailure (cfg := config) (C := contract) (evm := evmCat)
        (evm' := evmVat) (locals := locals1) (receiver := .storage vatRef)
        (retVar := "_fluxRet") (name := "flux")
        (target := flipperVatAddress evmCat.accountMap evmCat.executionEnv) (sendVal := 0)
        (args := [.storage ilkRef, thisAddr, sender, .storage (bidsF (.var "id") "lot")])
        (argVals := yankFluxArgValsOf evmCat (yankId I)) (out := outVat) (perm := true)
        hguardVat hvat hargsVat hcallVat
  have htail :
      ExecBlock config { contract := contract, locals := locals1 } evmCat
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, sender, .storage (bidsF (.var "id") "lot")]
          "_fluxRet" ++
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet" ++
        [ .delete (bidRef (.var "id")) ]))
        .reverted := by
    exact execBlock_append_term
      (s2 :=
        checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet" ++
        [ .delete (bidRef (.var "id")) ])
      hvatBlock (by intro f' e' h; cases h)
  have hcalls :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage catRef) "claw" (.intLit 0)
          [.storage (bidsF (.var "id") "tab")] "_clawRet" ++
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, sender, .storage (bidsF (.var "id") "lot")]
          "_fluxRet" ++
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet" ++
        [ .delete (bidRef (.var "id")) ])))
        .reverted := by
    exact execBlock_append hcatBlock htail
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 yankTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauthGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hbidGuard) ?_
    simpa [yankTransition, checkedExternalCallStmts, List.append_assoc] using hcalls
  simpa [ExecTransitionBody, yankTransition, nonpayable, auth, checkedExternalCallStmts,
    locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperYankSourceBlockAfterFluxSuccess {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCat evmVat : EVM.State} {outCat outVat : ByteArray} {r : ExecResult}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (hguy : bidGuyWord (yankId I) σ I ≠ ⟨0⟩)
    (hbidLt :
      (bidBidWord (yankId I) σ I).toNat < (bidTabWord (yankId I) σ I).toNat)
    (hcatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperCatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallCat :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperCatAddress σ I)) "claw" 0
        (yankClawArgVals (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
        (true, evmCat, outCat) true)
    (hvatCode :
      0 <
        (UInt256.ofNat
          ((evmCat.lookupAccount (flipperVatAddress evmCat.accountMap evmCat.executionEnv)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM config evmCat
        (EVM.address (flipperVatAddress evmCat.accountMap evmCat.executionEnv)) "flux" 0
        (yankFluxArgValsOf evmCat (yankId I)) (true, evmVat, outVat) true)
    (htail :
      ExecBlock config
        { contract := contract,
          locals :=
            ((yankLocals I).insert "_clawRet" (collapseReturns [])).insert "_fluxRet"
              (collapseReturns []) }
        evmVat
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet" ++
        [ .delete (bidRef (.var "id")) ])
        r) :
    let locals := yankLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let locals1 := (yankLocals I).insert "_clawRet" (collapseReturns [])
    let locals2 := locals1.insert "_fluxRet" (collapseReturns [])
    ExecBlock config { contract := contract, locals := locals } evm0 yankTransition.body r := by
  intro locals evm0 locals1 locals2
  have hauthGuard := flipperAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, yankLocals]) hauth
  have hguyGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
          .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_yankGuyNeZero_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hguy
  have hbidGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .lt (.storage (bidsF (.var "id") "bid"))
          (.storage (bidsF (.var "id") "tab"))) = .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_yankBidLtTab_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hbidLt
  have hcat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage catRef) =
        .ok (.address (flipperCatAddress evm0.accountMap evm0.executionEnv)) := by
    exact evalExpr_flipperStorageCatOfLocals (by simpa [locals] using yankLocals_get_cat I)
  have hguardCat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage catRef)) (.intLit 0)) = .ok (.bool true) := by
    simpa [evm0, initState, flipperCatAddress] using
      evalExpr_flipperCatCodeGuard_true_ofLocals (evm := evm0) (locals := locals) hcat
        hcatCode
  have hargsCat :
      evalExprs? config { contract := contract, locals := locals } evm0
        [.storage (bidsF (.var "id") "tab")] = .ok (yankClawArgVals evm0) := by
    simpa [locals] using evalExprs_yankClawArgs (evm := evm0)
  have hcallCat' :
      typedCallViaEVM config evm0
        (EVM.address (flipperCatAddress evm0.accountMap evm0.executionEnv)) "claw" 0
        (yankClawArgVals evm0) (true, evmCat, outCat) true := by
    simpa [evm0, initState, flipperCatAddress] using hcallCat
  have hdecCat : config.externalABI.decode? "claw" outCat = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hcatBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage catRef) "claw" (.intLit 0)
          [.storage (bidsF (.var "id") "tab")] "_clawRet")
        (.ok { contract := contract, locals := locals1 } evmCat) := by
    simpa [checkedExternalCallStmts, locals1, locals] using
      checkedExternalCallSuccess (cfg := config) (C := contract) (evm := evm0)
        (evm' := evmCat) (locals := locals) (receiver := .storage catRef)
        (retVar := "_clawRet") (name := "claw")
        (target := flipperCatAddress evm0.accountMap evm0.executionEnv) (sendVal := 0)
        (args := [.storage (bidsF (.var "id") "tab")])
        (argVals := yankClawArgVals evm0) (out := outCat) (perm := true) (value := [])
        hguardCat hcat hargsCat hcallCat' hdecCat
  have hvat : evalExpr? config { contract := contract, locals := locals1 } evmCat
      (.storage vatRef) =
        .ok (.address (flipperVatAddress evmCat.accountMap evmCat.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals
      (by simpa [locals1] using yankLocalsAfterClaw_get_vat I)
  have hguardVat :
      evalExpr? config { contract := contract, locals := locals1 } evmCat
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_flipperVatCodeGuard_true_ofLocals hvat hvatCode
  have hargsVat :
      evalExprs? config { contract := contract, locals := locals1 } evmCat
        [.storage ilkRef, thisAddr, sender, .storage (bidsF (.var "id") "lot")] =
        .ok (yankFluxArgValsOf evmCat (yankId I)) := by
    exact evalExprs_yankFluxArgs_ofLocals
      (by simpa [locals1] using yankLocalsAfterClaw_get_id I)
      (by simpa [locals1] using yankLocalsAfterClaw_get_bids I)
      (by simpa [locals1] using yankLocalsAfterClaw_get_ilk I)
  have hdecVat : config.externalABI.decode? "flux" outVat = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hvatBlock :
      ExecBlock config { contract := contract, locals := locals1 } evmCat
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, sender, .storage (bidsF (.var "id") "lot")]
          "_fluxRet")
        (.ok { contract := contract, locals := locals2 } evmVat) := by
    simpa [checkedExternalCallStmts, locals2, locals1] using
      checkedExternalCallSuccess (cfg := config) (C := contract) (evm := evmCat)
        (evm' := evmVat) (locals := locals1) (receiver := .storage vatRef)
        (retVar := "_fluxRet") (name := "flux")
        (target := flipperVatAddress evmCat.accountMap evmCat.executionEnv) (sendVal := 0)
        (args := [.storage ilkRef, thisAddr, sender, .storage (bidsF (.var "id") "lot")])
        (argVals := yankFluxArgValsOf evmCat (yankId I)) (out := outVat) (perm := true)
        (value := []) hguardVat hvat hargsVat hcallVat hdecVat
  have htail' :
      ExecBlock config { contract := contract, locals := locals2 } evmVat
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet" ++
        [ .delete (bidRef (.var "id")) ])
        r := by
    simpa [locals2, locals1] using htail
  have hvatTail :
      ExecBlock config { contract := contract, locals := locals1 } evmCat
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, sender, .storage (bidsF (.var "id") "lot")]
          "_fluxRet" ++
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet" ++
        [ .delete (bidRef (.var "id")) ]))
        r := by
    exact execBlock_append hvatBlock htail'
  have hcalls :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage catRef) "claw" (.intLit 0)
          [.storage (bidsF (.var "id") "tab")] "_clawRet" ++
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, sender, .storage (bidsF (.var "id") "lot")]
          "_fluxRet" ++
        checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet" ++
        [ .delete (bidRef (.var "id")) ]))
        r := by
    exact execBlock_append hcatBlock hvatTail
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hauthGuard) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hbidGuard) ?_
  simpa [yankTransition, checkedExternalCallStmts, List.append_assoc] using hcalls

theorem flipperYankSourceBodyMoveNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCat evmVat : EVM.State} {outCat outVat : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (hguy : bidGuyWord (yankId I) σ I ≠ ⟨0⟩)
    (hbidLt :
      (bidBidWord (yankId I) σ I).toNat < (bidTabWord (yankId I) σ I).toNat)
    (hcatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperCatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallCat :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperCatAddress σ I)) "claw" 0
        (yankClawArgVals (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
        (true, evmCat, outCat) true)
    (hvatCode :
      0 <
        (UInt256.ofNat
          ((evmCat.lookupAccount (flipperVatAddress evmCat.accountMap evmCat.executionEnv)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM config evmCat
        (EVM.address (flipperVatAddress evmCat.accountMap evmCat.executionEnv)) "flux" 0
        (yankFluxArgValsOf evmCat (yankId I)) (true, evmVat, outVat) true)
    (hmoveNoCode :
      (UInt256.ofNat
        ((evmVat.lookupAccount
          (flipperVatAddress evmVat.accountMap evmVat.executionEnv)).option
          0 (fun acc => acc.code.size))).toNat = 0) :
    let locals := yankLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let locals1 := (yankLocals I).insert "_clawRet" (collapseReturns [])
    let locals2 := locals1.insert "_fluxRet" (collapseReturns [])
    ExecTransitionBody config contract evm0 locals yankTransition.body .reverted := by
  intro locals evm0 locals1 locals2
  have hvat : evalExpr? config { contract := contract, locals := locals2 } evmVat
      (.storage vatRef) =
        .ok (.address (flipperVatAddress evmVat.accountMap evmVat.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals
      (by simpa [locals2, locals1] using yankLocalsAfterFlux_get_vat I)
  have hguardMove :
      evalExpr? config { contract := contract, locals := locals2 } evmVat
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
    exact evalExpr_flipperVatCodeGuard_false_ofLocals hvat hmoveNoCode
  have hmoveBlock :
      ExecBlock config { contract := contract, locals := locals2 } evmVat
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallNoCode (cfg := config) (C := contract) (evm := evmVat)
        (locals := locals2) (receiver := .storage vatRef) (retVar := "_moveRet")
        (name := "move") (sendVal := 0)
        (args := [sender, .storage (bidsF (.var "id") "guy"),
          .storage (bidsF (.var "id") "bid")])
        hguardMove
  have htail :
      ExecBlock config { contract := contract, locals := locals2 } evmVat
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet" ++
        [ .delete (bidRef (.var "id")) ])
        .reverted := by
    exact execBlock_append_term (s2 := [ .delete (bidRef (.var "id")) ])
      hmoveBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 yankTransition.body
        .reverted := by
    simpa [locals, evm0, locals1, locals2] using
      (flipperYankSourceBlockAfterFluxSuccess (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmCat := evmCat) (evmVat := evmVat) (outCat := outCat) (outVat := outVat)
        hwv hauth hguy hbidLt hcatCode hcallCat hvatCode hcallVat htail)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperYankSourceBodyMoveCallFailure {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCat evmVat evmMove : EVM.State} {outCat outVat outMove : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (hguy : bidGuyWord (yankId I) σ I ≠ ⟨0⟩)
    (hbidLt :
      (bidBidWord (yankId I) σ I).toNat < (bidTabWord (yankId I) σ I).toNat)
    (hcatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperCatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallCat :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperCatAddress σ I)) "claw" 0
        (yankClawArgVals (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
        (true, evmCat, outCat) true)
    (hvatCode :
      0 <
        (UInt256.ofNat
          ((evmCat.lookupAccount (flipperVatAddress evmCat.accountMap evmCat.executionEnv)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM config evmCat
        (EVM.address (flipperVatAddress evmCat.accountMap evmCat.executionEnv)) "flux" 0
        (yankFluxArgValsOf evmCat (yankId I)) (true, evmVat, outVat) true)
    (hmoveCode :
      0 <
        (UInt256.ofNat
          ((evmVat.lookupAccount
            (flipperVatAddress evmVat.accountMap evmVat.executionEnv)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallMove :
      typedCallViaEVM config evmVat
        (EVM.address (flipperVatAddress evmVat.accountMap evmVat.executionEnv)) "move" 0
        (yankMoveArgValsOf evmVat (yankId I)) (false, evmMove, outMove) true) :
    let locals := yankLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let locals1 := (yankLocals I).insert "_clawRet" (collapseReturns [])
    let locals2 := locals1.insert "_fluxRet" (collapseReturns [])
    ExecTransitionBody config contract evm0 locals yankTransition.body .reverted := by
  intro locals evm0 locals1 locals2
  have hvat : evalExpr? config { contract := contract, locals := locals2 } evmVat
      (.storage vatRef) =
        .ok (.address (flipperVatAddress evmVat.accountMap evmVat.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals
      (by simpa [locals2, locals1] using yankLocalsAfterFlux_get_vat I)
  have hguardMove :
      evalExpr? config { contract := contract, locals := locals2 } evmVat
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_flipperVatCodeGuard_true_ofLocals hvat hmoveCode
  have hargsMove :
      evalExprs? config { contract := contract, locals := locals2 } evmVat
        [sender, .storage (bidsF (.var "id") "guy"),
          .storage (bidsF (.var "id") "bid")] =
        .ok (yankMoveArgValsOf evmVat (yankId I)) := by
    exact evalExprs_yankMoveArgs_ofLocals
      (by simpa [locals2, locals1] using yankLocalsAfterFlux_get_id I)
      (by simpa [locals2, locals1] using yankLocalsAfterFlux_get_bids I)
  have hmoveBlock :
      ExecBlock config { contract := contract, locals := locals2 } evmVat
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallFailure (cfg := config) (C := contract) (evm := evmVat)
        (evm' := evmMove) (locals := locals2) (receiver := .storage vatRef)
        (retVar := "_moveRet") (name := "move")
        (target := flipperVatAddress evmVat.accountMap evmVat.executionEnv) (sendVal := 0)
        (args := [sender, .storage (bidsF (.var "id") "guy"),
          .storage (bidsF (.var "id") "bid")])
        (argVals := yankMoveArgValsOf evmVat (yankId I)) (out := outMove) (perm := true)
        hguardMove hvat hargsMove hcallMove
  have htail :
      ExecBlock config { contract := contract, locals := locals2 } evmVat
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet" ++
        [ .delete (bidRef (.var "id")) ])
        .reverted := by
    exact execBlock_append_term (s2 := [ .delete (bidRef (.var "id")) ])
      hmoveBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 yankTransition.body
        .reverted := by
    simpa [locals, evm0, locals1, locals2] using
      (flipperYankSourceBlockAfterFluxSuccess (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmCat := evmCat) (evmVat := evmVat) (outCat := outCat) (outVat := outVat)
        hwv hauth hguy hbidLt hcatCode hcallCat hvatCode hcallVat htail)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperYankSourceBodySuccess {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCat evmVat evmMove : EVM.State} {outCat outVat outMove : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (hguy : bidGuyWord (yankId I) σ I ≠ ⟨0⟩)
    (hbidLt :
      (bidBidWord (yankId I) σ I).toNat < (bidTabWord (yankId I) σ I).toNat)
    (hcatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperCatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallCat :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperCatAddress σ I)) "claw" 0
        (yankClawArgVals (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
        (true, evmCat, outCat) true)
    (hvatCode :
      0 <
        (UInt256.ofNat
          ((evmCat.lookupAccount (flipperVatAddress evmCat.accountMap evmCat.executionEnv)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM config evmCat
        (EVM.address (flipperVatAddress evmCat.accountMap evmCat.executionEnv)) "flux" 0
        (yankFluxArgValsOf evmCat (yankId I)) (true, evmVat, outVat) true)
    (hmoveCode :
      0 <
        (UInt256.ofNat
          ((evmVat.lookupAccount
            (flipperVatAddress evmVat.accountMap evmVat.executionEnv)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallMove :
      typedCallViaEVM config evmVat
        (EVM.address (flipperVatAddress evmVat.accountMap evmVat.executionEnv)) "move" 0
        (yankMoveArgValsOf evmVat (yankId I)) (true, evmMove, outMove) true) :
    let locals := yankLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let locals1 := (yankLocals I).insert "_clawRet" (collapseReturns [])
    let locals2 := locals1.insert "_fluxRet" (collapseReturns [])
    let locals3 := locals2.insert "_moveRet" (collapseReturns [])
    let evmDeleted := bidDeletedEVM evmMove (yankId I)
    ExecTransitionBody config contract evm0 locals yankTransition.body
      (.returned { contract := contract, locals := locals3 } evmDeleted none) := by
  intro locals evm0 locals1 locals2 locals3 evmDeleted
  have hvat : evalExpr? config { contract := contract, locals := locals2 } evmVat
      (.storage vatRef) =
        .ok (.address (flipperVatAddress evmVat.accountMap evmVat.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals
      (by simpa [locals2, locals1] using yankLocalsAfterFlux_get_vat I)
  have hguardMove :
      evalExpr? config { contract := contract, locals := locals2 } evmVat
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_flipperVatCodeGuard_true_ofLocals hvat hmoveCode
  have hargsMove :
      evalExprs? config { contract := contract, locals := locals2 } evmVat
        [sender, .storage (bidsF (.var "id") "guy"),
          .storage (bidsF (.var "id") "bid")] =
        .ok (yankMoveArgValsOf evmVat (yankId I)) := by
    exact evalExprs_yankMoveArgs_ofLocals
      (by simpa [locals2, locals1] using yankLocalsAfterFlux_get_id I)
      (by simpa [locals2, locals1] using yankLocalsAfterFlux_get_bids I)
  have hdecMove : config.externalABI.decode? "move" outMove = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hmoveBlock :
      ExecBlock config { contract := contract, locals := locals2 } evmVat
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet")
        (.ok { contract := contract, locals := locals3 } evmMove) := by
    simpa [checkedExternalCallStmts, locals3, locals2] using
      checkedExternalCallSuccess (cfg := config) (C := contract) (evm := evmVat)
        (evm' := evmMove) (locals := locals2) (receiver := .storage vatRef)
        (retVar := "_moveRet") (name := "move")
        (target := flipperVatAddress evmVat.accountMap evmVat.executionEnv) (sendVal := 0)
        (args := [sender, .storage (bidsF (.var "id") "guy"),
          .storage (bidsF (.var "id") "bid")])
        (argVals := yankMoveArgValsOf evmVat (yankId I)) (out := outMove) (perm := true)
        (value := []) hguardMove hvat hargsMove hcallMove hdecMove
  have hdelete :
      ExecBlock config { contract := contract, locals := locals3 } evmMove
        [ .delete (bidRef (.var "id")) ]
        (.ok { contract := contract, locals := locals3 } evmDeleted) := by
    exact ExecBlock.consNormal
      (ExecStmt.delete (by
        simpa [evmDeleted, locals3, locals2, locals1] using
          deleteStorage_bidRef_of_get_id (evm := evmMove) (id := yankId I)
            (yankLocalsAfterCalls_get_id I) (yankLocalsAfterCalls_get_bids I)))
      ExecBlock.nil
  have htail :
      ExecBlock config { contract := contract, locals := locals2 } evmVat
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet" ++
        [ .delete (bidRef (.var "id")) ])
        (.ok { contract := contract, locals := locals3 } evmDeleted) := by
    exact execBlock_append hmoveBlock hdelete
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 yankTransition.body
        (.ok { contract := contract, locals := locals3 } evmDeleted) := by
    simpa [locals, evm0, locals1, locals2] using
      (flipperYankSourceBlockAfterFluxSuccess (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmCat := evmCat) (evmVat := evmVat) (outCat := outCat) (outVat := outVat)
        hwv hauth hguy hbidLt hcatCode hcallCat hvatCode hcallVat htail)
  simpa [ExecTransitionBody, locals, evm0, locals1, locals2, locals3, evmDeleted] using
    ExecFuncBody.execBlockOK hblock

theorem flipperYankX_vatCallFailure {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {aw target id ret sel selector : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode I g s0 ⟨1482⟩
      (⟨0⟩ :: ⟨260⟩ :: selector :: target :: id :: ret :: sel :: [])
      mem aw out acc k C)
    (houtsz : out.size < UInt256.size) :
    RDrev flipperBytecode g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨1482⟩) (okPc := ⟨1498⟩) h
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    houtsz (by simp)

theorem flipperYankX_vatCallSuccessToMoveStart {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {aw target id ret sel selector : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode I g s0 ⟨1482⟩
      (⟨1⟩ :: ⟨260⟩ :: selector :: target :: id :: ret :: sel :: [])
      mem aw out acc k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨1501⟩
      (selector :: target :: id :: ret :: sel :: []) mem aw out acc k' C' := by
  obtain ⟨k1500, C1500, rd1500⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨1482⟩) (okPc := ⟨1498⟩) h
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp)
  have rd1501 := rd1500.pop (by native_decide) (by evm_ov)
  exact ⟨k1500 + 1, C1500 + 2, by simpa using rd1501⟩

theorem flipperYankX_toMoveExtcodesizeGuard {cA σmem σflux σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {out : ByteArray} {ret sel selector target : UInt256}
    (h : RD flipperBytecode I g s0 ⟨1501⟩
      (selector :: target :: yankId I :: ret :: sel :: [])
      (yankVatFluxCallMem σmem σflux I) (UInt256.ofNat 9) out (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨1599⟩
      (flipperVatTargetWord σ I :: flipperVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨100⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
        flipperVatTargetWord σ I :: yankId I :: ret :: sel :: [])
      (yankVatMoveCallMem σmem σflux σ I) (UInt256.ofNat 9) out (cA, σ) k' C' := by
  let rawVat := flipperSlotWord ⟨2⟩ σ I
  let rawPacked := flipperSlotWord (bidPackedSlotOfWord (yankId I)) σ I
  let base := solcMappingSlot ⟨1⟩ (yankId I)
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hvatClean : UInt256.land rawVat solcAddrMask = flipperVatTargetWord σ I := by
    simp [rawVat, flipperVatTargetWord, flipperAddressReturnWord]
  have hpackedClean : UInt256.land rawPacked solcAddrMask = bidGuyWord (yankId I) σ I := by
    simp [rawPacked, bidGuyWord, flipperAddressReturnWord]
  have hpackedCleanLeft :
      UInt256.land solcAddrMask rawPacked = bidGuyWord (yankId I) σ I := by
    simpa [u256_land_comm] using hpackedClean
  have hmload64Hash :
      (if (⟨64⟩ : UInt256).toNat ≥ (yankMoveHashMem σmem σflux I (yankId I)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((yankMoveHashMem σmem σflux I (yankId I)).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [yankMoveHashMem_size]; decide) (by decide)
      (yankMoveHashMem_read64 σmem σflux I (yankId I))
  have hmload64Move :
      (if (⟨64⟩ : UInt256).toNat ≥ (yankVatMoveCallMem σmem σflux σ I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((yankVatMoveCallMem σmem σflux σ I).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [yankVatMoveCallMem_size]; decide) (by decide)
      (yankVatMoveCallMem_read64 σmem σflux σ I)
  have rd1504 := evm_run h with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k1505, C1505, rd1505raw⟩ := rd1504.sload (by native_decide) (by evm_ov)
  have rd1505 : RD flipperBytecode I g s0 ⟨1505⟩
      (rawVat :: ⟨2⟩ :: selector :: target :: yankId I :: ret :: sel :: [])
      (yankVatFluxCallMem σmem σflux I) (UInt256.ofNat 9) out (cA, σ) k1505 C1505 := by
    simpa [rawVat, flipperSlotWord, solcSlotWord] using rd1505raw
  have rd1523pre := evm_run rd1505 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (yankId I) (yankVatFluxCallMem σmem σflux I))
      (UInt256.ofNat 9) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (yankMoveHashMem σmem σflux I (yankId I)) (UInt256.ofNat 9)
      (by native_decide) mem_cost (by
        dsimp [yankMoveHashMem, wordAt0Mem, Reasoning.Theory.writeWord, writeCascade]
        rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw keccak256 0 base (UInt256.ofNat 9)
      (by native_decide) mem_cost
      (by simpa [base] using yankMoveHashMem_solcMappingSlot σmem σflux I (yankId I))
      (by decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k1524, C1524, rd1524raw⟩ := rd1523pre.sload (by native_decide) (by evm_ov)
  have rd1524 : RD flipperBytecode I g s0 ⟨1524⟩
      (rawPacked :: ⟨64⟩ :: ⟨0⟩ :: rawVat :: base :: selector :: target ::
        yankId I :: ret :: sel :: [])
      (yankMoveHashMem σmem σflux I (yankId I)) (UInt256.ofNat 9) out
      (cA, σ) k1524 C1524 := by
    have hslotAdd :
        base + (⟨2⟩ : UInt256) = solcMappingSlot ⟨1⟩ (yankId I) + ⟨2⟩ := by
      simp [base]
    simpa [rawPacked, bidPackedSlotOfWord, bidBaseOfWord, flipperSlotWord, hslotAdd]
      using rd1524raw
  have rd1525pre := rd1524.swap4 (by native_decide) (by evm_ov)
  obtain ⟨k1526, C1526, rd1526raw⟩ := rd1525pre.sload (by native_decide) (by evm_ov)
  have rd1526 : RD flipperBytecode I g s0 ⟨1526⟩
      (bidBidWord (yankId I) σ I :: ⟨64⟩ :: ⟨0⟩ :: rawVat :: rawPacked ::
        selector :: target :: yankId I :: ret :: sel :: [])
      (yankMoveHashMem σmem σflux I (yankId I)) (UInt256.ofNat 9) out
      (cA, σ) k1526 C1526 := by
    simpa [bidBidWord, bidBaseOfWord, flipperSlotWord, base] using rd1526raw
  let mem1 := Reasoning.Theory.writeWord
    (yankMoveHashMem σmem σflux I (yankId I)) 128
    yankVatMoveSelectorWord
  let mem2 := Reasoning.Theory.writeWord mem1 132 (solcSourceWord I)
  let mem3 := Reasoning.Theory.writeWord mem2 164 (bidGuyWord (yankId I) σ I)
  have rd1538 := evm_run rd1526 with [
    raw dup2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64Hash (by decide) (by evm_ov),
    raw push4 ⟨3140843579⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 mem1 (UInt256.ofNat 9)
      (by native_decide) mem_cost (by
        dsimp [mem1, yankVatMoveSelectorWord, Reasoning.Theory.writeWord]
        rfl) (by decide) (by evm_ov)]
  have rd1544 := evm_run rd1538 with [
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 mem2 (UInt256.ofNat 9)
      (by native_decide) mem_cost (by
        dsimp [mem1, mem2, solcSourceWord, Reasoning.Theory.writeWord]
        rfl) (by decide) (by evm_ov)]
  have rd1560 := evm_run rd1544 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap6 (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 mem3 (UInt256.ofNat 9)
      (by native_decide) mem_cost (by
        rw [hmask160, hpackedCleanLeft]
        dsimp [mem2, mem3, Reasoning.Theory.writeWord]
        rfl) (by decide) (by evm_ov)]
  have rd1568 := evm_run rd1560 with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw mstore 0 (yankVatMoveCallMem σmem σflux σ I) (UInt256.ofNat 9)
      (by native_decide) mem_cost (by
        dsimp [mem1, mem2, mem3, yankVatMoveCallMem, Reasoning.Theory.writeWord,
          writeCascade]
        rfl) (by decide) (by evm_ov)]
  have rd1599 := evm_run rd1568 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64Move (by decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push4 ⟨3140843579⟩ (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  rw [hmask160, hvatClean] at rd1599
  exact ⟨_, _, by
    convert rd1599 using 1 <;> native_decide⟩

theorem flipperYankX_moveNoCode {cA σmem σflux σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out : ByteArray} {ret sel selector target : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) = ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨1501⟩
      (selector :: target :: yankId I :: ret :: sel :: [])
      (yankVatFluxCallMem σmem σflux I) (UInt256.ofNat 9) out (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨_, _, rd1599⟩ := flipperYankX_toMoveExtcodesizeGuard h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨1599⟩) (okPc := ⟨1611⟩) rd1599
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem flipperYankX_toMoveCall {cA σmem σflux σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out : ByteArray} {ret sel selector target : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨1501⟩
      (selector :: target :: yankId I :: ret :: sel :: [])
      (yankVatFluxCallMem σmem σflux I) (UInt256.ofNat 9) out (cA, σ) k C) :
    ∃ gasWord k' C', RD flipperBytecode I g s0 ⟨1614⟩
      (gasWord :: flipperVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
        flipperVatTargetWord σ I :: yankId I :: ret :: sel :: [])
      (yankVatMoveCallMem σmem σflux σ I) (UInt256.ofNat 9) out (cA, σ) k' C' := by
  obtain ⟨_, _, rd1599⟩ := flipperYankX_toMoveExtcodesizeGuard h
  obtain ⟨gasWord, k1614, C1614, rd1614⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1599⟩) (okPc := ⟨1611⟩) rd1599
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k1614, C1614, by simpa using rd1614⟩

theorem flipperYankX_movePostCall
    {cA0 gh bl σbase σ₀ A I} {g : UInt256}
    {cA : Batteries.RBSet AccountAddress compare}
    {σmem σflux σ : AccountMap} {Acur : Substate}
    {k C : ℕ} {out0 : ByteArray} {ret sel selector target : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (h : RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨1501⟩
      (selector :: target :: yankId I :: ret :: sel :: [])
      (yankVatFluxCallMem σmem σflux I) (UInt256.ofNat 9) out0 (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨1615⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: ⟨3140843579⟩ ::
          flipperVatTargetWord σ I :: yankId I :: ret :: sel :: [])
        (yankVatMoveCallMem σmem σflux σ I) (UInt256.ofNat 9) out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        ({ initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ, substate := Acur, createdAccounts := cA })
        (EVM.address (flipperVatAddress σ I)) "move" 0
        (yankMoveArgValsOf
          ({ initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ, substate := Acur, createdAccounts := cA })
          (yankId I))
        (z,
          { { initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ, substate := Acur, createdAccounts := cA } with
            accountMap := σ', substate := A', createdAccounts := cA' },
          out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd1614⟩ := flipperYankX_toMoveCall hcodeSize h
  obtain ⟨cA', σ', z, out, A_in, callGas, k1615, C1615, hΘpack, rd1615raw,
      houtsz⟩ :=
    RD.call rd1614 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k1615, C1615, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
          (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 9 := by
      native_decide
    have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
      rfl
    have rd1615 : RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨1615⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: ⟨3140843579⟩ ::
          flipperVatTargetWord σ I :: yankId I :: ret :: sel :: [])
        (out.write 0 (yankVatMoveCallMem σmem σflux σ I) 128
          (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 9) out (cA', σ') k1615 C1615 :=
      haw ▸ rd1615raw
    rw [hmin, byteArray_write_len_zero] at rd1615
    exact rd1615
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := flipperVatTargetWord σ I)
      (mem := yankVatMoveCallMem σmem σflux σ I) (inOff := ⟨128⟩) (inSize := ⟨100⟩)
      (fun hdepthEq => by
        have hEq : I.depth = (1024 : Fin 1025) := by
          simpa [initState] using hdepthEq
        exact absurd hdepth (by rw [hEq]; decide))
      (flipperVatEvmAddress_eq_target_of_accountMapEquiv (accountMapEquiv.refl σ))
      ?_ ?_
    · simpa [yankMoveArgValsOf, initState, flipperSlotWord, solcSlotWord,
        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        bidGuyWord, bidPackedSlotOfWord, bidBaseOfWord, flipperAddressReturnWord] using
        yankVatMoveCallMem_encode σmem σflux σ I
    · simpa [initState, hperm] using hΘ

theorem flipperYankX_moveCallFailure {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {aw target id ret sel selector : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode I g s0 ⟨1615⟩
      (⟨0⟩ :: ⟨228⟩ :: selector :: target :: id :: ret :: sel :: [])
      mem aw out acc k C)
    (houtsz : out.size < UInt256.size) :
    RDrev flipperBytecode g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨1615⟩) (okPc := ⟨1631⟩) h
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    houtsz (by simp)

theorem flipperYankX_moveCallSuccessToDeleteStart {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {aw target id ret sel selector : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode I g s0 ⟨1615⟩
      (⟨1⟩ :: ⟨228⟩ :: selector :: target :: id :: ret :: sel :: [])
      mem aw out acc k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨1635⟩
      (target :: id :: ret :: sel :: []) mem aw out acc k' C' := by
  obtain ⟨_, _, rd1633⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨1615⟩) (okPc := ⟨1631⟩) h
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp)
  have rd1635 := evm_run rd1633 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd1635⟩

noncomputable abbrev yankDeleteHashMem (σmem σflux σ : AccountMap) (I : ExecutionEnv)
    (id : UInt256) : ByteArray :=
  writeCascade (yankVatMoveCallMem σmem σflux σ I) [(0, id), (32, ⟨1⟩)]

abbrev yankBidDeleteAccountMap (I : ExecutionEnv) (σ : AccountMap) (id : UInt256) :
    AccountMap :=
  bidDeleteCollapsedAccountMap I.codeOwner σ id

theorem yankDeleteHashMem_size (σmem σflux σ : AccountMap) (I : ExecutionEnv)
    (id : UInt256) :
    (yankDeleteHashMem σmem σflux σ I id).size = 260 := by
  unfold yankDeleteHashMem
  apply writeCascade_size_of_base
  · exact yankVatMoveCallMem_size σmem σflux σ I
  · simp [WriteGapsOk]
  · rfl

theorem yankDeleteHashMem_read0 (σmem σflux σ : AccountMap) (I : ExecutionEnv)
    (id : UInt256) :
    (yankDeleteHashMem σmem σflux σ I id).readWithPadding 0 32 =
      UInt256.toByteArray id := by
  unfold yankDeleteHashMem
  exact writeCascade_read_word_of_head_of_base
    (yankVatMoveCallMem σmem σflux σ I) (base := 260) (off := 0) (word := id)
    (rest := [(32, (⟨1⟩ : UInt256))])
    (yankVatMoveCallMem_size σmem σflux σ I)
    (by native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem yankDeleteHashMem_read32 (σmem σflux σ : AccountMap) (I : ExecutionEnv)
    (id : UInt256) :
    (yankDeleteHashMem σmem σflux σ I id).readWithPadding 32 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold yankDeleteHashMem
  rw [writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord (yankVatMoveCallMem σmem σflux σ I) 0 id) (base := 260) (off := 32)
    (word := (⟨1⟩ : UInt256)) (rest := [])
    (by
      rw [writeWord_size]
      · rw [yankVatMoveCallMem_size]; native_decide
      · rw [yankVatMoveCallMem_size]; native_decide)
    (by native_decide)
    (by simp [WindowDisjointFromWrites])

theorem yankDeleteHashMem_read0_64 (σmem σflux σ : AccountMap) (I : ExecutionEnv)
    (id : UInt256) :
    (yankDeleteHashMem σmem σflux σ I id).readWithPadding 0 64 =
      UInt256.toByteArray id ++ UInt256.toByteArray (⟨1⟩ : UInt256) := by
  rw [byteArray_readWithPadding_split (yankDeleteHashMem σmem σflux σ I id) 0 32 32
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [yankDeleteHashMem_size]; omega)]
  rw [yankDeleteHashMem_read0, yankDeleteHashMem_read32]

theorem yankDeleteHashMem_solcMappingSlot (σmem σflux σ : AccountMap) (I : ExecutionEnv)
    (id : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((yankDeleteHashMem σmem σflux σ I id).readWithPadding 0 64))) =
      solcMappingSlot ⟨1⟩ id := by
  rw [yankDeleteHashMem_read0_64]
  unfold solcMappingSlot
  exact mappingSlot_single id ⟨1⟩

theorem yankSetAddressOffset0Word_zero (old : UInt256) :
    setAddressOffset0Word old ⟨0⟩ =
      UInt256.land old (UInt256.lnot solcAddrMask) := by
  rw [setAddressOffset0Word]
  rw [show UInt256.land (⟨0⟩ : UInt256) solcAddrMask = ⟨0⟩ by native_decide]
  exact u256_lor_zero _

theorem flipperYankX_deleteReturn {I} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σmem σflux σcall σ : AccountMap}
    {k C : ℕ} {out : ByteArray} {target id sel : UInt256}
    (hperm : I.perm = true)
    (h : RD flipperBytecode I g s0 ⟨1635⟩
      (target :: id :: ⟨323⟩ :: sel :: [])
      (yankVatMoveCallMem σmem σflux σcall I) (UInt256.ofNat 9) out (cA, σ) k C) :
    RDret flipperBytecode g s0 (cA, yankBidDeleteAccountMap I σ id) ByteArray.empty := by
  let base := bidBaseOfWord id
  let memHash := yankDeleteHashMem σmem σflux σcall I id
  let σ0 := sstoreAccountMap I.codeOwner σ base ⟨0⟩
  let σ1 := sstoreAccountMap I.codeOwner σ0 (base + ⟨1⟩) ⟨0⟩
  let σ2 := sstoreAccountMap I.codeOwner σ1 (base + ⟨2⟩) ⟨0⟩
  let old3 := solcSlotWord σ2 I (base + ⟨3⟩)
  let clear3 := setAddressOffset0Word old3 ⟨0⟩
  let σ3 := sstoreAccountMap I.codeOwner σ2 (base + ⟨3⟩) clear3
  let old4 := solcSlotWord σ3 I (base + ⟨4⟩)
  let clear4 := setAddressOffset0Word old4 ⟨0⟩
  let σ4 := sstoreAccountMap I.codeOwner σ3 (base + ⟨4⟩) clear4
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (memHash.readWithPadding 0 64))) =
        base := by
    simpa [memHash, base, bidBaseOfWord] using
      yankDeleteHashMem_solcMappingSlot σmem σflux σcall I id
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hclear3 :
      UInt256.land (UInt256.lnot solcAddrMask) old3 = clear3 := by
    dsimp [clear3]
    rw [u256_land_comm, yankSetAddressOffset0Word_zero]
  have hclear4 :
      UInt256.land (UInt256.lnot solcAddrMask) old4 = clear4 := by
    dsimp [clear4]
    rw [u256_land_comm, yankSetAddressOffset0Word_zero]
  have rd1648 := evm_run h with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem id (yankVatMoveCallMem σmem σflux σcall I))
      (UInt256.ofNat 9)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 memHash (UInt256.ofNat 9)
      (by native_decide) mem_cost (by
        dsimp [memHash, yankDeleteHashMem, wordAt0Mem, Reasoning.Theory.writeWord,
          writeCascade]
        rfl) (by decide) (by evm_ov)]
  have rd1654 := evm_run rd1648 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw keccak256 0 base (UInt256.ofNat 9)
      (by native_decide) mem_cost hslot (by decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  obtain ⟨k1655, C1655, rd1655raw⟩ := rd1654.sstore hperm (by native_decide) (by evm_ov)
  have rd1655 : RD flipperBytecode I g s0 ⟨1655⟩
      (base :: ⟨1⟩ :: ⟨0⟩ :: ⟨323⟩ :: sel :: [])
      memHash (UInt256.ofNat 9) out (cA, σ0) k1655 C1655 := by
    simpa [σ0] using rd1655raw
  have rd1660 := evm_run rd1655 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k1661, C1661, rd1661raw⟩ := rd1660.sstore hperm (by native_decide) (by evm_ov)
  have rd1661 : RD flipperBytecode I g s0 ⟨1661⟩
      (base :: ⟨0⟩ :: ⟨323⟩ :: sel :: [])
      memHash (UInt256.ofNat 9) out (cA, σ1) k1661 C1661 := by
    simpa [σ1] using rd1661raw
  have rd1667 := evm_run rd1661 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k1668, C1668, rd1668raw⟩ := rd1667.sstore hperm (by native_decide) (by evm_ov)
  have rd1668 : RD flipperBytecode I g s0 ⟨1668⟩
      (base :: ⟨0⟩ :: ⟨323⟩ :: sel :: [])
      memHash (UInt256.ofNat 9) out (cA, σ2) k1668 C1668 := by
    simpa [σ2] using rd1668raw
  have rd1672 := evm_run rd1668 with [
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k1674, C1674, rd1674raw⟩ := rd1672.sload (by native_decide) (by evm_ov)
  have rd1674 : RD flipperBytecode I g s0 ⟨1674⟩
      (old3 :: (base + ⟨3⟩) :: base :: ⟨0⟩ :: ⟨323⟩ :: sel :: [])
      memHash (UInt256.ofNat 9) out (cA, σ2) k1674 C1674 := by
    simpa [old3, solcSlotWord] using rd1674raw
  have rd1688 := evm_run rd1674 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  rw [hmask160, hclear3] at rd1688
  obtain ⟨k1689, C1689, rd1689raw⟩ := rd1688.sstore hperm (by native_decide) (by evm_ov)
  have rd1689 : RD flipperBytecode I g s0 ⟨1689⟩
      (UInt256.lnot solcAddrMask :: base :: ⟨0⟩ :: ⟨323⟩ :: sel :: [])
      memHash (UInt256.ofNat 9) out (cA, σ3) k1689 C1689 := by
    simpa [σ3, clear3] using rd1689raw
  have rd1693 := evm_run rd1689 with [
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k1695, C1695, rd1695raw⟩ := rd1693.sload (by native_decide) (by evm_ov)
  have rd1695 : RD flipperBytecode I g s0 ⟨1695⟩
      (old4 :: (base + ⟨4⟩) :: UInt256.lnot solcAddrMask :: base :: ⟨0⟩ ::
        ⟨323⟩ :: sel :: [])
      memHash (UInt256.ofNat 9) out (cA, σ3) k1695 C1695 := by
    simpa [old4, solcSlotWord] using rd1695raw
  have rd1699 := evm_run rd1695 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  rw [hclear4] at rd1699
  obtain ⟨k1700, C1700, rd1700raw⟩ := rd1699.sstore hperm (by native_decide) (by evm_ov)
  have rd1700 : RD flipperBytecode I g s0 ⟨1700⟩
      (base :: ⟨0⟩ :: ⟨323⟩ :: sel :: [])
      memHash (UInt256.ofNat 9) out (cA, σ4) k1700 C1700 := by
    simpa [σ4, clear4] using rd1700raw
  have rd1703 := evm_run rd1700 with [
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hbase5 : (⟨5⟩ : UInt256) + base = base + ⟨5⟩ := u256_add_comm _ _
  rw [hbase5] at rd1703
  obtain ⟨k1704, C1704, rd1704raw⟩ := rd1703.sstore hperm (by native_decide) (by evm_ov)
  have rd1704 : RD flipperBytecode I g s0 ⟨1704⟩
      (⟨323⟩ :: sel :: []) memHash (UInt256.ofNat 9) out
      (cA, yankBidDeleteAccountMap I σ id) k1704 C1704 := by
    simpa [yankBidDeleteAccountMap, bidDeleteCollapsedAccountMap, base, σ0, σ1, σ2,
      σ3, σ4, old3, old4, clear3, clear4, solcSlotWord] using rd1704raw
  have rd323 := rd1704.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd324 := rd323.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd324 (by native_decide) (by evm_ov)

theorem flipperYankX_deleteReturnFromPostCall {cA gh bl σmem σflux σcall σ σ₀ A I}
    {g : UInt256} {cA' : Batteries.RBSet AccountAddress compare} {k C : ℕ}
    {out : ByteArray} (hperm : I.perm = true)
    (h : RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σmem σ₀ (Sat256.ofUInt256 g) A I) ⟨1635⟩
      (flipperVatTargetWord σcall I :: yankId I :: ⟨323⟩ :: flipperSelWord I :: [])
      (yankVatMoveCallMem σmem σflux σcall I) (UInt256.ofNat 9) out (cA', σ) k C) :
    RDret flipperBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σmem σ₀ (Sat256.ofUInt256 g) A I)
      (cA', yankBidDeleteAccountMap I σ (yankId I)) ByteArray.empty :=
  flipperYankX_deleteReturn (target := flipperVatTargetWord σcall I)
    (id := yankId I) (sel := flipperSelWord I) hperm h

end Benchmarks.Dss.Flipper
