import Benchmarks.Dss.Flipper.Dispatch
import Benchmarks.Dss.Flipper.BidAccess
import Benchmarks.Dss.Flipper.ExternalTargets
import Benchmarks.Dss.Flipper.ExternalCallTransport
import Reasoning.ExternalCall
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## `yank(uint256)` -/

abbrev yankId (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev yankLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "id" (.int (Int.ofNat (yankId I).toNat))

noncomputable abbrev yankAuthMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem

noncomputable abbrev yankHashMem0 (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (yankId I) ⟨1⟩ (yankAuthMem I)

noncomputable abbrev yankHashMem1 (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (yankId I) ⟨1⟩ (yankHashMem0 I)

abbrev yankCatSelectorWord : UInt256 :=
  UInt256.shiftLeft (⟨3865913243⟩ : UInt256) ⟨224⟩

abbrev yankVatFluxSelectorWord : UInt256 :=
  UInt256.shiftLeft (⟨814276375⟩ : UInt256) ⟨225⟩

noncomputable abbrev yankCatHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (yankId I) ⟨1⟩ (yankHashMem1 I)

noncomputable abbrev yankCatSelectorMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray yankCatSelectorWord).write 0 (yankCatHashMem I) 128 32

noncomputable abbrev yankCatCallMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (bidTabWord (yankId I) σ I)).write 0
    (yankCatSelectorMem I) 132 32

noncomputable abbrev yankVatHashMem (σmem : AccountMap) (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (yankId I) ⟨1⟩ (yankCatCallMem σmem I)

noncomputable abbrev yankVatFluxSelectorMem (σmem : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray yankVatFluxSelectorWord).write 0 (yankVatHashMem σmem I) 128 32

noncomputable abbrev yankVatFluxIlkMem (σmem σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray (flipperSlotWord ⟨3⟩ σ I)).write 0
    (yankVatFluxSelectorMem σmem I) 132 32

noncomputable abbrev yankVatFluxThisMem (σmem σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray (EVM.word I.codeOwner.val)).write 0
    (yankVatFluxIlkMem σmem σ I) 164 32

noncomputable abbrev yankVatFluxSenderMem (σmem σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray (solcSourceWord I)).write 0
    (yankVatFluxThisMem σmem σ I) 196 32

noncomputable abbrev yankVatFluxCallMem (σmem σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray (bidLotWord (yankId I) σ I)).write 0
    (yankVatFluxSenderMem σmem σ I) 228 32

abbrev flipperYankAlreadyDentWord : UInt256 :=
  ⟨31853446598541861569097437671217369822380866045848489383477571240059572584448⟩

theorem yankHashMem1_size (I : ExecutionEnv) :
    (yankHashMem1 I).size = 96 := by
  unfold yankHashMem1 yankHashMem0 yankAuthMem
  exact twoWordHashMem_size_96 (yankId I) ⟨1⟩
    (twoWordHashMem_size_96 (yankId I) ⟨1⟩
      (twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size))

theorem yankHashMem1_read64 (I : ExecutionEnv) :
    (yankHashMem1 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold yankHashMem1 yankHashMem0 yankAuthMem
  exact twoWordHashMem_read64 (yankId I) ⟨1⟩
    (twoWordHashMem_size_96 (yankId I) ⟨1⟩
      (twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size))
    (twoWordHashMem_read64 (yankId I) ⟨1⟩
      (twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size)
      (twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
        solcFreePtrMem_read64))

theorem yankCatHashMem_size (I : ExecutionEnv) :
    (yankCatHashMem I).size = 96 := by
  unfold yankCatHashMem
  exact twoWordHashMem_size_96 (yankId I) ⟨1⟩ (yankHashMem1_size I)

theorem yankCatHashMem_read64 (I : ExecutionEnv) :
    (yankCatHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold yankCatHashMem
  exact twoWordHashMem_read64 (yankId I) ⟨1⟩ (yankHashMem1_size I)
    (yankHashMem1_read64 I)

theorem yankCatSelectorMem_size (I : ExecutionEnv) :
    (yankCatSelectorMem I).size = 160 := by
  unfold yankCatSelectorMem
  exact toByteArray_write32_size_of_ge (yankCatHashMem I) yankCatSelectorWord 128 96 160
    (yankCatHashMem_size I) (by omega) (by native_decide) (by omega)

theorem yankCatSelectorMem_read64 (I : ExecutionEnv) :
    (yankCatSelectorMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold yankCatSelectorMem
  rw [toByteArray_write_read_below_of_gap yankCatSelectorWord (yankCatHashMem I) 128 64]
  · exact yankCatHashMem_read64 I
  · rw [yankCatHashMem_size]
  · omega
  · rw [yankCatHashMem_size]
    native_decide

theorem yankCatCallMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (yankCatCallMem σ I).size = 164 := by
  unfold yankCatCallMem
  exact toByteArray_write32_size_of_le (yankCatSelectorMem I)
    (bidTabWord (yankId I) σ I) 132 160 164
    (yankCatSelectorMem_size I)
    (by rw [yankCatSelectorMem_size]; omega)
    (by native_decide)

theorem yankCatCallMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (yankCatCallMem σ I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold yankCatCallMem
  rw [toByteArray_write_read_below_of_gap
    (bidTabWord (yankId I) σ I) (yankCatSelectorMem I) 132 64]
  · exact yankCatSelectorMem_read64 I
  · rw [yankCatSelectorMem_size]
    omega
  · omega
  · rw [yankCatSelectorMem_size]
    native_decide

theorem yankCatSelectorWord_prefix :
    (UInt256.toByteArray yankCatSelectorWord).extract 0 4 = catClawSelector := by
  native_decide

theorem yankCatCallMem_read (σ : AccountMap) (I : ExecutionEnv) :
    (yankCatCallMem σ I).readWithPadding 128 36 =
      catClawSelector ++ UInt256.toByteArray (bidTabWord (yankId I) σ I) := by
  rw [byteArray_readWithPadding_split (yankCatCallMem σ I) 128 4 32
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [yankCatCallMem_size])]
  · unfold yankCatCallMem
    rw [toByteArray_write_read_below_len_of_gap
      (bidTabWord (yankId I) σ I)
      (yankCatSelectorMem I)
      132 128 4]
    · rw [toByteArray_write_read_window_of_gap yankCatSelectorWord (yankCatHashMem I) 128 0 4
        (by omega) (by omega) (by norm_num)]
      · change (UInt256.toByteArray yankCatSelectorWord).extract 0 4 ++
            ((UInt256.toByteArray (bidTabWord (yankId I) σ I)).write 0
              (yankCatSelectorMem I) 132 32).readWithPadding (128 + 4) 32 =
          catClawSelector ++ UInt256.toByteArray (bidTabWord (yankId I) σ I)
        rw [yankCatSelectorWord_prefix]
        rw [toByteArray_write_read_back_of_gap (bidTabWord (yankId I) σ I)
          (yankCatSelectorMem I) 132 (by
            rw [yankCatSelectorMem_size]
            native_decide)]
      · rw [yankCatHashMem_size]
        native_decide
    · rw [yankCatSelectorMem_size]
      omega
    · omega
    · omega
    · omega
    · rw [yankCatSelectorMem_size]
      native_decide

theorem yankEncodeABIValue_uint256_word (w : UInt256) :
    encodeABIValue? uint256 (.int (Int.ofNat w.toNat)) =
      some (UInt256.toByteArray w).toList := by
  have hlt : w.toNat < EVM.twoPow 256 := w.val.isLt
  have hword : EVM.word w.toNat = w := u256_ofNat_toNat w
  simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hlt, hword,
    toByteArray_eq_toBytesBE, byteArray_toList_eq]

theorem yankCatCallMem_encode (σ : AccountMap) (I : ExecutionEnv) :
    config.externalABI.encode? "claw"
      [Value.int (Int.ofNat (bidTabWord (yankId I) σ I).toNat)] =
        some ((yankCatCallMem σ I).readWithPadding 128 36) := by
  rw [yankCatCallMem_read]
  unfold config externalABI
  simp only [if_true]
  unfold ABI.encodeCallWithSelector?
  have hpayload :
      encodeABIValues? [uint256]
        [Value.int (Int.ofNat (bidTabWord (yankId I) σ I).toNat)] =
          some (UInt256.toByteArray (bidTabWord (yankId I) σ I)).toList := by
    unfold encodeABIValues?
    rw [show abiTupleHeadSize? [uint256] = some 32 by native_decide]
    simp only [encodeABIValuesFrom?, Option.bind, bind]
    rw [yankEncodeABIValue_uint256_word]
    simp [show isDynamicABIType uint256 = false by native_decide]
  rw [hpayload]
  apply congrArg some
  apply ByteArray.ext
  simp [catClawSelector, byteArray_toList_eq]

theorem yankVatHashMem_size (σmem : AccountMap) (I : ExecutionEnv) :
    (yankVatHashMem σmem I).size = 164 := by
  unfold yankVatHashMem twoWordHashMem wordAt32Mem wordAt0Mem
  have h0 :
      ((UInt256.toByteArray (yankId I)).write 0 (yankCatCallMem σmem I) 0 32).size =
        164 := by
    exact toByteArray_write32_size_of_le (yankCatCallMem σmem I) (yankId I) 0 164 164
      (yankCatCallMem_size σmem I)
      (by rw [yankCatCallMem_size]; omega)
      (by omega)
  exact toByteArray_write32_size_of_le
    ((UInt256.toByteArray (yankId I)).write 0 (yankCatCallMem σmem I) 0 32)
    (⟨1⟩ : UInt256) 32 164 164 h0
    (by rw [h0]; omega)
    (by omega)

theorem yankVatHashMem_read64 (σmem : AccountMap) (I : ExecutionEnv) :
    (yankVatHashMem σmem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold yankVatHashMem twoWordHashMem wordAt32Mem wordAt0Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by
        have h0 :
            ((UInt256.toByteArray (yankId I)).write 0 (yankCatCallMem σmem I) 0 32).size =
              164 := by
          exact toByteArray_write32_size_of_le (yankCatCallMem σmem I) (yankId I) 0 164 164
            (yankCatCallMem_size σmem I)
            (by rw [yankCatCallMem_size]; omega)
            (by omega)
        rw [h0]; omega)
      (by omega)
      (by
        have h0 :
            ((UInt256.toByteArray (yankId I)).write 0 (yankCatCallMem σmem I) 0 32).size =
              164 := by
          exact toByteArray_write32_size_of_le (yankCatCallMem σmem I) (yankId I) 0 164 164
            (yankCatCallMem_size σmem I)
            (by rw [yankCatCallMem_size]; omega)
            (by omega)
        rw [h0]; omega)]
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [yankCatCallMem_size]; omega)
      (by omega)
      (by rw [yankCatCallMem_size]; omega)]
  exact yankCatCallMem_read64 σmem I

theorem yankVatHashMem_read0 (σmem : AccountMap) (I : ExecutionEnv) :
    (yankVatHashMem σmem I).readWithPadding 0 32 = UInt256.toByteArray (yankId I) := by
  unfold yankVatHashMem twoWordHashMem wordAt32Mem wordAt0Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by
        have h0 :
            ((UInt256.toByteArray (yankId I)).write 0 (yankCatCallMem σmem I) 0 32).size =
              164 := by
          exact toByteArray_write32_size_of_le (yankCatCallMem σmem I) (yankId I) 0 164 164
            (yankCatCallMem_size σmem I)
            (by rw [yankCatCallMem_size]; omega)
            (by omega)
        rw [h0]; omega)
      (by omega)]
  exact toByteArray_write32_read_back (yankCatCallMem σmem I) (yankId I) 0
    (by rw [yankCatCallMem_size]; omega)

theorem yankVatHashMem_read32 (σmem : AccountMap) (I : ExecutionEnv) :
    (yankVatHashMem σmem I).readWithPadding 32 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold yankVatHashMem twoWordHashMem wordAt32Mem
  exact toByteArray_write32_read_back (wordAt0Mem (yankId I) (yankCatCallMem σmem I))
    (⟨1⟩ : UInt256) 32
    (by
      unfold wordAt0Mem
      have h0 :
          ((UInt256.toByteArray (yankId I)).write 0 (yankCatCallMem σmem I) 0 32).size =
            164 := by
        exact toByteArray_write32_size_of_le (yankCatCallMem σmem I) (yankId I) 0 164 164
          (yankCatCallMem_size σmem I)
          (by rw [yankCatCallMem_size]; omega)
          (by omega)
      rw [h0]; omega)

theorem yankVatHashMem_read0_64 (σmem : AccountMap) (I : ExecutionEnv) :
    (yankVatHashMem σmem I).readWithPadding 0 64 =
      UInt256.toByteArray (yankId I) ++ UInt256.toByteArray (⟨1⟩ : UInt256) := by
  rw [byteArray_readWithPadding_split (yankVatHashMem σmem I) 0 32 32
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [yankVatHashMem_size]; omega)]
  rw [yankVatHashMem_read0, yankVatHashMem_read32]

theorem yankVatHashMem_solcMappingSlot (σmem : AccountMap) (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((yankVatHashMem σmem I).readWithPadding 0 64))) =
      solcMappingSlot ⟨1⟩ (yankId I) := by
  rw [yankVatHashMem_read0_64]
  unfold solcMappingSlot
  exact mappingSlot_single (yankId I) ⟨1⟩

theorem yankVatFluxCallMem_eq_cascade (σmem σ : AccountMap) (I : ExecutionEnv) :
    yankVatFluxCallMem σmem σ I =
      writeCascade (yankVatHashMem σmem I)
        [(128, yankVatFluxSelectorWord),
         (132, flipperSlotWord ⟨3⟩ σ I),
         (164, EVM.word I.codeOwner.val),
         (196, solcSourceWord I),
         (228, bidLotWord (yankId I) σ I)] := by
  rfl

theorem yankVatFluxCallMem_size (σmem σ : AccountMap) (I : ExecutionEnv) :
    (yankVatFluxCallMem σmem σ I).size = 260 := by
  rw [yankVatFluxCallMem_eq_cascade]
  exact writeCascade_size_of_base (yankVatHashMem σmem I)
    [(128, yankVatFluxSelectorWord),
     (132, flipperSlotWord ⟨3⟩ σ I),
     (164, EVM.word I.codeOwner.val),
     (196, solcSourceWord I),
     (228, bidLotWord (yankId I) σ I)]
    (yankVatHashMem_size σmem I)
    (by simp [WriteGapsOk] <;> native_decide)
    (by norm_num [writeCascadeSize])

theorem yankVatFluxCallMem_read64 (σmem σ : AccountMap) (I : ExecutionEnv) :
    (yankVatFluxCallMem σmem σ I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [yankVatFluxCallMem_eq_cascade]
  rw [writeCascade_read_preserved_of_base (yankVatHashMem σmem I)
    [(128, yankVatFluxSelectorWord),
     (132, flipperSlotWord ⟨3⟩ σ I),
     (164, EVM.word I.codeOwner.val),
     (196, solcSourceWord I),
     (228, bidLotWord (yankId I) σ I)]
    (yankVatHashMem_size σmem I)
    (by simp [WindowDisjointFromWrites] <;> native_decide)]
  exact yankVatHashMem_read64 σmem I

theorem yankLocals_get_id (I : ExecutionEnv) :
    (yankLocals I).get? "id" =
      some (.int (Int.ofNat (yankId I).toNat)) := by
  rw [yankLocals, store_get_self]

theorem yankLocals_get_bids (I : ExecutionEnv) :
    (yankLocals I).get? "bids" = none := by
  rw [yankLocals, store_get_ne _ _ (by decide)]
  simp

theorem yankLocals_get_cat (I : ExecutionEnv) :
    (yankLocals I).get? "cat" = none := by
  rw [yankLocals, store_get_ne _ _ (by decide)]
  simp

theorem flipperDecode_yank_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (yankTransition.params.map Param.name)
      (transitionSignature yankTransition).paramTypes I.calldata =
        some (yankLocals I) := by
  simpa [config, yankTransition, transitionSignature, yankLocals, yankId]
    using (flipperDecodeCalldataLegacyUInt256_ok (cd := I.calldata) (x := "id") hsz36)

theorem flipperDecode_yank_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (yankTransition.params.map Param.name)
      (transitionSignature yankTransition).paramTypes I.calldata = none := by
  simpa [config, yankTransition, transitionSignature]
    using (flipperDecodeCalldataLegacyUInt256_none_short (cd := I.calldata)
      (x := "id") hsz4 hshort)

theorem flipperReachYankBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flipperSelBytes 18)) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨294⟩ [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flipperSelWord I = ⟨0x26e027f1⟩ :=
    flipperSelWord_eq_of_beq I hsz 0x26 0xe0 0x27 0xf1 ⟨0x26e027f1⟩
      (by native_decide) (by simpa [flipperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat flipperBytecode flipperHighSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperHighLowFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperHighLowFirstArmPc 0))
        (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact flipperReachHighLowBody 0 (by omega) ⟨294⟩ hcode hwv hsz hsize hroot hhigh
    heq0 htake (by jump_dest) (by native_decide)

theorem RD.flipperYankDecodeToRoutine {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨316⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = flipperBytecode)
    (hroutine : (D_J code 0).contains ⟨967⟩ = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨967⟩
      (calldataWord ee.calldata 4 :: ret :: sel :: R) mem aw rdata acc k' C' := by
  subst hwf
  have rd967 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw push2 ⟨967⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) hroutine (by evm_ov)]
  exact ⟨_, _, by simpa [calldataWord] using rd967⟩

theorem flipperYankDecodePushAlreadyDent1201 :
    decode flipperBytecode (⟨1201⟩ : UInt256) =
      some (.Push .PUSH32, some (flipperYankAlreadyDentWord, 32)) := by
  native_decide

theorem flipperYankX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flipperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨294⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨967⟩
        [yankId I, ⟨323⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flipperBytecode) (sel := sel) (entry := ⟨294⟩) (ret := ⟨323⟩)
    (decoded := ⟨316⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by
      exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.flipperYankDecodeToRoutine
    (code := flipperBytecode) (ret := ⟨323⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [yankId] using hroutine⟩

theorem evalExpr_yankGuyNeZero_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguy : bidGuyWord (yankId I) σ I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := yankLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
        .ok (.bool false) := by
  have hguyEval := evalExpr_bidGuy_of_get_id (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := yankLocals I)
    (id := yankId I) (yankLocals_get_id I) (yankLocals_get_bids I)
  have hguyNat : (bidGuyWord (yankId I) σ I).toNat = 0 := by
    rw [hguy]
    rfl
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hguyEval]
  rw [hguyNat]
  simp only [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, bind, pure,
    EvalResult.ofOption]
  norm_num [evalBinaryOp?]
  all_goals
    intro h
    cases h

theorem evalExpr_yankGuyNeZero_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguy : bidGuyWord (yankId I) σ I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := yankLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
        .ok (.bool true) := by
  have hguyEval := evalExpr_bidGuy_of_get_id (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := yankLocals I)
    (id := yankId I) (yankLocals_get_id I) (yankLocals_get_bids I)
  have hguyAddr :
      AccountAddress.ofNat (bidGuyWord (yankId I) σ I).toNat ≠ AccountAddress.ofNat 0 := by
    intro hzeroAddr
    have hmask := keyValueToWord_address_ofNat_mask (bidGuyWord (yankId I) σ I)
    rw [hzeroAddr] at hmask
    have hclean :
        UInt256.land solcAddrMask (bidGuyWord (yankId I) σ I) =
          bidGuyWord (yankId I) σ I := by
      simpa [bidGuyWord, flipperAddressReturnWord, u256_land_comm] using
        (solcAddrMask_clean
          (solcAddrMask_result_canonical
            (flipperSlotWord (bidPackedSlotOfWord (yankId I)) σ I)))
    exact hguy (by simpa [keyValueToWord_address, hclean] using hmask.symm)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hguyEval]
  simp only [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, bind, pure,
    EvalResult.ofOption]
  norm_num [evalBinaryOp?]
  · exact hguyAddr
  all_goals
    intro h
    cases h

theorem evalExpr_yankBidLtTab_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hge : (bidTabWord (yankId I) σ I).toNat ≤ (bidBidWord (yankId I) σ I).toNat) :
    evalExpr? config { contract := contract, locals := yankLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .lt (.storage (bidsF (.var "id") "bid"))
        (.storage (bidsF (.var "id") "tab"))) =
        .ok (.bool false) := by
  have hbidEval := evalExpr_bidBid_of_get_id (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := yankLocals I)
    (id := yankId I) (yankLocals_get_id I) (yankLocals_get_bids I)
  have htabEval := evalExpr_bidTab_of_get_id (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := yankLocals I)
    (id := yankId I) (yankLocals_get_id I) (yankLocals_get_bids I)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hbidEval, htabEval]
  norm_num [evalBinaryOp?]
  · exact hge
  · intro h
    cases h
  · intro h
    cases h

theorem evalExpr_yankBidLtTab_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlt : (bidBidWord (yankId I) σ I).toNat < (bidTabWord (yankId I) σ I).toNat) :
    evalExpr? config { contract := contract, locals := yankLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .lt (.storage (bidsF (.var "id") "bid"))
        (.storage (bidsF (.var "id") "tab"))) =
        .ok (.bool true) := by
  have hbidEval := evalExpr_bidBid_of_get_id (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := yankLocals I)
    (id := yankId I) (yankLocals_get_id I) (yankLocals_get_bids I)
  have htabEval := evalExpr_bidTab_of_get_id (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := yankLocals I)
    (id := yankId I) (yankLocals_get_id I) (yankLocals_get_bids I)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hbidEval, htabEval]
  norm_num [evalBinaryOp?]
  · exact hlt
  · intro h
    cases h
  · intro h
    cases h

abbrev yankClawArgValsOf (evm : EVM.State) (id : UInt256) : List Value :=
  [.int (Int.ofNat
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (bidSlotOfWord id ⟨5⟩)).toNat)]

abbrev yankClawArgVals (evm : EVM.State) : List Value :=
  yankClawArgValsOf evm (yankId evm.executionEnv)

theorem evalExprs_yankClawArgs_ofLocals {evm : EVM.State} {locals : Store} {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExprs? config { contract := contract, locals := locals } evm
      [.storage (bidsF (.var "id") "tab")] = .ok (yankClawArgValsOf evm id) := by
  have htab := evalExpr_bidTab_of_get_id_evm (evm := evm)
    (locals := locals) (id := id) hid hbids
  unfold evalExprs?
  simp only [EvalResult.bind, bind, pure]
  rw [htab]
  rfl

theorem evalExprs_yankClawArgs {evm : EVM.State} :
    evalExprs? config { contract := contract, locals := yankLocals evm.executionEnv } evm
      [.storage (bidsF (.var "id") "tab")] = .ok (yankClawArgVals evm) := by
  exact evalExprs_yankClawArgs_ofLocals (yankLocals_get_id evm.executionEnv)
    (yankLocals_get_bids evm.executionEnv)

theorem yankLocalsAfterClaw_get_id (I : ExecutionEnv) :
    ((yankLocals I).insert "_clawRet" (collapseReturns [])).get? "id" =
      some (.int (Int.ofNat (yankId I).toNat)) := by
  rw [store_get_ne _ _ (by decide)]
  exact yankLocals_get_id I

theorem yankLocalsAfterClaw_get_bids (I : ExecutionEnv) :
    ((yankLocals I).insert "_clawRet" (collapseReturns [])).get? "bids" = none := by
  rw [store_get_ne _ _ (by decide)]
  exact yankLocals_get_bids I

theorem yankLocalsAfterClaw_get_vat (I : ExecutionEnv) :
    ((yankLocals I).insert "_clawRet" (collapseReturns [])).get? "vat" = none := by
  rw [store_get_ne _ _ (by decide)]
  rw [yankLocals, store_get_ne _ _ (by decide)]
  simp

theorem yankLocalsAfterClaw_get_ilk (I : ExecutionEnv) :
    ((yankLocals I).insert "_clawRet" (collapseReturns [])).get? "ilk" = none := by
  rw [store_get_ne _ _ (by decide)]
  rw [yankLocals, store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_yankIlk_ofLocals {evm : EVM.State} {locals : Store}
    (hilk : locals.get? "ilk" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage ilkRef) =
        .ok (.fixedBytes bytes32Width
          (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩))) := by
  rw [evalExpr_storage_scalar
    (t := .bytes bytes32Width)
    (er := ({ base := "ilk", steps := [] } : EvaledStorageRef))
    (loc := bytes32Loc ⟨3⟩)
    (hbase := hilk)
    (her := by
      simp [evalStorageRef, evalStorageRefSteps, ilkRef, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, bytes32St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, ilkRef])]
  exact congrArg EvalResult.ok (flipperStorageLocLoad_bytes32 evm ⟨3⟩)

abbrev yankFluxArgValsOf (evm : EVM.State) (id : UInt256) : List Value :=
  [.fixedBytes bytes32Width
      (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)),
    .address evm.executionEnv.codeOwner,
    .address evm.executionEnv.source,
    .int (Int.ofNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidSlotOfWord id ⟨1⟩)).toNat)]

theorem evalExprs_yankFluxArgs_ofLocals {evm : EVM.State} {locals : Store} {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none)
    (hilk : locals.get? "ilk" = none) :
    evalExprs? config { contract := contract, locals := locals } evm
      [.storage ilkRef, thisAddr, sender, .storage (bidsF (.var "id") "lot")] =
        .ok (yankFluxArgValsOf evm id) := by
  have hilkEval := evalExpr_yankIlk_ofLocals (evm := evm) (locals := locals) hilk
  have hlot := evalExpr_bidLot_of_get_id_evm (evm := evm)
    (locals := locals) (id := id) hid hbids
  simp only [evalExprs?, evalExpr?, envValue, thisAddr, sender, hilkEval, hlot,
    yankFluxArgValsOf, EvalResult.bind, bind, pure]

theorem flipperYankSourceBodyGuyZero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (hguy : bidGuyWord (yankId I) σ I = ⟨0⟩) :
    let locals := yankLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals yankTransition.body .reverted := by
  intro locals evm0
  have hauthGuard := flipperAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, yankLocals]) hauth
  have hguyGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
          .ok (.bool false) := by
    simpa [locals, evm0] using
      evalExpr_yankGuyNeZero_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hguy
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 yankTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauthGuard) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguyGuard)
  simpa [ExecTransitionBody, yankTransition, nonpayable, auth, checkedExternalCallStmts,
    locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperYankSourceBodyNotDent {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (hguy : bidGuyWord (yankId I) σ I ≠ ⟨0⟩)
    (hge : (bidTabWord (yankId I) σ I).toNat ≤ (bidBidWord (yankId I) σ I).toNat) :
    let locals := yankLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals yankTransition.body .reverted := by
  intro locals evm0
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
          (.storage (bidsF (.var "id") "tab"))) = .ok (.bool false) := by
    simpa [locals, evm0] using
      evalExpr_yankBidLtTab_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hge
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 yankTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauthGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hbidGuard)
  simpa [ExecTransitionBody, yankTransition, nonpayable, auth, checkedExternalCallStmts,
    locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperYankSourceBodyCatNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (hguy : bidGuyWord (yankId I) σ I ≠ ⟨0⟩)
    (hbidLt :
      (bidBidWord (yankId I) σ I).toNat < (bidTabWord (yankId I) σ I).toNat)
    (hnoCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (flipperCatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0) :
    let locals := yankLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals yankTransition.body .reverted := by
  intro locals evm0
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
        (.binary .gt (.extCodeSize (.storage catRef)) (.intLit 0)) = .ok (.bool false) := by
    simpa [evm0, initState, flipperCatAddress] using
      evalExpr_flipperCatCodeGuard_false_ofLocals (evm := evm0) (locals := locals) hcat
        hnoCode
  have hcallBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage catRef) "claw" (.intLit 0)
          [.storage (bidsF (.var "id") "tab")] "_clawRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallNoCode (cfg := config) (C := contract) (evm := evm0)
        (locals := locals) (receiver := .storage catRef) (retVar := "_clawRet")
        (name := "claw") (sendVal := 0)
        (args := [.storage (bidsF (.var "id") "tab")]) hguardCat
  have hcallFull :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage catRef) "claw" (.intLit 0)
          [.storage (bidsF (.var "id") "tab")] "_clawRet" ++
        (
        checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, sender, .storage (bidsF (.var "id") "lot")]
          "_fluxRet" ++
        checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet" ++
        [ .delete (bidRef (.var "id")) ]))
        .reverted := by
    exact execBlock_append_term
      (cfg := config)
      (s2 :=
        checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, sender, .storage (bidsF (.var "id") "lot")]
          "_fluxRet" ++
        checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet" ++
        [ .delete (bidRef (.var "id")) ])
      hcallBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 yankTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauthGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hbidGuard) ?_
    simpa [yankTransition, checkedExternalCallStmts, List.append_assoc] using hcallFull
  simpa [ExecTransitionBody, yankTransition, nonpayable, auth, checkedExternalCallStmts,
    locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperYankSourceBodyCatCallFailure {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCat : EVM.State} {outCat : ByteArray}
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
        (false, evmCat, outCat) true) :
    let locals := yankLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals yankTransition.body .reverted := by
  intro locals evm0
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
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0
        [.storage (bidsF (.var "id") "tab")] = .ok (yankClawArgVals evm0) := by
    simpa [locals] using evalExprs_yankClawArgs (evm := evm0)
  have hcallCat' :
      typedCallViaEVM config evm0
        (EVM.address (flipperCatAddress evm0.accountMap evm0.executionEnv)) "claw" 0
        (yankClawArgVals evm0) (false, evmCat, outCat) true := by
    simpa [evm0, initState, flipperCatAddress] using hcallCat
  have hcallBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage catRef) "claw" (.intLit 0)
          [.storage (bidsF (.var "id") "tab")] "_clawRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallFailure (cfg := config) (C := contract) (evm := evm0)
        (evm' := evmCat) (locals := locals) (receiver := .storage catRef)
        (retVar := "_clawRet") (name := "claw")
        (target := flipperCatAddress evm0.accountMap evm0.executionEnv) (sendVal := 0)
        (args := [.storage (bidsF (.var "id") "tab")])
        (argVals := yankClawArgVals evm0) (out := outCat) (perm := true)
        hguardCat hcat hargs hcallCat'
  have hcallFull :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage catRef) "claw" (.intLit 0)
          [.storage (bidsF (.var "id") "tab")] "_clawRet" ++
        (
        checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, sender, .storage (bidsF (.var "id") "lot")]
          "_fluxRet" ++
        checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet" ++
        [ .delete (bidRef (.var "id")) ]))
        .reverted := by
    exact execBlock_append_term
      (cfg := config)
      (s2 :=
        checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, sender, .storage (bidsF (.var "id") "lot")]
          "_fluxRet" ++
        checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet" ++
        [ .delete (bidRef (.var "id")) ])
      hcallBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 yankTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauthGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hbidGuard) ?_
    simpa [yankTransition, checkedExternalCallStmts, List.append_assoc] using hcallFull
  simpa [ExecTransitionBody, yankTransition, nonpayable, auth, checkedExternalCallStmts,
    locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperYankSourceBodyVatNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCat : EVM.State} {outCat : ByteArray}
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
    (hvatNoCode :
      (UInt256.ofNat
        ((evmCat.lookupAccount (flipperVatAddress evmCat.accountMap evmCat.executionEnv)).option
          0 (fun acc => acc.code.size))).toNat = 0) :
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
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
    exact evalExpr_flipperVatCodeGuard_false_ofLocals hvat hvatNoCode
  have hvatBlock :
      ExecBlock config { contract := contract, locals := locals1 } evmCat
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, sender, .storage (bidsF (.var "id") "lot")]
          "_fluxRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallNoCode (cfg := config) (C := contract) (evm := evmCat)
        (locals := locals1) (receiver := .storage vatRef) (retVar := "_fluxRet")
        (name := "flux") (sendVal := 0)
        (args := [.storage ilkRef, thisAddr, sender, .storage (bidsF (.var "id") "lot")])
        hguardVat
  have htail :
      ExecBlock config { contract := contract, locals := locals1 } evmCat
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, sender, .storage (bidsF (.var "id") "lot")]
          "_fluxRet" ++
        checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet" ++
        [ .delete (bidRef (.var "id")) ])
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
        checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet" ++
        [ .delete (bidRef (.var "id")) ]))
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

theorem flipperYankX_authOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (h : RD flipperBytecode I g s0 ⟨967⟩ [yankId I, ret, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨1049⟩ [yankId I, ret, sel]
      (yankAuthMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [flipperCallerWardsSlot, flipperSlotWord] using hauth
  obtain ⟨_, _, hafterAuth⟩ := RD.flipperAuthCheckOk
    (code := flipperBytecode) (pc := ⟨967⟩) (okPc := ⟨1049⟩) (key := yankId I)
    (ret := ret) (R := [sel]) h
    (by
      unfold flipperAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    hauthSolc (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [yankAuthMem] using hafterAuth⟩

theorem flipperYankX_guyNonzero {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hguy : bidGuyWord (yankId I) σ I ≠ ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨1049⟩ [yankId I, ret, sel]
      (yankAuthMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨1147⟩ [yankId I, ret, sel]
      (yankHashMem0 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd1064 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (yankId I) (yankAuthMem I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (yankHashMem0 I) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (yankId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (yankId I)
        (twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size))
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k1068, C1068, rd1068raw⟩ := rd1064.sload (by native_decide) (by evm_ov)
  have rd1068 : RD flipperBytecode I g s0 ⟨1068⟩
      [flipperSlotWord (bidPackedSlotOfWord (yankId I)) σ I, yankId I, ret, sel]
      (yankHashMem0 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1068 C1068 := by
    have hslotAdd :
        ⟨2⟩ + solcMappingSlot ⟨1⟩ (yankId I) =
          solcMappingSlot ⟨1⟩ (yankId I) + ⟨2⟩ := by
      exact u256_add_comm _ _
    simpa [yankHashMem0, yankAuthMem, bidPackedSlotOfWord, bidBaseOfWord,
      flipperSlotWord, hslotAdd] using rd1068raw
  have rd1077 := evm_run rd1068 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hraw :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        (flipperSlotWord (bidPackedSlotOfWord (yankId I)) σ I) =
          bidGuyWord (yankId I) σ I := by
    have hmask :
        UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask := by
      native_decide
    simp [bidGuyWord, flipperAddressReturnWord, hmask, u256_land_comm]
  rw [hraw] at rd1077
  have rd1147 := evm_run rd1077 with [
    raw push2 ⟨1147⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) hguy (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa using rd1147⟩

theorem flipperYankX_guyZero {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hguy : bidGuyWord (yankId I) σ I = ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨1049⟩ [yankId I, ret, sel]
      (yankAuthMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  have rd1064 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (yankId I) (yankAuthMem I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (yankHashMem0 I) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (yankId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (yankId I)
        (twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size))
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k1068, C1068, rd1068raw⟩ := rd1064.sload (by native_decide) (by evm_ov)
  have rd1068 : RD flipperBytecode I g s0 ⟨1068⟩
      [flipperSlotWord (bidPackedSlotOfWord (yankId I)) σ I, yankId I, ret, sel]
      (yankHashMem0 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1068 C1068 := by
    have hslotAdd :
        ⟨2⟩ + solcMappingSlot ⟨1⟩ (yankId I) =
          solcMappingSlot ⟨1⟩ (yankId I) + ⟨2⟩ := by
      exact u256_add_comm _ _
    simpa [yankHashMem0, yankAuthMem, bidPackedSlotOfWord, bidBaseOfWord,
      flipperSlotWord, hslotAdd] using rd1068raw
  have rd1077 := evm_run rd1068 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hraw :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        (flipperSlotWord (bidPackedSlotOfWord (yankId I)) σ I) = ⟨0⟩ := by
    simpa [bidGuyWord, flipperAddressReturnWord, solcAddrMask, u256_land_comm] using hguy
  rw [hraw] at rd1077
  have rd1081 := evm_run rd1077 with [
    raw push2 ⟨1147⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)]
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1081⟩) (len := ⟨19⟩)
    (rawWord := (⟨392624042470857692800460698066570017893046621⟩ : UInt256))
    (shift := ⟨106⟩) (op := .PUSH19) (width := 19)
    (word := UInt256.shiftLeft
      (⟨392624042470857692800460698066570017893046621⟩ : UInt256) ⟨106⟩)
    rd1081
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) (by rfl)
    (twoWordHashMem_size_96 (yankId I) ⟨1⟩
      (twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size))
    (twoWordHashMem_read64 (yankId I) ⟨1⟩
      (twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size)
      (twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
        solcFreePtrMem_read64))
    (by simp)

theorem flipperYankX_bidLt {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hlt : (bidBidWord (yankId I) σ I).toNat < (bidTabWord (yankId I) σ I).toNat)
    (h : RD flipperBytecode I g s0 ⟨1147⟩ [yankId I, ret, sel]
      (yankHashMem0 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨1250⟩ [yankId I, ret, sel]
      (yankHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd1162 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (yankId I) (yankHashMem0 I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (yankHashMem1 I) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (yankId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (yankId I)
        (twoWordHashMem_size_96 (yankId I) ⟨1⟩
          (twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size)))
      (by decide) (by evm_ov),
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k1167, C1167, rd1167raw⟩ := rd1162.sload (by native_decide) (by evm_ov)
  have rd1167 : RD flipperBytecode I g s0 ⟨1167⟩
      [bidTabWord (yankId I) σ I, solcMappingSlot ⟨1⟩ (yankId I), yankId I, ret, sel]
      (yankHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1167 C1167 := by
    have hslotAdd :
        ⟨5⟩ + solcMappingSlot ⟨1⟩ (yankId I) =
          solcMappingSlot ⟨1⟩ (yankId I) + ⟨5⟩ := by
      exact u256_add_comm _ _
    simpa [yankHashMem1, yankHashMem0, yankAuthMem, bidTabWord, bidSlotOfWord,
      bidBaseOfWord, flipperSlotWord, hslotAdd] using rd1167raw
  obtain ⟨k1169, C1169, rd1169raw⟩ :=
    (evm_run rd1167 with [
      raw swap1 (by native_decide) (by evm_ov)]).sload (by native_decide) (by evm_ov)
  have rd1169 : RD flipperBytecode I g s0 ⟨1169⟩
      [bidBidWord (yankId I) σ I, bidTabWord (yankId I) σ I, yankId I, ret, sel]
      (yankHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1169 C1169 := by
    simpa [bidBidWord, bidBaseOfWord, flipperSlotWord] using rd1169raw
  have rd1170 := evm_run rd1169 with [
    raw lt (by native_decide) (by evm_ov)]
  have hltWord : UInt256.lt (bidBidWord (yankId I) σ I) (bidTabWord (yankId I) σ I) =
      ⟨1⟩ :=
    Reasoning.Theory.ult_one hlt
  rw [hltWord] at rd1170
  have rd1250 := evm_run rd1170 with [
    raw push2 ⟨1250⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest)
      (by evm_ov)]
  exact ⟨_, _, by simpa using rd1250⟩

theorem flipperYankX_toCatExtcodesizeGuard {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (h : RD flipperBytecode I g s0 ⟨1250⟩ [yankId I, ret, sel]
      (yankHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨1330⟩
      (flipperCatTargetWord σ I :: flipperCatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨36⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨164⟩ :: ⟨3865913243⟩ ::
        flipperCatTargetWord σ I :: yankId I :: ret :: sel :: [])
      (yankCatCallMem σ I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k' C' := by
  let rawTarget := flipperSlotWord ⟨7⟩ σ I
  have rd1253 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨7⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1254, C1254, rd1254raw⟩ := rd1253.sload (by native_decide) (by evm_ov)
  have rd1254 : RD flipperBytecode I g s0 ⟨1254⟩
      (rawTarget :: yankId I :: ret :: sel :: [])
      (yankHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1254 C1254 := by
    simpa [rawTarget, flipperSlotWord, solcSlotWord] using rd1254raw
  have hmload64Hash :
      (if (⟨64⟩ : UInt256).toNat ≥ (yankCatHashMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((yankCatHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [yankCatHashMem_size]; decide) (by decide)
      (yankCatHashMem_read64 I)
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (yankCatCallMem σ I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((yankCatCallMem σ I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [yankCatCallMem_size]; decide) (by decide)
      (yankCatCallMem_read64 σ I)
  have rd1272 := evm_run rd1254 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (yankId I) (yankHashMem1 I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (yankCatHashMem I) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (yankId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (yankId I) (yankHashMem1_size I))
      (by decide) (by evm_ov),
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k1273, C1273, rd1273raw⟩ := rd1272.sload (by native_decide) (by evm_ov)
  have rd1273 : RD flipperBytecode I g s0 ⟨1273⟩
      (bidTabWord (yankId I) σ I :: ⟨64⟩ :: ⟨0⟩ :: rawTarget ::
        yankId I :: ret :: sel :: [])
      (yankCatHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1273 C1273 := by
    have hslotAdd :
        ⟨5⟩ + solcMappingSlot ⟨1⟩ (yankId I) =
          solcMappingSlot ⟨1⟩ (yankId I) + ⟨5⟩ := by
      exact u256_add_comm _ _
    simpa [yankCatHashMem, bidTabWord, bidSlotOfWord, bidBaseOfWord,
      flipperSlotWord, hslotAdd] using rd1273raw
  have rd1330 := evm_run rd1273 with [
    raw dup2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64Hash (by decide) (by evm_ov),
    raw push4 ⟨3865913243⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (yankCatSelectorMem I) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw mstore 3 (yankCatCallMem σ I) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push4 ⟨3865913243⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [rawTarget, flipperCatTargetWord, flipperAddressReturnWord, flipperSlotWord,
      solcSlotWord, solcAddrMask, yankCatSelectorWord] using rd1330⟩

theorem flipperYankX_catNoCode {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperCatTargetWord σ I) = ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨1250⟩ [yankId I, ret, sel]
      (yankHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨_, _, rd1330⟩ := flipperYankX_toCatExtcodesizeGuard h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨1330⟩) (okPc := ⟨1342⟩) rd1330
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem flipperYankX_toCatCall {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperCatTargetWord σ I) ≠ ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨1250⟩ [yankId I, ret, sel]
      (yankHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ gasWord k' C', RD flipperBytecode I g s0 ⟨1345⟩
      (gasWord :: flipperCatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨36⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨164⟩ :: ⟨3865913243⟩ ::
        flipperCatTargetWord σ I :: yankId I :: ret :: sel :: [])
      (yankCatCallMem σ I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd1330⟩ := flipperYankX_toCatExtcodesizeGuard h
  obtain ⟨gasWord, k1345, C1345, rd1345⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1330⟩) (okPc := ⟨1342⟩) rd1330
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k1345, C1345, by simpa using rd1345⟩

theorem flipperYankX_catPostCall
    {cA gh bl σ σ₀ A I} {g : UInt256} {k C : ℕ} {ret sel : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperCatTargetWord σ I) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (h : RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1250⟩
      [yankId I, ret, sel] (yankHashMem1 I) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1346⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: ⟨3865913243⟩ ::
          flipperCatTargetWord σ I :: yankId I :: ret :: sel :: [])
        (yankCatCallMem σ I) (UInt256.ofNat 6) out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperCatAddress σ I)) "claw" 0
        [Value.int (Int.ofNat (bidTabWord (yankId I) σ I).toNat)]
        (z,
          { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', substate := A', createdAccounts := cA' },
          out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd1345⟩ := flipperYankX_toCatCall hcodeSize h
  obtain ⟨cA', σ', z, out, A_in, callGas, k1346, C1346, hΘpack, rd1346raw,
      houtsz⟩ :=
    RD.call rd1345 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k1346, C1346, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          (⟨128⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
      native_decide
    have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
      rfl
    have rd1346 : RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1346⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: ⟨3865913243⟩ ::
          flipperCatTargetWord σ I :: yankId I :: ret :: sel :: [])
        (out.write 0 (yankCatCallMem σ I) 128
          (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 6) out (cA', σ') k1346 C1346 :=
      haw ▸ rd1346raw
    rw [hmin, byteArray_write_len_zero] at rd1346
    exact rd1346
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := flipperCatTargetWord σ I)
      (mem := yankCatCallMem σ I) (inOff := ⟨128⟩) (inSize := ⟨36⟩)
      (fun hdepthEq => by
        have hEq : I.depth = (1024 : Fin 1025) := by
          simpa [initState] using hdepthEq
        exact absurd hdepth (by rw [hEq]; decide))
      (flipperCatEvmAddress_eq_target_of_accountMapEquiv (accountMapEquiv.refl σ))
      (yankCatCallMem_encode σ I) ?_
    simpa [initState, hperm] using hΘ

theorem flipperYankX_catCallFailure {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {aw target id ret sel selector : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode I g s0 ⟨1346⟩
      (⟨0⟩ :: ⟨164⟩ :: selector :: target :: id :: ret :: sel :: [])
      mem aw out acc k C)
    (houtsz : out.size < UInt256.size) :
    RDrev flipperBytecode g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨1346⟩) (okPc := ⟨1362⟩) h
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    houtsz (by simp)

theorem flipperYankX_catCallDepthLimit {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperCatTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (h : RD flipperBytecode I g s0 ⟨1250⟩ [yankId I, ret, sel]
      (yankHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨gasWord, _, _, rd1345⟩ := flipperYankX_toCatCall hcodeSize h
  obtain ⟨k1346, C1346, rd1346raw⟩ :=
    RD.callDepthLimit
      (code := flipperBytecode) (ee := I) (g := g) (s0 := s0) (pc := ⟨1345⟩)
      (mem := yankCatCallMem σ I) (aw := UInt256.ofNat 6) (rdata := ByteArray.empty)
      (cA := cA) (σ := σ) (gasArg := gasWord) (target := flipperCatTargetWord σ I)
      (inOffset := ⟨128⟩) (inSize := ⟨36⟩) (outOffset := ⟨128⟩) (outSize := ⟨0⟩)
      (t := [⟨164⟩, ⟨3865913243⟩, flipperCatTargetWord σ I, yankId I, ret, sel])
      rd1345 (by native_decide) hdepth (by simp)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        (⟨128⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
    native_decide
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    rfl
  have rd1346 : RD flipperBytecode I g s0 ⟨1346⟩
      (⟨0⟩ :: ⟨164⟩ :: ⟨3865913243⟩ ::
        flipperCatTargetWord σ I :: yankId I :: ret :: sel :: [])
      (yankCatCallMem σ I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k1346 C1346 :=
    by
      rw [hmin, byteArray_write_len_zero] at rd1346raw
      exact haw ▸ rd1346raw
  exact flipperYankX_catCallFailure rd1346 (by native_decide)

theorem flipperYankX_catCallSuccessToVatStart {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {aw target id ret sel selector : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode I g s0 ⟨1346⟩
      (⟨1⟩ :: ⟨164⟩ :: selector :: target :: id :: ret :: sel :: [])
      mem aw out acc k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨1365⟩
      (selector :: target :: id :: ret :: sel :: [])
      mem aw out acc k' C' := by
  obtain ⟨k1364, C1364, rd1364⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨1346⟩) (okPc := ⟨1362⟩) h
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp)
  have rd1365 := rd1364.pop (by native_decide) (by evm_ov)
  exact ⟨k1364 + 1, C1364 + 2, by simpa using rd1365⟩

theorem flipperYankX_toVatExtcodesizeGuard {cA σmem σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out : ByteArray} {ret sel selector target : UInt256}
    (h : RD flipperBytecode I g s0 ⟨1365⟩
      (selector :: target :: yankId I :: ret :: sel :: [])
      (yankCatCallMem σmem I) (UInt256.ofNat 6) out (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨1466⟩
      (flipperVatTargetWord σ I :: flipperVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨132⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: ⟨1628552750⟩ ::
        flipperVatTargetWord σ I :: yankId I :: ret :: sel :: [])
      (yankVatFluxCallMem σmem σ I) (UInt256.ofNat 9) out (cA, σ) k' C' := by
  let rawVat := flipperSlotWord ⟨2⟩ σ I
  let rawIlk := flipperSlotWord ⟨3⟩ σ I
  let base := solcMappingSlot ⟨1⟩ (yankId I)
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hvatClean : UInt256.land rawVat solcAddrMask = flipperVatTargetWord σ I := by
    simp [rawVat, flipperVatTargetWord, flipperAddressReturnWord]
  have hmload64Hash :
      (if (⟨64⟩ : UInt256).toNat ≥ (yankVatHashMem σmem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((yankVatHashMem σmem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [yankVatHashMem_size]; decide) (by decide)
      (yankVatHashMem_read64 σmem I)
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (yankVatFluxCallMem σmem σ I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((yankVatFluxCallMem σmem σ I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [yankVatFluxCallMem_size]; decide) (by decide)
      (yankVatFluxCallMem_read64 σmem σ I)
  have rd1367pre := h.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1367, C1367, rd1367raw⟩ := rd1367pre.sload (by native_decide) (by evm_ov)
  have rd1368 : RD flipperBytecode I g s0 ⟨1368⟩
      (rawVat :: selector :: target :: yankId I :: ret :: sel :: [])
      (yankCatCallMem σmem I) (UInt256.ofNat 6) out (cA, σ) k1367 C1367 := by
    simpa [rawVat, flipperSlotWord, solcSlotWord] using rd1367raw
  have rd1370pre := rd1368.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1370, C1370, rd1370raw⟩ := rd1370pre.sload (by native_decide) (by evm_ov)
  have rd1371 : RD flipperBytecode I g s0 ⟨1371⟩
      (rawIlk :: rawVat :: selector :: target :: yankId I :: ret :: sel :: [])
      (yankCatCallMem σmem I) (UInt256.ofNat 6) out (cA, σ) k1370 C1370 := by
    simpa [rawIlk, flipperSlotWord, solcSlotWord] using rd1370raw
  have rd1391pre := evm_run rd1371 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (yankId I) (yankCatCallMem σmem I)) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 (yankVatHashMem σmem I) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw keccak256 0 base (UInt256.ofNat 6)
      (by native_decide) mem_cost
      (by simpa [base] using yankVatHashMem_solcMappingSlot σmem I)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k1392, C1392, rd1392raw⟩ := rd1391pre.sload (by native_decide) (by evm_ov)
  have rd1392 : RD flipperBytecode I g s0 ⟨1392⟩
      (bidLotWord (yankId I) σ I :: ⟨64⟩ :: ⟨0⟩ :: rawIlk :: rawVat ::
        selector :: target :: yankId I :: ret :: sel :: [])
      (yankVatHashMem σmem I) (UInt256.ofNat 6) out (cA, σ) k1392 C1392 := by
    have hslotAdd :
        (⟨1⟩ : UInt256) + base = solcMappingSlot ⟨1⟩ (yankId I) + ⟨1⟩ := by
      simpa [base] using
        (u256_add_comm (⟨1⟩ : UInt256) (solcMappingSlot ⟨1⟩ (yankId I)))
    simpa [bidLotWord, bidSlotOfWord, bidBaseOfWord, flipperSlotWord, hslotAdd]
      using rd1392raw
  have rd1412 := evm_run rd1392 with [
    raw dup2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Hash (by decide) (by evm_ov),
    raw push4 ⟨814276375⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨225⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (yankVatFluxSelectorMem σmem I) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw mstore 0 (yankVatFluxIlkMem σmem σ I) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1413 := RD.address rd1412 (by native_decide) (by evm_ov)
  have rd1466 := evm_run rd1413 with [
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (yankVatFluxThisMem σmem σ I) (UInt256.ofNat 7)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (yankVatFluxSenderMem σmem σ I) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (yankVatFluxCallMem σmem σ I) (UInt256.ofNat 9)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push4 ⟨1628552750⟩ (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨132⟩ (by native_decide) (by evm_ov),
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
  rw [hmask160, hvatClean] at rd1466
  exact ⟨_, _, by
    convert rd1466 using 1 <;> native_decide⟩

theorem flipperYankX_vatNoCode {cA σmem σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out : ByteArray} {ret sel selector target : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) = ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨1365⟩
      (selector :: target :: yankId I :: ret :: sel :: [])
      (yankCatCallMem σmem I) (UInt256.ofNat 6) out (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨_, _, rd1466⟩ := flipperYankX_toVatExtcodesizeGuard h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨1466⟩) (okPc := ⟨1478⟩) rd1466
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem flipperYankX_bidNotLt {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hge : (bidTabWord (yankId I) σ I).toNat ≤ (bidBidWord (yankId I) σ I).toNat)
    (h : RD flipperBytecode I g s0 ⟨1147⟩ [yankId I, ret, sel]
      (yankHashMem0 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  have rd1162 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (yankId I) (yankHashMem0 I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (yankHashMem1 I) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (yankId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (yankId I)
        (twoWordHashMem_size_96 (yankId I) ⟨1⟩
          (twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size)))
      (by decide) (by evm_ov),
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k1167, C1167, rd1167raw⟩ := rd1162.sload (by native_decide) (by evm_ov)
  have rd1167 : RD flipperBytecode I g s0 ⟨1167⟩
      [bidTabWord (yankId I) σ I, solcMappingSlot ⟨1⟩ (yankId I), yankId I, ret, sel]
      (yankHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1167 C1167 := by
    have hslotAdd :
        ⟨5⟩ + solcMappingSlot ⟨1⟩ (yankId I) =
          solcMappingSlot ⟨1⟩ (yankId I) + ⟨5⟩ := by
      exact u256_add_comm _ _
    simpa [yankHashMem1, yankHashMem0, yankAuthMem, bidTabWord, bidSlotOfWord,
      bidBaseOfWord, flipperSlotWord, hslotAdd] using rd1167raw
  obtain ⟨k1169, C1169, rd1169raw⟩ :=
    (evm_run rd1167 with [
      raw swap1 (by native_decide) (by evm_ov)]).sload (by native_decide) (by evm_ov)
  have rd1169 : RD flipperBytecode I g s0 ⟨1169⟩
      [bidBidWord (yankId I) σ I, bidTabWord (yankId I) σ I, yankId I, ret, sel]
      (yankHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1169 C1169 := by
    simpa [bidBidWord, bidBaseOfWord, flipperSlotWord] using rd1169raw
  have rd1170 := evm_run rd1169 with [
    raw lt (by native_decide) (by evm_ov)]
  have hlt : UInt256.lt (bidBidWord (yankId I) σ I) (bidTabWord (yankId I) σ I) =
      ⟨0⟩ :=
    Reasoning.Theory.ult_zero hge
  rw [hlt] at rd1170
  have rd1174 := evm_run rd1170 with [
    raw push2 ⟨1250⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)]
  have hmem : (yankHashMem1 I).size = 96 := by
    unfold yankHashMem1 yankHashMem0 yankAuthMem
    exact twoWordHashMem_size_96 (yankId I) ⟨1⟩
      (twoWordHashMem_size_96 (yankId I) ⟨1⟩
        (twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size))
  have hread64 :
      (yankHashMem1 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    unfold yankHashMem1 yankHashMem0 yankAuthMem
    exact twoWordHashMem_read64 (yankId I) ⟨1⟩
      (twoWordHashMem_size_96 (yankId I) ⟨1⟩
        (twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size))
      (twoWordHashMem_read64 (yankId I) ⟨1⟩
        (twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size)
        (twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
          solcFreePtrMem_read64))
  have rdMload := evm_run rd1174 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 (yankHashMem1 I)) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 (yankHashMem1 I)) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨26⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 (⟨26⟩ : UInt256) (yankHashMem1 I))
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst flipperYankAlreadyDentWord
    (width := 32) (op := .PUSH32) (by decide) flipperYankDecodePushAlreadyDent1201
    (by evm_ov)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3
      (solcErrorStringMem3 (⟨26⟩ : UInt256) flipperYankAlreadyDentWord (yankHashMem1 I))
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide) mem_cost
      (solcErrorStringMem3_mload64 (⟨26⟩ : UInt256) flipperYankAlreadyDentWord
        hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxRecDepth 2000000 in
theorem flipperYankX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD flipperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨294⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flipperBytecode) (sel := sel) (entry := ⟨294⟩) (ret := ⟨323⟩)
    (decoded := ⟨316⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

end Benchmarks.Dss.Flipper
