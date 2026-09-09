import Benchmarks.Dss.Flipper.DealSource
import Reasoning.ExternalCall
import Reasoning.MemCascade
import Benchmarks.Dss.Flipper.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## EVM-side helpers for `deal(uint256)` -/

theorem RD.flipperDealDecodeToRoutine {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨863⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = flipperBytecode)
    (hroutine : (D_J code 0).contains ⟨5365⟩ = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨5365⟩
      (calldataWord ee.calldata 4 :: ret :: sel :: R) mem aw rdata acc k' C' := by
  subst hwf
  have rd5365 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw calldataload (by decide +native) (by evm_ov),
    raw push2 ⟨5365⟩ (by decide +native) (by evm_ov),
    raw jump (by decide +native) hroutine (by evm_ov)]
  exact ⟨_, _, by simpa [calldataWord] using rd5365⟩

theorem flipperDealX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flipperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨841⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5365⟩
        [dealId I, ⟨323⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flipperBytecode) (sel := sel) (entry := ⟨841⟩) (ret := ⟨323⟩)
    (decoded := ⟨863⟩) (need := ⟨32⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest)
    (by
      exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.flipperDealDecodeToRoutine
    (code := flipperBytecode) (ret := ⟨323⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [dealId] using hroutine⟩

theorem flipperDealX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD flipperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨841⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flipperBytecode) (sel := sel) (entry := ⟨841⟩) (ret := ⟨323⟩)
    (decoded := ⟨863⟩) (need := ⟨32⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) hlt

theorem flipperDealDecodePushMask5391 :
    decode flipperBytecode (⟨5391⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  decide +native

theorem flipperDealDecodePushMask5435 :
    decode flipperBytecode (⟨5435⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  decide +native

theorem flipperDealDecodePushMask5477 :
    decode flipperBytecode (⟨5477⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  decide +native

abbrev dealCatSelectorWord : UInt256 :=
  UInt256.shiftLeft (⟨3865913243⟩ : UInt256) ⟨224⟩

abbrev dealVatFluxSelectorWord : UInt256 :=
  UInt256.shiftLeft (⟨814276375⟩ : UInt256) ⟨225⟩

noncomputable abbrev dealHashMem0 (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (dealId I) ⟨1⟩ solcFreePtrMem

noncomputable abbrev dealHashMem1 (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (dealId I) ⟨1⟩ (dealHashMem0 I)

noncomputable abbrev dealHashMem2 (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (dealId I) ⟨1⟩ (dealHashMem1 I)

noncomputable abbrev dealCatHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (dealId I) ⟨1⟩ (dealHashMem2 I)

noncomputable abbrev dealCatSelectorMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray dealCatSelectorWord).write 0 (dealCatHashMem I) 128 32

noncomputable abbrev dealCatCallMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (bidTabWord (dealId I) σ I)).write 0
    (dealCatSelectorMem I) 132 32

noncomputable abbrev dealVatHashMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (dealId I) ⟨1⟩ (dealCatCallMem σ I)

noncomputable abbrev dealVatFluxSelectorMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray dealVatFluxSelectorWord).write 0 (dealVatHashMem σ I) 128 32

noncomputable abbrev dealVatFluxIlkMem (σmem σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (flipperSlotWord ⟨3⟩ σ I)).write 0
    (dealVatFluxSelectorMem σmem I) 132 32

noncomputable abbrev dealVatFluxThisMem (σmem σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (EVM.word I.codeOwner.val)).write 0
    (dealVatFluxIlkMem σmem σ I) 164 32

noncomputable abbrev dealVatFluxGuyMem (σmem σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (bidGuyWord (dealId I) σ I)).write 0
    (dealVatFluxThisMem σmem σ I) 196 32

noncomputable abbrev dealVatFluxCallMem (σmem σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (bidLotWord (dealId I) σ I)).write 0
    (dealVatFluxGuyMem σmem σ I) 228 32

theorem dealHashMem2_size (I : ExecutionEnv) :
    (dealHashMem2 I).size = 96 := by
  unfold dealHashMem2 dealHashMem1 dealHashMem0
  exact twoWordHashMem_size_96 (dealId I) ⟨1⟩
    (twoWordHashMem_size_96 (dealId I) ⟨1⟩
      (twoWordHashMem_size_96 (dealId I) ⟨1⟩ solcFreePtrMem_size))

theorem dealHashMem2_read64 (I : ExecutionEnv) :
    (dealHashMem2 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dealHashMem2 dealHashMem1 dealHashMem0
  exact twoWordHashMem_read64 (dealId I) ⟨1⟩
    (twoWordHashMem_size_96 (dealId I) ⟨1⟩
      (twoWordHashMem_size_96 (dealId I) ⟨1⟩ solcFreePtrMem_size))
    (twoWordHashMem_read64 (dealId I) ⟨1⟩
      (twoWordHashMem_size_96 (dealId I) ⟨1⟩ solcFreePtrMem_size)
      (twoWordHashMem_read64 (dealId I) ⟨1⟩ solcFreePtrMem_size
        solcFreePtrMem_read64))

theorem dealCatHashMem_size (I : ExecutionEnv) :
    (dealCatHashMem I).size = 96 := by
  unfold dealCatHashMem
  exact twoWordHashMem_size_96 (dealId I) ⟨1⟩ (dealHashMem2_size I)

theorem dealCatHashMem_read64 (I : ExecutionEnv) :
    (dealCatHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dealCatHashMem
  exact twoWordHashMem_read64 (dealId I) ⟨1⟩ (dealHashMem2_size I)
    (dealHashMem2_read64 I)

theorem dealCatSelectorWord_prefix :
    (UInt256.toByteArray dealCatSelectorWord).extract 0 4 = catClawSelector := by
  decide +native

theorem dealCatSelectorMem_size (I : ExecutionEnv) :
    (dealCatSelectorMem I).size = 160 := by
  unfold dealCatSelectorMem
  exact toByteArray_write32_size_of_ge (dealCatHashMem I) dealCatSelectorWord 128 96 160
    (dealCatHashMem_size I) (by omega) (by decide +native) (by omega)

theorem dealCatSelectorMem_read64 (I : ExecutionEnv) :
    (dealCatSelectorMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dealCatSelectorMem
  rw [toByteArray_write_read_below_of_gap dealCatSelectorWord (dealCatHashMem I) 128 64]
  · exact dealCatHashMem_read64 I
  · rw [dealCatHashMem_size]
  · omega
  · rw [dealCatHashMem_size]
    decide +native

theorem dealCatCallMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (dealCatCallMem σ I).size = 164 := by
  unfold dealCatCallMem
  exact toByteArray_write32_size_of_le (dealCatSelectorMem I)
    (bidTabWord (dealId I) σ I) 132 160 164
    (dealCatSelectorMem_size I)
    (by rw [dealCatSelectorMem_size]; omega)
    (by decide +native)

theorem dealCatCallMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (dealCatCallMem σ I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dealCatCallMem
  rw [toByteArray_write_read_below_of_gap
    (bidTabWord (dealId I) σ I) (dealCatSelectorMem I) 132 64]
  · exact dealCatSelectorMem_read64 I
  · rw [dealCatSelectorMem_size]
    omega
  · omega
  · rw [dealCatSelectorMem_size]
    decide +native

theorem dealCatCallMem_read (σ : AccountMap) (I : ExecutionEnv) :
    (dealCatCallMem σ I).readWithPadding 128 36 =
      catClawSelector ++ UInt256.toByteArray (bidTabWord (dealId I) σ I) := by
  rw [byteArray_readWithPadding_split (dealCatCallMem σ I) 128 4 32
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [dealCatCallMem_size])]
  · unfold dealCatCallMem
    rw [toByteArray_write_read_below_len_of_gap
      (bidTabWord (dealId I) σ I)
      (dealCatSelectorMem I)
      132 128 4]
    · rw [toByteArray_write_read_window_of_gap dealCatSelectorWord (dealCatHashMem I) 128 0 4
        (by omega) (by omega) (by norm_num)]
      · change (UInt256.toByteArray dealCatSelectorWord).extract 0 4 ++
            ((UInt256.toByteArray (bidTabWord (dealId I) σ I)).write 0
              (dealCatSelectorMem I) 132 32).readWithPadding (128 + 4) 32 =
          catClawSelector ++ UInt256.toByteArray (bidTabWord (dealId I) σ I)
        rw [dealCatSelectorWord_prefix]
        rw [toByteArray_write_read_back_of_gap (bidTabWord (dealId I) σ I)
          (dealCatSelectorMem I) 132 (by
            rw [dealCatSelectorMem_size]
            decide +native)]
      · rw [dealCatHashMem_size]
        decide +native
    · rw [dealCatSelectorMem_size]
      omega
    · omega
    · omega
    · omega
    · rw [dealCatSelectorMem_size]
      decide +native

theorem dealEncodeABIValue_uint256_word (w : UInt256) :
    encodeABIValue? uint256 (.int (Int.ofNat w.toNat)) =
      some (UInt256.toByteArray w).toList := by
  have hlt : w.toNat < EVM.twoPow 256 := w.val.isLt
  have hword : EVM.word w.toNat = w := u256_ofNat_toNat w
  simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hlt, hword,
    toByteArray_eq_toBytesBE, byteArray_toList_eq]

theorem dealCatCallMem_encode (σ : AccountMap) (I : ExecutionEnv) :
    config.externalABI.encode? "claw"
      [Value.int (Int.ofNat (bidTabWord (dealId I) σ I).toNat)] =
        some ((dealCatCallMem σ I).readWithPadding 128 36) := by
  rw [dealCatCallMem_read]
  unfold config externalABI
  simp only [if_true]
  unfold ABI.encodeCallWithSelector?
  have hpayload :
      encodeABIValues? [uint256]
        [Value.int (Int.ofNat (bidTabWord (dealId I) σ I).toNat)] =
          some (UInt256.toByteArray (bidTabWord (dealId I) σ I)).toList := by
    unfold encodeABIValues?
    rw [show abiTupleHeadSize? [uint256] = some 32 by decide +native]
    simp only [encodeABIValuesFrom?, Option.bind, bind]
    rw [dealEncodeABIValue_uint256_word]
    simp [show isDynamicABIType uint256 = false by decide +native]
  rw [hpayload]
  apply congrArg some
  apply ByteArray.ext
  simp [catClawSelector, byteArray_toList_eq]

theorem dealVatFluxSelectorWord_prefix :
    (UInt256.toByteArray dealVatFluxSelectorWord).extract 0 4 = vatFluxSelector := by
  decide +native

theorem dealVatHashMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (dealVatHashMem σ I).size = 164 := by
  unfold dealVatHashMem twoWordHashMem wordAt32Mem wordAt0Mem
  have h0 :
      ((UInt256.toByteArray (dealId I)).write 0 (dealCatCallMem σ I) 0 32).size =
        164 := by
    exact toByteArray_write32_size_of_le (dealCatCallMem σ I) (dealId I) 0 164 164
      (dealCatCallMem_size σ I)
      (by rw [dealCatCallMem_size]; omega)
      (by omega)
  exact toByteArray_write32_size_of_le
    ((UInt256.toByteArray (dealId I)).write 0 (dealCatCallMem σ I) 0 32)
    (⟨1⟩ : UInt256) 32 164 164 h0
    (by rw [h0]; omega)
    (by omega)

theorem dealVatHashMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (dealVatHashMem σ I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dealVatHashMem twoWordHashMem wordAt32Mem wordAt0Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by
        have h0 :
            ((UInt256.toByteArray (dealId I)).write 0 (dealCatCallMem σ I) 0 32).size =
              164 := by
          exact toByteArray_write32_size_of_le (dealCatCallMem σ I) (dealId I) 0 164 164
            (dealCatCallMem_size σ I)
            (by rw [dealCatCallMem_size]; omega)
            (by omega)
        rw [h0]; omega)
      (by omega)
      (by
        have h0 :
            ((UInt256.toByteArray (dealId I)).write 0 (dealCatCallMem σ I) 0 32).size =
              164 := by
          exact toByteArray_write32_size_of_le (dealCatCallMem σ I) (dealId I) 0 164 164
            (dealCatCallMem_size σ I)
            (by rw [dealCatCallMem_size]; omega)
            (by omega)
        rw [h0]; omega)]
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [dealCatCallMem_size]; omega)
      (by omega)
      (by rw [dealCatCallMem_size]; omega)]
  exact dealCatCallMem_read64 σ I

theorem dealVatHashMem_read0 (σ : AccountMap) (I : ExecutionEnv) :
    (dealVatHashMem σ I).readWithPadding 0 32 = UInt256.toByteArray (dealId I) := by
  unfold dealVatHashMem twoWordHashMem wordAt32Mem wordAt0Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by
        have h0 :
            ((UInt256.toByteArray (dealId I)).write 0 (dealCatCallMem σ I) 0 32).size =
              164 := by
          exact toByteArray_write32_size_of_le (dealCatCallMem σ I) (dealId I) 0 164 164
            (dealCatCallMem_size σ I)
            (by rw [dealCatCallMem_size]; omega)
            (by omega)
        rw [h0]; omega)
      (by omega)]
  exact toByteArray_write32_read_back (dealCatCallMem σ I) (dealId I) 0
    (by rw [dealCatCallMem_size]; omega)

theorem dealVatHashMem_read32 (σ : AccountMap) (I : ExecutionEnv) :
    (dealVatHashMem σ I).readWithPadding 32 32 = UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold dealVatHashMem twoWordHashMem wordAt32Mem
  exact toByteArray_write32_read_back (wordAt0Mem (dealId I) (dealCatCallMem σ I))
    (⟨1⟩ : UInt256) 32
    (by
      unfold wordAt0Mem
      have h0 :
          ((UInt256.toByteArray (dealId I)).write 0 (dealCatCallMem σ I) 0 32).size =
            164 := by
        exact toByteArray_write32_size_of_le (dealCatCallMem σ I) (dealId I) 0 164 164
          (dealCatCallMem_size σ I)
          (by rw [dealCatCallMem_size]; omega)
          (by omega)
      rw [h0]; omega)

theorem dealVatHashMem_read0_64 (σ : AccountMap) (I : ExecutionEnv) :
    (dealVatHashMem σ I).readWithPadding 0 64 =
      UInt256.toByteArray (dealId I) ++ UInt256.toByteArray (⟨1⟩ : UInt256) := by
  rw [byteArray_readWithPadding_split (dealVatHashMem σ I) 0 32 32
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [dealVatHashMem_size]; omega)]
  rw [dealVatHashMem_read0, dealVatHashMem_read32]

theorem dealVatHashMem_solcMappingSlot (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((dealVatHashMem σ I).readWithPadding 0 64))) =
      solcMappingSlot ⟨1⟩ (dealId I) := by
  rw [dealVatHashMem_read0_64]
  unfold solcMappingSlot
  exact mappingSlot_single (dealId I) ⟨1⟩

theorem dealVatFluxCallMem_eq_cascade (σmem σ : AccountMap) (I : ExecutionEnv) :
    dealVatFluxCallMem σmem σ I =
      writeCascade (dealVatHashMem σmem I)
        [(128, dealVatFluxSelectorWord),
         (132, flipperSlotWord ⟨3⟩ σ I),
         (164, EVM.word I.codeOwner.val),
         (196, bidGuyWord (dealId I) σ I),
         (228, bidLotWord (dealId I) σ I)] := by
  rfl

theorem dealVatFluxCallMem_size (σmem σ : AccountMap) (I : ExecutionEnv) :
    (dealVatFluxCallMem σmem σ I).size = 260 := by
  rw [dealVatFluxCallMem_eq_cascade]
  exact writeCascade_size_of_base (dealVatHashMem σmem I)
    [(128, dealVatFluxSelectorWord),
     (132, flipperSlotWord ⟨3⟩ σ I),
     (164, EVM.word I.codeOwner.val),
     (196, bidGuyWord (dealId I) σ I),
     (228, bidLotWord (dealId I) σ I)]
    (dealVatHashMem_size σmem I)
    (by simp [WriteGapsOk] <;> decide +native)
    (by norm_num [writeCascadeSize])

theorem dealVatFluxCallMem_read64 (σmem σ : AccountMap) (I : ExecutionEnv) :
    (dealVatFluxCallMem σmem σ I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [dealVatFluxCallMem_eq_cascade]
  rw [writeCascade_read_preserved_of_base (dealVatHashMem σmem I)
    [(128, dealVatFluxSelectorWord),
     (132, flipperSlotWord ⟨3⟩ σ I),
     (164, EVM.word I.codeOwner.val),
     (196, bidGuyWord (dealId I) σ I),
     (228, bidLotWord (dealId I) σ I)]
    (dealVatHashMem_size σmem I)
    (by simp [WindowDisjointFromWrites] <;> decide +native)]
  exact dealVatHashMem_read64 σmem I

theorem dealVatFluxCallMem_read128_4 (σmem σ : AccountMap) (I : ExecutionEnv) :
    (dealVatFluxCallMem σmem σ I).readWithPadding 128 4 = vatFluxSelector := by
  rw [dealVatFluxCallMem_eq_cascade]
  rw [writeCascade_read_window_of_head (dealVatHashMem σmem I) 128 0 4
    dealVatFluxSelectorWord
    [(132, flipperSlotWord ⟨3⟩ σ I),
     (164, EVM.word I.codeOwner.val),
     (196, bidGuyWord (dealId I) σ I),
     (228, bidLotWord (dealId I) σ I)]
    (by rw [dealVatHashMem_size]; decide +native)
    (by simp [WindowDisjointFromWrites] <;> decide +native)
    (by norm_num) (by norm_num) (by norm_num)]
  exact dealVatFluxSelectorWord_prefix

theorem dealVatFluxCallMem_read132 (σmem σ : AccountMap) (I : ExecutionEnv) :
    (dealVatFluxCallMem σmem σ I).readWithPadding 132 32 =
      UInt256.toByteArray (flipperSlotWord ⟨3⟩ σ I) := by
  rw [dealVatFluxCallMem_eq_cascade, writeCascade_cons]
  have hbase :
      (writeWord (dealVatHashMem σmem I) 128 dealVatFluxSelectorWord).size = 164 := by
    rw [writeWord_size]
    · rw [dealVatHashMem_size]; decide +native
    · rw [dealVatHashMem_size]; decide +native
  exact writeCascade_read_word_of_head_of_base
    (writeWord (dealVatHashMem σmem I) 128 dealVatFluxSelectorWord)
    (base := 164) (off := 132) (word := flipperSlotWord ⟨3⟩ σ I)
    (rest := [(164, EVM.word I.codeOwner.val),
      (196, bidGuyWord (dealId I) σ I),
      (228, bidLotWord (dealId I) σ I)])
    hbase (by decide +native)
    (by simp [WindowDisjointFromWrites] <;> decide +native)

theorem dealVatFluxCallMem_read164 (σmem σ : AccountMap) (I : ExecutionEnv) :
    (dealVatFluxCallMem σmem σ I).readWithPadding 164 32 =
      UInt256.toByteArray (EVM.word I.codeOwner.val) := by
  rw [dealVatFluxCallMem_eq_cascade, writeCascade_cons, writeCascade_cons]
  let mem1 := writeWord (dealVatHashMem σmem I) 128 dealVatFluxSelectorWord
  have hmem1 : mem1.size = 164 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [dealVatHashMem_size]; decide +native
    · rw [dealVatHashMem_size]; decide +native
  have hbase :
      (writeWord mem1 132 (flipperSlotWord ⟨3⟩ σ I)).size = 164 := by
    rw [writeWord_size]
    · rw [hmem1]; decide +native
    · rw [hmem1]; decide +native
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem1 132 (flipperSlotWord ⟨3⟩ σ I))
    (base := 164) (off := 164) (word := EVM.word I.codeOwner.val)
    (rest := [(196, bidGuyWord (dealId I) σ I),
      (228, bidLotWord (dealId I) σ I)])
    hbase (by decide +native)
    (by simp [WindowDisjointFromWrites] <;> decide +native)

theorem dealVatFluxCallMem_read196 (σmem σ : AccountMap) (I : ExecutionEnv) :
    (dealVatFluxCallMem σmem σ I).readWithPadding 196 32 =
      UInt256.toByteArray (bidGuyWord (dealId I) σ I) := by
  rw [dealVatFluxCallMem_eq_cascade, writeCascade_cons, writeCascade_cons,
    writeCascade_cons]
  let mem1 := writeWord (dealVatHashMem σmem I) 128 dealVatFluxSelectorWord
  let mem2 := writeWord mem1 132 (flipperSlotWord ⟨3⟩ σ I)
  have hmem1 : mem1.size = 164 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [dealVatHashMem_size]; decide +native
    · rw [dealVatHashMem_size]; decide +native
  have hmem2 : mem2.size = 164 := by
    dsimp [mem2]
    rw [writeWord_size]
    · rw [hmem1]; decide +native
    · rw [hmem1]; decide +native
  have hbase : (writeWord mem2 164 (EVM.word I.codeOwner.val)).size = 196 := by
    rw [writeWord_size]
    · rw [hmem2]; decide +native
    · rw [hmem2]; decide +native
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem2 164 (EVM.word I.codeOwner.val))
    (base := 196) (off := 196) (word := bidGuyWord (dealId I) σ I)
    (rest := [(228, bidLotWord (dealId I) σ I)])
    hbase (by decide +native)
    (by simp [WindowDisjointFromWrites] <;> decide +native)

theorem dealVatFluxCallMem_read228 (σmem σ : AccountMap) (I : ExecutionEnv) :
    (dealVatFluxCallMem σmem σ I).readWithPadding 228 32 =
      UInt256.toByteArray (bidLotWord (dealId I) σ I) := by
  rw [dealVatFluxCallMem_eq_cascade, writeCascade_cons, writeCascade_cons,
    writeCascade_cons, writeCascade_cons]
  let mem1 := writeWord (dealVatHashMem σmem I) 128 dealVatFluxSelectorWord
  let mem2 := writeWord mem1 132 (flipperSlotWord ⟨3⟩ σ I)
  let mem3 := writeWord mem2 164 (EVM.word I.codeOwner.val)
  have hmem1 : mem1.size = 164 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [dealVatHashMem_size]; decide +native
    · rw [dealVatHashMem_size]; decide +native
  have hmem2 : mem2.size = 164 := by
    dsimp [mem2]
    rw [writeWord_size]
    · rw [hmem1]; decide +native
    · rw [hmem1]; decide +native
  have hmem3 : mem3.size = 196 := by
    dsimp [mem3]
    rw [writeWord_size]
    · rw [hmem2]; decide +native
    · rw [hmem2]; decide +native
  have hbase : (writeWord mem3 196 (bidGuyWord (dealId I) σ I)).size = 228 := by
    rw [writeWord_size]
    · rw [hmem3]; decide +native
    · rw [hmem3]; decide +native
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem3 196 (bidGuyWord (dealId I) σ I))
    (base := 228) (off := 228) (word := bidLotWord (dealId I) σ I)
    (rest := [])
    hbase (by decide +native)
    (by simp [WindowDisjointFromWrites] <;> decide +native)

theorem dealVatFluxCallMem_read (σmem σ : AccountMap) (I : ExecutionEnv) :
    (dealVatFluxCallMem σmem σ I).readWithPadding 128 132 =
      vatFluxSelector ++
      UInt256.toByteArray (flipperSlotWord ⟨3⟩ σ I) ++
      UInt256.toByteArray (EVM.word I.codeOwner.val) ++
      UInt256.toByteArray (bidGuyWord (dealId I) σ I) ++
      UInt256.toByteArray (bidLotWord (dealId I) σ I) := by
  rw [byteArray_readWithPadding_split (dealVatFluxCallMem σmem σ I) 128 4 128
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [dealVatFluxCallMem_size])]
  rw [dealVatFluxCallMem_read128_4]
  rw [byteArray_readWithPadding_split (dealVatFluxCallMem σmem σ I) 132 32 96
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [dealVatFluxCallMem_size])]
  rw [dealVatFluxCallMem_read132]
  rw [byteArray_readWithPadding_split (dealVatFluxCallMem σmem σ I) 164 32 64
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [dealVatFluxCallMem_size])]
  rw [dealVatFluxCallMem_read164]
  rw [byteArray_readWithPadding_split (dealVatFluxCallMem σmem σ I) 196 32 32
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [dealVatFluxCallMem_size])]
  rw [dealVatFluxCallMem_read196, dealVatFluxCallMem_read228]
  simp [ByteArray.append_assoc]

noncomputable abbrev dealDeleteHashMem (σmem σ : AccountMap) (I : ExecutionEnv)
    (id : UInt256) : ByteArray :=
  writeCascade (dealVatFluxCallMem σmem σ I) [(0, id), (32, ⟨1⟩)]

abbrev dealBidDeleteAccountMap (I : ExecutionEnv) (σ : AccountMap) (id : UInt256) :
    AccountMap :=
  bidDeleteCollapsedAccountMap I.codeOwner σ id

theorem dealDeleteHashMem_size (σmem σ : AccountMap) (I : ExecutionEnv) (id : UInt256) :
    (dealDeleteHashMem σmem σ I id).size = 260 := by
  unfold dealDeleteHashMem
  apply writeCascade_size_of_base
  · exact dealVatFluxCallMem_size σmem σ I
  · simp [WriteGapsOk]
  · rfl

theorem dealDeleteHashMem_read0 (σmem σ : AccountMap) (I : ExecutionEnv) (id : UInt256) :
    (dealDeleteHashMem σmem σ I id).readWithPadding 0 32 = UInt256.toByteArray id := by
  unfold dealDeleteHashMem
  exact writeCascade_read_word_of_head_of_base
    (dealVatFluxCallMem σmem σ I) (base := 260) (off := 0) (word := id)
    (rest := [(32, (⟨1⟩ : UInt256))])
    (dealVatFluxCallMem_size σmem σ I)
    (by decide +native)
    (by simp [WindowDisjointFromWrites] <;> decide +native)

theorem dealDeleteHashMem_read32 (σmem σ : AccountMap) (I : ExecutionEnv) (id : UInt256) :
    (dealDeleteHashMem σmem σ I id).readWithPadding 32 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold dealDeleteHashMem
  rw [writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord (dealVatFluxCallMem σmem σ I) 0 id) (base := 260) (off := 32)
    (word := (⟨1⟩ : UInt256)) (rest := [])
    (by
      rw [writeWord_size]
      · rw [dealVatFluxCallMem_size]; decide +native
      · rw [dealVatFluxCallMem_size]; decide +native)
    (by decide +native)
    (by simp [WindowDisjointFromWrites])

theorem dealDeleteHashMem_read0_64 (σmem σ : AccountMap) (I : ExecutionEnv)
    (id : UInt256) :
    (dealDeleteHashMem σmem σ I id).readWithPadding 0 64 =
      UInt256.toByteArray id ++ UInt256.toByteArray (⟨1⟩ : UInt256) := by
  rw [byteArray_readWithPadding_split (dealDeleteHashMem σmem σ I id) 0 32 32
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [dealDeleteHashMem_size]; omega)]
  rw [dealDeleteHashMem_read0, dealDeleteHashMem_read32]

theorem dealDeleteHashMem_solcMappingSlot (σmem σ : AccountMap) (I : ExecutionEnv)
    (id : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((dealDeleteHashMem σmem σ I id).readWithPadding 0 64))) =
      solcMappingSlot ⟨1⟩ id := by
  rw [dealDeleteHashMem_read0_64]
  unfold solcMappingSlot
  exact mappingSlot_single id ⟨1⟩

theorem setAddressOffset0Word_zero (old : UInt256) :
    setAddressOffset0Word old ⟨0⟩ =
      UInt256.land old (UInt256.lnot solcAddrMask) := by
  rw [setAddressOffset0Word]
  rw [show UInt256.land (⟨0⟩ : UInt256) solcAddrMask = ⟨0⟩ by decide +native]
  exact u256_lor_zero _

theorem dealEncodeABIValue_bytes32_word (w : UInt256) :
    encodeABIValue? bytes32 (.fixedBytes bytes32Width (EVM.Word.toBytesBE w)) =
      some (UInt256.toByteArray w).toList := by
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    simpa [toByteArray_eq_toBytesBE] using word_toBytesBE_toByteArray_size w
  have hz : zeroBytes 0 = [] := by decide +native
  simp [bytes32, bytes32Width, encodeABIValue?, hlen, hz,
    toByteArray_eq_toBytesBE, byteArray_toList_eq]

theorem dealEncodeABIValue_address_word (w : UInt256) :
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

theorem dealEncodeABIValue_this_address (I : ExecutionEnv) :
    encodeABIValue? addr (.address I.codeOwner) =
      some (UInt256.toByteArray (EVM.word I.codeOwner.val)).toList := by
  have hword : EVM.word I.codeOwner.val = EVM.word I.codeOwner.val := rfl
  simp [addr, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat,
    EVM.addressModulus, hword, toByteArray_eq_toBytesBE, byteArray_toList_eq]

theorem dealVatFluxCallMem_encode (σmem σ : AccountMap) (I : ExecutionEnv) :
    config.externalABI.encode? "flux"
      [.fixedBytes bytes32Width (EVM.Word.toBytesBE (flipperSlotWord ⟨3⟩ σ I)),
        .address I.codeOwner,
        .address (AccountAddress.ofNat (bidGuyWord (dealId I) σ I).toNat),
        .int (Int.ofNat (bidLotWord (dealId I) σ I).toNat)] =
        some ((dealVatFluxCallMem σmem σ I).readWithPadding 128 132) := by
  rw [dealVatFluxCallMem_read]
  unfold config externalABI
  simp only [if_true]
  unfold ABI.encodeCallWithSelector?
  have hguy :
      encodeABIValue? addr
          (.address (AccountAddress.ofNat (bidGuyWord (dealId I) σ I).toNat)) =
        some (UInt256.toByteArray (bidGuyWord (dealId I) σ I)).toList := by
    simpa [bidGuyWord, flipperAddressReturnWord] using
      dealEncodeABIValue_address_word (flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ I)
  have hpayload :
      encodeABIValues? [bytes32, addr, addr, uint256]
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (flipperSlotWord ⟨3⟩ σ I)),
          .address I.codeOwner,
          .address (AccountAddress.ofNat (bidGuyWord (dealId I) σ I).toNat),
          .int (Int.ofNat (bidLotWord (dealId I) σ I).toNat)] =
          some (UInt256.toByteArray (flipperSlotWord ⟨3⟩ σ I) ++
            UInt256.toByteArray (EVM.word I.codeOwner.val) ++
            UInt256.toByteArray (bidGuyWord (dealId I) σ I) ++
            UInt256.toByteArray (bidLotWord (dealId I) σ I)).toList := by
    unfold encodeABIValues?
    rw [show abiTupleHeadSize? [bytes32, addr, addr, uint256] = some 128 by decide +native]
    simp only [encodeABIValuesFrom?, Option.bind, bind]
    rw [dealEncodeABIValue_bytes32_word, dealEncodeABIValue_this_address, hguy,
      dealEncodeABIValue_uint256_word]
    simp [show isDynamicABIType bytes32 = false by decide +native,
      show isDynamicABIType addr = false by decide +native,
      show isDynamicABIType uint256 = false by decide +native,
      ByteArray.append_assoc, byteArray_toList_eq]
  rw [hpayload]
  apply congrArg some
  apply ByteArray.ext
  simp [vatFluxSelector, byteArray_toList_eq, ByteArray.append_assoc]

theorem flipperDealX_ticFlag {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (h : RD flipperBytecode I g s0 ⟨5365⟩ [dealId I, ret, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨5400⟩
      [UInt256.isZero (bidTicWord (dealId I) σ I), dealId I, ret, sel]
      (dealHashMem0 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd5382 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dealId I) solcFreePtrMem) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 (dealHashMem0 I) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (dealId I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (dealId I) solcFreePtrMem_size)
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k5384, C5384, rd5384raw⟩ := rd5382.sload (by decide +native) (by evm_ov)
  have rd5384 : RD flipperBytecode I g s0 ⟨5384⟩
      [flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ I, dealId I, ret, sel]
      (dealHashMem0 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k5384 C5384 := by
    have hslotAdd :
        ⟨2⟩ + solcMappingSlot ⟨1⟩ (dealId I) =
          solcMappingSlot ⟨1⟩ (dealId I) + ⟨2⟩ := by
      exact u256_add_comm _ _
    simpa [dealHashMem0, bidPackedSlotOfWord, bidBaseOfWord, flipperSlotWord,
      hslotAdd] using rd5384raw
  have rd5399 := evm_run rd5384 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by decide +native)
      flipperDealDecodePushMask5391
      (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov)]
  have hraw :
      UInt256.land uint48Mask
        (UInt256.div (flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ I)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)) =
        bidTicWord (dealId I) σ I := by
    simp [bidTicWord, flipperUint48Offset20Word, uint48Divisor20, u256_land_comm]
  rw [hraw] at rd5399
  exact ⟨_, _, by
    convert rd5399 using 1 <;> decide +native⟩

theorem flipperDealX_ticZero {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (htic : bidTicWord (dealId I) σ I = ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨5365⟩ [dealId I, ret, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  have rd5382 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dealId I) solcFreePtrMem) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 (dealHashMem0 I) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (dealId I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (dealId I) solcFreePtrMem_size)
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k5384, C5384, rd5384raw⟩ := rd5382.sload (by decide +native) (by evm_ov)
  have rd5384 : RD flipperBytecode I g s0 ⟨5384⟩
      [flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ I, dealId I, ret, sel]
      (dealHashMem0 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k5384 C5384 := by
    have hslotAdd :
        ⟨2⟩ + solcMappingSlot ⟨1⟩ (dealId I) =
          solcMappingSlot ⟨1⟩ (dealId I) + ⟨2⟩ := by
      exact u256_add_comm _ _
    simpa [dealHashMem0, bidPackedSlotOfWord, bidBaseOfWord, flipperSlotWord,
      hslotAdd] using rd5384raw
  have rd5399 := evm_run rd5384 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by decide +native)
      flipperDealDecodePushMask5391
      (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov)]
  have hraw :
      UInt256.land uint48Mask
        (UInt256.div (flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ I)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)) = ⟨0⟩ := by
    simpa [bidTicWord, flipperUint48Offset20Word, uint48Divisor20, u256_land_comm]
      using htic
  rw [hraw] at rd5399
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd5399
  have rd5486 := evm_run rd5399 with [
    raw dup1 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw push2 ⟨5486⟩ (by decide +native) (by evm_ov),
    raw jumpiT (by decide +native) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov)]
  have rd5491 := evm_run rd5486 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push2 ⟨5558⟩ (by decide +native) (by evm_ov),
    raw jumpiNT (by decide +native) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov)]
  exact RD.solcErrorStringRevertTail
    (pc := ⟨5491⟩) (len := ⟨20⟩)
    (rawWord := (⟨100511754872539569357457718180397213934685919577⟩ : UInt256))
    (shift := ⟨98⟩) (op := .PUSH20) (width := 20)
    (word := UInt256.shiftLeft
      (⟨100511754872539569357457718180397213934685919577⟩ : UInt256) ⟨98⟩)
    rd5491
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | decide +native)
    (by decide) (by rfl)
    (twoWordHashMem_size_96 (dealId I) ⟨1⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 (dealId I) ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp [dealHashMem0])

theorem flipperDealX_ticExpired {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hticNe : bidTicWord (dealId I) σ I ≠ ⟨0⟩)
    (hticLt : (bidTicWord (dealId I) σ I).toNat <
      (UInt256.ofNat I.header.timestamp).toNat)
    (h : RD flipperBytecode I g s0 ⟨5365⟩ [dealId I, ret, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨5558⟩ [dealId I, ret, sel]
      (dealHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd5400⟩ := flipperDealX_ticFlag (I := I) h
  rw [Reasoning.Theory.isZero_eq_zero_of_ne hticNe] at rd5400
  have rd5408 := evm_run rd5400 with [
    raw dup1 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw push2 ⟨5486⟩ (by decide +native) (by evm_ov),
    raw jumpiNT (by decide +native) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  have rd5444 := evm_run rd5408 with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dealId I) (dealHashMem0 I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 (dealHashMem1 I) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (dealId I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (dealId I)
        (twoWordHashMem_size_96 (dealId I) ⟨1⟩ solcFreePtrMem_size))
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k5426, C5426, rd5426raw⟩ := rd5444.sload (by decide +native) (by evm_ov)
  have rd5426 : RD flipperBytecode I g s0 ⟨5426⟩
      [flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ I, dealId I, ret, sel]
      (dealHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k5426 C5426 := by
    have hslotAdd :
        ⟨2⟩ + solcMappingSlot ⟨1⟩ (dealId I) =
          solcMappingSlot ⟨1⟩ (dealId I) + ⟨2⟩ := by
      exact u256_add_comm _ _
    simpa [dealHashMem1, bidPackedSlotOfWord, bidBaseOfWord, flipperSlotWord,
      hslotAdd] using rd5426raw
  have rd5444lt := evm_run rd5426 with [
    raw timestamp (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by decide +native)
      flipperDealDecodePushMask5435
      (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov)]
  have hraw :
      UInt256.land uint48Mask
        (UInt256.div (flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ I)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)) =
        bidTicWord (dealId I) σ I := by
    simp [bidTicWord, flipperUint48Offset20Word, uint48Divisor20, u256_land_comm]
  have hltWord :
      UInt256.lt (bidTicWord (dealId I) σ I)
        (UInt256.ofNat I.header.timestamp) = ⟨1⟩ := by
    exact Reasoning.Theory.ult_one hticLt
  rw [hraw, hltWord] at rd5444lt
  have rd5558 := evm_run rd5444lt with [
    raw dup1 (by decide +native) (by evm_ov),
    raw push2 ⟨5486⟩ (by decide +native) (by evm_ov),
    raw jumpiT (by decide +native) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov),
    raw jumpdest (by decide +native) (by evm_ov),
    raw push2 ⟨5558⟩ (by decide +native) (by evm_ov),
    raw jumpiT (by decide +native) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa using rd5558⟩

theorem flipperDealX_endCheckStart {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hticNe : bidTicWord (dealId I) σ I ≠ ⟨0⟩)
    (hticGe : (UInt256.ofNat I.header.timestamp).toNat ≤
      (bidTicWord (dealId I) σ I).toNat)
    (h : RD flipperBytecode I g s0 ⟨5365⟩ [dealId I, ret, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨5450⟩ [dealId I, ret, sel]
      (dealHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd5400⟩ := flipperDealX_ticFlag (I := I) h
  rw [Reasoning.Theory.isZero_eq_zero_of_ne hticNe] at rd5400
  have rd5408 := evm_run rd5400 with [
    raw dup1 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw push2 ⟨5486⟩ (by decide +native) (by evm_ov),
    raw jumpiNT (by decide +native) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  have rd5444 := evm_run rd5408 with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dealId I) (dealHashMem0 I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 (dealHashMem1 I) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (dealId I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (dealId I)
        (twoWordHashMem_size_96 (dealId I) ⟨1⟩ solcFreePtrMem_size))
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k5426, C5426, rd5426raw⟩ := rd5444.sload (by decide +native) (by evm_ov)
  have rd5426 : RD flipperBytecode I g s0 ⟨5426⟩
      [flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ I, dealId I, ret, sel]
      (dealHashMem1 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k5426 C5426 := by
    have hslotAdd :
        ⟨2⟩ + solcMappingSlot ⟨1⟩ (dealId I) =
          solcMappingSlot ⟨1⟩ (dealId I) + ⟨2⟩ := by
      exact u256_add_comm _ _
    simpa [dealHashMem1, bidPackedSlotOfWord, bidBaseOfWord, flipperSlotWord,
      hslotAdd] using rd5426raw
  have rd5444lt := evm_run rd5426 with [
    raw timestamp (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by decide +native)
      flipperDealDecodePushMask5435
      (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov)]
  have hraw :
      UInt256.land uint48Mask
        (UInt256.div (flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ I)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)) =
        bidTicWord (dealId I) σ I := by
    simp [bidTicWord, flipperUint48Offset20Word, uint48Divisor20, u256_land_comm]
  have hltWord :
      UInt256.lt (bidTicWord (dealId I) σ I)
        (UInt256.ofNat I.header.timestamp) = ⟨0⟩ := by
    exact Reasoning.Theory.ult_zero hticGe
  rw [hraw, hltWord] at rd5444lt
  have rd5450 := evm_run rd5444lt with [
    raw dup1 (by decide +native) (by evm_ov),
    raw push2 ⟨5486⟩ (by decide +native) (by evm_ov),
    raw jumpiNT (by decide +native) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  exact ⟨_, _, by simpa using rd5450⟩

theorem flipperDealX_endExpired {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hticNe : bidTicWord (dealId I) σ I ≠ ⟨0⟩)
    (hticGe : (UInt256.ofNat I.header.timestamp).toNat ≤
      (bidTicWord (dealId I) σ I).toNat)
    (hendLt : (bidEndWord (dealId I) σ I).toNat <
      (UInt256.ofNat I.header.timestamp).toNat)
    (h : RD flipperBytecode I g s0 ⟨5365⟩ [dealId I, ret, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨5558⟩ [dealId I, ret, sel]
      (dealHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd5450⟩ := flipperDealX_endCheckStart hticNe hticGe h
  have rd5486 := evm_run rd5450 with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dealId I) (dealHashMem1 I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 (dealHashMem2 I) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (dealId I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (dealId I)
        (twoWordHashMem_size_96 (dealId I) ⟨1⟩
          (twoWordHashMem_size_96 (dealId I) ⟨1⟩ solcFreePtrMem_size)))
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k5468, C5468, rd5468raw⟩ := rd5486.sload (by decide +native) (by evm_ov)
  have rd5468 : RD flipperBytecode I g s0 ⟨5468⟩
      [flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ I, dealId I, ret, sel]
      (dealHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k5468 C5468 := by
    have hslotAdd :
        ⟨2⟩ + solcMappingSlot ⟨1⟩ (dealId I) =
          solcMappingSlot ⟨1⟩ (dealId I) + ⟨2⟩ := by
      exact u256_add_comm _ _
    simpa [dealHashMem2, bidPackedSlotOfWord, bidBaseOfWord, flipperSlotWord,
      hslotAdd] using rd5468raw
  have rd5486lt := evm_run rd5468 with [
    raw timestamp (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨208⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by decide +native)
      flipperDealDecodePushMask5477
      (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov)]
  have hraw :
      UInt256.land uint48Mask
        (UInt256.div (flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ I)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩)) =
        bidEndWord (dealId I) σ I := by
    simp [bidEndWord, flipperUint48Offset26Word, uint48Divisor26, u256_land_comm]
  have hltWord :
      UInt256.lt (bidEndWord (dealId I) σ I)
        (UInt256.ofNat I.header.timestamp) = ⟨1⟩ := by
    exact Reasoning.Theory.ult_one hendLt
  rw [hraw, hltWord] at rd5486lt
  have rd5558 := evm_run rd5486lt with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push2 ⟨5558⟩ (by decide +native) (by evm_ov),
    raw jumpiT (by decide +native) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa using rd5558⟩

theorem flipperDealX_notFinished {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hticNe : bidTicWord (dealId I) σ I ≠ ⟨0⟩)
    (hticGe : (UInt256.ofNat I.header.timestamp).toNat ≤
      (bidTicWord (dealId I) σ I).toNat)
    (hendGe : (UInt256.ofNat I.header.timestamp).toNat ≤
      (bidEndWord (dealId I) σ I).toNat)
    (h : RD flipperBytecode I g s0 ⟨5365⟩ [dealId I, ret, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨_, _, rd5450⟩ := flipperDealX_endCheckStart hticNe hticGe h
  have rd5486 := evm_run rd5450 with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dealId I) (dealHashMem1 I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 (dealHashMem2 I) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (dealId I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (dealId I)
        (twoWordHashMem_size_96 (dealId I) ⟨1⟩
          (twoWordHashMem_size_96 (dealId I) ⟨1⟩ solcFreePtrMem_size)))
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k5468, C5468, rd5468raw⟩ := rd5486.sload (by decide +native) (by evm_ov)
  have rd5468 : RD flipperBytecode I g s0 ⟨5468⟩
      [flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ I, dealId I, ret, sel]
      (dealHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k5468 C5468 := by
    have hslotAdd :
        ⟨2⟩ + solcMappingSlot ⟨1⟩ (dealId I) =
          solcMappingSlot ⟨1⟩ (dealId I) + ⟨2⟩ := by
      exact u256_add_comm _ _
    simpa [dealHashMem2, bidPackedSlotOfWord, bidBaseOfWord, flipperSlotWord,
      hslotAdd] using rd5468raw
  have rd5486lt := evm_run rd5468 with [
    raw timestamp (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨208⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by decide +native)
      flipperDealDecodePushMask5477
      (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov)]
  have hraw :
      UInt256.land uint48Mask
        (UInt256.div (flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ I)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩)) =
        bidEndWord (dealId I) σ I := by
    simp [bidEndWord, flipperUint48Offset26Word, uint48Divisor26, u256_land_comm]
  have hltWord :
      UInt256.lt (bidEndWord (dealId I) σ I)
        (UInt256.ofNat I.header.timestamp) = ⟨0⟩ := by
    exact Reasoning.Theory.ult_zero hendGe
  rw [hraw, hltWord] at rd5486lt
  have rd5491 := evm_run rd5486lt with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push2 ⟨5558⟩ (by decide +native) (by evm_ov),
    raw jumpiNT (by decide +native) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov)]
  exact RD.solcErrorStringRevertTail
    (pc := ⟨5491⟩) (len := ⟨20⟩)
    (rawWord := (⟨100511754872539569357457718180397213934685919577⟩ : UInt256))
    (shift := ⟨98⟩) (op := .PUSH20) (width := 20)
    (word := UInt256.shiftLeft
      (⟨100511754872539569357457718180397213934685919577⟩ : UInt256) ⟨98⟩)
    rd5491
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | decide +native)
    (by decide) (by rfl)
    (twoWordHashMem_size_96 (dealId I) ⟨1⟩
      (twoWordHashMem_size_96 (dealId I) ⟨1⟩
        (twoWordHashMem_size_96 (dealId I) ⟨1⟩ solcFreePtrMem_size)))
    (twoWordHashMem_read64 (dealId I) ⟨1⟩
      (twoWordHashMem_size_96 (dealId I) ⟨1⟩
        (twoWordHashMem_size_96 (dealId I) ⟨1⟩ solcFreePtrMem_size))
      (twoWordHashMem_read64 (dealId I) ⟨1⟩
        (twoWordHashMem_size_96 (dealId I) ⟨1⟩ solcFreePtrMem_size)
        (twoWordHashMem_read64 (dealId I) ⟨1⟩ solcFreePtrMem_size
          solcFreePtrMem_read64)))
    (by simp [dealHashMem2])

theorem flipperDealX_toCatExtcodesizeGuard {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (h : RD flipperBytecode I g s0 ⟨5558⟩ [dealId I, ret, sel]
      (dealHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨5638⟩
      (flipperCatTargetWord σ I :: flipperCatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨36⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨164⟩ :: ⟨3865913243⟩ ::
        flipperCatTargetWord σ I :: dealId I :: ret :: sel :: [])
      (dealCatCallMem σ I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k' C' := by
  let rawTarget := flipperSlotWord ⟨7⟩ σ I
  have rd5561 := h.jumpdest (by decide +native) (by evm_ov)
    |>.push1 ⟨7⟩ (by decide +native) (by evm_ov)
  obtain ⟨k5562, C5562, rd5562raw⟩ := rd5561.sload (by decide +native) (by evm_ov)
  have rd5562 : RD flipperBytecode I g s0 ⟨5562⟩
      (rawTarget :: dealId I :: ret :: sel :: [])
      (dealHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k5562 C5562 := by
    simpa [rawTarget, flipperSlotWord, solcSlotWord] using rd5562raw
  have hmload64Hash :
      (if (⟨64⟩ : UInt256).toNat ≥ (dealCatHashMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((dealCatHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [dealCatHashMem_size]; decide) (by decide)
      (dealCatHashMem_read64 I)
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (dealCatCallMem σ I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((dealCatCallMem σ I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [dealCatCallMem_size]; decide) (by decide)
      (dealCatCallMem_read64 σ I)
  have rd5580 := evm_run rd5562 with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dealId I) (dealHashMem2 I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 (dealCatHashMem I) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (dealId I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (dealId I) (dealHashMem2_size I))
      (by decide) (by evm_ov),
    raw push1 ⟨5⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k5581, C5581, rd5581raw⟩ := rd5580.sload (by decide +native) (by evm_ov)
  have rd5581 : RD flipperBytecode I g s0 ⟨5581⟩
      (bidTabWord (dealId I) σ I :: ⟨64⟩ :: ⟨0⟩ :: rawTarget ::
        dealId I :: ret :: sel :: [])
      (dealCatHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k5581 C5581 := by
    have hslotAdd :
        ⟨5⟩ + solcMappingSlot ⟨1⟩ (dealId I) =
          solcMappingSlot ⟨1⟩ (dealId I) + ⟨5⟩ := by
      exact u256_add_comm _ _
    simpa [dealCatHashMem, bidTabWord, bidSlotOfWord, bidBaseOfWord,
      flipperSlotWord, hslotAdd] using rd5581raw
  have rd5638 := evm_run rd5581 with [
    raw dup2 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native)
      mem_cost hmload64Hash (by decide) (by evm_ov),
    raw push4 ⟨3865913243⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨224⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 6 (dealCatSelectorMem I) (UInt256.ofNat 5)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw mstore 3 (dealCatCallMem σ I) (UInt256.ofNat 6)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push4 ⟨3865913243⟩ (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 ⟨36⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  exact ⟨_, _, by
    simpa [rawTarget, flipperCatTargetWord, flipperAddressReturnWord, flipperSlotWord,
      solcSlotWord, solcAddrMask, dealCatSelectorWord] using rd5638⟩

theorem flipperDealX_catNoCode {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperCatTargetWord σ I) = ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨5558⟩ [dealId I, ret, sel]
      (dealHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨_, _, rd5638⟩ := flipperDealX_toCatExtcodesizeGuard h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨5638⟩) (okPc := ⟨5650⟩) rd5638
    hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp)

theorem flipperDealX_toCatCall {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperCatTargetWord σ I) ≠ ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨5558⟩ [dealId I, ret, sel]
      (dealHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ gasWord k' C', RD flipperBytecode I g s0 ⟨5653⟩
      (gasWord :: flipperCatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ :: ⟨36⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨164⟩ :: ⟨3865913243⟩ ::
        flipperCatTargetWord σ I :: dealId I :: ret :: sel :: [])
      (dealCatCallMem σ I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd5638⟩ := flipperDealX_toCatExtcodesizeGuard h
  obtain ⟨gasWord, k5653, C5653, rd5653⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨5638⟩) (okPc := ⟨5650⟩) rd5638
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp)
  exact ⟨gasWord, k5653, C5653, by simpa using rd5653⟩

theorem flipperDealX_catPostCall
    {cA gh bl σ σ₀ A I} {g : UInt256} {k C : ℕ} {ret sel : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperCatTargetWord σ I) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (h : RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5558⟩
      [dealId I, ret, sel] (dealHashMem2 I) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5654⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: ⟨3865913243⟩ ::
          flipperCatTargetWord σ I :: dealId I :: ret :: sel :: [])
        (dealCatCallMem σ I) (UInt256.ofNat 6) out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperCatAddress σ I)) "claw" 0
        [Value.int (Int.ofNat (bidTabWord (dealId I) σ I).toNat)]
        (z,
          { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', substate := A', createdAccounts := cA' },
          out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd5653⟩ := flipperDealX_toCatCall hcodeSize h
  obtain ⟨cA', σ', z, out, A_in, callGas, k5654, C5654, hΘpack, rd5654raw,
      houtsz⟩ :=
    RD.call rd5653 (by decide +native) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k5654, C5654, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          (⟨128⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
      decide +native
    have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
      rfl
    have rd5654 : RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5654⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: ⟨3865913243⟩ ::
          flipperCatTargetWord σ I :: dealId I :: ret :: sel :: [])
        (out.write 0 (dealCatCallMem σ I) 128
          (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 6) out (cA', σ') k5654 C5654 :=
      haw ▸ rd5654raw
    rw [hmin, byteArray_write_len_zero] at rd5654
    exact rd5654
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := flipperCatTargetWord σ I)
      (mem := dealCatCallMem σ I) (inOff := ⟨128⟩) (inSize := ⟨36⟩)
      (fun hdepthEq => by
        have hEq : I.depth = (1024 : Fin 1025) := by
          simpa [initState] using hdepthEq
        exact absurd hdepth (by rw [hEq]; decide))
      (flipperCatEvmAddress_eq_target_of_accountMapEquiv (accountMapEquiv.refl σ))
      (dealCatCallMem_encode σ I) ?_
    simpa [initState, hperm] using hΘ

theorem flipperDealX_catCallFailure {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {aw target id ret sel selector : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode I g s0 ⟨5654⟩
      (⟨0⟩ :: ⟨164⟩ :: selector :: target :: id :: ret :: sel :: [])
      mem aw out acc k C)
    (houtsz : out.size < UInt256.size) :
    RDrev flipperBytecode g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨5654⟩) (okPc := ⟨5670⟩) h
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    houtsz (by simp)

theorem flipperDealX_catCallDepthLimit {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperCatTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (h : RD flipperBytecode I g s0 ⟨5558⟩ [dealId I, ret, sel]
      (dealHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨gasWord, _, _, rd5653⟩ := flipperDealX_toCatCall hcodeSize h
  obtain ⟨k5654, C5654, rd5654raw⟩ :=
    RD.callDepthLimit
      (code := flipperBytecode) (ee := I) (g := g) (s0 := s0) (pc := ⟨5653⟩)
      (mem := dealCatCallMem σ I) (aw := UInt256.ofNat 6) (rdata := ByteArray.empty)
      (cA := cA) (σ := σ) (gasArg := gasWord) (target := flipperCatTargetWord σ I)
      (inOffset := ⟨128⟩) (inSize := ⟨36⟩) (outOffset := ⟨128⟩) (outSize := ⟨0⟩)
      (t := [⟨164⟩, ⟨3865913243⟩, flipperCatTargetWord σ I, dealId I, ret, sel])
      rd5653 (by decide +native) hdepth (by simp)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        (⟨128⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
    decide +native
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    rfl
  have rd5654 : RD flipperBytecode I g s0 ⟨5654⟩
      (⟨0⟩ :: ⟨164⟩ :: ⟨3865913243⟩ ::
        flipperCatTargetWord σ I :: dealId I :: ret :: sel :: [])
      (dealCatCallMem σ I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k5654 C5654 :=
    by
      rw [hmin, byteArray_write_len_zero] at rd5654raw
      exact haw ▸ rd5654raw
  exact flipperDealX_catCallFailure rd5654 (by decide +native)

theorem flipperDealX_catCallSuccessToVatStart {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {aw target id ret sel selector : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode I g s0 ⟨5654⟩
      (⟨1⟩ :: ⟨164⟩ :: selector :: target :: id :: ret :: sel :: [])
      mem aw out acc k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨5673⟩
      (selector :: target :: id :: ret :: sel :: [])
      mem aw out acc k' C' := by
  obtain ⟨k5672, C5672, rd5672⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨5654⟩) (okPc := ⟨5670⟩) h
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
      (by simp)
  have rd5673 := rd5672.pop (by decide +native) (by evm_ov)
  exact ⟨k5672 + 1, C5672 + 2, by simpa using rd5673⟩

theorem flipperDealX_toVatExtcodesizeGuard {cA σmem σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out : ByteArray} {ret sel selector target : UInt256}
    (h : RD flipperBytecode I g s0 ⟨5673⟩
      (selector :: target :: dealId I :: ret :: sel :: [])
      (dealCatCallMem σmem I) (UInt256.ofNat 6) out (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨5782⟩
      (flipperVatTargetWord σ I :: flipperVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨132⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: ⟨1628552750⟩ ::
        flipperVatTargetWord σ I :: dealId I :: ret :: sel :: [])
      (dealVatFluxCallMem σmem σ I) (UInt256.ofNat 9) out (cA, σ) k' C' := by
  let rawVat := flipperSlotWord ⟨2⟩ σ I
  let rawIlk := flipperSlotWord ⟨3⟩ σ I
  let rawPacked := flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ I
  let base := solcMappingSlot ⟨1⟩ (dealId I)
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide +native
  have hvatClean : UInt256.land rawVat solcAddrMask = flipperVatTargetWord σ I := by
    simp [rawVat, flipperVatTargetWord, flipperAddressReturnWord]
  have hpackedClean : UInt256.land rawPacked solcAddrMask = bidGuyWord (dealId I) σ I := by
    simp [rawPacked, bidGuyWord, flipperAddressReturnWord]
  have hpackedCleanLeft :
      UInt256.land solcAddrMask rawPacked = bidGuyWord (dealId I) σ I := by
    simpa [u256_land_comm] using hpackedClean
  have hmload64Hash :
      (if (⟨64⟩ : UInt256).toNat ≥ (dealVatHashMem σmem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((dealVatHashMem σmem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [dealVatHashMem_size]; decide) (by decide)
      (dealVatHashMem_read64 σmem I)
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (dealVatFluxCallMem σmem σ I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((dealVatFluxCallMem σmem σ I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [dealVatFluxCallMem_size]; decide) (by decide)
      (dealVatFluxCallMem_read64 σmem σ I)
  have rd5676 := evm_run h with [
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  obtain ⟨k5677, C5677, rd5677raw⟩ := rd5676.sload (by decide +native) (by evm_ov)
  have rd5677 : RD flipperBytecode I g s0 ⟨5677⟩
      (rawVat :: ⟨2⟩ :: selector :: target :: dealId I :: ret :: sel :: [])
      (dealCatCallMem σmem I) (UInt256.ofNat 6) out (cA, σ) k5677 C5677 := by
    simpa [rawVat, flipperSlotWord, solcSlotWord] using rd5677raw
  have rd5679 := rd5677.push1 ⟨3⟩ (by decide +native) (by evm_ov)
  obtain ⟨k5680, C5680, rd5680raw⟩ := rd5679.sload (by decide +native) (by evm_ov)
  have rd5680 : RD flipperBytecode I g s0 ⟨5680⟩
      (rawIlk :: rawVat :: ⟨2⟩ :: selector :: target :: dealId I :: ret :: sel :: [])
      (dealCatCallMem σmem I) (UInt256.ofNat 6) out (cA, σ) k5680 C5680 := by
    simpa [rawIlk, flipperSlotWord, solcSlotWord] using rd5680raw
  have rd5699 := evm_run rd5680 with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dealId I) (dealCatCallMem σmem I)) (UInt256.ofNat 6)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 0 (dealVatHashMem σmem I) (UInt256.ofNat 6)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw keccak256 0 base (UInt256.ofNat 6)
      (by decide +native) mem_cost
      (by simpa [base] using dealVatHashMem_solcMappingSlot σmem I)
      (by decide) (by evm_ov),
    raw swap6 (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k5701, C5701, rd5701raw⟩ := rd5699.sload (by decide +native) (by evm_ov)
  have rd5701 : RD flipperBytecode I g s0 ⟨5701⟩
      (rawPacked :: ⟨64⟩ :: ⟨1⟩ :: ⟨0⟩ :: rawIlk :: rawVat ::
        base :: selector :: target :: dealId I :: ret :: sel :: [])
      (dealVatHashMem σmem I) (UInt256.ofNat 6) out (cA, σ) k5701 C5701 := by
    have hslotAdd :
        base + (⟨2⟩ : UInt256) = solcMappingSlot ⟨1⟩ (dealId I) + ⟨2⟩ := by
      simp [base]
    simpa [rawPacked, bidPackedSlotOfWord, bidBaseOfWord, flipperSlotWord, hslotAdd]
      using rd5701raw
  have rd5704 := evm_run rd5701 with [
    raw swap6 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k5706, C5706, rd5706raw⟩ := rd5704.sload (by decide +native) (by evm_ov)
  have rd5706 : RD flipperBytecode I g s0 ⟨5706⟩
      (bidLotWord (dealId I) σ I :: ⟨64⟩ :: ⟨0⟩ :: rawIlk :: rawVat ::
        rawPacked :: selector :: target :: dealId I :: ret :: sel :: [])
      (dealVatHashMem σmem I) (UInt256.ofNat 6) out (cA, σ) k5706 C5706 := by
    have hslotAdd :
        (⟨1⟩ : UInt256) + base = solcMappingSlot ⟨1⟩ (dealId I) + ⟨1⟩ := by
      simpa [base] using
        (u256_add_comm (⟨1⟩ : UInt256) (solcMappingSlot ⟨1⟩ (dealId I)))
    simpa [bidLotWord, bidSlotOfWord, bidBaseOfWord, flipperSlotWord, hslotAdd]
      using rd5706raw
  have rd5726 := evm_run rd5706 with [
    raw dup2 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64Hash (by decide) (by evm_ov),
    raw push4 ⟨814276375⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨225⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (dealVatFluxSelectorMem σmem I) (UInt256.ofNat 6)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap5 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap5 (by decide +native) (by evm_ov),
    raw mstore 0 (dealVatFluxIlkMem σmem σ I) (UInt256.ofNat 6)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd5727 := RD.address rd5726 (by decide +native) (by evm_ov)
  have rd5782 := evm_run rd5727 with [
    raw push1 ⟨36⟩ (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (dealVatFluxThisMem σmem σ I) (UInt256.ofNat 7)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw swap6 (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw push1 ⟨68⟩ (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (dealVatFluxGuyMem σmem σ I) (UInt256.ofNat 8)
      (by decide +native) mem_cost
      (by
        rw [hmask160, hpackedCleanLeft]
        change (UInt256.toByteArray (bidGuyWord (dealId I) σ I)).write 0
            (dealVatFluxThisMem σmem σ I) 196 32 =
          dealVatFluxGuyMem σmem σ I
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨100⟩ (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (dealVatFluxCallMem σmem σ I) (UInt256.ofNat 9)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide +native)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap5 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push4 ⟨1628552750⟩ (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨132⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  rw [hmask160, hvatClean] at rd5782
  exact ⟨_, _, by
    convert rd5782 using 1 <;> decide +native⟩

theorem flipperDealX_vatNoCode {cA σmem σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out : ByteArray} {ret sel selector target : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) = ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨5673⟩
      (selector :: target :: dealId I :: ret :: sel :: [])
      (dealCatCallMem σmem I) (UInt256.ofNat 6) out (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨_, _, rd5782⟩ := flipperDealX_toVatExtcodesizeGuard h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨5782⟩) (okPc := ⟨1611⟩) rd5782
    hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp)

theorem flipperDealX_toVatCall {cA σmem σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out : ByteArray} {ret sel selector target : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨5673⟩
      (selector :: target :: dealId I :: ret :: sel :: [])
      (dealCatCallMem σmem I) (UInt256.ofNat 6) out (cA, σ) k C) :
    ∃ gasWord k' C', RD flipperBytecode I g s0 ⟨1614⟩
      (gasWord :: flipperVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ :: ⟨132⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: ⟨1628552750⟩ ::
        flipperVatTargetWord σ I :: dealId I :: ret :: sel :: [])
      (dealVatFluxCallMem σmem σ I) (UInt256.ofNat 9) out (cA, σ) k' C' := by
  obtain ⟨_, _, rd5782⟩ := flipperDealX_toVatExtcodesizeGuard h
  obtain ⟨gasWord, k1614, C1614, rd1614⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨5782⟩) (okPc := ⟨1611⟩) rd5782
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp)
  exact ⟨gasWord, k1614, C1614, by simpa using rd1614⟩

theorem flipperDealX_vatPostCall
    {cA0 gh bl σbase σ₀ A I} {g : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σmem σ : AccountMap} {Acur : Substate}
    {k C : ℕ} {out0 : ByteArray} {ret sel selector target : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (h : RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨5673⟩
      (selector :: target :: dealId I :: ret :: sel :: [])
      (dealCatCallMem σmem I) (UInt256.ofNat 6) out0 (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨1615⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: ⟨1628552750⟩ ::
          flipperVatTargetWord σ I :: dealId I :: ret :: sel :: [])
        (dealVatFluxCallMem σmem σ I) (UInt256.ofNat 9) out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        ({ initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ, substate := Acur, createdAccounts := cA })
        (EVM.address (flipperVatAddress σ I)) "flux" 0
        (dealFluxArgValsOf
          ({ initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ, substate := Acur, createdAccounts := cA })
          (dealId I))
        (z,
          { { initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ, substate := Acur, createdAccounts := cA } with
            accountMap := σ', substate := A', createdAccounts := cA' },
          out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd1614⟩ := flipperDealX_toVatCall hcodeSize h
  obtain ⟨cA', σ', z, out, A_in, callGas, k1615, C1615, hΘpack, rd1615raw,
      houtsz⟩ :=
    RD.call rd1614 (by decide +native) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k1615, C1615, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
          (⟨128⟩ : UInt256).toNat (⟨132⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 9 := by
      decide +native
    have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
      rfl
    have rd1615 : RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨1615⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: ⟨1628552750⟩ ::
          flipperVatTargetWord σ I :: dealId I :: ret :: sel :: [])
        (out.write 0 (dealVatFluxCallMem σmem σ I) 128
          (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 9) out (cA', σ') k1615 C1615 :=
      haw ▸ rd1615raw
    rw [hmin, byteArray_write_len_zero] at rd1615
    exact rd1615
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := flipperVatTargetWord σ I)
      (mem := dealVatFluxCallMem σmem σ I) (inOff := ⟨128⟩) (inSize := ⟨132⟩)
      (fun hdepthEq => by
        have hEq : I.depth = (1024 : Fin 1025) := by
          simpa [initState] using hdepthEq
        exact absurd hdepth (by rw [hEq]; decide))
      (flipperVatEvmAddress_eq_target_of_accountMapEquiv (accountMapEquiv.refl σ))
      ?_ ?_
    · simpa [dealFluxArgValsOf, initState, flipperSlotWord, solcSlotWord,
        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        bidGuyWord, bidLotWord, bidSlotOfWord, bidPackedSlotOfWord, bidBaseOfWord] using
        dealVatFluxCallMem_encode σmem σ I
    · simpa [initState, hperm] using hΘ

theorem flipperDealX_vatCallFailure {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {aw target id ret sel selector : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode I g s0 ⟨1615⟩
      (⟨0⟩ :: ⟨260⟩ :: selector :: target :: id :: ret :: sel :: [])
      mem aw out acc k C)
    (houtsz : out.size < UInt256.size) :
    RDrev flipperBytecode g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨1615⟩) (okPc := ⟨1631⟩) h
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    houtsz (by simp)

theorem flipperDealX_vatCallDepthLimit {cA σmem σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out : ByteArray} {ret sel selector target : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (h : RD flipperBytecode I g s0 ⟨5673⟩
      (selector :: target :: dealId I :: ret :: sel :: [])
      (dealCatCallMem σmem I) (UInt256.ofNat 6) out (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨gasWord, _, _, rd1614⟩ := flipperDealX_toVatCall hcodeSize h
  obtain ⟨k1615, C1615, rd1615raw⟩ :=
    RD.callDepthLimit
      (code := flipperBytecode) (ee := I) (g := g) (s0 := s0) (pc := ⟨1614⟩)
      (mem := dealVatFluxCallMem σmem σ I) (aw := UInt256.ofNat 9) (rdata := out)
      (cA := cA) (σ := σ) (gasArg := gasWord) (target := flipperVatTargetWord σ I)
      (inOffset := ⟨128⟩) (inSize := ⟨132⟩) (outOffset := ⟨128⟩) (outSize := ⟨0⟩)
      (t := [⟨260⟩, ⟨1628552750⟩, flipperVatTargetWord σ I, dealId I, ret, sel])
      rd1614 (by decide +native) hdepth (by simp)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
        (⟨128⟩ : UInt256).toNat (⟨132⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 9 := by
    decide +native
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    rfl
  have rd1615 : RD flipperBytecode I g s0 ⟨1615⟩
      (⟨0⟩ :: ⟨260⟩ :: ⟨1628552750⟩ ::
        flipperVatTargetWord σ I :: dealId I :: ret :: sel :: [])
      (dealVatFluxCallMem σmem σ I) (UInt256.ofNat 9) ByteArray.empty (cA, σ)
      k1615 C1615 :=
    by
      rw [hmin, byteArray_write_len_zero] at rd1615raw
      exact haw ▸ rd1615raw
  exact flipperDealX_vatCallFailure rd1615 (by decide +native)

theorem flipperDealX_vatCallSuccessToDeleteStart {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {aw target id ret sel selector : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode I g s0 ⟨1615⟩
      (⟨1⟩ :: ⟨260⟩ :: selector :: target :: id :: ret :: sel :: [])
      mem aw out acc k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨1633⟩
      (⟨260⟩ :: selector :: target :: id :: ret :: sel :: [])
      mem aw out acc k' C' := by
  obtain ⟨k1633, C1633, rd1633⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨1615⟩) (okPc := ⟨1631⟩) h
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
      (by simp)
  exact ⟨k1633, C1633, by simpa using rd1633⟩

theorem flipperDealX_vatDeleteReturn {I} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σmem σcall σ : AccountMap}
    {k C : ℕ} {out : ByteArray} {selector target id sel : UInt256}
    (hperm : I.perm = true)
    (h : RD flipperBytecode I g s0 ⟨1633⟩
      (⟨260⟩ :: selector :: target :: id :: ⟨323⟩ :: sel :: [])
      (dealVatFluxCallMem σmem σcall I) (UInt256.ofNat 9) out (cA, σ) k C) :
    RDret flipperBytecode g s0 (cA, dealBidDeleteAccountMap I σ id) ByteArray.empty := by
  let base := bidBaseOfWord id
  let memHash := dealDeleteHashMem σmem σcall I id
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
      dealDeleteHashMem_solcMappingSlot σmem σcall I id
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide +native
  have hclear3 :
      UInt256.land (UInt256.lnot solcAddrMask) old3 = clear3 := by
    dsimp [clear3]
    rw [u256_land_comm, setAddressOffset0Word_zero]
  have hclear4 :
      UInt256.land (UInt256.lnot solcAddrMask) old4 = clear4 := by
    dsimp [clear4]
    rw [u256_land_comm, setAddressOffset0Word_zero]
  have rd1648 := evm_run h with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem id (dealVatFluxCallMem σmem σcall I)) (UInt256.ofNat 9)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 0 memHash (UInt256.ofNat 9)
      (by decide +native) mem_cost (by
        dsimp [memHash, dealDeleteHashMem]
        rfl) (by decide) (by evm_ov)]
  have rd1654 := evm_run rd1648 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw keccak256 0 base (UInt256.ofNat 9)
      (by decide +native) mem_cost hslot (by decide) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  obtain ⟨k1655, C1655, rd1655raw⟩ := rd1654.sstore hperm (by decide +native) (by evm_ov)
  have rd1655 : RD flipperBytecode I g s0 ⟨1655⟩
      (base :: ⟨1⟩ :: ⟨0⟩ :: ⟨323⟩ :: sel :: [])
      memHash (UInt256.ofNat 9) out (cA, σ0) k1655 C1655 := by
    simpa [σ0] using rd1655raw
  have rd1660 := evm_run rd1655 with [
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  obtain ⟨k1661, C1661, rd1661raw⟩ := rd1660.sstore hperm (by decide +native) (by evm_ov)
  have rd1661 : RD flipperBytecode I g s0 ⟨1661⟩
      (base :: ⟨0⟩ :: ⟨323⟩ :: sel :: [])
      memHash (UInt256.ofNat 9) out (cA, σ1) k1661 C1661 := by
    simpa [σ1] using rd1661raw
  have rd1667 := evm_run rd1661 with [
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  obtain ⟨k1668, C1668, rd1668raw⟩ := rd1667.sstore hperm (by decide +native) (by evm_ov)
  have rd1668 : RD flipperBytecode I g s0 ⟨1668⟩
      (base :: ⟨0⟩ :: ⟨323⟩ :: sel :: [])
      memHash (UInt256.ofNat 9) out (cA, σ2) k1668 C1668 := by
    simpa [σ2] using rd1668raw
  have rd1672 := evm_run rd1668 with [
    raw push1 ⟨3⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  obtain ⟨k1674, C1674, rd1674raw⟩ := rd1672.sload (by decide +native) (by evm_ov)
  have rd1674 : RD flipperBytecode I g s0 ⟨1674⟩
      (old3 :: (base + ⟨3⟩) :: base :: ⟨0⟩ :: ⟨323⟩ :: sel :: [])
      memHash (UInt256.ofNat 9) out (cA, σ2) k1674 C1674 := by
    simpa [old3, solcSlotWord] using rd1674raw
  have rd1688 := evm_run rd1674 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw not (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov)]
  rw [hmask160, hclear3] at rd1688
  obtain ⟨k1689, C1689, rd1689raw⟩ := rd1688.sstore hperm (by decide +native) (by evm_ov)
  have rd1689 : RD flipperBytecode I g s0 ⟨1689⟩
      (UInt256.lnot solcAddrMask :: base :: ⟨0⟩ :: ⟨323⟩ :: sel :: [])
      memHash (UInt256.ofNat 9) out (cA, σ3) k1689 C1689 := by
    simpa [σ3, clear3] using rd1689raw
  have rd1693 := evm_run rd1689 with [
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  obtain ⟨k1695, C1695, rd1695raw⟩ := rd1693.sload (by decide +native) (by evm_ov)
  have rd1695 : RD flipperBytecode I g s0 ⟨1695⟩
      (old4 :: (base + ⟨4⟩) :: UInt256.lnot solcAddrMask :: base :: ⟨0⟩ ::
        ⟨323⟩ :: sel :: [])
      memHash (UInt256.ofNat 9) out (cA, σ3) k1695 C1695 := by
    simpa [old4, solcSlotWord] using rd1695raw
  have rd1699 := evm_run rd1695 with [
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  rw [hclear4] at rd1699
  obtain ⟨k1700, C1700, rd1700raw⟩ := rd1699.sstore hperm (by decide +native) (by evm_ov)
  have rd1700 : RD flipperBytecode I g s0 ⟨1700⟩
      (base :: ⟨0⟩ :: ⟨323⟩ :: sel :: [])
      memHash (UInt256.ofNat 9) out (cA, σ4) k1700 C1700 := by
    simpa [σ4, clear4] using rd1700raw
  have rd1703 := evm_run rd1700 with [
    raw push1 ⟨5⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  have hbase5 : (⟨5⟩ : UInt256) + base = base + ⟨5⟩ := u256_add_comm _ _
  rw [hbase5] at rd1703
  obtain ⟨k1704, C1704, rd1704raw⟩ := rd1703.sstore hperm (by decide +native) (by evm_ov)
  have rd1704 : RD flipperBytecode I g s0 ⟨1704⟩
      (⟨323⟩ :: sel :: []) memHash (UInt256.ofNat 9) out
      (cA, dealBidDeleteAccountMap I σ id) k1704 C1704 := by
    simpa [dealBidDeleteAccountMap, bidDeleteCollapsedAccountMap, base, σ0, σ1, σ2, σ3, σ4,
      old3, old4, clear3, clear4, solcSlotWord] using rd1704raw
  have rd323 := rd1704.jump (by decide +native) (by jump_dest) (by evm_ov)
  have rd324 := rd323.jumpdest (by decide +native) (by evm_ov)
  exact RD.stop rd324 (by decide +native) (by evm_ov)

theorem flipperDealX_vatDeleteReturnFromPostCall {cA gh bl σmem σcall σ σ₀ A I}
    {g : UInt256} {cA' : Batteries.RBSet AccountAddress compare} {k C : ℕ}
    {out : ByteArray} (hperm : I.perm = true)
    (h : RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σmem σ₀ (Sat256.ofUInt256 g) A I) ⟨1633⟩
      (⟨260⟩ :: ⟨1628552750⟩ :: flipperVatTargetWord σcall I ::
        dealId I :: ⟨323⟩ :: flipperSelWord I :: [])
      (dealVatFluxCallMem σmem σcall I) (UInt256.ofNat 9) out (cA', σ) k C) :
    RDret flipperBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σmem σ₀ (Sat256.ofUInt256 g) A I)
      (cA', dealBidDeleteAccountMap I σ (dealId I)) ByteArray.empty :=
  flipperDealX_vatDeleteReturn
    (selector := ⟨1628552750⟩) (target := flipperVatTargetWord σcall I)
    (id := dealId I) (sel := flipperSelWord I) hperm h

end Benchmarks.Dss.Flipper
