import Benchmarks.Dss.End.Trusted

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

/-! ## `pack(uint256)` -/

abbrev packWadWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev packStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "wad" (.int (Int.ofNat (packWadWord I).toNat))

def packDebtWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord ⟨11⟩ σ I

def packVatWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord ⟨1⟩ σ I

def packVowWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord ⟨4⟩ σ I

abbrev packVatMaskedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (packVatWord σ I)

abbrev packVowMaskedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (packVowWord σ I)

abbrev packMoveSelectorWord : UInt256 :=
  ⟨3140843579⟩

abbrev packRayWord : UInt256 :=
  ⟨1000000000000000000000000000⟩

abbrev packAmtWord (I : ExecutionEnv) : UInt256 :=
  UInt256.mul (packWadWord I) packRayWord

abbrev packSourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev packBagStorageSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨16⟩ (packSourceWord I)

def packBagWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (packBagStorageSlot I) σ I

noncomputable def packBagHashMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  twoWordHashMem (packSourceWord I) ⟨16⟩ mem

abbrev packMoveSelectorShifted : UInt256 :=
  UInt256.shiftLeft packMoveSelectorWord ⟨224⟩

abbrev packMoveOutPtr : UInt256 := ⟨128⟩

abbrev packMoveInSize : UInt256 := ⟨100⟩

abbrev packMoveOutSize : UInt256 := ⟨0⟩

abbrev packMoveEndPtr : UInt256 := ⟨228⟩

noncomputable def packMoveSelectorMem (mem : ByteArray) : ByteArray :=
  packMoveSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def packMoveSourceMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (packSourceWord I).toByteArray.write 0 (packMoveSelectorMem mem) 132 32

noncomputable def packMoveVowMem (σ : AccountMap) (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  (packVowMaskedWord σ I).toByteArray.write 0 (packMoveSourceMem I mem) 164 32

noncomputable def packMoveCalldataMem (σ : AccountMap) (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  (packAmtWord I).toByteArray.write 0 (packMoveVowMem σ I mem) 196 32

theorem packMoveSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (packMoveSelectorMem mem).size = 160 := by
  unfold packMoveSelectorMem
  exact toByteArray_write32_size_of_ge mem packMoveSelectorShifted 128 96 160 hmem
    (by native_decide) (by native_decide) (by native_decide)

theorem packMoveSourceMem_size (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 96) :
    (packMoveSourceMem I mem).size = 164 := by
  unfold packMoveSourceMem
  exact toByteArray_write32_size_of_le (packMoveSelectorMem mem) (packSourceWord I) 132
    160 164 (packMoveSelectorMem_size hmem)
    (by rw [packMoveSelectorMem_size hmem]; native_decide) (by native_decide)

theorem packMoveVowMem_size (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (packMoveVowMem σ I mem).size = 196 := by
  unfold packMoveVowMem
  exact toByteArray_write32_size_of_le (packMoveSourceMem I mem) (packVowMaskedWord σ I) 164
    164 196 (packMoveSourceMem_size I hmem)
    (by rw [packMoveSourceMem_size I hmem]) (by native_decide)

theorem packMoveCalldataMem_size (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (packMoveCalldataMem σ I mem).size = 228 := by
  unfold packMoveCalldataMem
  exact toByteArray_write32_size_of_le (packMoveVowMem σ I mem) (packAmtWord I) 196
    196 228 (packMoveVowMem_size σ I hmem)
    (by rw [packMoveVowMem_size σ I hmem]) (by native_decide)

theorem packMoveSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (packMoveSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold packMoveSelectorMem
  rw [toByteArray_write_read_below_of_gap packMoveSelectorShifted mem 128 64
    (by rw [hmem]) (by omega) (by rw [hmem]; native_decide), hread64]

theorem packMoveSourceMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (packMoveSourceMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold packMoveSourceMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [packMoveSelectorMem_size hmem]; omega) (by omega),
    packMoveSelectorMem_read64 hmem hread64]

theorem packMoveVowMem_read64 (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (packMoveVowMem σ I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold packMoveVowMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [packMoveSourceMem_size I hmem]) (by omega),
    packMoveSourceMem_read64 I hmem hread64]

theorem packMoveCalldataMem_read64 (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (packMoveCalldataMem σ I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold packMoveCalldataMem
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
    (by rw [packMoveVowMem_size σ I hmem]) (by omega),
    packMoveVowMem_read64 σ I hmem hread64]

theorem packMoveCalldataMem_read128_4 (σ : AccountMap) (I : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (packMoveCalldataMem σ I mem).readWithPadding 128 4 = moveSelector := by
  have hSelectorSize := packMoveSelectorMem_size hmem
  have hSourceSize := packMoveSourceMem_size I hmem
  have hVowSize := packMoveVowMem_size σ I hmem
  unfold packMoveCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (packAmtWord I)
      (packMoveVowMem σ I mem) 196 128 4
      (by rw [hVowSize]; omega)
      (by omega) (by omega) (by omega)
      (by rw [hVowSize]; native_decide)]
  unfold packMoveVowMem
  rw [toByteArray_write_read_below_len_of_gap (packVowMaskedWord σ I)
      (packMoveSourceMem I mem) 164 128 4
      (by rw [hSourceSize]; omega)
      (by omega) (by omega) (by omega)
      (by rw [hSourceSize]; native_decide)]
  unfold packMoveSourceMem
  rw [toByteArray_write_read_below_len_of_gap (packSourceWord I)
      (packMoveSelectorMem mem) 132 128 4
      (by rw [hSelectorSize]; omega)
      (by omega) (by omega) (by omega)
      (by rw [hSelectorSize]; native_decide)]
  unfold packMoveSelectorMem
  rw [toByteArray_write_read_window_of_gap packMoveSelectorShifted mem 128 0 4
      (by omega) (by omega) (by omega)
      (by rw [hmem]; native_decide)]
  native_decide

theorem packMoveCalldataMem_read132_32 (σ : AccountMap) (I : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (packMoveCalldataMem σ I mem).readWithPadding 132 32 =
      (packSourceWord I).toByteArray := by
  have hSourceSize := packMoveSourceMem_size I hmem
  have hVowSize := packMoveVowMem_size σ I hmem
  unfold packMoveCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (packAmtWord I)
      (packMoveVowMem σ I mem) 196 132 32
      (by rw [hVowSize]; omega)
      (by omega) (by omega) (by omega)
      (by rw [hVowSize]; native_decide)]
  unfold packMoveVowMem
  rw [toByteArray_write_read_below_len_of_gap (packVowMaskedWord σ I)
      (packMoveSourceMem I mem) 164 132 32
      (by rw [hSourceSize])
      (by omega) (by omega) (by omega)
      (by rw [hSourceSize]; native_decide)]
  unfold packMoveSourceMem
  rw [toByteArray_write_read_back_of_gap (packSourceWord I) (packMoveSelectorMem mem) 132
      (by rw [packMoveSelectorMem_size hmem]; native_decide)]

theorem packMoveCalldataMem_read164_32 (σ : AccountMap) (I : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (packMoveCalldataMem σ I mem).readWithPadding 164 32 =
      (packVowMaskedWord σ I).toByteArray := by
  have hVowSize := packMoveVowMem_size σ I hmem
  unfold packMoveCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (packAmtWord I)
      (packMoveVowMem σ I mem) 196 164 32
      (by rw [hVowSize])
      (by omega) (by omega) (by omega)
      (by rw [hVowSize]; native_decide)]
  unfold packMoveVowMem
  rw [toByteArray_write_read_back_of_gap (packVowMaskedWord σ I) (packMoveSourceMem I mem) 164
      (by rw [packMoveSourceMem_size I hmem]; native_decide)]

theorem packMoveCalldataMem_read196_32 (σ : AccountMap) (I : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (packMoveCalldataMem σ I mem).readWithPadding 196 32 =
      (packAmtWord I).toByteArray := by
  unfold packMoveCalldataMem
  rw [toByteArray_write_read_back_of_gap (packAmtWord I) (packMoveVowMem σ I mem) 196
      (by rw [packMoveVowMem_size σ I hmem]; native_decide)]

theorem packMoveCalldataMem_read128_100 (σ : AccountMap) (I : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (packMoveCalldataMem σ I mem).readWithPadding 128 100 =
      moveSelector ++ (packSourceWord I).toByteArray ++ (packVowMaskedWord σ I).toByteArray ++
        (packAmtWord I).toByteArray := by
  have hsize : (packMoveCalldataMem σ I mem).size = 228 :=
    packMoveCalldataMem_size σ I hmem
  rw [show 100 = 4 + 96 from rfl,
    byteArray_readWithPadding_split (packMoveCalldataMem σ I mem) 128 4 96
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split (packMoveCalldataMem σ I mem) 132 32 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (packMoveCalldataMem σ I mem) 164 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [packMoveCalldataMem_read128_4 σ I hmem, packMoveCalldataMem_read132_32 σ I hmem,
    packMoveCalldataMem_read164_32 σ I hmem, packMoveCalldataMem_read196_32 σ I hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem packVowAddressWord (σ : AccountMap) (I : ExecutionEnv) :
    EVM.word ↑(AccountAddress.ofUInt256 (packVowMaskedWord σ I)) =
      packVowMaskedWord σ I := by
  have hcanon : (packVowMaskedWord σ I).toNat < EVM.addressModulus := by
    simpa [packVowMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (packVowWord σ I)
  have hcanonVal : ↑(packVowMaskedWord σ I).val < EVM.addressModulus := by
    simpa [UInt256.toNat] using hcanon
  apply u256_inj
  simp only [EVM.word, EVM.uintN, UInt256.toNat, AccountAddress.ofUInt256, Fin.ofNat]
  rw [show AccountAddress.size = EVM.addressModulus from by decide]
  rw [Nat.mod_eq_of_lt hcanonVal]
  rw [Nat.mod_eq_of_lt hcanonVal]
  rw [Nat.mod_eq_of_lt (lt_trans hcanonVal (by decide))]

theorem packBagHashMem_size {mem : ByteArray} (I : ExecutionEnv) (hmem : mem.size = 228) :
    (packBagHashMem I mem).size = 228 := by
  unfold packBagHashMem twoWordHashMem wordAt32Mem wordAt0Mem
  have h0 :
      ((packSourceWord I).toByteArray.write 0 mem 0 32).size = 228 :=
    toByteArray_write32_size_of_le mem (packSourceWord I) 0 228 228 hmem
      (by rw [hmem]; native_decide) (by native_decide)
  exact toByteArray_write32_size_of_le
    ((packSourceWord I).toByteArray.write 0 mem 0 32) (⟨16⟩ : UInt256) 32
    228 228 h0 (by rw [h0]; native_decide) (by native_decide)

theorem packBagHashMem_read0 (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 228) :
    (packBagHashMem I mem).readWithPadding 0 32 =
      (packSourceWord I).toByteArray := by
  unfold packBagHashMem twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by
        unfold wordAt0Mem
        rw [toByteArray_write32_size_of_le mem (packSourceWord I) 0 228 228 hmem
          (by rw [hmem]; native_decide) (by native_decide)]
        native_decide)
      (by omega)]
  exact wordAt0Mem_read0 (packSourceWord I) mem

theorem packBagHashMem_read32 (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 228) :
    (packBagHashMem I mem).readWithPadding 32 32 =
      (⟨16⟩ : UInt256).toByteArray := by
  unfold packBagHashMem twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by
        unfold wordAt0Mem
        rw [toByteArray_write32_size_of_le mem (packSourceWord I) 0 228 228 hmem
          (by rw [hmem]; native_decide) (by native_decide)]
        native_decide)]
  rw [toByteArray_extract_all]

theorem packBagHashMem_read0_64 (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 228) :
    (packBagHashMem I mem).readWithPadding 0 64 =
      (packSourceWord I).toByteArray ++ (⟨16⟩ : UInt256).toByteArray := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [packBagHashMem_size I hmem]; omega)]
  have hleft :
      (packBagHashMem I mem).extract 0 32 = (packSourceWord I).toByteArray := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [packBagHashMem_size I hmem]; omega),
      packBagHashMem_read0 I hmem]
  have hright :
      (packBagHashMem I mem).extract 32 64 = (⟨16⟩ : UInt256).toByteArray := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [packBagHashMem_size I hmem]; omega),
      packBagHashMem_read32 I hmem]
  rw [show (packBagHashMem I mem).extract 0 64 =
      (packBagHashMem I mem).extract 0 32 ++
        (packBagHashMem I mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem packBagHashMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (packBagHashMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold packBagHashMem twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by
        unfold wordAt0Mem
        rw [toByteArray_write32_size_of_le mem (packSourceWord I) 0 228 228 hmem
          (by rw [hmem]; native_decide) (by native_decide)]
        native_decide)
      (by native_decide)
      (by
        unfold wordAt0Mem
        rw [toByteArray_write32_size_of_le mem (packSourceWord I) 0 228 228 hmem
          (by rw [hmem]; native_decide) (by native_decide)]
        native_decide)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by native_decide) (by rw [hmem]; native_decide)]
  exact hread64

noncomputable def packBagLogMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (packWadWord I).toByteArray.write 0 (packBagHashMem I (packBagHashMem I mem)) 128 32

theorem packBagLogMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (packBagLogMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold packBagLogMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [packBagHashMem_size I (packBagHashMem_size I hmem)]; native_decide)
    (by native_decide)]
  exact packBagHashMem_read64 I (packBagHashMem_size I hmem)
    (packBagHashMem_read64 I hmem hread64)

theorem RD.endPackMoveExtcodesizeGuard
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨6462⟩
      (packAmtWord I :: packVowMaskedWord σ I :: packSourceWord I ::
        packMoveSelectorWord :: packVatMaskedWord σ I :: packWadWord I :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨6536⟩
      (packVatMaskedWord σ I :: packVatMaskedWord σ I :: ⟨0⟩ ::
        packMoveOutPtr :: packMoveInSize :: packMoveOutPtr :: packMoveOutSize ::
        packMoveEndPtr :: packMoveSelectorWord :: packVatMaskedWord σ I ::
        packWadWord I :: ⟨562⟩ :: [sel])
      (packMoveCalldataMem σ I solcFreePtrMem)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ) k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ solcFreePtrMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (solcFreePtrMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [solcFreePtrMem_size]; decide) (by decide) solcFreePtrMem_read64
  have hCallMemSize : (packMoveCalldataMem σ I solcFreePtrMem).size = 228 :=
    packMoveCalldataMem_size σ I solcFreePtrMem_size
  have hCallRead64 :
      (packMoveCalldataMem σ I solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    packMoveCalldataMem_read64 σ I solcFreePtrMem_size solcFreePtrMem_read64
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (packMoveCalldataMem σ I solcFreePtrMem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((packMoveCalldataMem σ I solcFreePtrMem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hCallMemSize]; decide) (by decide) hCallRead64
  have hsourceCanon : (packSourceWord I).toNat < EVM.addressModulus := by
    change I.source.val % UInt256.size < EVM.addressModulus
    rw [Nat.mod_eq_of_lt (lt_trans I.source.isLt (by native_decide))]
    change (↑I.source : ℕ) < AccountAddress.size
    exact I.source.isLt
  have hsourceMask :
      UInt256.land solcAddrMask (packSourceWord I) = packSourceWord I :=
    solcAddrMask_clean_left hsourceCanon
  have hvowCanon : (packVowMaskedWord σ I).toNat < EVM.addressModulus := by
    simpa [packVowMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (packVowWord σ I)
  have hvowMask :
      UInt256.land solcAddrMask (packVowMaskedWord σ I) = packVowMaskedWord σ I :=
    solcAddrMask_clean_left hvowCanon
  have rd6536 := evm_run rd with [
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
    raw mstore 6 (packMoveSelectorMem solcFreePtrMem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
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
    raw mstore 3 (packMoveSourceMem I solcFreePtrMem) (UInt256.ofNat 6)
      (by native_decide) mem_cost
      (by
        simp [packMoveSourceMem, hsourceMask,
          show ({ val := 4 } + { val := 128 } : UInt256).toNat = 132 from by native_decide,
          show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask from by decide])
      (by native_decide) (by evm_ov),
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
    raw mstore 3 (packMoveVowMem σ I solcFreePtrMem) (UInt256.ofNat 7)
      (by native_decide) mem_cost
      (by
        simp [packMoveVowMem, hvowMask,
          show ({ val := 32 } + ({ val := 4 } + { val := 128 }) : UInt256).toNat = 164
            from by native_decide,
          show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask from by decide])
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩,
    add,
    dup3,
    dup2,
    raw mstore 3 (packMoveCalldataMem σ I solcFreePtrMem) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
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
      mem_cost hmload64Call
      (by decide) (by evm_ov),
    dup1,
    dup4,
    sub,
    dup2,
    push1 ⟨0⟩,
    dup8,
    dup1]
  exact ⟨_, _, by
    simpa [packMoveSelectorShifted, packMoveSelectorWord, packMoveSelectorMem,
      packMoveSourceMem, packMoveVowMem, packMoveCalldataMem, packMoveOutPtr,
      packMoveInSize, packMoveOutSize, packMoveEndPtr, solcAddrMask, u256_land_comm,
      hsourceMask, hvowMask,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide] using rd6536⟩

theorem RD.endPackMoveCall
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨6462⟩
      (packAmtWord I :: packVowMaskedWord σ I :: packSourceWord I ::
        packMoveSelectorWord :: packVatMaskedWord σ I :: packWadWord I :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (packVatMaskedWord σ I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g s0 ⟨6551⟩
      (gasWord :: packVatMaskedWord σ I :: ⟨0⟩ ::
        packMoveOutPtr :: packMoveInSize :: packMoveOutPtr :: packMoveOutSize ::
        packMoveEndPtr :: packMoveSelectorWord :: packVatMaskedWord σ I ::
        packWadWord I :: ⟨562⟩ :: [sel])
      (packMoveCalldataMem σ I solcFreePtrMem)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd6536⟩ := RD.endPackMoveExtcodesizeGuard rd
  obtain ⟨gasWord, k', C', rd6551⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨6536⟩) (okPc := ⟨6548⟩)
      rd6536 hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by evm_ov)
  exact ⟨gasWord, k', C', rd6551⟩

theorem RD.endPackMoveNoCode
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨6462⟩
      (packAmtWord I :: packVowMaskedWord σ I :: packSourceWord I ::
        packMoveSelectorWord :: packVatMaskedWord σ I :: packWadWord I :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (packVatMaskedWord σ I) = ⟨0⟩) :
    RDrev endBytecode g s0 := by
  obtain ⟨_, _, rd6536⟩ := RD.endPackMoveExtcodesizeGuard rd
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨6536⟩) (okPc := ⟨6548⟩)
    rd6536 hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.endPackMovePostCallRaw
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨6462⟩
      (packAmtWord I :: packVowMaskedWord σ I :: packSourceWord I ::
        packMoveSelectorWord :: packVatMaskedWord σ I :: packWadWord I :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (packVatMaskedWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (k' C' : ℕ),
      RD endBytecode I g s0 ⟨6552⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: packMoveEndPtr :: packMoveSelectorWord ::
          packVatMaskedWord σ I :: packWadWord I :: ⟨562⟩ :: [sel])
        (out.write 0 (packMoveCalldataMem σ I solcFreePtrMem) packMoveOutPtr.toNat
          (min packMoveOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 8) out (cA', σ') k' C'
    ∧ out.size < UInt256.size := by
  obtain ⟨_, _, _, rd6551⟩ := RD.endPackMoveCall rd hcodeSize
  obtain ⟨cA', σ', z, out, A_in, callGas, k6552, C6552, hΘpack, rd6552raw, houtsz⟩ :=
    RD.call rd6551 (by native_decide) hdepth (by evm_ov)
  obtain ⟨_, _, _⟩ := hΘpack
  refine ⟨cA', σ', z, out, k6552, C6552, ?_, houtsz⟩
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        packMoveOutPtr.toNat packMoveInSize.toNat)
        packMoveOutPtr.toNat packMoveOutSize.toNat) = UInt256.ofNat 8 := by
    unfold packMoveOutPtr packMoveInSize packMoveOutSize
    native_decide
  exact haw ▸ rd6552raw

theorem RD.endPackMoveCallFailure
    {cA σ I} {g : Sat256} {s0 : State} {mem o : ByteArray} {aw : UInt256}
    {k C : ℕ} {rest : List UInt256}
    (rd : RD endBytecode I g s0 ⟨6552⟩
      (⟨0⟩ :: rest) mem aw o (cA, σ) k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev endBytecode g s0 := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨6552⟩) (okPc := ⟨6568⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hosz hov

theorem RD.endPackMoveCallSuccessToBag
    {cA σ I} {g : Sat256} {s0 : State} {mem o : ByteArray} {aw : UInt256}
    {k C : ℕ} {d0 d1 d2 : UInt256} {R : List UInt256}
    (rd : RD endBytecode I g s0 ⟨6552⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: R) mem aw o (cA, σ) k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD endBytecode I g s0 ⟨6570⟩
      (d0 :: d1 :: d2 :: R) mem aw o (cA, σ) k' C' := by
  exact RD.uniswapCallSuccessGuardOk (pc := ⟨6552⟩) (okPc := ⟨6568⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simpa only [List.length_cons] using hov)

theorem RD.endPackLoadBagToAdd
    {cA σ I} {g : Sat256} {s0 : State} {mem o : ByteArray}
    {k C : ℕ} {sel vatWord : UInt256}
    (rd : RD endBytecode I g s0 ⟨6570⟩
      (packMoveEndPtr :: packMoveSelectorWord :: vatWord :: packWadWord I ::
        ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 8) o (cA, σ) k C)
    (hmem : mem.size = 228) :
    ∃ k' C', RD endBytecode I g s0 ⟨10092⟩
      (packWadWord I :: packBagWord σ I :: ⟨6599⟩ ::
        packWadWord I :: ⟨562⟩ :: [sel])
      (packBagHashMem I mem) (UInt256.ofNat 8) o (cA, σ) k' C' := by
  have hslot :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC ((packBagHashMem I mem).readWithPadding 0 64))) =
        packBagStorageSlot I := by
    rw [packBagHashMem_read0_64 I hmem]
    simpa [packBagStorageSlot, solcMappingSlot] using
      mappingSlot_single (packSourceWord I) (⟨16⟩ : UInt256)
  have rd6586 := evm_run rd with [
    raw pop (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (packSourceWord I) mem) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by
        simp [wordAt0Mem, packSourceWord])
      (by native_decide) (by evm_ov),
    raw push1 ⟨16⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (packBagHashMem I mem) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by
        simp [packBagHashMem, twoWordHashMem, wordAt32Mem,
          show (⟨32⟩ : UInt256).toNat = 32 from by native_decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd6586hash := rd6586.keccak256 0 (packBagStorageSlot I)
    (UInt256.ofNat 8) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨k6586, C6586, rd6586sload⟩ := rd6586hash.sload (by native_decide) (by evm_ov)
  have rd6587 : RD endBytecode I g s0 ⟨6587⟩
      (packBagWord σ I :: packMoveSelectorWord :: vatWord :: packWadWord I ::
        ⟨562⟩ :: [sel])
      (packBagHashMem I mem) (UInt256.ofNat 8) o (cA, σ) k6586 C6586 := by
    simpa [packBagWord, endSlotWord, packBagStorageSlot] using rd6586sload
  have rd10092 := evm_run rd6587 with [
    raw push2 ⟨6599⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨10092⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, rd10092.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem RD.endPackBagAddSuccess
    {cA σ I} {g : Sat256} {s0 : State} {mem o : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨10092⟩
      (packWadWord I :: packBagWord σ I :: ⟨6599⟩ ::
        packWadWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 8) o (cA, σ) k C)
    (hfit : (packBagWord σ I).toNat + (packWadWord I).toNat < UInt256.size) :
    ∃ k' C', RD endBytecode I g s0 ⟨6599⟩
      ((packBagWord σ I + packWadWord I) :: packWadWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 8) o (cA, σ) k' C' := by
  have haddNat :
      (packBagWord σ I + packWadWord I).toNat =
        (packBagWord σ I).toNat + (packWadWord I).toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hfit]
  have haddNat' :
      (packWadWord I + packBagWord σ I).toNat =
        (packWadWord I).toNat + (packBagWord σ I).toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt (by omega)]
  have hlt : UInt256.lt (packWadWord I + packBagWord σ I) (packBagWord σ I) = ⟨0⟩ :=
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
  have rd6599 := evm_run (rd10108raw.jumpdest (by native_decide) (by evm_ov)) with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by
    simpa [u256_add_comm (packWadWord I) (packBagWord σ I)] using rd6599⟩

set_option maxHeartbeats 3000000 in
theorem RD.endPackStoreBagAndReturn
    {cA σ I} {g : Sat256} {s0 : State} {mem o : ByteArray}
    {k C : ℕ} {sel bagNew : UInt256}
    (rd : RD endBytecode I g s0 ⟨6599⟩
      (bagNew :: packWadWord I :: ⟨562⟩ :: [sel])
      (packBagHashMem I mem) (UInt256.ofNat 8) o (cA, σ) k C)
    (hperm : I.perm = true)
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDret endBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ (packBagStorageSlot I) bagNew)
      ByteArray.empty := by
  have hbaseSize : (packBagHashMem I mem).size = 228 := packBagHashMem_size I hmem
  have hhashSize : (packBagHashMem I (packBagHashMem I mem)).size = 228 :=
    packBagHashMem_size I hbaseSize
  have hhashRead64 :
      (packBagHashMem I (packBagHashMem I mem)).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    packBagHashMem_read64 I hbaseSize (packBagHashMem_read64 I hmem hread64)
  have hlogRead64 :
      (packBagLogMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
    packBagLogMem_read64 I hmem hread64
  have hslot :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC ((packBagHashMem I (packBagHashMem I mem)).readWithPadding 0 64))) =
        packBagStorageSlot I := by
    rw [packBagHashMem_read0_64 I hbaseSize]
    simpa [packBagStorageSlot, solcMappingSlot] using
      mappingSlot_single (packSourceWord I) (⟨16⟩ : UInt256)
  have rd6618pre := evm_run rd with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (packSourceWord I) (packBagHashMem I mem))
      (UInt256.ofNat 8) (by native_decide) mem_cost (by
        simp [wordAt0Mem, packSourceWord])
      (by native_decide) (by evm_ov),
    raw push1 ⟨16⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (packBagHashMem I (packBagHashMem I mem))
      (UInt256.ofNat 8) (by native_decide) mem_cost (by
        simp [packBagHashMem, twoWordHashMem, wordAt32Mem,
          show (⟨32⟩ : UInt256).toNat = 32 from by native_decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd6618 := rd6618pre.keccak256 0 (packBagStorageSlot I)
    (UInt256.ofNat 8) (by native_decide) mem_cost hslot (by native_decide)
    (by evm_ov)
  have rd6621pre := evm_run rd6618 with [
    raw swap4 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov)]
  obtain ⟨k6623, C6623, rd6623raw⟩ := rd6621pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6624pre := RD.dup1 rd6623raw (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6625 := RD.mload 0 ⟨128⟩ (UInt256.ofNat 8) rd6624pre
    (by native_decide) mem_cost
    (mloadFreePtrValue (by rw [hhashSize]; native_decide) (by native_decide)
      hhashRead64)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6629pre := evm_run rd6625 with [
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (packBagLogMem I mem) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd6630 := RD.mload 0 ⟨128⟩ (UInt256.ofNat 8) rd6629pre
    (by native_decide) mem_cost
    (mloadFreePtrValue (by
      unfold packBagLogMem
      rw [toByteArray_write32_size_of_le (packBagHashMem I (packBagHashMem I mem))
        (packWadWord I) 128 228 228 hhashSize (by rw [hhashSize]; native_decide)
        (by native_decide)]
      native_decide) (by native_decide) hlogRead64)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6632pre := evm_run rd6630 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  have rd6665 := rd6632pre.pushConst
    (⟨32413705573444452749964784915662512924629124419856669116056918598247152483852⟩ :
      UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd6672pre := evm_run rd6665 with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hlogLen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨32⟩ = ⟨32⟩ := by
    native_decide
  have rd6673 := RD.log2
    (a := ⟨128⟩) (b := ⟨32⟩)
    (c := ⟨32413705573444452749964784915662512924629124419856669116056918598247152483852⟩)
    (d := packSourceWord I) (t := [packWadWord I, ⟨562⟩, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 8).toNat (⟨128⟩ : UInt256).toNat
        (⟨32⟩ : UInt256).toNat))
    (by simpa [packSourceWord, hlogLen] using rd6672pre)
    (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6674pre := RD.pop (a := packWadWord I) (t := [⟨562⟩, sel]) rd6673
    (by native_decide) (by evm_ov)
  have rd562 := RD.jump (a := ⟨562⟩) (t := [sel]) rd6674pre
    (by native_decide) (by jump_dest) (by evm_ov)
  have rd563 := RD.jumpdest (pc := ⟨562⟩) (stk := [sel]) rd562
    (by native_decide) (by evm_ov)
  exact RD.stop rd563 (by native_decide) (by evm_ov)

theorem evalExpr_packVatStorage (evm : EVM.State) {locals : Store}
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

theorem evalExpr_packVatCodeGuard_false {evm : EVM.State} {locals : Store}
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

theorem evalExpr_packVarUInt256 {evm : EVM.State} {locals : Store}
    {name : Ident} {value : UInt256}
    (h : locals.get? name = some (.int (Int.ofNat value.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat value.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) =
    .ok (.int (Int.ofNat value.toNat))
  rw [h]
  rfl

theorem evalExpr_packDivUInt256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b q : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hb : b ≠ ⟨0⟩)
    (hq : q = UInt256.div a b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .div x y) =
      .ok (.int (Int.ofNat q.toNat)) := by
  have hbNat : ¬ b.toNat = 0 := by
    intro hzero
    exact hb (uint256_toNat_eq_zero hzero)
  have hqNat : q.toNat = a.toNat / b.toNat := by
    rw [hq, udiv_toNat]
  simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, hbNat, hqNat]

theorem evalExpr_packEqInt_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a = b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .eq lhs rhs) =
      .ok (.bool true) := by
  subst h
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]

theorem evalExpr_packEqInt_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a ≠ b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .eq lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem evalExpr_packOr_false_right {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {b : Bool}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool false))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.bool b)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool b) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs, hrhs]

theorem evalExpr_pack_debt_false (evm : EVM.State) (I : ExecutionEnv)
    (hdebt :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := packStore I } evm
      (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := packStore I } evm
        (.storage debtRef) = .ok (.int 0) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := packStore I })
      (slot := debtRef)
      (er := ({ base := "debt", steps := [] } : EvaledStorageRef))
      (t := .int uint256Int)
      (loc := wordLoc ⟨11⟩)
      (value := .int 0)
      (hbase := by simp [packStore, debtRef])
      (her := by simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simp [endStorageLocLoad_uint256 evm ⟨11⟩, hdebt])]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?]
  native_decide

theorem endPackSourceBodyDebtZeroReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hdebt : packDebtWord σ I = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (packStore I) packTransition.body .reverted := by
  intro evm0
  refine ExecFuncBody.execBlockRevert ?_
  simpa [packTransition, nonpayable, packDebtWord, endSlotWord, initState,
    Solm.EVM.storageLoad, State.lookupAccount] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := packStore I })
      (evm := evm0)
      (guard := .binary .ne (.storage debtRef) (.intLit 0))
      (rest := [ .internalCall "mul" [.var "wad", .intLit RAY] "amt" ] ++
        checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, vowAddr, .var "amt"] "_move" ++
        [ .internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew",
          .assign .storage (bagRef sender) (.var "bagNew") ])
      (by simp [evm0, initState]; exact hwv)
      (evalExpr_pack_debt_false evm0 I (by
        simpa [evm0, packDebtWord, endSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hdebt))

abbrev packMulLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "y" (.int (Int.ofNat packRayWord.toNat))).insert "x"
    (.int (Int.ofNat (packWadWord I).toNat))

theorem packMulLocals_get_x (I : ExecutionEnv) :
    (packMulLocals I).get? "x" = some (.int (Int.ofNat (packWadWord I).toNat)) := by
  unfold packMulLocals
  simp

theorem packMulLocals_get_y (I : ExecutionEnv) :
    (packMulLocals I).get? "y" = some (.int (Int.ofNat packRayWord.toNat)) := by
  unfold packMulLocals
  rw [store_get_ne]
  · simp
  · native_decide

abbrev packMulLocalsZ (I : ExecutionEnv) (z : UInt256) : Store :=
  (packMulLocals I).insert "z" (.int (Int.ofNat z.toNat))

abbrev packStoreAmt (I : ExecutionEnv) : Store :=
  (packStore I).insert "amt" (.int (Int.ofNat (packAmtWord I).toNat))

abbrev packAddLocals (x y : UInt256) : Store :=
  (((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x"
    (.int (Int.ofNat x.toNat)))

abbrev packAddLocalsZ (x y z : UInt256) : Store :=
  (packAddLocals x y).insert "z" (.int (Int.ofNat z.toNat))

abbrev packStoreAmtBagNew (I : ExecutionEnv) (bagNew : UInt256) : Store :=
  (packStoreAmt I).insert "bagNew" (.int (Int.ofNat bagNew.toNat))

theorem packMulLocalsZ_get_x (I : ExecutionEnv) (z : UInt256) :
    (packMulLocalsZ I z).get? "x" = some (.int (Int.ofNat (packWadWord I).toNat)) := by
  unfold packMulLocalsZ
  rw [store_get_ne]
  · exact packMulLocals_get_x I
  · native_decide

theorem packMulLocalsZ_get_y (I : ExecutionEnv) (z : UInt256) :
    (packMulLocalsZ I z).get? "y" = some (.int (Int.ofNat packRayWord.toNat)) := by
  unfold packMulLocalsZ
  rw [store_get_ne]
  · exact packMulLocals_get_y I
  · native_decide

theorem packMulLocalsZ_get_z (I : ExecutionEnv) (z : UInt256) :
    (packMulLocalsZ I z).get? "z" = some (.int (Int.ofNat z.toNat)) := by
  unfold packMulLocalsZ
  simp

theorem packAddLocals_get_x (x y : UInt256) :
    (packAddLocals x y).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  unfold packAddLocals
  simp

theorem packAddLocals_get_y (x y : UInt256) :
    (packAddLocals x y).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  unfold packAddLocals
  rw [store_get_ne]
  · simp
  · native_decide

theorem packAddLocalsZ_get_x (x y z : UInt256) :
    (packAddLocalsZ x y z).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  unfold packAddLocalsZ
  rw [store_get_ne]
  · exact packAddLocals_get_x x y
  · native_decide

theorem packAddLocalsZ_get_z (x y z : UInt256) :
    (packAddLocalsZ x y z).get? "z" = some (.int (Int.ofNat z.toNat)) := by
  unfold packAddLocalsZ
  simp

theorem packStoreAmtBagNew_get_bagNew (I : ExecutionEnv) (bagNew : UInt256) :
    (packStoreAmtBagNew I bagNew).get? "bagNew" =
      some (.int (Int.ofNat bagNew.toNat)) := by
  unfold packStoreAmtBagNew
  simp

theorem evalExpr_pack_mul_ok (evm : EVM.State) (I : ExecutionEnv)
    (hmul : (packWadWord I).toNat * packRayWord.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := packMulLocals I } evm
      (u256 (.binary .mul (.var "x") (.var "y"))) =
        .ok (.int (Int.ofNat (packAmtWord I).toNat)) := by
  have hx :
      evalExpr? config { contract := contract, locals := packMulLocals I } evm (.var "x") =
        .ok (.int (Int.ofNat (packWadWord I).toNat)) := by
    simpa using evalExpr_packVarUInt256 (evm := evm) (locals := packMulLocals I)
      (name := "x") (value := packWadWord I) (packMulLocals_get_x I)
  have hy :
      evalExpr? config { contract := contract, locals := packMulLocals I } evm (.var "y") =
        .ok (.int (Int.ofNat packRayWord.toNat)) := by
    simpa using evalExpr_packVarUInt256 (evm := evm) (locals := packMulLocals I)
      (name := "y") (value := packRayWord) (packMulLocals_get_y I)
  have hlt : ¬ Int.ofNat ((packWadWord I).toNat * packRayWord.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hmul))
  have hword :
      (packAmtWord I).toNat = (packWadWord I).toNat * packRayWord.toNat := by
    rw [packAmtWord, u256_mul_toNat, Nat.mod_eq_of_lt hmul]
  simp [u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem packAmt_div_ray_ok (I : ExecutionEnv)
    (hmul : (packWadWord I).toNat * packRayWord.toNat < UInt256.size) :
    UInt256.div (packAmtWord I) packRayWord = packWadWord I := by
  apply u256_inj
  rw [udiv_toNat, packAmtWord, u256_mul_toNat, Nat.mod_eq_of_lt hmul]
  have hray : packRayWord.toNat = 1000000000000000000000000000 := by rfl
  rw [Nat.mul_comm (packWadWord I).toNat packRayWord.toNat]
  rw [hray]
  exact Nat.mul_div_right _ (by norm_num : 0 < 1000000000000000000000000000)

theorem evalExpr_pack_mul_overflow (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ (packWadWord I).toNat * packRayWord.toNat) :
    evalExpr? config { contract := contract, locals := packMulLocals I } evm
      (u256 (.binary .mul (.var "x") (.var "y"))) = .revert := by
  unfold u256
  simp only [evalExpr?, packMulLocals_get_x, packMulLocals_get_y, EvalResult.bind, bind,
    EvalResult.ofOption, pure, evalBinaryOp?, uint256Int]
  have hge :
      Int.ofNat (packWadWord I).toNat * Int.ofNat packRayWord.toNat ≥ 2 ^ (256 : Nat) := by
    have hgeNat : 2 ^ (256 : Nat) ≤ (packWadWord I).toNat * packRayWord.toNat := by
      simpa [UInt256.size] using hover
    have hgeInt :
        (2 ^ (256 : Nat) : Int) ≤
          ((packWadWord I).toNat * packRayWord.toNat : Int) := by
      exact_mod_cast hgeNat
    simpa [Nat.cast_mul, Nat.cast_pow] using hgeInt
  have hcond :
      (decide (Int.ofNat (packWadWord I).toNat * Int.ofNat packRayWord.toNat < 0) ||
        decide (Int.ofNat (packWadWord I).toNat * Int.ofNat packRayWord.toNat ≥
          2 ^ (256 : Nat))) = true := by
    rw [Bool.or_eq_true]
    exact Or.inr (decide_eq_true hge)
  rw [hcond]
  rfl

theorem packMulFunctionBodyReverts (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ (packWadWord I).toNat * packRayWord.toNat) :
    ExecFuncBody config { contract := contract, locals := packMulLocals I } evm
      mulFunction.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consRevert <|
      ExecStmt.letDeclRevert (evalExpr_pack_mul_overflow evm I hover)

theorem packMulFunctionBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hmul : (packWadWord I).toNat * packRayWord.toNat < UInt256.size) :
    ExecFuncBody config { contract := contract, locals := packMulLocals I } evm
      mulFunction.body
      (.returned { contract := contract, locals := packMulLocalsZ I (packAmtWord I) } evm
        (some [.int (Int.ofNat (packAmtWord I).toNat)])) := by
  let locals := packMulLocals I
  let localsZ := packMulLocalsZ I (packAmtWord I)
  have hMul :
      evalExpr? config { contract := contract, locals := locals } evm
        (u256 (.binary .mul (.var "x") (.var "y"))) =
          .ok (.int (Int.ofNat (packAmtWord I).toNat)) := by
    simpa [locals] using evalExpr_pack_mul_ok evm I hmul
  have hxZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat (packWadWord I).toNat)) := by
    simpa [localsZ] using evalExpr_packVarUInt256 (evm := evm) (locals := localsZ)
      (name := "x") (value := packWadWord I) (packMulLocalsZ_get_x I (packAmtWord I))
  have hyZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "y") =
        .ok (.int (Int.ofNat packRayWord.toNat)) := by
    simpa [localsZ] using evalExpr_packVarUInt256 (evm := evm) (locals := localsZ)
      (name := "y") (value := packRayWord) (packMulLocalsZ_get_y I (packAmtWord I))
  have hzZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat (packAmtWord I).toNat)) := by
    simpa [localsZ] using evalExpr_packVarUInt256 (evm := evm) (locals := localsZ)
      (name := "z") (value := packAmtWord I) (packMulLocalsZ_get_z I (packAmtWord I))
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
      exact (by native_decide : packRayWord ≠ ⟨0⟩)
        (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
    have hdivWord : UInt256.div (packAmtWord I) packRayWord = packWadWord I :=
      packAmt_div_ray_ok I hmul
    have hDiv :
        evalExpr? config { contract := contract, locals := localsZ } evm
          (.binary .div (.var "z") (.var "y")) =
            .ok (.int (Int.ofNat (packWadWord I).toNat)) := by
      have h := evalExpr_packDivUInt256_ok (evm := evm) (locals := localsZ)
        (x := .var "z") (y := .var "y") (a := packAmtWord I) (b := packRayWord)
        (q := UInt256.div (packAmtWord I) packRayWord) hzZ hyZ
        (by native_decide : packRayWord ≠ ⟨0⟩) rfl
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
          (some [.int (Int.ofNat (packAmtWord I).toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hMul) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzZ))
  simpa [mulFunction, locals, localsZ] using ExecFuncBody.execBlockRet hblock

theorem evalExpr_pack_ge_uint256_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hge : b.toNat ≤ a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ge lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hge

theorem evalExpr_pack_add_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b sum : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hsum : sum = a + b)
    (hfit : a.toNat + b.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm
      (u256 (.binary .add x y)) = .ok (.int (Int.ofNat sum.toNat)) := by
  have hlt : ¬ Int.ofNat (a.toNat + b.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hword : sum.toNat = a.toNat + b.toNat := by
    rw [hsum, uadd_toNat, Nat.mod_eq_of_lt hfit]
  simp [u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem packAddFunctionBodyReturns (evm : EVM.State) {x y sum : UInt256}
    (hsum : sum = x + y) (hfit : x.toNat + y.toNat < UInt256.size) :
    ExecFuncBody config { contract := contract, locals := packAddLocals x y } evm
      addFunction.body
      (.returned { contract := contract, locals := packAddLocalsZ x y sum } evm
        (some [.int (Int.ofNat sum.toNat)])) := by
  let locals := packAddLocals x y
  let localsZ := packAddLocalsZ x y sum
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
  have hAdd :
      evalExpr? config { contract := contract, locals := locals } evm
        (u256 (.binary .add (.var "x") (.var "y"))) =
          .ok (.int (Int.ofNat sum.toNat)) :=
    evalExpr_pack_add_ok hx hy hsum hfit
  have hz :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat sum.toNat)) := by
    simpa [localsZ] using evalExpr_packVarUInt256 (evm := evm) (locals := localsZ)
      (name := "z") (value := sum) (packAddLocalsZ_get_z x y sum)
  have hxZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [localsZ] using evalExpr_packVarUInt256 (evm := evm) (locals := localsZ)
      (name := "x") (value := x) (packAddLocalsZ_get_x x y sum)
  have hsumNat : sum.toNat = x.toNat + y.toNat := by
    rw [hsum, uadd_toNat, Nat.mod_eq_of_lt hfit]
  have hReq :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .ge (.var "z") (.var "x")) = .ok (.bool true) :=
    evalExpr_pack_ge_uint256_true hz hxZ (by rw [hsumNat]; omega)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm addFunction.body
        (.returned { contract := contract, locals := localsZ } evm
          (some [.int (Int.ofNat sum.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hAdd) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hz))
  simpa [addFunction, locals, localsZ] using ExecFuncBody.execBlockRet hblock

theorem evalExpr_packBagStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "bag" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage (bagRef sender)) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (packBagStorageSlot evm.executionEnv)).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := bagRef sender)
    (er := ({ base := "bag", steps := [.mindex (.address evm.executionEnv.source)] } :
      EvaledStorageRef))
    (t := .int uint256Int)
    (loc := wordLoc (packBagStorageSlot evm.executionEnv))
    (value := .int (Int.ofNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (packBagStorageSlot evm.executionEnv)).toNat))
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
        some (wordLoc (packBagStorageSlot evm.executionEnv))
      simp [storageLayoutRaw, bagSlot, mapSlot, packBagStorageSlot, solcMappingSlot,
        packSourceWord, keyValueToWord_address])
    (hload := by
      simpa [wordLoc, uint256Loc, uint256Int] using
        storageLocLoad_uint256 evm (packBagStorageSlot evm.executionEnv))]

theorem assign_packBagStorage (evm : EVM.State) {locals : Store}
    (bagNew : UInt256) (hbase : locals.get? "bag" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (bagRef sender) (.int (Int.ofNat bagNew.toNat)) =
        .ok ({ contract := contract, locals := locals },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (packBagStorageSlot evm.executionEnv) bagNew) := by
  exact assignStorageRef_storage_scalar
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (packBagStorageSlot evm.executionEnv) bagNew)
    (slot := bagRef sender)
    (er := ({ base := "bag", steps := [.mindex (.address evm.executionEnv.source)] } :
      EvaledStorageRef))
    (ty := .elem (.int uint256Int))
    (loc := wordLoc (packBagStorageSlot evm.executionEnv))
    (n := Int.ofNat bagNew.toNat)
    hbase
    (by
      simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bagRef, sender,
        envValue, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?])
    (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (by
      funext x
      change storageLayoutRaw
          { base := "bag", steps := [.mindex (.address evm.executionEnv.source)] } x =
        some (wordLoc (packBagStorageSlot evm.executionEnv))
      simp [storageLayoutRaw, bagSlot, mapSlot, packBagStorageSlot, solcMappingSlot,
        packSourceWord, keyValueToWord_address])
    (storageLocStore_uint256 evm (packBagStorageSlot evm.executionEnv) bagNew)

theorem endPackSourceBodyMulOverflowReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hdebt : packDebtWord σ I ≠ ⟨0⟩)
    (hover : UInt256.size ≤ (packWadWord I).toNat * packRayWord.toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (packStore I) packTransition.body .reverted := by
  intro evm0
  have hdebtGuard :
      evalExpr? config { contract := contract, locals := packStore I } evm0
        (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := packStore I } evm0
          (.storage debtRef) =
          .ok (.int (Int.ofNat (packDebtWord σ I).toNat)) := by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := packStore I })
        (slot := debtRef)
        (er := ({ base := "debt", steps := [] } : EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc ⟨11⟩)
        (value := .int (Int.ofNat (packDebtWord σ I).toNat))
        (hbase := by simp [packStore, debtRef])
        (her := by simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind])
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [packDebtWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
            State.lookupAccount] using endStorageLocLoad_uint256 evm0 ⟨11⟩)]
    have hne : (Value.int (Int.ofNat (packDebtWord σ I).toNat) == Value.int 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro hbad
      rw [Value.int.injEq] at hbad
      exact hdebt (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
    simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?, hne, Bool.not_false]
  have hargs :
      evalExprs? config { contract := contract, locals := packStore I } evm0
        [.var "wad", .intLit RAY] =
        .ok [Value.int (Int.ofNat (packWadWord I).toNat),
          Value.int (Int.ofNat packRayWord.toNat)] := by
    change evalExprs? config { contract := contract, locals := packStore I } evm0
        [.var "wad", .intLit RAY] =
        .ok [Value.int (Int.ofNat (packWadWord I).toNat),
          Value.int (Int.ofNat 1000000000000000000000000000)]
    simp [evalExprs?, evalExpr?, packStore, RAY, EvalResult.ofOption, EvalResult.bind, bind,
      pure]
  have hlookup : lookupCallable? contract "mul" = some mulFunction.toCallable := by
    simp [lookupCallable?, lookupFunction?, contract, functions, addFunction, subFunction,
      mulFunction]
  have hbind :
      bindParams? mulFunction.params
        [Value.int (Int.ofNat (packWadWord I).toNat),
          Value.int (Int.ofNat packRayWord.toNat)] = some (packMulLocals I) := by
    simp [mulFunction, packMulLocals, bindParams?]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := packStore I } evm0
        (.internalCall "mul" [.var "wad", .intLit RAY] "amt") .reverted := by
    exact internalCallFunctionRevert hargs hlookup hbind (packMulFunctionBodyReverts evm0 I hover)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [packTransition, nonpayable] using
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
      simp [evm0, initState]; exact hwv))) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hdebtGuard) <|
        ExecBlock.consRevert hmulStmt

theorem endPackSourceBodyNoCodeReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hdebt : packDebtWord σ I ≠ ⟨0⟩)
    (hmul : (packWadWord I).toNat * packRayWord.toNat < UInt256.size)
    (hvatNoCode :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (packVatMaskedWord σ I) = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (packStore I) packTransition.body .reverted := by
  intro evm0
  have hdebtGuard :
      evalExpr? config { contract := contract, locals := packStore I } evm0
        (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := packStore I } evm0
          (.storage debtRef) =
          .ok (.int (Int.ofNat (packDebtWord σ I).toNat)) := by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := packStore I })
        (slot := debtRef)
        (er := ({ base := "debt", steps := [] } : EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc ⟨11⟩)
        (value := .int (Int.ofNat (packDebtWord σ I).toNat))
        (hbase := by simp [packStore, debtRef])
        (her := by simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind])
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [packDebtWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
            State.lookupAccount] using endStorageLocLoad_uint256 evm0 ⟨11⟩)]
    have hne : (Value.int (Int.ofNat (packDebtWord σ I).toNat) == Value.int 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro hbad
      rw [Value.int.injEq] at hbad
      exact hdebt (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
    simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?, hne, Bool.not_false]
  have hargs :
      evalExprs? config { contract := contract, locals := packStore I } evm0
        [.var "wad", .intLit RAY] =
        .ok [Value.int (Int.ofNat (packWadWord I).toNat),
          Value.int (Int.ofNat packRayWord.toNat)] := by
    change evalExprs? config { contract := contract, locals := packStore I } evm0
        [.var "wad", .intLit RAY] =
        .ok [Value.int (Int.ofNat (packWadWord I).toNat),
          Value.int (Int.ofNat 1000000000000000000000000000)]
    simp [evalExprs?, evalExpr?, packStore, RAY, EvalResult.ofOption, EvalResult.bind, bind,
      pure]
  have hlookup : lookupCallable? contract "mul" = some mulFunction.toCallable := by
    simp [lookupCallable?, lookupFunction?, contract, functions, addFunction, subFunction,
      mulFunction]
  have hbind :
      bindParams? mulFunction.params
        [Value.int (Int.ofNat (packWadWord I).toNat),
          Value.int (Int.ofNat packRayWord.toNat)] = some (packMulLocals I) := by
    simp [mulFunction, packMulLocals, bindParams?]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := packStore I } evm0
        (.internalCall "mul" [.var "wad", .intLit RAY] "amt")
        (.ok { contract := contract, locals := packStoreAmt I } evm0) := by
    have hbody := packMulFunctionBodyReturns evm0 I hmul
    simpa [packStoreAmt, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := packStore I })
        (evm := evm0) (calleeEvm := evm0) (name := "mul") (retVar := "amt")
        (args := [.var "wad", .intLit RAY])
        (argVals := [Value.int (Int.ofNat (packWadWord I).toNat),
          Value.int (Int.ofNat packRayWord.toNat)])
        (callee := mulFunction) (locals := packMulLocals I)
        (calleeSolm := { contract := contract, locals := packMulLocalsZ I (packAmtWord I) })
        (value := some [.int (Int.ofNat (packAmtWord I).toNat)]) hargs hlookup hbind hbody)
  have hvat :
      evalExpr? config { contract := contract, locals := packStoreAmt I } evm0 (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (packVatMaskedWord σ I).toNat)) := by
    simpa [packVatMaskedWord, packVatWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, u256_land_comm] using
      evalExpr_packVatStorage (evm := evm0) (locals := packStoreAmt I)
        (by simp [packStoreAmt, packStore])
  have hvatNoCodeNat :
      (UInt256.ofNat
        ((evm0.lookupAccount (AccountAddress.ofNat (packVatMaskedWord σ I).toNat)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    have hnat := congrArg UInt256.toNat hvatNoCode
    simp [Reasoning.Theory.uniswapExtCodeSizeWord, evm0, initState, State.lookupAccount,
      accountAddress_ofUInt256_eq_ofNat_toNat] at hnat ⊢
    cases hfind : σ.find? (AccountAddress.ofNat (packVatMaskedWord σ I).toNat)
    · native_decide
    · simp [hfind, Option.option, Function.comp] at hnat ⊢
      exact hnat
  have hguard :
      evalExpr? config { contract := contract, locals := packStoreAmt I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_packVatCodeGuard_false hvat hvatNoCodeNat
  refine ExecFuncBody.execBlockRevert ?_
  simpa [packTransition, nonpayable, checkedExternalCallStmts] using
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
      simp [evm0, initState]; exact hwv))) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hdebtGuard) <|
        ExecBlock.consNormal hmulStmt <|
          ExecBlock.consRevert (ExecStmt.requireFalse hguard)

theorem endDecode_pack_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (packTransition.params.map Param.name)
      (transitionSignature packTransition).paramTypes I.calldata = some (packStore I) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["wad"] [uint256] I.calldata =
    some (packStore I)
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 :
      ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) = calldataWord I.calldata 4 :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq
    (names := ["wad"]) (types := [uint256]) (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?, uint256, uint256Int, bind, Option.bind]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := I.calldata.toList.drop 4) (start := 0) (by simpa using htake4)]
  simp [decodeCalldata.insertValues, packStore, packWadWord, hword4]

theorem endDecode_pack_none_short {I : ExecutionEnv} (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (packTransition.params.map Param.name)
      (transitionSignature packTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["wad"] [uint256] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq
    (names := ["wad"]) (types := [uint256]) (cd := I.calldata) (by decide)]
  by_cases hsz4 : I.calldata.size < 4
  · rw [if_pos (by rw [htlen]; omega : I.calldata.toList.length < 4)]
  · rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
    simp only [decodeScalarWordsWithMode?, uint256, uint256Int, bind, Option.bind]
    rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
      (bytes := I.calldata.toList.drop 4) (start := 0) (by
        rw [List.drop_zero, List.length_take, List.length_drop, htlen]
        omega)]

theorem endDispatchPackLocal {I : ExecutionEnv} (hsel : selIs I (endSelBytes 30)) :
    dispatchMsg contract I.calldata = some packTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 30 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some packTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, packSelectorBytes]
  native_decide

set_option maxHeartbeats 5000000 in
theorem endReachPackBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (endSelBytes 30)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨806⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x6ea42555⟩ :=
    endSelWord_eq_of_beq I hsz 0x6e 0xa4 0x25 0x55 ⟨0x6ea42555⟩
      (by native_decide) (by simpa [endSelBytes] using hsel)
  obtain ⟨_, _, h32⟩ :=
    endReachRootSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have hroot :
      UInt256.gt (armSelNat endBytecode (⟨32⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h271 := RD.selectorSplitTakenAuto h32
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    hroot (by jump_dest) (by simp)
  have h272 := h271.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have h272gt :
      UInt256.gt (armSelNat endBytecode (⟨272⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h283 := by
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
      selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h272
        (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
        h272gt (by simp)
  have h283gt :
      UInt256.gt (armSelNat endBytecode (⟨283⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h294 := by
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
      selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h283
        (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
        h283gt (by simp)
  have hcage0 :
      UInt256.eq (armSelNat endBytecode (⟨294⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have hpack :
      UInt256.eq (armSelNat endBytecode (⟨305⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h806 := h294
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      hcage0 (by simp)
    |>.selectorArmTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      hpack (by jump_dest) (by simp)
  exact ⟨_, _, h806⟩

theorem endPackX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨806⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6345⟩
        [packWadWord I, ⟨562⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := endBytecode) (sel := sel) (entry := ⟨806⟩) (ret := ⟨562⟩)
    (decoded := ⟨828⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneBytes32ExternalJump
    (code := endBytecode) (decoded := ⟨828⟩) (ret := ⟨562⟩) (routine := ⟨6345⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [packWadWord] using hroutine⟩

theorem endPackX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨806⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel) (entry := ⟨806⟩) (ret := ⟨562⟩)
    (decoded := ⟨828⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem endPackX_debtZero {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hdebt : packDebtWord σ I = ⟨0⟩)
    (h : RD endBytecode I g s0 ⟨6345⟩
      [packWadWord I, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have rd6348pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨11⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k6349, C6349, rd6349raw⟩ := rd6348pre.sload (by native_decide) (by evm_ov)
  have rd6349 : RD endBytecode I g s0 ⟨6349⟩
      (packDebtWord σ I :: packWadWord I :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k6349 C6349 := by
    simpa [packDebtWord, endSlotWord] using rd6349raw
  have rd6352pre := rd6349.pushConst (⟨6413⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  rw [hdebt] at rd6352pre
  have rd6353 := rd6352pre.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨6353⟩)
    (len := ⟨13⟩)
    (rawWord := ⟨5500907680949753345960233497199⟩)
    (shift := ⟨152⟩)
    (word := ⟨31404631181696111852587681435152519789922048605590159656180814133474522824704⟩)
    (op := .PUSH13)
    (width := 13)
    rd6353
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endPackX_toMul {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hdebt : packDebtWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g s0 ⟨6345⟩
      [packWadWord I, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨10170⟩
      (packRayWord :: packWadWord I :: ⟨6462⟩ :: packVowMaskedWord σ I ::
        packSourceWord I :: packMoveSelectorWord :: packVatMaskedWord σ I ::
        packWadWord I :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd6348pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨11⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k6349, C6349, rd6349raw⟩ := rd6348pre.sload (by native_decide) (by evm_ov)
  have rd6349 : RD endBytecode I g s0 ⟨6349⟩
      (packDebtWord σ I :: packWadWord I :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k6349 C6349 := by
    simpa [packDebtWord, endSlotWord] using rd6349raw
  have rd6352pre := rd6349.pushConst (⟨6413⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd6413raw := rd6352pre.jumpiT (by native_decide) hdebt (by jump_dest) (by evm_ov)
  have rd6414 := rd6413raw.jumpdest (by native_decide) (by evm_ov)
  have rd6417pre := rd6414.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  obtain ⟨k6417, C6417, rd6417raw⟩ := rd6417pre.sload (by native_decide) (by evm_ov)
  have rd6417 : RD endBytecode I g s0 ⟨6417⟩
      (packVatWord σ I :: packWadWord I :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k6417 C6417 := by
    simpa [packVatWord, endSlotWord] using rd6417raw
  have rd6420pre := rd6417.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  obtain ⟨k6420, C6420, rd6420raw⟩ := rd6420pre.sload (by native_decide) (by evm_ov)
  have rd6420 : RD endBytecode I g s0 ⟨6420⟩
      (packVowWord σ I :: packVatWord σ I :: packWadWord I :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k6420 C6420 := by
    simpa [packVowWord, endSlotWord] using rd6420raw
  have rd6445pre := evm_run rd6420 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push4 packMoveSelectorWord (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push2 ⟨6462⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov)]
  have rd6458pre := rd6445pre.pushConst packRayWord
    (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
  have rd6461pre := rd6458pre.push2 ⟨10170⟩ (by native_decide) (by evm_ov)
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  have hvow :
      (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩).land (packVowWord σ I) =
        packVowMaskedWord σ I := by
    simpa [packVowMaskedWord] using
      congrArg (fun m : UInt256 => UInt256.land m (packVowWord σ I)) hmask
  have hvat :
      (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩).land (packVatWord σ I) =
        packVatMaskedWord σ I := by
    simpa [packVatMaskedWord] using
      congrArg (fun m : UInt256 => UInt256.land m (packVatWord σ I)) hmask
  rw [hvow, hvat] at rd6461pre
  exact ⟨_, _, by
    simpa [packSourceWord] using
      rd6461pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem packAmt_div_ray (I : ExecutionEnv)
    (hmul : (packWadWord I).toNat * packRayWord.toNat < UInt256.size) :
    UInt256.div (packAmtWord I) packRayWord = packWadWord I := by
  apply u256_inj
  rw [udiv_toNat, packAmtWord, u256_mul_toNat, Nat.mod_eq_of_lt hmul]
  have hray : packRayWord.toNat = 1000000000000000000000000000 := by rfl
  rw [Nat.mul_comm (packWadWord I).toNat packRayWord.toNat]
  rw [hray]
  exact Nat.mul_div_right _ (by norm_num : 0 < 1000000000000000000000000000)

theorem udiv_mul_wrap_ne_of_overflow {a b : UInt256}
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    UInt256.div (UInt256.mul a b) b ≠ a := by
  intro hbad
  have hnat := congrArg UInt256.toNat hbad
  rw [udiv_toNat] at hnat
  have hle : a.toNat * b.toNat ≤ (UInt256.mul a b).toNat := by
    exact Nat.mul_le_of_le_div b.toNat a.toNat (UInt256.mul a b).toNat
      (by exact le_of_eq hnat.symm)
  have hlt : (UInt256.mul a b).toNat < UInt256.size := (UInt256.mul a b).val.isLt
  exact (not_lt_of_ge (le_trans hover hle)) hlt

theorem endPackX_mulOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hmul : (packWadWord I).toNat * packRayWord.toNat < UInt256.size)
    (h : RD endBytecode I g s0 ⟨10170⟩
      (packRayWord :: packWadWord I :: ⟨6462⟩ :: packVowMaskedWord σ I ::
        packSourceWord I :: packMoveSelectorWord :: packVatMaskedWord σ I ::
        packWadWord I :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨6462⟩
      (packAmtWord I :: packVowMaskedWord σ I :: packSourceWord I ::
        packMoveSelectorWord :: packVatMaskedWord σ I :: packWadWord I :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd10180pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨10197⟩ (by native_decide) (by evm_ov)]
  have hrayNonzero : UInt256.isZero packRayWord = ⟨0⟩ := by native_decide
  rw [hrayNonzero] at rd10180pre
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
    rd10192pre.jumpiT (by native_decide)
      (by native_decide : packRayWord ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov)
  have rd10197pre := evm_run (rd10194raw.jumpdest (by native_decide) (by evm_ov)) with [
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have hdiv : UInt256.div (packAmtWord I) packRayWord = packWadWord I :=
    packAmt_div_ray I hmul
  rw [hdiv, u256_eq_refl] at rd10197pre
  have rd10108 :=
    rd10197pre.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)
  have rd10113pre := evm_run (rd10108.jumpdest (by native_decide) (by evm_ov)) with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [packAmtWord] using
      rd10113pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem endPackX_mulOverflow {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hdivne : UInt256.div (packAmtWord I) packRayWord ≠ packWadWord I)
    (h : RD endBytecode I g s0 ⟨10170⟩
      (packRayWord :: packWadWord I :: ⟨6462⟩ :: packVowMaskedWord σ I ::
        packSourceWord I :: packMoveSelectorWord :: packVatMaskedWord σ I ::
        packWadWord I :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have rd10180pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨10197⟩ (by native_decide) (by evm_ov)]
  have hrayNonzero : UInt256.isZero packRayWord = ⟨0⟩ := by native_decide
  rw [hrayNonzero] at rd10180pre
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
    rd10192pre.jumpiT (by native_decide)
      (by native_decide : packRayWord ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov)
  have rd10197pre := evm_run (rd10194raw.jumpdest (by native_decide) (by evm_ov)) with [
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have heqZero :
      UInt256.eq (UInt256.div (packAmtWord I) packRayWord) (packWadWord I) = ⟨0⟩ :=
    u256_eq_of_ne hdivne
  rw [heqZero] at rd10197pre
  have rd10202 := rd10197pre.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.uniswapPush1Dup1Revert0 rd10202
    (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

end Benchmarks.Dss.End
