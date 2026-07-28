import Benchmarks.Dss.Flipper.TendIncreaseGuard
import Benchmarks.Dss.Flipper.BidAccess
import Benchmarks.Dss.Flipper.YankCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## Tail helpers for `tend(uint256,uint256,uint256)` -/

noncomputable abbrev tendPayHashMem (mem : ByteArray) (I : ExecutionEnv) :
    ByteArray :=
  twoWordHashMem (tendId I) ⟨1⟩ mem

noncomputable abbrev tendVatPayCallMem (mem : ByteArray) (σ : AccountMap)
    (I : ExecutionEnv) : ByteArray :=
  writeCascade (tendPayHashMem mem I)
    [(128, yankVatMoveSelectorWord),
     (132, solcSourceWord I),
     (164, bidGalWord (tendId I) σ I),
     (196, UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I))]

noncomputable abbrev tendVatRefundCallMem (mem : ByteArray) (σ : AccountMap)
    (I : ExecutionEnv) : ByteArray :=
  writeCascade (tendPayHashMem mem I)
    [(128, yankVatMoveSelectorWord),
     (132, solcSourceWord I),
     (164, bidGuyWord (tendId I) σ I),
     (196, bidBidWord (tendId I) σ I)]

abbrev tendNow (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.header.timestamp

abbrev tendNow48 (I : ExecutionEnv) : UInt256 :=
  UInt256.land (tendNow I) uint48Mask

abbrev tendTtlWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperUint48Offset0Word ⟨5⟩ σ I

abbrev tendTicNewWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (tendNow48 I + tendTtlWord σ I) uint48Mask

abbrev tendAfterBidMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (bidBaseOfWord (tendId I)) (tendBid I)

abbrev tendStoredTicWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  setUint48Offset20Word
    (flipperSlotWord (bidPackedSlotOfWord (tendId I)) σ I)
    (tendTicNewWord σ I)

abbrev tendStoreTicMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (bidPackedSlotOfWord (tendId I))
    (tendStoredTicWord σ I)

abbrev tendAfterTicMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  tendStoreTicMap (tendAfterBidMap σ I) I

theorem tendNow48_bound (I : ExecutionEnv) :
    (tendNow48 I).toNat < 2 ^ 48 := by
  simpa [tendNow48, EVM.twoPow] using uint48Mask_bound (tendNow I)

theorem tendTtlWord_bound (σ : AccountMap) (I : ExecutionEnv) :
    (tendTtlWord σ I).toNat < 2 ^ 48 := by
  simpa [tendTtlWord, EVM.twoPow] using uint48Mask_bound (flipperSlotWord ⟨5⟩ σ I)

theorem tendTicNewWord_bound (σ : AccountMap) (I : ExecutionEnv) :
    (tendTicNewWord σ I).toNat < 2 ^ 48 := by
  simpa [tendTicNewWord, EVM.twoPow] using uint48Mask_bound (tendNow48 I + tendTtlWord σ I)

theorem tendTicNewWord_toNat (σ : AccountMap) (I : ExecutionEnv) :
    (tendTicNewWord σ I).toNat =
      ((tendNow48 I).toNat + (tendTtlWord σ I).toNat) % 2 ^ 48 := by
  rw [tendTicNewWord, uint48Mask_toNat_mod, uadd_toNat]
  have hnow := tendNow48_bound I
  have httl := tendTtlWord_bound σ I
  have hsum :
      (tendNow48 I).toNat + (tendTtlWord σ I).toNat < UInt256.size := by
    calc
      (tendNow48 I).toNat + (tendTtlWord σ I).toNat < 2 ^ 48 + 2 ^ 48 :=
        Nat.add_lt_add hnow httl
      _ = 2 ^ 49 := by norm_num
      _ < UInt256.size := by norm_num [UInt256.size]
  rw [Nat.mod_eq_of_lt hsum]

theorem tendTicNewWord_fullTimestampAdd (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.land (tendNow I + tendTtlWord σ I) uint48Mask = tendTicNewWord σ I := by
  apply u256_inj
  rw [uint48Mask_toNat_mod, tendTicNewWord_toNat, uadd_toNat]
  have hdvd : 2 ^ 48 ∣ UInt256.size := by
    norm_num [UInt256.size]
  rw [Nat.mod_mod_of_dvd _ hdvd]
  rw [Nat.add_mod]
  rw [← uint48Mask_toNat_mod (tendNow I)]
  rw [Nat.mod_eq_of_lt (tendTtlWord_bound σ I)]

theorem tendTicNewWord_toNat_noOverflow {σ : AccountMap} {I : ExecutionEnv}
    (hfit : (tendNow48 I).toNat + (tendTtlWord σ I).toNat < 2 ^ 48) :
    (tendTicNewWord σ I).toNat =
      (tendNow48 I).toNat + (tendTtlWord σ I).toNat := by
  rw [tendTicNewWord_toNat]
  exact Nat.mod_eq_of_lt hfit

theorem tendTicNewWord_toNat_overflow {σ : AccountMap} {I : ExecutionEnv}
    (hover : 2 ^ 48 ≤ (tendNow48 I).toNat + (tendTtlWord σ I).toNat) :
    (tendTicNewWord σ I).toNat =
      (tendNow48 I).toNat + (tendTtlWord σ I).toNat - 2 ^ 48 := by
  rw [tendTicNewWord_toNat]
  have hlt :
      (tendNow48 I).toNat + (tendTtlWord σ I).toNat - 2 ^ 48 < 2 ^ 48 := by
    have hnow := tendNow48_bound I
    have httl := tendTtlWord_bound σ I
    omega
  rw [Nat.mod_eq_sub_mod hover, Nat.mod_eq_of_lt hlt]

theorem tendTicNewWord_ge_now48_noOverflow {σ : AccountMap} {I : ExecutionEnv}
    (hfit : (tendNow48 I).toNat + (tendTtlWord σ I).toNat < 2 ^ 48) :
    (tendNow48 I).toNat ≤ (tendTicNewWord σ I).toNat := by
  rw [tendTicNewWord_toNat_noOverflow hfit]
  omega

theorem tendTicNewWord_lt_now48_overflow {σ : AccountMap} {I : ExecutionEnv}
    (hover : 2 ^ 48 ≤ (tendNow48 I).toNat + (tendTtlWord σ I).toNat) :
    (tendTicNewWord σ I).toNat < (tendNow48 I).toNat := by
  rw [tendTicNewWord_toNat_overflow hover]
  have httl := tendTtlWord_bound σ I
  omega

theorem uint48MulDivisor20_eq_shiftLeft (w : UInt256) :
    UInt256.mul w uint48Divisor20 = UInt256.shiftLeft w ⟨160⟩ := by
  apply u256_inj
  rw [u256_mul_toNat]
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ ((⟨160⟩ : UInt256).val ≥ 256))]
  change w.toNat * uint48Divisor20.toNat % UInt256.size =
    (w.toNat <<< 160) % UInt256.size
  rw [show uint48Divisor20.toNat = 2 ^ 160 by native_decide]
  rw [Nat.shiftLeft_eq]

theorem setUint48Offset20RuntimeWord (old data : UInt256) :
    UInt256.lor
        (UInt256.land old (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨160⟩)))
        (UInt256.mul (UInt256.land data uint48Mask) uint48Divisor20) =
      setUint48Offset20Word old (UInt256.land data uint48Mask) := by
  have hlow :
      UInt256.land (UInt256.land data uint48Mask) uint48Mask =
        UInt256.land data uint48Mask := by
    exact uint48Mask_clean (uint48Mask_bound data)
  have hshift :
      UInt256.mul (UInt256.land data uint48Mask) uint48Divisor20 =
        UInt256.shiftLeft (UInt256.land data uint48Mask) ⟨160⟩ := by
    exact uint48MulDivisor20_eq_shiftLeft (UInt256.land data uint48Mask)
  calc
    UInt256.lor
        (UInt256.land old (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨160⟩)))
        (UInt256.mul (UInt256.land data uint48Mask) uint48Divisor20) =
        UInt256.lor
          (UInt256.land old (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨160⟩)))
          (UInt256.shiftLeft (UInt256.land data uint48Mask) ⟨160⟩) := by
          rw [hshift]
    _ = setUint48Offset20Word old (UInt256.land data uint48Mask) := by
          unfold setUint48Offset20Word
          rw [hlow]

theorem tendStoredTicRuntimeWord (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.lor
        (UInt256.land (flipperSlotWord (bidPackedSlotOfWord (tendId I)) σ I)
          (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨160⟩)))
        (UInt256.mul
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)
          (UInt256.land uint48Mask (tendNow I + tendTtlWord σ I))) =
      tendStoredTicWord σ I := by
  have hdiv20 :
      UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩ = uint48Divisor20 := by
    rfl
  calc
    UInt256.lor
        (UInt256.land (flipperSlotWord (bidPackedSlotOfWord (tendId I)) σ I)
          (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨160⟩)))
        (UInt256.mul
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)
          (UInt256.land uint48Mask (tendNow I + tendTtlWord σ I))) =
      UInt256.lor
        (UInt256.land (flipperSlotWord (bidPackedSlotOfWord (tendId I)) σ I)
          (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨160⟩)))
        (UInt256.mul
          (UInt256.land (tendNow I + tendTtlWord σ I) uint48Mask)
          uint48Divisor20) := by
        rw [hdiv20, u256_land_comm uint48Mask (tendNow I + tendTtlWord σ I),
          u256_mul_comm]
    _ =
      setUint48Offset20Word (flipperSlotWord (bidPackedSlotOfWord (tendId I)) σ I)
        (UInt256.land (tendNow I + tendTtlWord σ I) uint48Mask) := by
        exact setUint48Offset20RuntimeWord
          (flipperSlotWord (bidPackedSlotOfWord (tendId I)) σ I)
          (tendNow I + tendTtlWord σ I)
    _ = tendStoredTicWord σ I := by
        unfold tendStoredTicWord
        rw [tendTicNewWord_fullTimestampAdd]

theorem tendTwoWordHashMem_read0_of_size_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  have hword0Size : (wordAt0Mem key mem).size = mem.size := by
    unfold wordAt0Mem
    change (writeWord mem 0 key).size = mem.size
    rw [writeWord_size]
    · omega
    · have hzero : 0 - mem.size = 0 := by omega
      rw [hzero]
      native_decide
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [hword0Size]; omega) (by omega)]
  unfold wordAt0Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray key).size ≤ 32
    rw [toByteArray_size])

theorem tendTwoWordHashMem_read32_of_size_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  have hword0Size : (wordAt0Mem key mem).size = mem.size := by
    unfold wordAt0Mem
    change (writeWord mem 0 key).size = mem.size
    rw [writeWord_size]
    · omega
    · have hzero : 0 - mem.size = 0 := by omega
      rw [hzero]
      native_decide
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [hword0Size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

theorem tendTwoWordHashMem_size_of_size_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  have hword0Size : (wordAt0Mem key mem).size = mem.size := by
    unfold wordAt0Mem
    change (writeWord mem 0 key).size = mem.size
    rw [writeWord_size]
    · omega
    · have hzero : 0 - mem.size = 0 := by omega
      rw [hzero]
      native_decide
  unfold twoWordHashMem wordAt32Mem
  change (writeWord (wordAt0Mem key mem) 32 slot).size = mem.size
  rw [writeWord_size]
  · rw [hword0Size]
    omega
  · rw [hword0Size]
    have hzero : 32 - mem.size = 0 := by omega
    rw [hzero]
    native_decide

theorem tendTwoWordHashMem_read0_64_of_size_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  have hsize := tendTwoWordHashMem_size_of_size_ge (mem := mem) key slot hmem
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [hsize]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0 (by rw [hsize]; omega),
      tendTwoWordHashMem_read0_of_size_ge key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32 (by rw [hsize]; omega),
      tendTwoWordHashMem_read32_of_size_ge key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem tendTwoWordHashMem_solcMappingSlot_of_size_ge
    (baseSlot key : UInt256) {mem : ByteArray} (hmem : 64 ≤ mem.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [tendTwoWordHashMem_read0_64_of_size_ge key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

theorem tendPayHashMem_size {mem : ByteArray} (I : ExecutionEnv)
    (hmemSize : mem.size = 96) :
    (tendPayHashMem mem I).size = 96 := by
  unfold tendPayHashMem
  exact twoWordHashMem_size_96 (tendId I) ⟨1⟩ hmemSize

theorem tendPayHashMem_read64 {mem : ByteArray} (I : ExecutionEnv)
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (tendPayHashMem mem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold tendPayHashMem
  exact twoWordHashMem_read64 (tendId I) ⟨1⟩ hmemSize hmemRead64

theorem tendVatPayCallMem_size {mem : ByteArray} (σ : AccountMap) (I : ExecutionEnv)
    (hmemSize : mem.size = 96) :
    (tendVatPayCallMem mem σ I).size = 228 := by
  unfold tendVatPayCallMem
  exact writeCascade_size_of_base (tendPayHashMem mem I)
    [(128, yankVatMoveSelectorWord),
     (132, solcSourceWord I),
     (164, bidGalWord (tendId I) σ I),
     (196, UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I))]
    (tendPayHashMem_size I hmemSize)
    (by simp [WriteGapsOk] <;> native_decide)
    (by norm_num [writeCascadeSize])

theorem tendVatPayCallMem_read64 {mem : ByteArray} (σ : AccountMap) (I : ExecutionEnv)
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (tendVatPayCallMem mem σ I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold tendVatPayCallMem
  rw [writeCascade_read_preserved_of_base (tendPayHashMem mem I)
    [(128, yankVatMoveSelectorWord),
     (132, solcSourceWord I),
     (164, bidGalWord (tendId I) σ I),
     (196, UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I))]
    (tendPayHashMem_size I hmemSize)
    (by simp [WindowDisjointFromWrites] <;> native_decide)]
  exact tendPayHashMem_read64 I hmemSize hmemRead64

theorem tendVatPayCallMem_read128_4 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 96) :
    (tendVatPayCallMem mem σ I).readWithPadding 128 4 = moveSelector := by
  unfold tendVatPayCallMem
  rw [writeCascade_read_window_of_head (tendPayHashMem mem I) 128 0 4
    yankVatMoveSelectorWord
    [(132, solcSourceWord I),
     (164, bidGalWord (tendId I) σ I),
     (196, UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I))]
    (by rw [tendPayHashMem_size I hmemSize]; native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)
    (by norm_num) (by norm_num) (by norm_num)]
  exact yankVatMoveSelectorWord_prefix

theorem tendVatPayCallMem_read132 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 96) :
    (tendVatPayCallMem mem σ I).readWithPadding 132 32 =
      UInt256.toByteArray (solcSourceWord I) := by
  unfold tendVatPayCallMem
  rw [writeCascade_cons]
  have hbase :
      (writeWord (tendPayHashMem mem I) 128 yankVatMoveSelectorWord).size = 160 := by
    rw [writeWord_size]
    · rw [tendPayHashMem_size I hmemSize]; native_decide
    · rw [tendPayHashMem_size I hmemSize]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord (tendPayHashMem mem I) 128 yankVatMoveSelectorWord)
    (base := 160) (off := 132) (word := solcSourceWord I)
    (rest := [(164, bidGalWord (tendId I) σ I),
      (196, UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I))])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem tendVatPayCallMem_read164 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 96) :
    (tendVatPayCallMem mem σ I).readWithPadding 164 32 =
      UInt256.toByteArray (bidGalWord (tendId I) σ I) := by
  unfold tendVatPayCallMem
  rw [writeCascade_cons, writeCascade_cons]
  let mem1 := writeWord (tendPayHashMem mem I) 128 yankVatMoveSelectorWord
  have hmem1 : mem1.size = 160 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [tendPayHashMem_size I hmemSize]; native_decide
    · rw [tendPayHashMem_size I hmemSize]; native_decide
  have hbase : (writeWord mem1 132 (solcSourceWord I)).size = 164 := by
    rw [writeWord_size]
    · rw [hmem1]; native_decide
    · rw [hmem1]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem1 132 (solcSourceWord I))
    (base := 164) (off := 164) (word := bidGalWord (tendId I) σ I)
    (rest := [(196, UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I))])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem tendVatPayCallMem_read196 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 96) :
    (tendVatPayCallMem mem σ I).readWithPadding 196 32 =
      UInt256.toByteArray (UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I)) := by
  unfold tendVatPayCallMem
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons]
  let mem1 := writeWord (tendPayHashMem mem I) 128 yankVatMoveSelectorWord
  let mem2 := writeWord mem1 132 (solcSourceWord I)
  have hmem1 : mem1.size = 160 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [tendPayHashMem_size I hmemSize]; native_decide
    · rw [tendPayHashMem_size I hmemSize]; native_decide
  have hmem2 : mem2.size = 164 := by
    dsimp [mem2]
    rw [writeWord_size]
    · rw [hmem1]; native_decide
    · rw [hmem1]; native_decide
  have hbase : (writeWord mem2 164 (bidGalWord (tendId I) σ I)).size = 196 := by
    rw [writeWord_size]
    · rw [hmem2]; native_decide
    · rw [hmem2]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem2 164 (bidGalWord (tendId I) σ I))
    (base := 196) (off := 196)
    (word := UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I))
    (rest := [])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites])

theorem tendVatPayCallMem_read {mem : ByteArray} (σ : AccountMap) (I : ExecutionEnv)
    (hmemSize : mem.size = 96) :
    (tendVatPayCallMem mem σ I).readWithPadding 128 100 =
      moveSelector ++
      UInt256.toByteArray (solcSourceWord I) ++
      UInt256.toByteArray (bidGalWord (tendId I) σ I) ++
      UInt256.toByteArray (UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I)) := by
  rw [byteArray_readWithPadding_split (tendVatPayCallMem mem σ I) 128 4 96
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [tendVatPayCallMem_size σ I hmemSize])]
  rw [tendVatPayCallMem_read128_4 σ I hmemSize]
  rw [byteArray_readWithPadding_split (tendVatPayCallMem mem σ I) 132 32 64
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [tendVatPayCallMem_size σ I hmemSize])]
  rw [tendVatPayCallMem_read132 σ I hmemSize]
  rw [byteArray_readWithPadding_split (tendVatPayCallMem mem σ I) 164 32 32
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [tendVatPayCallMem_size σ I hmemSize])]
  rw [tendVatPayCallMem_read164 σ I hmemSize, tendVatPayCallMem_read196 σ I hmemSize]
  simp [ByteArray.append_assoc]

theorem tendVatPayCallMem_encode {mem : ByteArray} (σ : AccountMap) (I : ExecutionEnv)
    (hmemSize : mem.size = 96) :
    config.externalABI.encode? "move"
      [.address I.source,
        .address (AccountAddress.ofNat (bidGalWord (tendId I) σ I).toNat),
        .int (Int.ofNat (UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I)).toNat)] =
        some ((tendVatPayCallMem mem σ I).readWithPadding 128 100) := by
  rw [tendVatPayCallMem_read σ I hmemSize]
  unfold config externalABI
  simp only [if_true]
  unfold ABI.encodeCallWithSelector?
  have hgal :
      encodeABIValue? addr
          (.address (AccountAddress.ofNat (bidGalWord (tendId I) σ I).toNat)) =
        some (UInt256.toByteArray (bidGalWord (tendId I) σ I)).toList := by
    simpa [bidGalWord, flipperAddressReturnWord] using
      yankEncodeABIValue_address_word (flipperSlotWord (bidSlotOfWord (tendId I) ⟨4⟩) σ I)
  have hpayload :
      encodeABIValues? [addr, addr, uint256]
        [.address I.source,
          .address (AccountAddress.ofNat (bidGalWord (tendId I) σ I).toNat),
          .int (Int.ofNat (UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I)).toNat)] =
          some (UInt256.toByteArray (solcSourceWord I) ++
            UInt256.toByteArray (bidGalWord (tendId I) σ I) ++
            UInt256.toByteArray
              (UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I))).toList := by
    unfold encodeABIValues?
    rw [show abiTupleHeadSize? [addr, addr, uint256] = some 96 by native_decide]
    simp only [encodeABIValuesFrom?, Option.bind, bind]
    rw [yankEncodeABIValue_source_address, hgal, yankEncodeABIValue_uint256_word]
    simp [show isDynamicABIType addr = false by native_decide,
      show isDynamicABIType uint256 = false by native_decide,
      ByteArray.append_assoc, byteArray_toList_eq]
  rw [hpayload]
  apply congrArg some
  apply ByteArray.ext
  simp [moveSelector, byteArray_toList_eq, ByteArray.append_assoc]

theorem tendVatRefundCallMem_size {mem : ByteArray} (σ : AccountMap) (I : ExecutionEnv)
    (hmemSize : mem.size = 96) :
    (tendVatRefundCallMem mem σ I).size = 228 := by
  unfold tendVatRefundCallMem
  exact writeCascade_size_of_base (tendPayHashMem mem I)
    [(128, yankVatMoveSelectorWord),
     (132, solcSourceWord I),
     (164, bidGuyWord (tendId I) σ I),
     (196, bidBidWord (tendId I) σ I)]
    (tendPayHashMem_size I hmemSize)
    (by simp [WriteGapsOk] <;> native_decide)
    (by norm_num [writeCascadeSize])

theorem tendVatRefundCallMem_read64 {mem : ByteArray} (σ : AccountMap) (I : ExecutionEnv)
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (tendVatRefundCallMem mem σ I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold tendVatRefundCallMem
  rw [writeCascade_read_preserved_of_base (tendPayHashMem mem I)
    [(128, yankVatMoveSelectorWord),
     (132, solcSourceWord I),
     (164, bidGuyWord (tendId I) σ I),
     (196, bidBidWord (tendId I) σ I)]
    (tendPayHashMem_size I hmemSize)
    (by simp [WindowDisjointFromWrites] <;> native_decide)]
  exact tendPayHashMem_read64 I hmemSize hmemRead64

theorem tendVatRefundCallMem_read128_4 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 96) :
    (tendVatRefundCallMem mem σ I).readWithPadding 128 4 = moveSelector := by
  unfold tendVatRefundCallMem
  rw [writeCascade_read_window_of_head (tendPayHashMem mem I) 128 0 4
    yankVatMoveSelectorWord
    [(132, solcSourceWord I),
     (164, bidGuyWord (tendId I) σ I),
     (196, bidBidWord (tendId I) σ I)]
    (by rw [tendPayHashMem_size I hmemSize]; native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)
    (by norm_num) (by norm_num) (by norm_num)]
  exact yankVatMoveSelectorWord_prefix

theorem tendVatRefundCallMem_read132 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 96) :
    (tendVatRefundCallMem mem σ I).readWithPadding 132 32 =
      UInt256.toByteArray (solcSourceWord I) := by
  unfold tendVatRefundCallMem
  rw [writeCascade_cons]
  have hbase :
      (writeWord (tendPayHashMem mem I) 128 yankVatMoveSelectorWord).size = 160 := by
    rw [writeWord_size]
    · rw [tendPayHashMem_size I hmemSize]; native_decide
    · rw [tendPayHashMem_size I hmemSize]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord (tendPayHashMem mem I) 128 yankVatMoveSelectorWord)
    (base := 160) (off := 132) (word := solcSourceWord I)
    (rest := [(164, bidGuyWord (tendId I) σ I),
      (196, bidBidWord (tendId I) σ I)])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem tendVatRefundCallMem_read164 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 96) :
    (tendVatRefundCallMem mem σ I).readWithPadding 164 32 =
      UInt256.toByteArray (bidGuyWord (tendId I) σ I) := by
  unfold tendVatRefundCallMem
  rw [writeCascade_cons, writeCascade_cons]
  let mem1 := writeWord (tendPayHashMem mem I) 128 yankVatMoveSelectorWord
  have hmem1 : mem1.size = 160 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [tendPayHashMem_size I hmemSize]; native_decide
    · rw [tendPayHashMem_size I hmemSize]; native_decide
  have hbase : (writeWord mem1 132 (solcSourceWord I)).size = 164 := by
    rw [writeWord_size]
    · rw [hmem1]; native_decide
    · rw [hmem1]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem1 132 (solcSourceWord I))
    (base := 164) (off := 164) (word := bidGuyWord (tendId I) σ I)
    (rest := [(196, bidBidWord (tendId I) σ I)])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem tendVatRefundCallMem_read196 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 96) :
    (tendVatRefundCallMem mem σ I).readWithPadding 196 32 =
      UInt256.toByteArray (bidBidWord (tendId I) σ I) := by
  unfold tendVatRefundCallMem
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons]
  let mem1 := writeWord (tendPayHashMem mem I) 128 yankVatMoveSelectorWord
  let mem2 := writeWord mem1 132 (solcSourceWord I)
  have hmem1 : mem1.size = 160 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [tendPayHashMem_size I hmemSize]; native_decide
    · rw [tendPayHashMem_size I hmemSize]; native_decide
  have hmem2 : mem2.size = 164 := by
    dsimp [mem2]
    rw [writeWord_size]
    · rw [hmem1]; native_decide
    · rw [hmem1]; native_decide
  have hbase : (writeWord mem2 164 (bidGuyWord (tendId I) σ I)).size = 196 := by
    rw [writeWord_size]
    · rw [hmem2]; native_decide
    · rw [hmem2]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem2 164 (bidGuyWord (tendId I) σ I))
    (base := 196) (off := 196) (word := bidBidWord (tendId I) σ I)
    (rest := [])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites])

theorem tendVatRefundCallMem_read {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 96) :
    (tendVatRefundCallMem mem σ I).readWithPadding 128 100 =
      moveSelector ++
      UInt256.toByteArray (solcSourceWord I) ++
      UInt256.toByteArray (bidGuyWord (tendId I) σ I) ++
      UInt256.toByteArray (bidBidWord (tendId I) σ I) := by
  rw [byteArray_readWithPadding_split (tendVatRefundCallMem mem σ I) 128 4 96
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [tendVatRefundCallMem_size σ I hmemSize])]
  rw [tendVatRefundCallMem_read128_4 σ I hmemSize]
  rw [byteArray_readWithPadding_split (tendVatRefundCallMem mem σ I) 132 32 64
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [tendVatRefundCallMem_size σ I hmemSize])]
  rw [tendVatRefundCallMem_read132 σ I hmemSize]
  rw [byteArray_readWithPadding_split (tendVatRefundCallMem mem σ I) 164 32 32
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [tendVatRefundCallMem_size σ I hmemSize])]
  rw [tendVatRefundCallMem_read164 σ I hmemSize,
    tendVatRefundCallMem_read196 σ I hmemSize]
  simp [ByteArray.append_assoc]

theorem tendVatRefundCallMem_encode {mem : ByteArray} (σ : AccountMap) (I : ExecutionEnv)
    (hmemSize : mem.size = 96) :
    config.externalABI.encode? "move"
      [.address I.source,
        .address (AccountAddress.ofNat (bidGuyWord (tendId I) σ I).toNat),
        .int (Int.ofNat (bidBidWord (tendId I) σ I).toNat)] =
        some ((tendVatRefundCallMem mem σ I).readWithPadding 128 100) := by
  rw [tendVatRefundCallMem_read σ I hmemSize]
  unfold config externalABI
  simp only [if_true]
  unfold ABI.encodeCallWithSelector?
  have hguy :
      encodeABIValue? addr
          (.address (AccountAddress.ofNat (bidGuyWord (tendId I) σ I).toNat)) =
        some (UInt256.toByteArray (bidGuyWord (tendId I) σ I)).toList := by
    simpa [bidGuyWord, flipperAddressReturnWord] using
      yankEncodeABIValue_address_word (flipperSlotWord (bidPackedSlotOfWord (tendId I)) σ I)
  have hpayload :
      encodeABIValues? [addr, addr, uint256]
        [.address I.source,
          .address (AccountAddress.ofNat (bidGuyWord (tendId I) σ I).toNat),
          .int (Int.ofNat (bidBidWord (tendId I) σ I).toNat)] =
          some (UInt256.toByteArray (solcSourceWord I) ++
            UInt256.toByteArray (bidGuyWord (tendId I) σ I) ++
            UInt256.toByteArray (bidBidWord (tendId I) σ I)).toList := by
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

abbrev tendPayMoveArgValsOf (evm : EVM.State) (I : ExecutionEnv) : List Value :=
  [.address evm.executionEnv.source,
    .address
      (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (bidSlotOfWord (tendId I) ⟨4⟩))
          solcAddrMask).toNat),
    .int (Int.ofNat
      (UInt256.sub (tendBid I)
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (bidBaseOfWord (tendId I)))).toNat)]

abbrev tendLocalsAfterPay (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (tendLocalsBidOneBegBid σ I).insert "_payRet" (collapseReturns [])

abbrev tendLocalsWithTic (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (tendLocalsAfterPay σ I).insert "tic_"
    (.int (Int.ofNat (tendTicNewWord σ I).toNat))

abbrev tendLocalsWithTicFrom (σpre σtic : AccountMap) (I : ExecutionEnv) : Store :=
  (tendLocalsAfterPay σpre I).insert "tic_"
    (.int (Int.ofNat (tendTicNewWord σtic I).toNat))

theorem tendLocalsBidOneBegBid_get_vat (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsBidOneBegBid σ I).get? "vat" = none := by
  simp [tendLocalsBidOneBegBid, tendLocalsBidOne, tendLocals, store_get_ne]

theorem tendLocalsBidOneBegBid_get_ttl (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsBidOneBegBid σ I).get? "ttl" = none := by
  simp [tendLocalsBidOneBegBid, tendLocalsBidOne, tendLocals, store_get_ne]

theorem tendLocalsAfterPay_get_id (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsAfterPay σ I).get? "id" =
      some (.int (Int.ofNat (tendId I).toNat)) := by
  rw [tendLocalsAfterPay, store_get_ne _ _ (by decide)]
  exact tendLocalsBidOneBegBid_get_id σ I

theorem tendLocalsAfterPay_get_bid (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsAfterPay σ I).get? "bid" =
      some (.int (Int.ofNat (tendBid I).toNat)) := by
  rw [tendLocalsAfterPay, store_get_ne _ _ (by decide)]
  exact tendLocalsBidOneBegBid_get_bid σ I

theorem tendLocalsAfterPay_get_bids (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsAfterPay σ I).get? "bids" = none := by
  rw [tendLocalsAfterPay, store_get_ne _ _ (by decide)]
  exact tendLocalsBidOneBegBid_get_bids σ I

theorem tendLocalsAfterPay_get_vat (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsAfterPay σ I).get? "vat" = none := by
  rw [tendLocalsAfterPay, store_get_ne _ _ (by decide)]
  simp [tendLocalsBidOneBegBid, tendLocalsBidOne, tendLocals, store_get_ne]

theorem tendLocalsAfterPay_get_ttl (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsAfterPay σ I).get? "ttl" = none := by
  rw [tendLocalsAfterPay, store_get_ne _ _ (by decide)]
  simp [tendLocalsBidOneBegBid, tendLocalsBidOne, tendLocals, store_get_ne]

theorem tendLocalsWithTic_get_id (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsWithTic σ I).get? "id" =
      some (.int (Int.ofNat (tendId I).toNat)) := by
  rw [tendLocalsWithTic, store_get_ne _ _ (by decide)]
  exact tendLocalsAfterPay_get_id σ I

theorem tendLocalsWithTic_get_bids (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsWithTic σ I).get? "bids" = none := by
  rw [tendLocalsWithTic, store_get_ne _ _ (by decide)]
  exact tendLocalsAfterPay_get_bids σ I

theorem tendLocalsWithTic_get_ttl (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsWithTic σ I).get? "ttl" = none := by
  rw [tendLocalsWithTic, store_get_ne _ _ (by decide)]
  exact tendLocalsAfterPay_get_ttl σ I

theorem tendLocalsWithTic_get_tic (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsWithTic σ I).get? "tic_" =
      some (.int (Int.ofNat (tendTicNewWord σ I).toNat)) := by
  rw [tendLocalsWithTic, store_get_self]

theorem tendLocalsWithTicFrom_get_id (σpre σtic : AccountMap) (I : ExecutionEnv) :
    (tendLocalsWithTicFrom σpre σtic I).get? "id" =
      some (.int (Int.ofNat (tendId I).toNat)) := by
  rw [tendLocalsWithTicFrom, store_get_ne _ _ (by decide)]
  exact tendLocalsAfterPay_get_id σpre I

theorem tendLocalsWithTicFrom_get_bids (σpre σtic : AccountMap) (I : ExecutionEnv) :
    (tendLocalsWithTicFrom σpre σtic I).get? "bids" = none := by
  rw [tendLocalsWithTicFrom, store_get_ne _ _ (by decide)]
  exact tendLocalsAfterPay_get_bids σpre I

theorem tendLocalsWithTicFrom_get_ttl (σpre σtic : AccountMap) (I : ExecutionEnv) :
    (tendLocalsWithTicFrom σpre σtic I).get? "ttl" = none := by
  rw [tendLocalsWithTicFrom, store_get_ne _ _ (by decide)]
  exact tendLocalsAfterPay_get_ttl σpre I

theorem tendLocalsWithTicFrom_get_tic (σpre σtic : AccountMap) (I : ExecutionEnv) :
    (tendLocalsWithTicFrom σpre σtic I).get? "tic_" =
      some (.int (Int.ofNat (tendTicNewWord σtic I).toNat)) := by
  rw [tendLocalsWithTicFrom, store_get_self]

theorem intModWord_sub_toNat (a b : UInt256) :
    (Int.ofNat a.toNat - Int.ofNat b.toNat) % wordModulus =
      Int.ofNat (UInt256.sub a b).toNat := by
  by_cases hle : b.toNat ≤ a.toNat
  · have hsub : Int.ofNat a.toNat - Int.ofNat b.toNat =
        Int.ofNat (a.toNat - b.toNat) := by
      exact (Int.ofNat_sub hle).symm
    have hlt : a.toNat - b.toNat < UInt256.size := by
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.val.isLt
    have hltInt : Int.ofNat (a.toNat - b.toNat) < wordModulus := by
      rw [wordModulus]
      norm_num [UInt256.size] at hlt ⊢
      exact_mod_cast hlt
    rw [hsub]
    rw [Int.emod_eq_of_lt (by exact Int.natCast_nonneg _) hltInt]
    rw [usub_toNat (a := a) (b := b) hle]
  · have hlt : a.toNat < b.toNat := Nat.lt_of_not_ge hle
    let d := b.toNat - a.toNat
    have hdpos : 0 < d := by
      dsimp [d]
      exact Nat.sub_pos_of_lt hlt
    have hdiff : Int.ofNat a.toNat - Int.ofNat b.toNat = -Int.ofNat d := by
      have hsub : Int.ofNat d = Int.ofNat b.toNat - Int.ofNat a.toNat := by
        dsimp [d]
        exact Int.ofNat_sub (le_of_lt hlt)
      rw [hsub]
      ring
    have hwrapEq : UInt256.size + a.toNat - b.toNat = UInt256.size - d := by
      dsimp [d]
      omega
    have hdLe : d ≤ UInt256.size := by
      dsimp [d]
      exact Nat.le_trans (Nat.sub_le _ _) (Nat.le_of_lt b.val.isLt)
    have hwrapLt : UInt256.size + a.toNat - b.toNat < UInt256.size := by
      rw [hwrapEq]
      exact Nat.sub_lt (by norm_num [UInt256.size]) hdpos
    have hwrapNonneg : (0 : Int) ≤ Int.ofNat (UInt256.size + a.toNat - b.toNat) :=
      Int.natCast_nonneg _
    have hwrapLtInt : Int.ofNat (UInt256.size + a.toNat - b.toNat) < wordModulus := by
      rw [wordModulus]
      norm_num [UInt256.size] at hwrapLt ⊢
      exact_mod_cast hwrapLt
    have hwrapMod : Int.ofNat (UInt256.size + a.toNat - b.toNat) % wordModulus =
        Int.ofNat (UInt256.size + a.toNat - b.toNat) :=
      Int.emod_eq_of_lt hwrapNonneg hwrapLtInt
    have hrepr : -Int.ofNat d =
        Int.ofNat (UInt256.size + a.toNat - b.toNat) - Int.ofNat UInt256.size := by
      rw [hwrapEq]
      have hcast : Int.ofNat (UInt256.size - d) =
          Int.ofNat UInt256.size - Int.ofNat d :=
        Int.ofNat_sub hdLe
      rw [hcast]
      ring
    rw [hdiff, hrepr]
    rw [Int.sub_emod]
    have hsizeMod : (Int.ofNat UInt256.size) % wordModulus = 0 := by
      rw [wordModulus]
      norm_num [UInt256.size]
    rw [hsizeMod]
    simp
    rw [usub_toNat_underflow (a := a) (b := b) hlt]
    exact hwrapMod

theorem evalExpr_tendPayDelta {evm : EVM.State} {locals : Store} {I : ExecutionEnv}
    (hid : locals.get? "id" = some (.int (Int.ofNat (tendId I).toNat)))
    (hbidLocal : locals.get? "bid" = some (.int (Int.ofNat (tendBid I).toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))) =
        .ok (.int (Int.ofNat
          (UInt256.sub (tendBid I)
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (bidBaseOfWord (tendId I)))).toNat)) := by
  have hbid := evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "bid")
    (value := tendBid I) hbidLocal
  have hstored := evalExpr_bidBid_of_get_id_evm (evm := evm) (locals := locals)
    (id := tendId I) hid hbids
  rw [wrap256]
  simp only [evalExpr?, hbid, hstored, EvalResult.bind, bind, pure]
  change (if wordModulus = 0 then EvalResult.revert else
      .ok (Value.int ((Int.ofNat (tendBid I).toNat -
        Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (bidBaseOfWord (tendId I))).toNat) % wordModulus))) =
    .ok (Value.int (Int.ofNat
      (UInt256.sub (tendBid I)
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (bidBaseOfWord (tendId I)))).toNat))
  rw [if_neg (by norm_num [wordModulus]), intModWord_sub_toNat]

theorem evalExprs_tendPayMoveArgs_ofLocals {evm : EVM.State} {locals : Store}
    {I : ExecutionEnv}
    (hid : locals.get? "id" = some (.int (Int.ofNat (tendId I).toNat)))
    (hbidLocal : locals.get? "bid" = some (.int (Int.ofNat (tendBid I).toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExprs? config { contract := contract, locals := locals } evm
      [sender, .storage (bidsF (.var "id") "gal"),
        wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))] =
        .ok (tendPayMoveArgValsOf evm I) := by
  have hgal := evalExpr_bidGal_of_get_id_evm (evm := evm) (locals := locals)
    (id := tendId I) hid hbids
  have hdelta := evalExpr_tendPayDelta (evm := evm) (locals := locals) (I := I)
    hid hbidLocal hbids
  simp only [evalExprs?, evalExpr?, envValue, sender, hgal, hdelta, tendPayMoveArgValsOf,
    EvalResult.bind, bind, pure]

theorem evalExpr_tendNow48 {evm : EVM.State} {locals : Store} {I : ExecutionEnv}
    (hts : evm.executionEnv.header.timestamp = I.header.timestamp) :
    evalExpr? config { contract := contract, locals := locals } evm now48 =
      .ok (.int (Int.ofNat (tendNow48 I).toNat)) := by
  have hmod :
      (Int.ofNat (tendNow I).toNat) % uint48Modulus =
        Int.ofNat (tendNow48 I).toNat := by
    calc
      (Int.ofNat (tendNow I).toNat) % uint48Modulus =
          Int.ofNat ((tendNow I).toNat % 2 ^ 48) := by
          rw [uint48Modulus]
          exact (Int.natCast_mod (tendNow I).toNat (2 ^ 48)).symm
      _ = Int.ofNat (tendNow48 I).toNat := by
          rw [← uint48Mask_toNat_mod (tendNow I)]
  rw [now48, wrap48]
  simp only [evalExpr?, envValue, hts, EvalResult.bind, bind, pure]
  change evalBinaryOp? .mod (Value.int (Int.ofNat (tendNow I).toNat))
      (Value.int uint48Modulus) =
    .ok (Value.int (Int.ofNat (tendNow48 I).toNat))
  change (if uint48Modulus = 0 then EvalResult.revert else
      .ok (Value.int ((Int.ofNat (tendNow I).toNat) % uint48Modulus))) =
    .ok (Value.int (Int.ofNat (tendNow48 I).toNat))
  rw [if_neg (by norm_num [uint48Modulus]), hmod]

theorem evalExpr_tendTtl {evm : EVM.State} {locals : Store} {I : ExecutionEnv}
    (httl : locals.get? "ttl" = none)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage ttlRef) =
      .ok (.int (Int.ofNat (tendTtlWord evm.accountMap I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint48Int)
    (er := ({ base := "ttl", steps := [] } : EvaledStorageRef))
    (loc := uint48Loc ⟨5⟩ ⟨0, by decide⟩ (by decide))
    (hbase := httl)
    (her := by simp [ttlRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
      pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint48St])
    (hloc := by rfl)]
  simpa [tendTtlWord, flipperUint48Offset0Word, flipperSlotWord, solcSlotWord,
    Solm.EVM.storageLoad, howner] using
    congrArg EvalResult.ok (flipperStorageLocLoad_uint48_offset0 evm ⟨5⟩)

theorem evalExpr_tendTicNew {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store} (httl : locals.get? "ttl" = none)
    (hts : evm.executionEnv.header.timestamp = I.header.timestamp)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExpr? config { contract := contract, locals := locals } evm
      (wrap48 (.binary .add now48 (.storage ttlRef))) =
        .ok (.int (Int.ofNat (tendTicNewWord evm.accountMap I).toNat)) := by
  have hnow := evalExpr_tendNow48 (evm := evm) (locals := locals) (I := I) hts
  have httlEval := evalExpr_tendTtl (evm := evm) (locals := locals) (I := I) httl howner
  rw [wrap48]
  simp only [evalExpr?, hnow, httlEval, EvalResult.bind, bind, pure]
  change (if uint48Modulus = 0 then EvalResult.revert else
      .ok (Value.int (((Int.ofNat (tendNow48 I).toNat) +
        Int.ofNat (tendTtlWord evm.accountMap I).toNat) % uint48Modulus))) =
    .ok (Value.int (Int.ofNat (tendTicNewWord evm.accountMap I).toNat))
  have hmod :
      ((Int.ofNat (tendNow48 I).toNat) + Int.ofNat (tendTtlWord evm.accountMap I).toNat) %
          uint48Modulus =
        Int.ofNat (tendTicNewWord evm.accountMap I).toNat := by
    calc
      ((Int.ofNat (tendNow48 I).toNat) + Int.ofNat (tendTtlWord evm.accountMap I).toNat) %
          uint48Modulus =
          Int.ofNat (((tendNow48 I).toNat +
            (tendTtlWord evm.accountMap I).toNat) % 2 ^ 48) := by
          rw [show (Int.ofNat (tendNow48 I).toNat +
              Int.ofNat (tendTtlWord evm.accountMap I).toNat) =
              Int.ofNat ((tendNow48 I).toNat + (tendTtlWord evm.accountMap I).toNat) by simp]
          rw [uint48Modulus]
          exact (Int.natCast_mod
            ((tendNow48 I).toNat + (tendTtlWord evm.accountMap I).toNat) (2 ^ 48)).symm
      _ = Int.ofNat (tendTicNewWord evm.accountMap I).toNat := by
          rw [← tendTicNewWord_toNat evm.accountMap I]
  rw [if_neg (by norm_num [uint48Modulus]), hmod]

theorem evalExpr_tendTicNewGeNow_true {evm : EVM.State} {I : ExecutionEnv}
    (hts : evm.executionEnv.header.timestamp = I.header.timestamp)
    (hfit : (tendNow48 I).toNat + (tendTtlWord evm.accountMap I).toNat < 2 ^ 48) :
    evalExpr? config { contract := contract, locals := tendLocalsWithTic evm.accountMap I } evm
      (.binary .ge (.var "tic_") now48) = .ok (.bool true) := by
  have htic := evalExpr_varUInt256
    (evm := evm) (locals := tendLocalsWithTic evm.accountMap I)
    (name := "tic_") (value := tendTicNewWord evm.accountMap I)
    (tendLocalsWithTic_get_tic evm.accountMap I)
  have hnow := evalExpr_tendNow48
    (evm := evm) (locals := tendLocalsWithTic evm.accountMap I) (I := I) hts
  have hle : (tendNow48 I).toNat ≤ (tendTicNewWord evm.accountMap I).toNat :=
    tendTicNewWord_ge_now48_noOverflow hfit
  have hnot :
      ¬ Int.ofNat (tendTicNewWord evm.accountMap I).toNat <
        Int.ofNat (tendNow48 I).toNat := by
    intro hbad
    exact (not_lt.mpr hle) (Int.ofNat_lt.mp hbad)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [htic, hnow]
  simp [evalBinaryOp?, hle]
  all_goals decide

theorem evalExpr_tendTicVarWithTic {evm : EVM.State} {σ : AccountMap}
    {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := tendLocalsWithTic σ I } evm
      (.var "tic_") = .ok (.int (Int.ofNat (tendTicNewWord σ I).toNat)) := by
  exact evalExpr_varUInt256 (evm := evm) (locals := tendLocalsWithTic σ I)
    (name := "tic_") (value := tendTicNewWord σ I) (tendLocalsWithTic_get_tic σ I)

theorem evalExpr_tendTicNewGeNow_true_from {evm : EVM.State} {σpre σtic : AccountMap}
    {I : ExecutionEnv}
    (hts : evm.executionEnv.header.timestamp = I.header.timestamp)
    (hfit : (tendNow48 I).toNat + (tendTtlWord σtic I).toNat < 2 ^ 48) :
    evalExpr? config { contract := contract, locals := tendLocalsWithTicFrom σpre σtic I }
      evm (.binary .ge (.var "tic_") now48) = .ok (.bool true) := by
  have htic := evalExpr_varUInt256
    (evm := evm) (locals := tendLocalsWithTicFrom σpre σtic I)
    (name := "tic_") (value := tendTicNewWord σtic I)
    (tendLocalsWithTicFrom_get_tic σpre σtic I)
  have hnow := evalExpr_tendNow48
    (evm := evm) (locals := tendLocalsWithTicFrom σpre σtic I) (I := I) hts
  have hle : (tendNow48 I).toNat ≤ (tendTicNewWord σtic I).toNat :=
    tendTicNewWord_ge_now48_noOverflow hfit
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [htic, hnow]
  simp [evalBinaryOp?, hle]
  all_goals decide

theorem evalExpr_tendTicVarWithTicFrom {evm : EVM.State} {σpre σtic : AccountMap}
    {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := tendLocalsWithTicFrom σpre σtic I }
      evm (.var "tic_") = .ok (.int (Int.ofNat (tendTicNewWord σtic I).toNat)) := by
  exact evalExpr_varUInt256 (evm := evm)
    (locals := tendLocalsWithTicFrom σpre σtic I)
    (name := "tic_") (value := tendTicNewWord σtic I)
    (tendLocalsWithTicFrom_get_tic σpre σtic I)

theorem evalExpr_tendIncreaseRequire_true_of_ge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hge : (tendBegBidWord σ I).toNat ≤ (tendBidOneWord I).toNat) :
    evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .or
        (.binary .ge (.var "bidOne") (.var "begBid"))
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab")))) =
        .ok (.bool true) := by
  have hbidOne :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := tendLocalsBidOneBegBid σ I) (name := "bidOne")
      (value := tendBidOneWord I) (tendLocalsBidOneBegBid_get_bidOne σ I)
  have hbegBid :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := tendLocalsBidOneBegBid σ I) (name := "begBid")
      (value := tendBegBidWord σ I) (tendLocalsBidOneBegBid_get_begBid σ I)
  exact evalExpr_or_true_left (evalExpr_ge_uint256_true hbidOne hbegBid hge)

theorem evalExpr_tendIncreaseRequire_true_of_tab {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlt : (tendBidOneWord I).toNat < (tendBegBidWord σ I).toNat)
    (htab : tendBid I = bidTabWord (tendId I) σ I) :
    evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .or
        (.binary .ge (.var "bidOne") (.var "begBid"))
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab")))) =
        .ok (.bool true) := by
  have hbidOne :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := tendLocalsBidOneBegBid σ I) (name := "bidOne")
      (value := tendBidOneWord I) (tendLocalsBidOneBegBid_get_bidOne σ I)
  have hbegBid :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := tendLocalsBidOneBegBid σ I) (name := "begBid")
      (value := tendBegBidWord σ I) (tendLocalsBidOneBegBid_get_begBid σ I)
  have hbid :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := tendLocalsBidOneBegBid σ I) (name := "bid")
      (value := tendBid I) (tendLocalsBidOneBegBid_get_bid σ I)
  have htabEval := evalExpr_bidTab_of_get_id (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (locals := tendLocalsBidOneBegBid σ I) (id := tendId I)
    (tendLocalsBidOneBegBid_get_id σ I) (tendLocalsBidOneBegBid_get_bids σ I)
  have hleft :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState cA gh bl σ σ₀ g A I)
        (.binary .ge (.var "bidOne") (.var "begBid")) = .ok (.bool false) :=
    evalExpr_ge_uint256_false hbidOne hbegBid hlt
  have hright :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState cA gh bl σ σ₀ g A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true) := by
    apply evalExpr_eq_int_true hbid htabEval
    rw [htab]
  exact evalExpr_or_false_right hleft hright

theorem evalExpr_tendCallerNeGuy_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcaller : solcSourceWord I = bidGuyWord (tendId I) σ I) :
    evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) =
        .ok (.bool false) := by
  have hsender :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState cA gh bl σ σ₀ g A I) sender = .ok (.address I.source) := by
    simp [sender, evalExpr?, envValue, initState]
    rfl
  have hguy := evalExpr_bidGuy_of_get_id (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (locals := tendLocalsBidOneBegBid σ I) (id := tendId I)
    (tendLocalsBidOneBegBid_get_id σ I) (tendLocalsBidOneBegBid_get_bids σ I)
  have haddr : AccountAddress.ofNat (bidGuyWord (tendId I) σ I).toNat = I.source := by
    rw [← hcaller, solcSource_ofNat]
  simp [evalExpr?, EvalResult.bind, bind, hsender, hguy, evalBinaryOp?, haddr]

theorem flipperTendX_skipRefund {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hcaller : solcSourceWord I = bidGuyWord (tendId I) σ I)
    (h : RD flipperBytecode I g s0 ⟨3486⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3686⟩
      [tendBid I, tendLot I, tendId I, ret, sel]
      (twoWordHashMem (tendId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd3504 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tendId I) mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (twoWordHashMem (tendId I) ⟨1⟩ mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (tendId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by simpa [bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (tendId I) hmemSize)
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k3505, C3505, rd3505raw⟩ := rd3504.sload (by native_decide) (by evm_ov)
  have rd3505 : RD flipperBytecode I g s0 ⟨3505⟩
      [bidPackedWord (tendId I) σ I, tendBid I, tendLot I, tendId I, ret, sel]
      (twoWordHashMem (tendId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3505 C3505 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (tendId I) = bidPackedSlotOfWord (tendId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (tendId I)))
    simpa [bidPackedWord, flipperSlotWord, hslotAdd] using rd3505raw
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have rd3516raw := evm_run rd3505 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  obtain ⟨k3516, C3516, rd3516⟩ : ∃ k' C',
      RD flipperBytecode I g s0 ⟨3516⟩
        [UInt256.eq (solcSourceWord I) (bidGuyWord (tendId I) σ I), tendBid I,
          tendLot I, tendId I, ret, sel]
        (twoWordHashMem (tendId I) ⟨1⟩ mem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by
      simpa [bidGuyWord, bidPackedWord, flipperAddressReturnWord, hmask160, u256_land_comm]
        using rd3516raw⟩
  have heq : UInt256.eq (solcSourceWord I) (bidGuyWord (tendId I) σ I) = ⟨1⟩ := by
    rw [hcaller]
    exact u256_eq_refl _
  rw [heq] at rd3516
  exact ⟨_, _, evm_run rd3516 with [
    raw push2 ⟨3686⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]⟩

theorem flipperTendX_toPayExtcodesizeGuard {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem rdata : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD flipperBytecode I g s0 ⟨3686⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3784⟩
      (flipperVatTargetWord σ I :: flipperVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨100⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
        flipperVatTargetWord σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (tendVatPayCallMem mem σ I) (UInt256.ofNat 8) rdata (cA, σ) k' C' := by
  let rawVat := flipperSlotWord ⟨2⟩ σ I
  let rawGal := flipperSlotWord (bidSlotOfWord (tendId I) ⟨4⟩) σ I
  let base := solcMappingSlot ⟨1⟩ (tendId I)
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hvatClean : UInt256.land rawVat solcAddrMask = flipperVatTargetWord σ I := by
    simp [rawVat, flipperVatTargetWord, flipperAddressReturnWord]
  have hgalCleanLeft :
      UInt256.land solcAddrMask rawGal = bidGalWord (tendId I) σ I := by
    simpa [rawGal, bidGalWord, flipperAddressReturnWord] using
      (u256_land_comm solcAddrMask rawGal)
  have hmload64Hash :
      (if (⟨64⟩ : UInt256).toNat ≥ (tendPayHashMem mem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((tendPayHashMem mem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [tendPayHashMem_size I hmemSize]; decide) (by decide)
      (tendPayHashMem_read64 I hmemSize hmemRead64)
  have hmload64Pay :
      (if (⟨64⟩ : UInt256).toNat ≥ (tendVatPayCallMem mem σ I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((tendVatPayCallMem mem σ I).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [tendVatPayCallMem_size σ I hmemSize]; decide) (by decide)
      (tendVatPayCallMem_read64 σ I hmemSize hmemRead64)
  have rd3689 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k3690, C3690, rd3690raw⟩ := rd3689.sload (by native_decide) (by evm_ov)
  have rd3690 : RD flipperBytecode I g s0 ⟨3690⟩
      [rawVat, tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) rdata (cA, σ) k3690 C3690 := by
    simpa [rawVat, flipperSlotWord, solcSlotWord] using rd3690raw
  have rd3709pre := evm_run rd3690 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tendId I) mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (tendPayHashMem mem I) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by
        dsimp [tendPayHashMem, twoWordHashMem, wordAt32Mem, wordAt0Mem]
        rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw keccak256 0 base (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by simpa [base, tendPayHashMem, bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (tendId I) hmemSize)
      (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k3711, C3711, rd3711raw⟩ := rd3709pre.sload (by native_decide) (by evm_ov)
  have rd3711 : RD flipperBytecode I g s0 ⟨3711⟩
      (rawGal :: ⟨4⟩ :: base :: ⟨64⟩ :: ⟨0⟩ :: rawVat :: tendBid I ::
        tendLot I :: tendId I :: ret :: sel :: [])
      (tendPayHashMem mem I) (UInt256.ofNat 3) rdata (cA, σ) k3711 C3711 := by
    have hslotAdd :
        (⟨4⟩ : UInt256) + base = bidSlotOfWord (tendId I) ⟨4⟩ := by
      simpa [base, bidSlotOfWord, bidBaseOfWord] using
        (u256_add_comm (⟨4⟩ : UInt256) (bidBaseOfWord (tendId I)))
    simpa [rawGal, flipperSlotWord, hslotAdd] using rd3711raw
  have rd3712pre := rd3711.swap2 (by native_decide) (by evm_ov)
  obtain ⟨k3713, C3713, rd3713raw⟩ := rd3712pre.sload (by native_decide) (by evm_ov)
  have rd3713 : RD flipperBytecode I g s0 ⟨3713⟩
      (bidBidWord (tendId I) σ I :: ⟨4⟩ :: rawGal :: ⟨64⟩ :: ⟨0⟩ ::
        rawVat :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (tendPayHashMem mem I) (UInt256.ofNat 3) rdata (cA, σ) k3713 C3713 := by
    simpa [bidBidWord, bidBaseOfWord, flipperSlotWord, base] using rd3713raw
  let mem1 := writeWord (tendPayHashMem mem I) 128 yankVatMoveSelectorWord
  let mem2 := writeWord mem1 132 (solcSourceWord I)
  let mem3 := writeWord mem2 164 (bidGalWord (tendId I) σ I)
  have rd3724 := evm_run rd3713 with [
    raw dup4 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64Hash (by decide) (by evm_ov),
    raw push4 ⟨3140843579⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 mem1 (UInt256.ofNat 5)
      (by native_decide) mem_cost (by
        dsimp [mem1, yankVatMoveSelectorWord, Reasoning.Theory.writeWord]
        rfl) (by decide) (by evm_ov)]
  have rd3732 := evm_run rd3724 with [
    raw caller (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw mstore 3 mem2 (UInt256.ofNat 6)
      (by native_decide) mem_cost (by
        dsimp [mem1, mem2, solcSourceWord, Reasoning.Theory.writeWord]
        rfl) (by decide) (by evm_ov)]
  have rd3748 := evm_run rd3732 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 mem3 (UInt256.ofNat 7)
      (by native_decide) mem_cost (by
        rw [hmask160, hgalCleanLeft]
        dsimp [mem2, mem3, Reasoning.Theory.writeWord]
        rfl) (by decide) (by evm_ov)]
  have rd3755 := evm_run rd3748 with [
    raw dup7 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (tendVatPayCallMem mem σ I) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by
        dsimp [mem1, mem2, mem3, tendVatPayCallMem, Reasoning.Theory.writeWord,
          writeCascade]
        rfl) (by decide) (by evm_ov)]
  have rd3784 := evm_run rd3755 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Pay (by decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push4 ⟨3140843579⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
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
  rw [hmask160, hvatClean] at rd3784
  exact ⟨_, _, by simpa using rd3784⟩

theorem flipperTendX_payNoCode {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem rdata : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) = ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨3686⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨_, _, rd3784⟩ := flipperTendX_toPayExtcodesizeGuard
    hmemSize hmemRead64 h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨3784⟩) (okPc := ⟨3796⟩) rd3784
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem flipperTendX_toPayCall {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem rdata : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨3686⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    ∃ gasWord k' C', RD flipperBytecode I g s0 ⟨3799⟩
      (gasWord :: flipperVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
        flipperVatTargetWord σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (tendVatPayCallMem mem σ I) (UInt256.ofNat 8) rdata
      (cA, σ) k' C' := by
  obtain ⟨_, _, rd3784⟩ := flipperTendX_toPayExtcodesizeGuard
    hmemSize hmemRead64 h
  obtain ⟨gasWord, k3799, C3799, rd3799⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨3784⟩) (okPc := ⟨3796⟩) rd3784
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k3799, C3799, by simpa using rd3799⟩

theorem flipperTendX_payPostCall
    {cA0 gh bl σbase σ₀ A I} {g : UInt256}
    {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap} {Acur : Substate}
    {k C : ℕ} {ret sel : UInt256} {mem out0 : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (h : RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨3686⟩
      [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) out0 (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨3800⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: ⟨3140843579⟩ ::
          flipperVatTargetWord σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
        (tendVatPayCallMem mem σ I) (UInt256.ofNat 8) out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        ({ initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ, substate := Acur, createdAccounts := cA })
        (EVM.address (flipperVatAddress σ I)) "move" 0
        (tendPayMoveArgValsOf
          ({ initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ, substate := Acur, createdAccounts := cA }) I)
        (z,
          { { initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ, substate := Acur, createdAccounts := cA } with
            accountMap := σ', substate := A', createdAccounts := cA' },
          out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd3799⟩ :=
    flipperTendX_toPayCall hmemSize hmemRead64 hcodeSize h
  obtain ⟨cA', σ', z, out, A_in, callGas, k3800, C3800, hΘpack, rd3800raw,
      houtsz⟩ :=
    RD.call rd3799 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k3800, C3800, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
      native_decide
    have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
      rfl
    have rd3800 : RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨3800⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: ⟨3140843579⟩ ::
          flipperVatTargetWord σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
        (out.write 0 (tendVatPayCallMem mem σ I) 128
          (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 8) out (cA', σ') k3800 C3800 :=
      haw ▸ rd3800raw
    rw [hmin, byteArray_write_len_zero] at rd3800
    exact rd3800
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := flipperVatTargetWord σ I)
      (mem := tendVatPayCallMem mem σ I) (inOff := ⟨128⟩) (inSize := ⟨100⟩)
      (fun hdepthEq => by
        have hEq : I.depth = (1024 : Fin 1025) := by
          simpa [initState] using hdepthEq
        exact absurd hdepth (by rw [hEq]; decide))
      (flipperVatEvmAddress_eq_target_of_accountMapEquiv (accountMapEquiv.refl σ))
      ?_ ?_
    · simpa [tendPayMoveArgValsOf, initState, flipperSlotWord, solcSlotWord,
        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        bidGalWord, bidSlotOfWord, bidBidWord, bidBaseOfWord, flipperAddressReturnWord]
        using tendVatPayCallMem_encode σ I hmemSize
    · simpa [initState, hperm] using hΘ

theorem flipperTendX_payCallFailure {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {aw target id ret sel selector bid lot : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode I g s0 ⟨3800⟩
      (⟨0⟩ :: ⟨228⟩ :: selector :: target :: bid :: lot :: id :: ret :: sel :: [])
      mem aw out acc k C)
    (houtsz : out.size < UInt256.size) :
    RDrev flipperBytecode g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨3800⟩) (okPc := ⟨3816⟩) h
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    houtsz (by simp)

theorem flipperTendX_payCallSuccessToStoreStart {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {aw target id ret sel selector bid lot : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode I g s0 ⟨3800⟩
      (⟨1⟩ :: ⟨228⟩ :: selector :: target :: bid :: lot :: id :: ret :: sel :: [])
      mem aw out acc k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3820⟩
      (target :: bid :: lot :: id :: ret :: sel :: []) mem aw out acc k' C' := by
  obtain ⟨_, _, rd3817⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨3800⟩) (okPc := ⟨3816⟩) h
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp)
  have rd3820 := evm_run rd3817 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd3820⟩

theorem flipperTendDecodePushMask3847 :
    decode flipperBytecode (⟨3847⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  native_decide

theorem flipperTendDecodePushMask3880 :
    decode flipperBytecode (⟨3880⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  native_decide

theorem flipperTendDecodePushMask3897 :
    decode flipperBytecode (⟨3897⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  native_decide

theorem flipperTendDecodePushMask6276 :
    decode flipperBytecode (⟨6276⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  native_decide

theorem flipperTendX_storeBidToAdd48 {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {target ret sel : UInt256}
    (hperm : I.perm = true)
    (hmemSize : 64 ≤ mem.size)
    (h : RD flipperBytecode I g s0 ⟨3820⟩
      [target, tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 8) out (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨6272⟩
      [tendTtlWord (tendAfterBidMap σ I) I, tendNow I, ⟨3859⟩,
        tendBid I, tendLot I, tendId I, ret, sel]
      (twoWordHashMem (tendId I) ⟨1⟩ mem) (UInt256.ofNat 8) out
      (cA, tendAfterBidMap σ I) k' C' := by
  let mem1 := wordAt0Mem (tendId I) mem
  let mem2 := twoWordHashMem (tendId I) ⟨1⟩ mem
  have rd3836 := evm_run h with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 mem1 (UInt256.ofNat 8) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 mem2 (UInt256.ofNat 8) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (tendId I)) (UInt256.ofNat 8)
      (by native_decide) mem_cost
      (by
        simpa [mem2, bidBaseOfWord] using
          tendTwoWordHashMem_solcMappingSlot_of_size_ge ⟨1⟩ (tendId I) hmemSize)
      (by decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k3837, C3837, rd3837raw⟩ := rd3836.sstore hperm (by native_decide) (by evm_ov)
  have rd3837 : RD flipperBytecode I g s0 ⟨3837⟩
      [target, tendBid I, tendLot I, tendId I, ret, sel]
      mem2 (UInt256.ofNat 8) out (cA, tendAfterBidMap σ I) k3837 C3837 := by
    simpa [mem2, tendAfterBidMap, bidBaseOfWord] using rd3837raw
  have rd3840 := evm_run rd3837 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k3841, C3841, rd3841raw⟩ := rd3840.sload (by native_decide) (by evm_ov)
  have rd3841 : RD flipperBytecode I g s0 ⟨3841⟩
      [flipperSlotWord ⟨5⟩ (tendAfterBidMap σ I) I,
        tendBid I, tendLot I, tendId I, ret, sel]
      mem2 (UInt256.ofNat 8) out (cA, tendAfterBidMap σ I) k3841 C3841 := by
    simpa [flipperSlotWord, solcSlotWord] using rd3841raw
  have rd3858 := evm_run rd3841 with [
    raw push2 ⟨3859⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw timestamp (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperTendDecodePushMask3847
      (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push2 ⟨6272⟩ (by native_decide) (by evm_ov)]
  have httlRaw :
      UInt256.land uint48Mask (flipperSlotWord ⟨5⟩ (tendAfterBidMap σ I) I) =
        tendTtlWord (tendAfterBidMap σ I) I := by
    simpa [tendTtlWord, flipperUint48Offset0Word, u256_land_comm]
  rw [httlRaw] at rd3858
  exact ⟨_, _, rd3858.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem flipperTendX_add48Success {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {ret sel : UInt256}
    (hfit : (tendNow48 I).toNat + (tendTtlWord σ I).toNat < 2 ^ 48)
    (h : RD flipperBytecode I g s0 ⟨6272⟩
      [tendTtlWord σ I, tendNow I, ⟨3859⟩, tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 8) out (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3859⟩
      [tendNow I + tendTtlWord σ I, tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 8) out (cA, σ) k' C' := by
  have rd6289 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperTendDecodePushMask6276
      (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov)]
  have hltWord :
      UInt256.lt (tendTicNewWord σ I) (tendNow48 I) = ⟨0⟩ :=
    ult_zero (tendTicNewWord_ge_now48_noOverflow hfit)
  have hltRaw :
      UInt256.lt
        (UInt256.land (tendNow I + tendTtlWord σ I) uint48Mask)
        (UInt256.land (tendNow I) uint48Mask) = ⟨0⟩ := by
    simpa [tendNow48, tendTicNewWord_fullTimestampAdd] using hltWord
  rw [hltRaw] at rd6289
  have rd6290 := rd6289.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6290
  have rd6299 := rd6290.push2 ⟨6299⟩ (by native_decide) (by evm_ov)
    |>.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd6299 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]⟩

theorem flipperTendX_add48Overflow {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {ret sel : UInt256}
    (hover : 2 ^ 48 ≤ (tendNow48 I).toNat + (tendTtlWord σ I).toNat)
    (h : RD flipperBytecode I g s0 ⟨6272⟩
      [tendTtlWord σ I, tendNow I, ⟨3859⟩, tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 8) out (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  have rd6289 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperTendDecodePushMask6276
      (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov)]
  have hltWord :
      UInt256.lt (tendTicNewWord σ I) (tendNow48 I) = ⟨1⟩ :=
    ult_one (tendTicNewWord_lt_now48_overflow hover)
  have hltRaw :
      UInt256.lt
        (UInt256.land (tendNow I + tendTtlWord σ I) uint48Mask)
        (UInt256.land (tendNow I) uint48Mask) = ⟨1⟩ := by
    simpa [tendNow48, tendTicNewWord_fullTimestampAdd] using hltWord
  rw [hltRaw] at rd6289
  have rd6290 := rd6289.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd6290
  have rd6295 := rd6290.push2 ⟨6299⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rd6295 (by native_decide) (by native_decide)
    (by native_decide) (by evm_ov)

theorem flipperTendX_storeTicReturn {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {sel : UInt256}
    (hperm : I.perm = true)
    (hmemSize : 64 ≤ mem.size)
    (h : RD flipperBytecode I g s0 ⟨3859⟩
      [tendNow I + tendTtlWord σ I, tendBid I, tendLot I, tendId I, ⟨323⟩, sel]
      mem (UInt256.ofNat 8) out (cA, σ) k C) :
    RDret flipperBytecode g s0 (cA, tendStoreTicMap σ I) ByteArray.empty := by
  let mem1 := wordAt0Mem (tendId I) mem
  let mem2 := twoWordHashMem (tendId I) ⟨1⟩ mem
  have rd3878 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw mstore 0 mem1 (UInt256.ofNat 8) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 mem2 (UInt256.ofNat 8) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (tendId I)) (UInt256.ofNat 8)
      (by native_decide) mem_cost
      (by
        simpa [mem2, bidBaseOfWord] using
          tendTwoWordHashMem_solcMappingSlot_of_size_ge ⟨1⟩ (tendId I) hmemSize)
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k3880, C3880, rd3880raw⟩ := rd3878.sload (by native_decide) (by evm_ov)
  have rd3880 : RD flipperBytecode I g s0 ⟨3880⟩
      [flipperSlotWord (bidPackedSlotOfWord (tendId I)) σ I,
        bidPackedSlotOfWord (tendId I), tendBid I, tendLot I,
        tendNow I + tendTtlWord σ I, ⟨323⟩, sel]
      mem2 (UInt256.ofNat 8) out (cA, σ) k3880 C3880 := by
    have hslotAdd :
        ⟨2⟩ + bidBaseOfWord (tendId I) = bidPackedSlotOfWord (tendId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (tendId I)))
    simpa [mem2, bidPackedSlotOfWord, flipperSlotWord, hslotAdd] using rd3880raw
  have rd3917 := evm_run rd3880 with [
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperTendDecodePushMask3880
      (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperTendDecodePushMask3897
      (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  have hstoredRaw := tendStoredTicRuntimeWord σ I
  rw [hstoredRaw] at rd3917
  obtain ⟨_, _, rd3918⟩ := rd3917.sstore hperm (by native_decide) (by evm_ov)
  have rd3920 := evm_run rd3918 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd324 := rd3920.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd324 (by native_decide) (by evm_ov)

end Benchmarks.Dss.Flipper
