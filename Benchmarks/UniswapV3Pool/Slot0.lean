import Benchmarks.UniswapV3Pool.Common
import Benchmarks.UniswapV3Pool.TickSpacing
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

abbrev slot0SlotWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I ⟨0⟩

abbrev slot0ShiftBytes (n : Nat) : UInt256 :=
  UInt256.ofNat (256 ^ n)

abbrev slot0Uint160Mask : UInt256 := UInt256.ofNat (2 ^ 160 - 1)
abbrev slot0Uint24Mask : UInt256 := UInt256.ofNat (2 ^ 24 - 1)
abbrev slot0Uint16Mask : UInt256 := UInt256.ofNat (2 ^ 16 - 1)
abbrev slot0Uint8Mask : UInt256 := UInt256.ofNat (2 ^ 8 - 1)

abbrev slot0SqrtPriceX96Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (slot0SlotWord σ I) slot0Uint160Mask

abbrev slot0TickRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 20)) slot0Uint24Mask

abbrev slot0TickReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.signextend ⟨2⟩ (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 20))

abbrev slot0ObservationIndexWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 23)) slot0Uint16Mask

abbrev slot0ObservationCardinalityWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 25)) slot0Uint16Mask

abbrev slot0ObservationCardinalityNextWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 27)) slot0Uint16Mask

abbrev slot0FeeProtocolWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 29)) slot0Uint8Mask

abbrev slot0UnlockedRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 30)) slot0Uint8Mask

abbrev slot0BoolReturnWord (u : UInt256) : UInt256 :=
  UInt256.isZero (UInt256.isZero u)

abbrev slot0ReturnValues (σ : AccountMap) (I : ExecutionEnv) : List Value :=
  [ .int (Int.ofNat (slot0SqrtPriceX96Word σ I).toNat),
    wordToElem (.int int24Int) (slot0TickRawWord σ I),
    .int (Int.ofNat (slot0ObservationIndexWord σ I).toNat),
    .int (Int.ofNat (slot0ObservationCardinalityWord σ I).toNat),
    .int (Int.ofNat (slot0ObservationCardinalityNextWord σ I).toNat),
    .int (Int.ofNat (slot0FeeProtocolWord σ I).toNat),
    wordToElem .bool (slot0UnlockedRawWord σ I) ]

theorem slot0Uint160Mask_bound (w : UInt256) :
    (UInt256.land w slot0Uint160Mask).toNat < EVM.twoPow 160 := by
  rw [show slot0Uint160Mask = solcAddrMask by native_decide]
  simpa [EVM.addressModulus] using solcAddrMask_result_canonical w

theorem slot0Uint160Mask_clean {w : UInt256} (hcanon : w.toNat < EVM.twoPow 160) :
    UInt256.land w slot0Uint160Mask = w := by
  rw [show slot0Uint160Mask = solcAddrMask by native_decide]
  exact solcAddrMask_clean (by simpa [EVM.addressModulus] using hcanon)

theorem slot0Uint24Mask_toNat :
    slot0Uint24Mask.toNat = 2 ^ 24 - 1 := by
  exact ulit_toNat' _ (by norm_num [UInt256.size])

theorem slot0Uint16Mask_toNat :
    slot0Uint16Mask.toNat = 2 ^ 16 - 1 := by
  exact ulit_toNat' _ (by norm_num [UInt256.size])

theorem slot0Uint16Mask_bound (w : UInt256) :
    (UInt256.land w slot0Uint16Mask).toNat < EVM.twoPow 16 := by
  rw [uland_toNat, slot0Uint16Mask_toNat]
  exact lt_of_le_of_lt (nat_land_le_right _ _) (by norm_num [EVM.twoPow])

theorem slot0Uint16Mask_clean {w : UInt256} (hcanon : w.toNat < EVM.twoPow 16) :
    UInt256.land w slot0Uint16Mask = w := by
  apply u256_inj
  show Nat.land w.toNat slot0Uint16Mask.toNat % EVM.twoPow 256 = w.toNat
  rw [slot0Uint16Mask_toNat, nat_land_mask_eq_mod]
  rw [show EVM.twoPow 16 = 2 ^ 16 from rfl] at hcanon
  rw [Nat.mod_eq_of_lt hcanon]
  exact Nat.mod_eq_of_lt w.val.isLt

theorem slot0Uint16Mask_clean_left {w : UInt256} (hcanon : w.toNat < EVM.twoPow 16) :
    UInt256.land slot0Uint16Mask w = w := by
  rw [u256_land_comm slot0Uint16Mask w]
  exact slot0Uint16Mask_clean hcanon

theorem slot0Uint8Mask_toNat :
    slot0Uint8Mask.toNat = 2 ^ 8 - 1 := by
  exact ulit_toNat' _ (by norm_num [UInt256.size])

theorem slot0Uint8Mask_bound (w : UInt256) :
    (UInt256.land w slot0Uint8Mask).toNat < EVM.twoPow 8 := by
  rw [uland_toNat, slot0Uint8Mask_toNat]
  exact lt_of_le_of_lt (nat_land_le_right _ _) (by norm_num [EVM.twoPow])

theorem slot0Uint8Mask_clean {w : UInt256} (hcanon : w.toNat < EVM.twoPow 8) :
    UInt256.land w slot0Uint8Mask = w := by
  apply u256_inj
  show Nat.land w.toNat slot0Uint8Mask.toNat % EVM.twoPow 256 = w.toNat
  rw [slot0Uint8Mask_toNat, nat_land_mask_eq_mod]
  rw [show EVM.twoPow 8 = 2 ^ 8 from rfl] at hcanon
  rw [Nat.mod_eq_of_lt hcanon]
  exact Nat.mod_eq_of_lt w.val.isLt

theorem slot0Sint24Value_mask (w : UInt256) :
    tickSpacingSint24Value (UInt256.land w slot0Uint24Mask) = tickSpacingSint24Value w := by
  unfold tickSpacingSint24Value
  have hmod : (UInt256.land w slot0Uint24Mask).toNat % EVM.twoPow 24 =
      w.toNat % EVM.twoPow 24 := by
    rw [uland_toNat, slot0Uint24Mask_toNat]
    change Nat.land w.toNat (2 ^ 24 - 1) % EVM.twoPow 24 =
      w.toNat % EVM.twoPow 24
    rw [nat_land_mask_eq_mod]
    simp [EVM.twoPow]
  rw [hmod]

theorem slot0Sint24Value_ge (w : UInt256) :
    -(2 ^ 23 : Int) ≤ tickSpacingSint24Value w := by
  unfold tickSpacingSint24Value
  by_cases h : w.toNat % EVM.twoPow 24 < EVM.twoPow 23
  · rw [if_pos h]
    exact le_trans (by norm_num : -(2 ^ 23 : Int) ≤ 0) (Int.natCast_nonneg _)
  · rw [if_neg h]
    have hmhi := Nat.mod_lt w.toNat (by norm_num [EVM.twoPow] : 0 < EVM.twoPow 24)
    norm_num [EVM.twoPow] at h hmhi ⊢
    omega

theorem slot0Sint24Value_lt (w : UInt256) :
    tickSpacingSint24Value w < (2 ^ 23 : Int) := by
  unfold tickSpacingSint24Value
  by_cases h : w.toNat % EVM.twoPow 24 < EVM.twoPow 23
  · rw [if_pos h]
    norm_num [EVM.twoPow] at h ⊢
    omega
  · rw [if_neg h]
    have hmhi := Nat.mod_lt w.toNat (by norm_num [EVM.twoPow] : 0 < EVM.twoPow 24)
    norm_num [EVM.twoPow] at h hmhi ⊢
    omega

theorem slot0TickRawValue_wordOfInt (w : UInt256) :
    EVM.wordOfInt (tickSpacingSint24Value (UInt256.land w slot0Uint24Mask)) =
      UInt256.signextend ⟨2⟩ w := by
  rw [slot0Sint24Value_mask]
  exact wordOfInt_sint24Value_eq_signextend_two w

theorem slot0SignextendTwo_idempotent (w : UInt256) :
    UInt256.signextend ⟨2⟩ (UInt256.signextend ⟨2⟩ w) =
      UInt256.signextend ⟨2⟩ w := by
  let i := tickSpacingSint24Value w
  have hword : EVM.wordOfInt i = UInt256.signextend ⟨2⟩ w := by
    simpa [i] using wordOfInt_sint24Value_eq_signextend_two w
  rw [← hword]
  exact signextend_two_wordOfInt_tickSpacing i (slot0Sint24Value_ge w)
    (slot0Sint24Value_lt w)

theorem slot0BoolABIEncoding (w : UInt256) :
    encodeABIValue? boolTy (wordToElem .bool w) =
      some (EVM.Word.toBytesBE (slot0BoolReturnWord w)) := by
  by_cases hval : w.val = 0
  · have hz : w = ⟨0⟩ := by
      apply u256_inj
      exact congrArg Fin.val hval
    simp [boolTy, wordToElem, hz, slot0BoolReturnWord, encodeABIValue?, encodeABIWord?,
      Bool.toUInt256_false]
    native_decide
  · have hz : w ≠ ⟨0⟩ := by
      intro hx
      apply hval
      rw [hx]
    have hiz : UInt256.isZero w = ⟨0⟩ := isZero_eq_zero_of_ne hz
    simp [boolTy, wordToElem, hval, slot0BoolReturnWord, hiz, encodeABIValue?, encodeABIWord?,
      Bool.toUInt256_true]
    native_decide

theorem slot0ReturnEncoding (σ : AccountMap) (I : ExecutionEnv) :
    encodeReturnValues? [uint160, int24, uint16, uint16, uint16, uint8, boolTy]
        (slot0ReturnValues σ I) =
      some (UInt256.toByteArray (slot0SqrtPriceX96Word σ I) ++
        UInt256.toByteArray (slot0TickReturnWord σ I) ++
          UInt256.toByteArray (slot0ObservationIndexWord σ I) ++
            UInt256.toByteArray (slot0ObservationCardinalityWord σ I) ++
              UInt256.toByteArray (slot0ObservationCardinalityNextWord σ I) ++
                UInt256.toByteArray (slot0FeeProtocolWord σ I) ++
                  UInt256.toByteArray (slot0BoolReturnWord (slot0UnlockedRawWord σ I))) := by
  have hwordSqrt : EVM.word (slot0SqrtPriceX96Word σ I).toNat =
      slot0SqrtPriceX96Word σ I := u256_ofNat_toNat _
  have hwordObsIndex : EVM.word (slot0ObservationIndexWord σ I).toNat =
      slot0ObservationIndexWord σ I := u256_ofNat_toNat _
  have hwordObsCardinality : EVM.word (slot0ObservationCardinalityWord σ I).toNat =
      slot0ObservationCardinalityWord σ I := u256_ofNat_toNat _
  have hwordObsCardinalityNext :
      EVM.word (slot0ObservationCardinalityNextWord σ I).toNat =
        slot0ObservationCardinalityNextWord σ I := u256_ofNat_toNat _
  have hwordFee : EVM.word (slot0FeeProtocolWord σ I).toNat =
      slot0FeeProtocolWord σ I := u256_ofNat_toNat _
  have hsqrtLt : (slot0SqrtPriceX96Word σ I).toNat < EVM.twoPow 160 := by
    simpa [slot0SqrtPriceX96Word] using slot0Uint160Mask_bound (slot0SlotWord σ I)
  have hobsIndexLt : (slot0ObservationIndexWord σ I).toNat < EVM.twoPow 16 := by
    simpa [slot0ObservationIndexWord] using
      slot0Uint16Mask_bound (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 23))
  have hobsCardinalityLt : (slot0ObservationCardinalityWord σ I).toNat <
      EVM.twoPow 16 := by
    simpa [slot0ObservationCardinalityWord] using
      slot0Uint16Mask_bound (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 25))
  have hobsCardinalityNextLt : (slot0ObservationCardinalityNextWord σ I).toNat <
      EVM.twoPow 16 := by
    simpa [slot0ObservationCardinalityNextWord] using
      slot0Uint16Mask_bound (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 27))
  have hfeeLt : (slot0FeeProtocolWord σ I).toNat < EVM.twoPow 8 := by
    simpa [slot0FeeProtocolWord] using
      slot0Uint8Mask_bound (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 29))
  have hencSqrt :
      encodeABIValue? uint160 (.int (Int.ofNat (slot0SqrtPriceX96Word σ I).toNat)) =
        some (EVM.Word.toBytesBE (slot0SqrtPriceX96Word σ I)) := by
    simp [uint160, uint160Int, encodeABIValue?, encodeABIWord?, hwordSqrt, hsqrtLt]
  have hencTick :
      encodeABIValue? int24 (wordToElem (.int int24Int) (slot0TickRawWord σ I)) =
        some (EVM.Word.toBytesBE (slot0TickReturnWord σ I)) := by
    change encodeABIValue? int24
        (.int (tickSpacingSint24Value (slot0TickRawWord σ I))) =
      some (EVM.Word.toBytesBE (slot0TickReturnWord σ I))
    have hge := slot0Sint24Value_ge (slot0TickRawWord σ I)
    have hlt := slot0Sint24Value_lt (slot0TickRawWord σ I)
    have hword : EVM.wordOfInt (tickSpacingSint24Value (slot0TickRawWord σ I)) =
        slot0TickReturnWord σ I := by
      dsimp [slot0TickRawWord, slot0TickReturnWord]
      exact slot0TickRawValue_wordOfInt
        (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 20))
    simp only [int24, int24Int, encodeABIValue?, encodeABIWord?]
    rw [if_neg (by decide : 24 ≠ 0), if_pos]
    · rw [hword]
      rfl
    · constructor
      · simpa [EVM.twoPow] using hge
      · simpa [EVM.twoPow] using hlt
  have hencObsIndex :
      encodeABIValue? uint16
          (.int (Int.ofNat (slot0ObservationIndexWord σ I).toNat)) =
        some (EVM.Word.toBytesBE (slot0ObservationIndexWord σ I)) := by
    simp [uint16, uint16Int, encodeABIValue?, encodeABIWord?, hwordObsIndex,
      hobsIndexLt]
  have hencObsCardinality :
      encodeABIValue? uint16
          (.int (Int.ofNat (slot0ObservationCardinalityWord σ I).toNat)) =
        some (EVM.Word.toBytesBE (slot0ObservationCardinalityWord σ I)) := by
    simp [uint16, uint16Int, encodeABIValue?, encodeABIWord?, hwordObsCardinality,
      hobsCardinalityLt]
  have hencObsCardinalityNext :
      encodeABIValue? uint16
          (.int (Int.ofNat (slot0ObservationCardinalityNextWord σ I).toNat)) =
        some (EVM.Word.toBytesBE (slot0ObservationCardinalityNextWord σ I)) := by
    simp [uint16, uint16Int, encodeABIValue?, encodeABIWord?, hwordObsCardinalityNext,
      hobsCardinalityNextLt]
  have hencFee :
      encodeABIValue? uint8 (.int (Int.ofNat (slot0FeeProtocolWord σ I).toNat)) =
        some (EVM.Word.toBytesBE (slot0FeeProtocolWord σ I)) := by
    simp [uint8, uint8Int, encodeABIValue?, encodeABIWord?, hwordFee, hfeeLt]
  have hencUnlocked :
      encodeABIValue? boolTy (wordToElem .bool (slot0UnlockedRawWord σ I)) =
        some (EVM.Word.toBytesBE (slot0BoolReturnWord (slot0UnlockedRawWord σ I))) :=
    slot0BoolABIEncoding (slot0UnlockedRawWord σ I)
  have hhead :
      abiTupleHeadSize? [uint160, int24, uint16, uint16, uint16, uint8, boolTy] =
        some 224 := by native_decide
  have hdyn160 : isDynamicABIType uint160 = false := by native_decide
  have hdyn24 : isDynamicABIType int24 = false := by native_decide
  have hdyn16 : isDynamicABIType uint16 = false := by native_decide
  have hdyn8 : isDynamicABIType uint8 = false := by native_decide
  have hdynBool : isDynamicABIType boolTy = false := by native_decide
  rw [toByteArray_eq_toBytesBE (slot0SqrtPriceX96Word σ I),
    toByteArray_eq_toBytesBE (slot0TickReturnWord σ I),
    toByteArray_eq_toBytesBE (slot0ObservationIndexWord σ I),
    toByteArray_eq_toBytesBE (slot0ObservationCardinalityWord σ I),
    toByteArray_eq_toBytesBE (slot0ObservationCardinalityNextWord σ I),
    toByteArray_eq_toBytesBE (slot0FeeProtocolWord σ I),
    toByteArray_eq_toBytesBE (slot0BoolReturnWord (slot0UnlockedRawWord σ I))]
  simp only [slot0ReturnValues, encodeReturnValues?, encodeABIValues?,
    encodeABIValuesFrom?, hhead, hencSqrt, hencTick, hencObsIndex,
    hencObsCardinality, hencObsCardinalityNext, hencFee, hencUnlocked,
    hdyn160, hdyn24, hdyn16, hdyn8, hdynBool, bind, Option.bind,
    Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

noncomputable def slot0ReturnMem1 (sqrt : UInt256) : ByteArray :=
  writeCascade solcFreePtrMem [(128, sqrt)]

noncomputable def slot0ReturnMem2 (sqrt tick : UInt256) : ByteArray :=
  writeCascade solcFreePtrMem [(128, sqrt), (160, tick)]

noncomputable def slot0ReturnMem3 (sqrt tick obsIndex : UInt256) : ByteArray :=
  writeCascade solcFreePtrMem [(128, sqrt), (160, tick), (192, obsIndex)]

noncomputable def slot0ReturnMem4 (sqrt tick obsIndex obsCardinality : UInt256) :
    ByteArray :=
  writeCascade solcFreePtrMem
    [(128, sqrt), (160, tick), (192, obsIndex), (224, obsCardinality)]

noncomputable def slot0ReturnMem5
    (sqrt tick obsIndex obsCardinality obsCardinalityNext : UInt256) : ByteArray :=
  writeCascade solcFreePtrMem
    [(128, sqrt), (160, tick), (192, obsIndex), (224, obsCardinality),
      (256, obsCardinalityNext)]

noncomputable def slot0ReturnMem6
    (sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol : UInt256) :
    ByteArray :=
  writeCascade solcFreePtrMem
    [(128, sqrt), (160, tick), (192, obsIndex), (224, obsCardinality),
      (256, obsCardinalityNext), (288, feeProtocol)]

noncomputable def slot0ReturnMem
    (sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol unlocked : UInt256) :
    ByteArray :=
  writeCascade solcFreePtrMem
    [(128, sqrt), (160, tick), (192, obsIndex), (224, obsCardinality),
      (256, obsCardinalityNext), (288, feeProtocol), (320, unlocked)]

theorem slot0ReturnMem1_eq (sqrt : UInt256) :
    slot0ReturnMem1 sqrt = writeWord solcFreePtrMem 128 sqrt := by
  rfl

theorem slot0ReturnMem2_eq (sqrt tick : UInt256) :
    slot0ReturnMem2 sqrt tick = writeWord (slot0ReturnMem1 sqrt) 160 tick := by
  rfl

theorem slot0ReturnMem3_eq (sqrt tick obsIndex : UInt256) :
    slot0ReturnMem3 sqrt tick obsIndex =
      writeWord (slot0ReturnMem2 sqrt tick) 192 obsIndex := by
  rfl

theorem slot0ReturnMem4_eq (sqrt tick obsIndex obsCardinality : UInt256) :
    slot0ReturnMem4 sqrt tick obsIndex obsCardinality =
      writeWord (slot0ReturnMem3 sqrt tick obsIndex) 224 obsCardinality := by
  rfl

theorem slot0ReturnMem5_eq
    (sqrt tick obsIndex obsCardinality obsCardinalityNext : UInt256) :
    slot0ReturnMem5 sqrt tick obsIndex obsCardinality obsCardinalityNext =
      writeWord (slot0ReturnMem4 sqrt tick obsIndex obsCardinality) 256
        obsCardinalityNext := by
  rfl

theorem slot0ReturnMem6_eq
    (sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol : UInt256) :
    slot0ReturnMem6 sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol =
      writeWord (slot0ReturnMem5 sqrt tick obsIndex obsCardinality obsCardinalityNext) 288
        feeProtocol := by
  rfl

theorem slot0ReturnMem_eq
    (sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol unlocked : UInt256) :
    slot0ReturnMem sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol unlocked =
      writeWord (slot0ReturnMem6 sqrt tick obsIndex obsCardinality obsCardinalityNext
        feeProtocol) 320 unlocked := by
  rfl

theorem slot0ReturnMem1_size (sqrt : UInt256) :
    (slot0ReturnMem1 sqrt).size = 160 := by
  unfold slot0ReturnMem1
  exact writeCascade_size_of_base solcFreePtrMem _ solcFreePtrMem_size
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem slot0ReturnMem2_size (sqrt tick : UInt256) :
    (slot0ReturnMem2 sqrt tick).size = 192 := by
  unfold slot0ReturnMem2
  exact writeCascade_size_of_base solcFreePtrMem _ solcFreePtrMem_size
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem slot0ReturnMem3_size (sqrt tick obsIndex : UInt256) :
    (slot0ReturnMem3 sqrt tick obsIndex).size = 224 := by
  unfold slot0ReturnMem3
  exact writeCascade_size_of_base solcFreePtrMem _ solcFreePtrMem_size
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem slot0ReturnMem4_size (sqrt tick obsIndex obsCardinality : UInt256) :
    (slot0ReturnMem4 sqrt tick obsIndex obsCardinality).size = 256 := by
  unfold slot0ReturnMem4
  exact writeCascade_size_of_base solcFreePtrMem _ solcFreePtrMem_size
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem slot0ReturnMem5_size
    (sqrt tick obsIndex obsCardinality obsCardinalityNext : UInt256) :
    (slot0ReturnMem5 sqrt tick obsIndex obsCardinality obsCardinalityNext).size = 288 := by
  unfold slot0ReturnMem5
  exact writeCascade_size_of_base solcFreePtrMem _ solcFreePtrMem_size
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem slot0ReturnMem6_size
    (sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol : UInt256) :
    (slot0ReturnMem6 sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol).size =
      320 := by
  unfold slot0ReturnMem6
  exact writeCascade_size_of_base solcFreePtrMem _ solcFreePtrMem_size
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem slot0ReturnMem_size
    (sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol unlocked : UInt256) :
    (slot0ReturnMem sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol unlocked).size =
      352 := by
  unfold slot0ReturnMem
  exact writeCascade_size_of_base solcFreePtrMem _ solcFreePtrMem_size
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem slot0ReturnMem_read64
    (sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol unlocked : UInt256) :
    (slot0ReturnMem sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol
      unlocked).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold slot0ReturnMem
  rw [writeCascade_read_preserved_of_base solcFreePtrMem _ solcFreePtrMem_size
    (by
      norm_num [WindowDisjointFromWrites]
      all_goals native_decide)]
  exact solcFreePtrMem_read64

theorem slot0ReturnMem_mload64
    (sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol unlocked : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (slot0ReturnMem sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol
            unlocked).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 11 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((slot0ReturnMem sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol
          unlocked).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue (by rw [slot0ReturnMem_size]; decide) (by decide)
    (slot0ReturnMem_read64 sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol
      unlocked)

theorem slot0ReturnMem_read128
    (sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol unlocked : UInt256) :
    (slot0ReturnMem sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol
      unlocked).readWithPadding 128 32 = UInt256.toByteArray sqrt := by
  unfold slot0ReturnMem
  exact writeCascade_read_word_of_head_of_base solcFreePtrMem (base := 96) (off := 128)
    sqrt [(160, tick), (192, obsIndex), (224, obsCardinality), (256, obsCardinalityNext),
      (288, feeProtocol), (320, unlocked)]
      solcFreePtrMem_size (by native_decide)
      (by
        norm_num [WindowDisjointFromWrites])

theorem slot0ReturnMem_read160
    (sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol unlocked : UInt256) :
    (slot0ReturnMem sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol
      unlocked).readWithPadding 160 32 = UInt256.toByteArray tick := by
  unfold slot0ReturnMem
  change (writeCascade (slot0ReturnMem1 sqrt)
      [(160, tick), (192, obsIndex), (224, obsCardinality), (256, obsCardinalityNext),
        (288, feeProtocol), (320, unlocked)]).readWithPadding 160 32 =
    UInt256.toByteArray tick
  exact writeCascade_read_word_of_head_of_base (slot0ReturnMem1 sqrt) (base := 160)
    (off := 160) tick
    [(192, obsIndex), (224, obsCardinality), (256, obsCardinalityNext), (288, feeProtocol),
      (320, unlocked)]
      (slot0ReturnMem1_size sqrt) (by native_decide)
      (by
        norm_num [WindowDisjointFromWrites])

theorem slot0ReturnMem_read192
    (sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol unlocked : UInt256) :
    (slot0ReturnMem sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol
      unlocked).readWithPadding 192 32 = UInt256.toByteArray obsIndex := by
  unfold slot0ReturnMem
  change (writeCascade (slot0ReturnMem2 sqrt tick)
      [(192, obsIndex), (224, obsCardinality), (256, obsCardinalityNext),
        (288, feeProtocol), (320, unlocked)]).readWithPadding 192 32 =
    UInt256.toByteArray obsIndex
  exact writeCascade_read_word_of_head_of_base (slot0ReturnMem2 sqrt tick) (base := 192)
    (off := 192) obsIndex
      [(224, obsCardinality), (256, obsCardinalityNext), (288, feeProtocol), (320, unlocked)]
      (slot0ReturnMem2_size sqrt tick) (by native_decide)
      (by
        norm_num [WindowDisjointFromWrites])

theorem slot0ReturnMem_read224
    (sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol unlocked : UInt256) :
    (slot0ReturnMem sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol
      unlocked).readWithPadding 224 32 = UInt256.toByteArray obsCardinality := by
  unfold slot0ReturnMem
  change (writeCascade (slot0ReturnMem3 sqrt tick obsIndex)
      [(224, obsCardinality), (256, obsCardinalityNext), (288, feeProtocol),
        (320, unlocked)]).readWithPadding 224 32 =
    UInt256.toByteArray obsCardinality
  exact writeCascade_read_word_of_head_of_base (slot0ReturnMem3 sqrt tick obsIndex)
    (base := 224) (off := 224) obsCardinality
      [(256, obsCardinalityNext), (288, feeProtocol), (320, unlocked)]
      (slot0ReturnMem3_size sqrt tick obsIndex) (by native_decide)
      (by
        norm_num [WindowDisjointFromWrites])

theorem slot0ReturnMem_read256
    (sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol unlocked : UInt256) :
    (slot0ReturnMem sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol
      unlocked).readWithPadding 256 32 = UInt256.toByteArray obsCardinalityNext := by
  unfold slot0ReturnMem
  change (writeCascade (slot0ReturnMem4 sqrt tick obsIndex obsCardinality)
      [(256, obsCardinalityNext), (288, feeProtocol), (320, unlocked)]).readWithPadding
        256 32 =
    UInt256.toByteArray obsCardinalityNext
  exact writeCascade_read_word_of_head_of_base
    (slot0ReturnMem4 sqrt tick obsIndex obsCardinality) (base := 256) (off := 256)
      obsCardinalityNext [(288, feeProtocol), (320, unlocked)]
      (slot0ReturnMem4_size sqrt tick obsIndex obsCardinality) (by native_decide)
      (by
        norm_num [WindowDisjointFromWrites])

theorem slot0ReturnMem_read288
    (sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol unlocked : UInt256) :
    (slot0ReturnMem sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol
      unlocked).readWithPadding 288 32 = UInt256.toByteArray feeProtocol := by
  unfold slot0ReturnMem
  change (writeCascade
      (slot0ReturnMem5 sqrt tick obsIndex obsCardinality obsCardinalityNext)
      [(288, feeProtocol), (320, unlocked)]).readWithPadding 288 32 =
    UInt256.toByteArray feeProtocol
  exact writeCascade_read_word_of_head_of_base
    (slot0ReturnMem5 sqrt tick obsIndex obsCardinality obsCardinalityNext) (base := 288)
    (off := 288) feeProtocol [(320, unlocked)]
      (slot0ReturnMem5_size sqrt tick obsIndex obsCardinality obsCardinalityNext)
      (by native_decide)
      (by
        norm_num [WindowDisjointFromWrites])

theorem slot0ReturnMem_read320
    (sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol unlocked : UInt256) :
    (slot0ReturnMem sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol
      unlocked).readWithPadding 320 32 = UInt256.toByteArray unlocked := by
  unfold slot0ReturnMem
  change (writeCascade
      (slot0ReturnMem6 sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol)
      [(320, unlocked)]).readWithPadding 320 32 =
    UInt256.toByteArray unlocked
  exact writeCascade_read_word_of_head_of_base
    (slot0ReturnMem6 sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol)
    (base := 320) (off := 320) unlocked []
      (slot0ReturnMem6_size sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol)
      (by native_decide)
      (by
        norm_num [WindowDisjointFromWrites])

theorem slot0ReturnMem_read128_224
    (sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol unlocked : UInt256) :
    (slot0ReturnMem sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol
      unlocked).readWithPadding 128 224 =
      UInt256.toByteArray sqrt ++ UInt256.toByteArray tick ++ UInt256.toByteArray obsIndex ++
        UInt256.toByteArray obsCardinality ++ UInt256.toByteArray obsCardinalityNext ++
          UInt256.toByteArray feeProtocol ++ UInt256.toByteArray unlocked := by
  let mem := slot0ReturnMem sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol
    unlocked
  have hsize : mem.size = 352 := by
    simpa [mem] using
      slot0ReturnMem_size sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol
        unlocked
  have h128 : mem.readWithPadding 128 32 = UInt256.toByteArray sqrt := by
    simpa [mem] using
      slot0ReturnMem_read128 sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol
        unlocked
  have h160 : mem.readWithPadding 160 32 = UInt256.toByteArray tick := by
    simpa [mem] using
      slot0ReturnMem_read160 sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol
        unlocked
  have h192 : mem.readWithPadding 192 32 = UInt256.toByteArray obsIndex := by
    simpa [mem] using
      slot0ReturnMem_read192 sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol
        unlocked
  have h224 : mem.readWithPadding 224 32 = UInt256.toByteArray obsCardinality := by
    simpa [mem] using
      slot0ReturnMem_read224 sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol
        unlocked
  have h256 : mem.readWithPadding 256 32 = UInt256.toByteArray obsCardinalityNext := by
    simpa [mem] using
      slot0ReturnMem_read256 sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol
        unlocked
  have h288 : mem.readWithPadding 288 32 = UInt256.toByteArray feeProtocol := by
    simpa [mem] using
      slot0ReturnMem_read288 sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol
        unlocked
  have h320 : mem.readWithPadding 320 32 = UInt256.toByteArray unlocked := by
    simpa [mem] using
      slot0ReturnMem_read320 sqrt tick obsIndex obsCardinality obsCardinalityNext feeProtocol
        unlocked
  change mem.readWithPadding 128 224 = _
  rw [byteArray_readWithPadding_split mem 128 32 192 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h128]
  rw [byteArray_readWithPadding_split mem 160 32 160 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h160]
  rw [byteArray_readWithPadding_split mem 192 32 128 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h192]
  rw [byteArray_readWithPadding_split mem 224 32 96 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h224]
  rw [byteArray_readWithPadding_split mem 256 32 64 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h256]
  rw [byteArray_readWithPadding_split mem 288 32 32 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h288, h320]
  simp only [ByteArray.append_assoc]

theorem storageLocLoad_sint_offset (evm : EVM.State) (slot : UInt256)
    (offset : Fin 32) (size : Fin 33) (width : ABI.BitWidth)
    {hbound : offset.val + size.val - 1 < 32}
    (hoff : 8 * offset.val < 256) (hsize : 8 * size.val ≤ 256) :
    storageLocLoad evm
        { slot := slot, offset := offset, size := size, hbound := hbound,
          type := .int (.sint width) } =
      wordToElem (.int (.sint width))
        (UInt256.land
          (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            (UInt256.ofNat (256 ^ offset.val)))
          (UInt256.ofNat (256 ^ size.val - 1))) := by
  unfold storageLocLoad
  change wordToElem (.int (.sint width))
      ⟨fromBytes'
        (((EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1).extract
            offset.val (offset.val + size.val)), _⟩ = _
  congr
  rw [List.extract_eq_take_drop]
  simpa [Nat.add_sub_cancel_left] using
    fromBytes'_drop_take_wordLE_land_div_mask
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) offset.val size.val hoff hsize

theorem storageLocLoad_bool_offset (evm : EVM.State) (slot : UInt256)
    (offset : Fin 32) {hbound : offset.val + (1 : Fin 33).val - 1 < 32}
    (hoff : 8 * offset.val < 256) :
    storageLocLoad evm
        { slot := slot, offset := offset, size := (1 : Fin 33), hbound := hbound,
          type := .bool } =
      wordToElem .bool
        (UInt256.land
          (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            (UInt256.ofNat (256 ^ offset.val)))
          slot0Uint8Mask) := by
  unfold storageLocLoad
  change wordToElem .bool
      ⟨fromBytes'
        (((EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1).extract
            offset.val (offset.val + 1)), _⟩ = _
  congr
  rw [List.extract_eq_take_drop]
  rw [← show UInt256.ofNat (256 ^ (1 : Nat) - 1) = slot0Uint8Mask by native_decide]
  simpa [Nat.add_sub_cancel_left] using
    fromBytes'_drop_take_wordLE_land_div_mask
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) offset.val 1 hoff
      (by decide)

theorem slot0StorageLocLoad_sqrtPriceX96 (evm : EVM.State) :
    storageLocLoad evm
        (loc ⟨0⟩ ⟨0, by decide⟩ ⟨20, by decide⟩ (by decide) (.int uint160Int)) =
      .int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) slot0Uint160Mask).toNat) := by
  rw [← show UInt256.ofNat (2 ^ (8 * 20) - 1) = slot0Uint160Mask by native_decide]
  simpa [loc, uint160Int] using
    storageLocLoad_uint_offset0 evm ⟨0⟩ (20 : Fin 33) ⟨160, by decide⟩
      (hbound := by decide) (by decide)

theorem slot0StorageLocLoad_tick (evm : EVM.State) :
    storageLocLoad evm
        (loc ⟨0⟩ ⟨20, by decide⟩ ⟨3, by decide⟩ (by decide) (.int int24Int)) =
      wordToElem (.int int24Int)
        (UInt256.land
          (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            (slot0ShiftBytes 20))
          slot0Uint24Mask) := by
  rw [← show UInt256.ofNat (256 ^ (20 : Nat)) = slot0ShiftBytes 20 by rfl]
  rw [← show UInt256.ofNat (256 ^ (3 : Nat) - 1) = slot0Uint24Mask by native_decide]
  simpa [loc, int24Int] using
    storageLocLoad_sint_offset evm ⟨0⟩ (20 : Fin 32) (3 : Fin 33) ⟨24, by decide⟩
      (hbound := by decide) (by decide) (by decide)

theorem slot0StorageLocLoad_observationIndex (evm : EVM.State) :
    storageLocLoad evm
        (loc ⟨0⟩ ⟨23, by decide⟩ ⟨2, by decide⟩ (by decide) (.int uint16Int)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
          (slot0ShiftBytes 23)) slot0Uint16Mask).toNat) := by
  rw [← show UInt256.ofNat (256 ^ (23 : Nat)) = slot0ShiftBytes 23 by rfl]
  rw [← show UInt256.ofNat (256 ^ (2 : Nat) - 1) = slot0Uint16Mask by native_decide]
  simpa [loc, uint16Int] using
    storageLocLoad_uint_offset evm ⟨0⟩ (23 : Fin 32) (2 : Fin 33) ⟨16, by decide⟩
      (hbound := by decide) (by decide) (by decide)

theorem slot0StorageLocLoad_observationCardinality (evm : EVM.State) :
    storageLocLoad evm
        (loc ⟨0⟩ ⟨25, by decide⟩ ⟨2, by decide⟩ (by decide) (.int uint16Int)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
          (slot0ShiftBytes 25)) slot0Uint16Mask).toNat) := by
  rw [← show UInt256.ofNat (256 ^ (25 : Nat)) = slot0ShiftBytes 25 by rfl]
  rw [← show UInt256.ofNat (256 ^ (2 : Nat) - 1) = slot0Uint16Mask by native_decide]
  simpa [loc, uint16Int] using
    storageLocLoad_uint_offset evm ⟨0⟩ (25 : Fin 32) (2 : Fin 33) ⟨16, by decide⟩
      (hbound := by decide) (by decide) (by decide)

theorem slot0StorageLocLoad_observationCardinalityNext (evm : EVM.State) :
    storageLocLoad evm
        (loc ⟨0⟩ ⟨27, by decide⟩ ⟨2, by decide⟩ (by decide) (.int uint16Int)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
          (slot0ShiftBytes 27)) slot0Uint16Mask).toNat) := by
  rw [← show UInt256.ofNat (256 ^ (27 : Nat)) = slot0ShiftBytes 27 by rfl]
  rw [← show UInt256.ofNat (256 ^ (2 : Nat) - 1) = slot0Uint16Mask by native_decide]
  simpa [loc, uint16Int] using
    storageLocLoad_uint_offset evm ⟨0⟩ (27 : Fin 32) (2 : Fin 33) ⟨16, by decide⟩
      (hbound := by decide) (by decide) (by decide)

theorem slot0StorageLocLoad_feeProtocol (evm : EVM.State) :
    storageLocLoad evm
        (loc ⟨0⟩ ⟨29, by decide⟩ ⟨1, by decide⟩ (by decide) (.int uint8Int)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
          (slot0ShiftBytes 29)) slot0Uint8Mask).toNat) := by
  rw [← show UInt256.ofNat (256 ^ (29 : Nat)) = slot0ShiftBytes 29 by rfl]
  rw [← show UInt256.ofNat (256 ^ (1 : Nat) - 1) = slot0Uint8Mask by native_decide]
  simpa [loc, uint8Int] using
    storageLocLoad_uint_offset evm ⟨0⟩ (29 : Fin 32) (1 : Fin 33) ⟨8, by decide⟩
      (hbound := by decide) (by decide) (by decide)

theorem slot0StorageLocLoad_unlocked (evm : EVM.State) :
    storageLocLoad evm
        (loc ⟨0⟩ ⟨30, by decide⟩ ⟨1, by decide⟩ (by decide) .bool) =
      wordToElem .bool
        (UInt256.land
          (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            (slot0ShiftBytes 30))
          slot0Uint8Mask) := by
  rw [← show UInt256.ofNat (256 ^ (30 : Nat)) = slot0ShiftBytes 30 by rfl]
  simpa [loc] using
    storageLocLoad_bool_offset evm ⟨0⟩ (30 : Fin 32) (hbound := by decide) (by decide)

theorem uniswapV3PoolSlot0ReachEntry {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 6 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨859⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := uniswapV3PoolReachSelector32
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hword : solcSelectorWord I = uniswapV3PoolSelNat 6 := by
    simpa [uniswapV3PoolSelBytes, uniswapV3PoolSelNat] using
      solcSelectorWord_eq_of_beq I hsz 0x38 0x50 0xc7 0xbd
        (uniswapV3PoolSelNat 6) (by native_decide) hsel
  have hgt32 : UInt256.gt (armSelNat code ⟨32⟩) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h239 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨239⟩) hpatch h32 hgt32
  have hgt239 : UInt256.gt (armSelNat code ⟨239⟩) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h250 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨250⟩) hpatch h239 hgt239
  have hgt250 : UInt256.gt (armSelNat code ⟨250⟩) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h310 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨310⟩) hpatch h250 hgt250
  have h859 := uniswapV3PoolSelectorArmHitTo (i := 6) (target := ⟨859⟩)
    hpatch hsz hsel h310
  exact ⟨_, _, h859⟩

theorem uniswapV3PoolSlot0Decode {v : PoolImmutables} {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode
      (slot0Transition.params.map Param.name)
      (transitionSignature slot0Transition).paramTypes I.calldata = some (∅ : Store) := by
  simpa [config, slot0Transition, transitionSignature] using
    decodeCalldataWithMode_empty_ok (mode := DecodeMode.legacySolc05) (cd := I.calldata) hsz

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolDispatch_slot0 {v : PoolImmutables} {cd : ByteArray}
    (hsel : (uniswapV3PoolSelBytes 6 == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some slot0Transition := by
  apply dispatchMsg_eq_some_of_split
    (pre := [burnTransition, collectTransition v, collectprotocolTransition v, factoryTransition v,
      feeTransition v, feegrowthglobal0X128Transition, feegrowthglobal1X128Transition,
      flashTransition v, increaseobservationcardinalitynextTransition v, initializeTransition,
      liquidityTransition, maxliquiditypertickTransition v, mintTransition v, observationsTransition,
      observeTransition v, positionsTransition, protocolfeesTransition, setfeeprotocolTransition v])
    (post := [snapshotcumulativesinsideTransition v, swapTransition v, tickbitmapTransition,
      tickspacingTransition v, ticksTransition, token0Transition v, token1Transition v])
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, burnSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 17) (j := 6)
          (by native_decide) hsel
    · rw [selectorOf, collectSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 10) (j := 6)
          (by native_decide) hsel
    · rw [selectorOf, collectProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 15) (j := 6)
          (by native_decide) hsel
    · rw [selectorOf, factorySelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 19) (j := 6)
          (by native_decide) hsel
    · rw [selectorOf, feeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 22) (j := 6)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal0X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 23) (j := 6)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal1X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 8) (j := 6)
          (by native_decide) hsel
    · rw [selectorOf, flashSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 9) (j := 6)
          (by native_decide) hsel
    · rw [selectorOf, increaseObservationCardinalityNextSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 5) (j := 6)
          (by native_decide) hsel
    · rw [selectorOf, initializeSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 25) (j := 6)
          (by native_decide) hsel
    · rw [selectorOf, liquiditySelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 2) (j := 6)
          (by native_decide) hsel
    · rw [selectorOf, maxLiquidityPerTickSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 13) (j := 6)
          (by native_decide) hsel
    · rw [selectorOf, mintSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 7) (j := 6)
          (by native_decide) hsel
    · rw [selectorOf, observationsSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 4) (j := 6)
          (by native_decide) hsel
    · rw [selectorOf, observeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 16) (j := 6)
          (by native_decide) hsel
    · rw [selectorOf, positionsSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 11) (j := 6)
          (by native_decide) hsel
    · rw [selectorOf, protocolFeesSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 3) (j := 6)
          (by native_decide) hsel
    · rw [selectorOf, setFeeProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 14) (j := 6)
          (by native_decide) hsel
  · rw [selectorOf, slot0SelectorBytes]
    simpa [uniswapV3PoolSelBytes] using hsel

theorem uniswapV3PoolSlot0SourceBody {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (∅ : Store) slot0Transition.body
      (.returned { contract := contract v, locals := ∅ }
        (initState cA gh bl σ σ₀ g A I) (some (slot0ReturnValues σ I))) := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (∅ : Store)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [(.storage (slot0F "sqrtPriceX96")), (.storage (slot0F "tick")),
          (.storage (slot0F "observationIndex")),
          (.storage (slot0F "observationCardinality")),
          (.storage (slot0F "observationCardinalityNext")), (.storage (slot0F "feeProtocol")),
          (.storage (slot0F "unlocked"))] ] _
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by simp [initState, hwv]))) <|
      ExecBlock.consReturn <| ExecStmt.return (by
        have hret0 :
            evalExpr? (config v) { contract := contract v, locals := ∅ }
              (initState cA gh bl σ σ₀ g A I) (.storage (slot0F "sqrtPriceX96")) =
            .ok (.int (Int.ofNat (slot0SqrtPriceX96Word σ I).toNat)) := by
          rw [evalExpr_storage_scalar
            (t := .int uint160Int)
            (slot := slot0F "sqrtPriceX96")
            (er := { base := "slot0", steps := [.field "sqrtPriceX96"] })
            (loc := loc ⟨0⟩ ⟨0, by decide⟩ ⟨20, by decide⟩ (by decide)
              (.int uint160Int))
            (hbase := by simp [slot0F])
            (her := by
              simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind])
            (hty := by
              simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy,
                uint160St])
            (hloc := by
              funext evm
              simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc])]
          simpa [initState, slot0SqrtPriceX96Word, slot0SlotWord, solcSlotWord] using
            slot0StorageLocLoad_sqrtPriceX96 (initState cA gh bl σ σ₀ g A I)
        have hret1 :
            evalExpr? (config v) { contract := contract v, locals := ∅ }
              (initState cA gh bl σ σ₀ g A I) (.storage (slot0F "tick")) =
            .ok (wordToElem (.int int24Int) (slot0TickRawWord σ I)) := by
          rw [evalExpr_storage_scalar
            (t := .int int24Int)
            (slot := slot0F "tick")
            (er := { base := "slot0", steps := [.field "tick"] })
            (loc := loc ⟨0⟩ ⟨20, by decide⟩ ⟨3, by decide⟩ (by decide) (.int int24Int))
            (hbase := by simp [slot0F])
            (her := by
              simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind])
            (hty := by
              simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy,
                int24St])
            (hloc := by
              funext evm
              simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc])]
          simpa [initState, slot0TickRawWord, slot0SlotWord, solcSlotWord] using
            slot0StorageLocLoad_tick (initState cA gh bl σ σ₀ g A I)
        have hret2 :
            evalExpr? (config v) { contract := contract v, locals := ∅ }
              (initState cA gh bl σ σ₀ g A I) (.storage (slot0F "observationIndex")) =
            .ok (.int (Int.ofNat (slot0ObservationIndexWord σ I).toNat)) := by
          rw [evalExpr_storage_scalar
            (t := .int uint16Int)
            (slot := slot0F "observationIndex")
            (er := { base := "slot0", steps := [.field "observationIndex"] })
            (loc := loc ⟨0⟩ ⟨23, by decide⟩ ⟨2, by decide⟩ (by decide)
              (.int uint16Int))
            (hbase := by simp [slot0F])
            (her := by
              simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind])
            (hty := by
              simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy,
                uint16St])
            (hloc := by
              funext evm
              simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc])]
          simpa [initState, slot0ObservationIndexWord, slot0SlotWord, solcSlotWord] using
            slot0StorageLocLoad_observationIndex (initState cA gh bl σ σ₀ g A I)
        have hret3 :
            evalExpr? (config v) { contract := contract v, locals := ∅ }
              (initState cA gh bl σ σ₀ g A I) (.storage (slot0F "observationCardinality")) =
            .ok (.int (Int.ofNat (slot0ObservationCardinalityWord σ I).toNat)) := by
          rw [evalExpr_storage_scalar
            (t := .int uint16Int)
            (slot := slot0F "observationCardinality")
            (er := { base := "slot0", steps := [.field "observationCardinality"] })
            (loc := loc ⟨0⟩ ⟨25, by decide⟩ ⟨2, by decide⟩ (by decide)
              (.int uint16Int))
            (hbase := by simp [slot0F])
            (her := by
              simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind])
            (hty := by
              simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy,
                uint16St])
            (hloc := by
              funext evm
              simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc])]
          simpa [initState, slot0ObservationCardinalityWord, slot0SlotWord, solcSlotWord] using
            slot0StorageLocLoad_observationCardinality (initState cA gh bl σ σ₀ g A I)
        have hret4 :
            evalExpr? (config v) { contract := contract v, locals := ∅ }
              (initState cA gh bl σ σ₀ g A I)
              (.storage (slot0F "observationCardinalityNext")) =
            .ok (.int (Int.ofNat (slot0ObservationCardinalityNextWord σ I).toNat)) := by
          rw [evalExpr_storage_scalar
            (t := .int uint16Int)
            (slot := slot0F "observationCardinalityNext")
            (er := { base := "slot0", steps := [.field "observationCardinalityNext"] })
            (loc := loc ⟨0⟩ ⟨27, by decide⟩ ⟨2, by decide⟩ (by decide)
              (.int uint16Int))
            (hbase := by simp [slot0F])
            (her := by
              simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind])
            (hty := by
              simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy,
                uint16St])
            (hloc := by
              funext evm
              simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc])]
          simpa [initState, slot0ObservationCardinalityNextWord, slot0SlotWord, solcSlotWord] using
            slot0StorageLocLoad_observationCardinalityNext (initState cA gh bl σ σ₀ g A I)
        have hret5 :
            evalExpr? (config v) { contract := contract v, locals := ∅ }
              (initState cA gh bl σ σ₀ g A I) (.storage (slot0F "feeProtocol")) =
            .ok (.int (Int.ofNat (slot0FeeProtocolWord σ I).toNat)) := by
          rw [evalExpr_storage_scalar
            (t := .int uint8Int)
            (slot := slot0F "feeProtocol")
            (er := { base := "slot0", steps := [.field "feeProtocol"] })
            (loc := loc ⟨0⟩ ⟨29, by decide⟩ ⟨1, by decide⟩ (by decide) (.int uint8Int))
            (hbase := by simp [slot0F])
            (her := by
              simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind])
            (hty := by
              simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy,
                uint8St])
            (hloc := by
              funext evm
              simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc])]
          simpa [initState, slot0FeeProtocolWord, slot0SlotWord, solcSlotWord] using
            slot0StorageLocLoad_feeProtocol (initState cA gh bl σ σ₀ g A I)
        have hret6 :
            evalExpr? (config v) { contract := contract v, locals := ∅ }
              (initState cA gh bl σ σ₀ g A I) (.storage (slot0F "unlocked")) =
            .ok (wordToElem .bool (slot0UnlockedRawWord σ I)) := by
          rw [evalExpr_storage_scalar
            (t := .bool)
            (slot := slot0F "unlocked")
            (er := { base := "slot0", steps := [.field "unlocked"] })
            (loc := loc ⟨0⟩ ⟨30, by decide⟩ ⟨1, by decide⟩ (by decide) .bool)
            (hbase := by simp [slot0F])
            (her := by
              simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind])
            (hty := by
              simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy,
                boolSt])
            (hloc := by
              funext evm
              simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc])]
          simpa [initState, slot0UnlockedRawWord, slot0SlotWord, solcSlotWord] using
            slot0StorageLocLoad_unlocked (initState cA gh bl σ σ₀ g A I)
        simp only [Solm.evalExprs?.eq_def, hret0, hret1, hret2, hret3, hret4, hret5,
          hret6, EvalResult.bind, bind, pure, slot0ReturnValues])

theorem uniswapV3PoolSlot0ValueTransport {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    some (slot0ReturnValues σ_solm I) = some (slot0ReturnValues σ_evm I) := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ (⟨0⟩ : UInt256)
  dsimp [slot0ReturnValues, slot0SqrtPriceX96Word, slot0TickRawWord,
    slot0ObservationIndexWord, slot0ObservationCardinalityWord,
    slot0ObservationCardinalityNextWord, slot0FeeProtocolWord, slot0UnlockedRawWord,
    slot0SlotWord, solcSlotWord]
  rw [← hslot]

private theorem uniswapV3PoolSlot0PatchDisjoint {v : PoolImmutables} {pc : UInt256}
    (hlo : 5654 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 6603) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;>
    omega

private theorem uniswapV3PoolPatchPreservesJumpDest5654 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨5654⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched5654 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨5654⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest5654

theorem uniswapV3PoolSlot0EntryWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcGetterEntryWf code ⟨859⟩ ⟨867⟩ ⟨5654⟩ := by
  dsimp [solcGetterEntryWf]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide

theorem uniswapV3PoolSlot0ReturnJumpDest {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨867⟩ = true :=
  uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide)

private def slot0StSignextend (s : State) (v : UInt256) (t : List UInt256) : State :=
  { s with
      machineState.stack := v :: t,
      machineState.gasAvailable := s.machineState.gasAvailable.subNat 5
      machineState.pc := s.machineState.pc + ⟨1⟩
      machineState.execLength := s.machineState.execLength + 1 }

private theorem slot0SignextendXstep {code : ByteArray} {s : State} {pc a b : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pc)
    (hdec : decode code pc = some (.SIGNEXTEND, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s =
      if s.machineState.gasAvailable.toNat < 5 then .error .OutOfGass
      else .ok (slot0StSignextend s (UInt256.signextend a b) t, .none) := by
  have hdecS : decode s.executionEnv.code s.machineState.pc = some (.SIGNEXTEND, .none) := by
    rw [hcode, hpc]
    exact hdec
  have hstep := step_signextend s hdecS
  have hnoOverflow : ¬ 1024 ≤ t.length := by omega
  simpa [hcode, hstk, GasConstants.Glow, slot0StSignextend, hnoOverflow] using hstep

private theorem slot0RDSignextend {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc : UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SIGNEXTEND, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.signextend a b :: t) mem aw rdata acc
      (k + 1) (C + 5) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee,
      hworld⟩
  · exact Or.inl hoog
  · have st := slot0SignextendXstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 5
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨slot0StSignextend s (UInt256.signextend a b) t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega,
        by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [slot0StSignextend]; exact hcode
      · simp only [slot0StSignextend]; rw [hpc]
      · rfl
      · simp only [slot0StSignextend]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [slot0StSignextend]; exact hmem
      · simp only [slot0StSignextend]; exact haw
      · simp only [slot0StSignextend]; exact hrdata
      · simp only [slot0StSignextend]; exact hacc
      · exact hee
      · exact hworld

private theorem slot0Swap9Xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP9, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t)
    (hov : t.length + 10 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (jj :: b :: c :: d :: e :: f :: gg :: hh :: ii :: a :: t),
          .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP9, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap9 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t).length - 10 + 10 >
          1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

private theorem slot0RDSwap9 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP9, .none)) (hov : t.length + 10 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (jj :: b :: c :: d :: e :: f :: gg :: hh :: ii :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => slot0Swap9Xstep hc hp hdec hs hov)

theorem uniswapV3PoolSlot0Routine {v : PoolImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨5654⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (slot0UnlockedRawWord σ ee :: slot0FeeProtocolWord σ ee ::
        slot0ObservationCardinalityNextWord σ ee ::
        slot0ObservationCardinalityWord σ ee :: slot0ObservationIndexWord σ ee ::
        slot0TickReturnWord σ ee :: slot0SqrtPriceX96Word σ ee :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  have rd5655 := h.jumpdest (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5657 := rd5655.push1 ⟨0⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd5658⟩ := rd5657.sload (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5678 := evm_run rd5658 with [
    raw push1 ⟨1⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw shl (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw sub (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw dup2 (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw and (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw shl (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw dup2 (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw div (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw push1 ⟨2⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov)]
  have rd5679 := slot0RDSignextend rd5678 (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5733 := evm_run rd5679 with [
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw push2 ⟨65535⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw push1 ⟨184⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw shl (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw dup3 (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw div (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw dup2 (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw and (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw swap2 (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw push1 ⟨200⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw shl (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw dup2 (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw div (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw dup3 (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw and (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw swap2 (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw push1 ⟨216⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw shl (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw dup3 (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw div (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw and (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw push1 ⟨255⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw push1 ⟨232⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw shl (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw dup3 (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw div (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw dup2 (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw and (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw swap2 (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw push1 ⟨240⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw shl (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw div (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw and (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov),
    raw dup8 (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide) (by evm_ov)]
  have rdRet := rd5733.jump (by
      rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
        (uniswapV3PoolSlot0PatchDisjoint (by native_decide) (by native_decide))]
      native_decide)
    hret (by simp only [List.length_cons]; omega)
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        slot0Uint160Mask := by
    native_decide
  have hmask16 : (⟨65535⟩ : UInt256) = slot0Uint16Mask := by
    native_decide
  have hmask8 : (⟨255⟩ : UInt256) = slot0Uint8Mask := by
    native_decide
  have hshift160 : UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩ = slot0ShiftBytes 20 := by
    native_decide
  have hshift184 : UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨184⟩ = slot0ShiftBytes 23 := by
    native_decide
  have hshift200 : UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨200⟩ = slot0ShiftBytes 25 := by
    native_decide
  have hshift216 : UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨216⟩ = slot0ShiftBytes 27 := by
    native_decide
  have hshift232 : UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨232⟩ = slot0ShiftBytes 29 := by
    native_decide
  have hshift240 : UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨240⟩ = slot0ShiftBytes 30 := by
    native_decide
  exact ⟨_, _, by
    rw [hmask160, hmask16, hmask8, hshift160, hshift184, hshift200, hshift216,
      hshift232, hshift240] at rdRet
    dsimp [slot0UnlockedRawWord, slot0FeeProtocolWord,
      slot0ObservationCardinalityNextWord, slot0ObservationCardinalityWord,
      slot0ObservationIndexWord, slot0TickReturnWord, slot0SqrtPriceX96Word, slot0SlotWord,
      solcSlotWord] at rdRet ⊢
    rw [u256_land_comm slot0Uint8Mask
        (UInt256.div ((σ.find? ee.codeOwner).option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) (slot0ShiftBytes 29)),
      u256_land_comm slot0Uint16Mask
        (UInt256.div ((σ.find? ee.codeOwner).option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) (slot0ShiftBytes 25)),
      u256_land_comm slot0Uint16Mask
        (UInt256.div ((σ.find? ee.codeOwner).option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) (slot0ShiftBytes 23))] at rdRet
    simpa using rdRet⟩

theorem uniswapV3PoolSlot0EvmAtReturn {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 6 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨867⟩
      (slot0UnlockedRawWord σ I :: slot0FeeProtocolWord σ I ::
        slot0ObservationCardinalityNextWord σ I ::
        slot0ObservationCardinalityWord σ I :: slot0ObservationIndexWord σ I ::
        slot0TickReturnWord σ I :: slot0SqrtPriceX96Word σ I :: ⟨867⟩ ::
        [solcSelectorWord I])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hreach := uniswapV3PoolSlot0ReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach
    (uniswapV3PoolSlot0EntryWf hpatch)
    (uniswapV3PoolJumpDestPatched5654 hpatch)
  exact uniswapV3PoolSlot0Routine hpatch rdRoutine
    (uniswapV3PoolSlot0ReturnJumpDest hpatch)
    (by simp only [List.length_singleton]; omega)

theorem uniswapV3PoolSlot0Return {v : PoolImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {unlocked feeProtocol obsCardinalityNext obsCardinality obsIndex tick sqrt : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨867⟩
      (unlocked :: feeProtocol :: obsCardinalityNext :: obsCardinality :: obsIndex :: tick ::
        sqrt :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 16 ≤ 1024) :
    RDret code g s0 acc
      (UInt256.toByteArray (UInt256.land sqrt slot0Uint160Mask) ++
        UInt256.toByteArray (UInt256.signextend ⟨2⟩ tick) ++
          UInt256.toByteArray (UInt256.land slot0Uint16Mask obsIndex) ++
            UInt256.toByteArray (UInt256.land slot0Uint16Mask obsCardinality) ++
              UInt256.toByteArray (UInt256.land slot0Uint16Mask obsCardinalityNext) ++
                UInt256.toByteArray (UInt256.land feeProtocol slot0Uint8Mask) ++
                  UInt256.toByteArray (slot0BoolReturnWord unlocked)) := by
  let sqrt' := UInt256.land sqrt slot0Uint160Mask
  let tick' := UInt256.signextend ⟨2⟩ tick
  let obsIndex' := UInt256.land slot0Uint16Mask obsIndex
  let obsCardinality' := UInt256.land slot0Uint16Mask obsCardinality
  let obsCardinalityNext' := UInt256.land slot0Uint16Mask obsCardinalityNext
  let feeProtocol' := UInt256.land feeProtocol slot0Uint8Mask
  let unlocked' := slot0BoolReturnWord unlocked
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        slot0Uint160Mask := by
    native_decide
  have hmask16 : (⟨65535⟩ : UInt256) = slot0Uint16Mask := by
    native_decide
  have hmask8 : (⟨255⟩ : UInt256) = slot0Uint8Mask := by
    native_decide
  have rd881 := evm_run h with [
    raw jumpdest (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw shl (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw sub (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov)]
  have rd882 := slot0RDSwap9 rd881 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide)
    (by omega)
  have rd890 := evm_run rd882 with [
    raw and (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup9 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mstore 6 (slot0ReturnMem1 sqrt') (UInt256.ofNat 5) (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) mem_cost
      (by
        dsimp [sqrt']
        rw [hmask160, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          slot0ReturnMem1_eq]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap7 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap7 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov)]
  have rd891 := slot0RDSignextend rd890 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd938 := evm_run rd891 with [
    raw push1 ⟨32⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup9 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mstore 3 (slot0ReturnMem2 sqrt' tick') (UInt256.ofNat 6) (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) mem_cost
      (by
        dsimp [tick']
        rw [show ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 from by decide,
          slot0ReturnMem2_eq]
        rfl)
      (by decide) (by evm_ov),
    raw push2 ⟨65535⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap5 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup6 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw and (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup8 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup8 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mstore 3 (slot0ReturnMem3 sqrt' tick' obsIndex') (UInt256.ofNat 7) (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) mem_cost
      (by
        dsimp [obsIndex']
        rw [hmask16, show ((⟨64⟩ : UInt256) + ⟨128⟩).toNat = 192 from by decide,
          slot0ReturnMem3_eq]
        rfl)
      (by decide) (by evm_ov),
    raw swap3 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup5 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw and (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨96⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup8 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mstore 3 (slot0ReturnMem4 sqrt' tick' obsIndex' obsCardinality')
      (UInt256.ofNat 8) (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide) mem_cost
      (by
        dsimp [obsCardinality']
        rw [hmask16, show ((⟨128⟩ : UInt256) + ⟨96⟩).toNat = 224 from by decide,
          slot0ReturnMem4_eq]
        rfl)
      (by decide) (by evm_ov),
    raw swap3 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw and (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨128⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup6 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mstore 3
      (slot0ReturnMem5 sqrt' tick' obsIndex' obsCardinality' obsCardinalityNext')
      (UInt256.ofNat 9) (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide) mem_cost
      (by
        dsimp [obsCardinalityNext']
        rw [hmask16, show ((⟨128⟩ : UInt256) + ⟨128⟩).toNat = 256 from by decide,
          slot0ReturnMem5_eq]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨255⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap2 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw and (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup5 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mstore 3
      (slot0ReturnMem6 sqrt' tick' obsIndex' obsCardinality' obsCardinalityNext'
        feeProtocol')
      (UInt256.ofNat 10) (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide) mem_cost
      (by
        dsimp [feeProtocol']
        rw [hmask8, show ((⟨128⟩ : UInt256) + ⟨160⟩).toNat = 288 from by decide,
          slot0ReturnMem6_eq]
        rfl)
      (by decide) (by evm_ov),
    raw iszero (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw iszero (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨192⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup4 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mstore 3
      (slot0ReturnMem sqrt' tick' obsIndex' obsCardinality' obsCardinalityNext'
        feeProtocol' unlocked')
      (UInt256.ofNat 11) (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide) mem_cost
      (by
        dsimp [unlocked', slot0BoolReturnWord]
        rw [show ((⟨128⟩ : UInt256) + ⟨192⟩).toNat = 320 from by decide,
          slot0ReturnMem_eq]
        rfl)
      (by decide) (by evm_ov)]
  exact evm_run rd938 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 11) (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) mem_cost
      (slot0ReturnMem_mload64 sqrt' tick' obsIndex' obsCardinality' obsCardinalityNext'
        feeProtocol' unlocked')
      (by decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup2 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw sub (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw ret 0
      (UInt256.toByteArray sqrt' ++ UInt256.toByteArray tick' ++
        UInt256.toByteArray obsIndex' ++ UInt256.toByteArray obsCardinality' ++
          UInt256.toByteArray obsCardinalityNext' ++ UInt256.toByteArray feeProtocol' ++
            UInt256.toByteArray unlocked')
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide) mem_cost
      (by
        dsimp [sqrt', tick', obsIndex', obsCardinality', obsCardinalityNext',
          feeProtocol', unlocked']
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨224⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat =
            224 from by decide]
        exact slot0ReturnMem_read128_224
          (UInt256.land sqrt slot0Uint160Mask) (UInt256.signextend ⟨2⟩ tick)
          (UInt256.land slot0Uint16Mask obsIndex)
          (UInt256.land slot0Uint16Mask obsCardinality)
          (UInt256.land slot0Uint16Mask obsCardinalityNext)
          (UInt256.land feeProtocol slot0Uint8Mask) (slot0BoolReturnWord unlocked))
      (by evm_ov)]

theorem uniswapV3PoolSlot0Evm {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 6 == I.calldata.extract 0 4) = true) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (slot0SqrtPriceX96Word σ I) ++
        UInt256.toByteArray (slot0TickReturnWord σ I) ++
          UInt256.toByteArray (slot0ObservationIndexWord σ I) ++
            UInt256.toByteArray (slot0ObservationCardinalityWord σ I) ++
              UInt256.toByteArray (slot0ObservationCardinalityNextWord σ I) ++
                UInt256.toByteArray (slot0FeeProtocolWord σ I) ++
                  UInt256.toByteArray (slot0BoolReturnWord (slot0UnlockedRawWord σ I))) := by
  obtain ⟨_, _, rdReturn⟩ := uniswapV3PoolSlot0EvmAtReturn
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  have hret := uniswapV3PoolSlot0Return hpatch rdReturn
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hsqrt : UInt256.land (slot0SqrtPriceX96Word σ I) slot0Uint160Mask =
      slot0SqrtPriceX96Word σ I := by
    exact slot0Uint160Mask_clean (by
      simpa [slot0SqrtPriceX96Word] using slot0Uint160Mask_bound (slot0SlotWord σ I))
  have htick : UInt256.signextend ⟨2⟩ (slot0TickReturnWord σ I) =
      slot0TickReturnWord σ I := by
    dsimp [slot0TickReturnWord]
    exact slot0SignextendTwo_idempotent
      (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 20))
  have hobsIndex : UInt256.land slot0Uint16Mask (slot0ObservationIndexWord σ I) =
      slot0ObservationIndexWord σ I := by
    exact slot0Uint16Mask_clean_left (by
      simpa [slot0ObservationIndexWord] using
        slot0Uint16Mask_bound (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 23)))
  have hobsCardinality :
      UInt256.land slot0Uint16Mask (slot0ObservationCardinalityWord σ I) =
        slot0ObservationCardinalityWord σ I := by
    exact slot0Uint16Mask_clean_left (by
      simpa [slot0ObservationCardinalityWord] using
        slot0Uint16Mask_bound (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 25)))
  have hobsCardinalityNext :
      UInt256.land slot0Uint16Mask (slot0ObservationCardinalityNextWord σ I) =
        slot0ObservationCardinalityNextWord σ I := by
    exact slot0Uint16Mask_clean_left (by
      simpa [slot0ObservationCardinalityNextWord] using
        slot0Uint16Mask_bound (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 27)))
  have hfee : UInt256.land (slot0FeeProtocolWord σ I) slot0Uint8Mask =
      slot0FeeProtocolWord σ I := by
    exact slot0Uint8Mask_clean (by
      simpa [slot0FeeProtocolWord] using
        slot0Uint8Mask_bound (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 29)))
  simpa [hsqrt, htick, hobsIndex, hobsCardinality, hobsCardinalityNext, hfee] using hret

theorem uniswapV3PoolSlot0BodyCore {v : PoolImmutables}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsel : (uniswapV3PoolSelBytes 6 == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch := uniswapV3PoolDispatch_slot0 (v := v) (cd := I.calldata) hsel
  have hdecode := uniswapV3PoolSlot0Decode (v := v) (I := I) hsz
  have hbody := uniswapV3PoolSlot0SourceBody (v := v) (cA := cA)
    (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hwv
  have hvalue := uniswapV3PoolSlot0ValueTransport (σ_evm := σ_evm)
    (σ_solm := σ_solm) (I := I) hAccounts
  have hrd := uniswapV3PoolSlot0Evm (v := v) (code := code)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel
  exact hrd.reEquivExecutionTransport hcode hdispatch hdecode hbody hvalue hAccounts
    (by
      rw [show slot0Transition.returnType =
        [uint160, int24, uint16, uint16, uint16, uint8, boolTy] from rfl]
      exact returnEquiv.returned rfl (slot0ReturnEncoding σ_evm I))

end Benchmarks.UniswapV3Pool
