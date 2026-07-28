import Benchmarks.UniswapV3Pool.Common

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

abbrev tickBitmapArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def tickBitmapSint16Value (w : UInt256) : Int :=
  let m := w.toNat % EVM.twoPow 16
  if m < EVM.twoPow 15 then (m : Int) else (m : Int) - (EVM.twoPow 16 : Int)

abbrev tickBitmapArgCleanWord (I : ExecutionEnv) : UInt256 :=
  UInt256.signextend ⟨1⟩ (tickBitmapArgWord I)

abbrev tickBitmapArgValue (I : ExecutionEnv) : Value :=
  .int (tickBitmapSint16Value (tickBitmapArgWord I))

abbrev tickBitmapArgKey (I : ExecutionEnv) : KeyValue :=
  .int (tickBitmapSint16Value (tickBitmapArgWord I))

abbrev tickBitmapStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (tickBitmapArgValue I)

abbrev tickBitmapStorageSlot (I : ExecutionEnv) : UInt256 :=
  tickBitmapSlot (tickBitmapArgKey I)

abbrev tickBitmapWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (tickBitmapStorageSlot I)

private theorem signextend_one_norm (w : UInt256) : UInt256.signextend ⟨1⟩ w =
    if UInt256.land w (UInt256.ofNat (2^15)) = ⟨0⟩ then
      UInt256.land w (UInt256.ofNat (2^15 - 1))
    else UInt256.lor w (UInt256.ofNat (UInt256.size - 2^15)) := by
  unfold UInt256.signextend
  rw [if_pos (by native_decide : (⟨1⟩ : UInt256).toNat ≤ 31)]
  have htest : (⟨1⟩ : UInt256) * ⟨8⟩ + ⟨7⟩ = ⟨15⟩ := by native_decide
  simp only [htest]
  have hsign : (⟨1⟩ : UInt256) <<< (⟨15⟩ : UInt256) = UInt256.ofNat (2^15) := by
    native_decide
  rw [hsign]
  have hsub1 : UInt256.ofNat (2 ^ 15) - ⟨1⟩ = UInt256.ofNat (2 ^ 15 - 1) := by
    native_decide
  have hsub2 : UInt256.size.toUInt256 - UInt256.ofNat (2 ^ 15) =
      UInt256.ofNat (UInt256.size - 2 ^ 15) := by
    native_decide
  rw [hsub1, hsub2]
  change (if UInt256.land w (UInt256.ofNat (2 ^ 15)) ≠ ⟨0⟩ then
      UInt256.lor w (UInt256.ofNat (UInt256.size - 2 ^ 15))
    else UInt256.land w (UInt256.ofNat (2 ^ 15 - 1))) = _
  by_cases hzero : UInt256.land w (UInt256.ofNat (2 ^ 15)) = ⟨0⟩
  · rw [if_neg (by exact not_not.mpr hzero), if_pos hzero]
  · rw [if_pos hzero, if_neg hzero]

private theorem signextend_one_sign_bit_zero (w : UInt256)
    (hm : w.toNat % EVM.twoPow 16 < EVM.twoPow 15) :
    UInt256.land w (UInt256.ofNat (2^15)) = ⟨0⟩ := by
  apply u256_inj
  rw [u256_land_toNat]
  have hbitm : (w.toNat % EVM.twoPow 16).testBit 15 = false := by
    exact Nat.testBit_lt_two_pow (x := w.toNat % EVM.twoPow 16) (i := 15) hm
  change (w.toNat % 2 ^ 16).testBit 15 = false at hbitm
  rw [Nat.testBit_mod_two_pow] at hbitm
  have hbitw : w.toNat.testBit 15 = false := by simpa using hbitm
  rw [show (UInt256.ofNat (2 ^ 15)).toNat = 2 ^ 15 by
    exact ulit_toNat' _ (by norm_num [UInt256.size])]
  change (w.toNat &&& 2 ^ 15) % UInt256.size = (⟨0⟩ : UInt256).toNat
  rw [Nat.and_two_pow, hbitw]
  norm_num

private theorem signextend_one_sign_bit_ne_zero (w : UInt256)
    (hm : ¬ w.toNat % EVM.twoPow 16 < EVM.twoPow 15) :
    UInt256.land w (UInt256.ofNat (2^15)) ≠ ⟨0⟩ := by
  intro hzero
  have hmhi : w.toNat % EVM.twoPow 16 < EVM.twoPow 16 :=
    Nat.mod_lt _ (by norm_num [EVM.twoPow])
  have hmge : EVM.twoPow 15 ≤ w.toNat % EVM.twoPow 16 := by omega
  have hdiv : (w.toNat % EVM.twoPow 16) / EVM.twoPow 15 = 1 := by
    apply Nat.div_eq_of_lt_le (k := 1)
    · simpa [EVM.twoPow] using hmge
    · simpa [EVM.twoPow] using hmhi
  have hbitm : (w.toNat % EVM.twoPow 16).testBit 15 = true := by
    simp [Nat.testBit, Nat.shiftRight_eq_div_pow, EVM.twoPow]
    have hdiv' : w.toNat % 65536 / 32768 = 1 := by simpa [EVM.twoPow] using hdiv
    rw [hdiv']
  change (w.toNat % 2 ^ 16).testBit 15 = true at hbitm
  rw [Nat.testBit_mod_two_pow] at hbitm
  have hbitw : w.toNat.testBit 15 = true := by simpa using hbitm
  have htoNat := congrArg UInt256.toNat hzero
  rw [u256_land_toNat] at htoNat
  rw [show (UInt256.ofNat (2 ^ 15)).toNat = 2 ^ 15 by
    exact ulit_toNat' _ (by norm_num [UInt256.size])] at htoNat
  change (w.toNat &&& 2 ^ 15) % UInt256.size = (⟨0⟩ : UInt256).toNat at htoNat
  rw [Nat.and_two_pow, hbitw] at htoNat
  norm_num [UInt256.size] at htoNat

private theorem nat_lor_high_mask_15 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.lor n (2 ^ 256 - 2 ^ 15) = n % 2 ^ 15 + (2 ^ 256 - 2 ^ 15) := by
  have hmask : 2 ^ 256 - 2 ^ 15 = (2 ^ (256 - 15) - 1) <<< 15 := by
    rw [Nat.shiftLeft_eq]
    norm_num [Nat.pow_add]
  rw [hmask]
  rw [Nat.shiftLeft_eq]
  rw [← nat_lor_shift_add (n % 2 ^ 15) (2 ^ (256 - 15) - 1) 15
    (Nat.mod_lt _ (by norm_num))]
  apply Nat.eq_of_testBit_eq
  intro i
  change (n ||| ((2 ^ (256 - 15) - 1) * 2 ^ 15)).testBit i =
    ((n % 2 ^ 15) ||| ((2 ^ (256 - 15) - 1) * 2 ^ 15)).testBit i
  rw [Nat.testBit_or, Nat.testBit_or]
  rw [show (2 ^ (256 - 15) - 1) * 2 ^ 15 =
      (2 ^ (256 - 15) - 1) <<< 15 by rw [Nat.shiftLeft_eq]]
  rw [testBit_shiftLeft]
  by_cases hi15 : i < 15
  · rw [if_pos hi15]
    conv_rhs => rw [Nat.testBit_mod_two_pow]
    simp [hi15]
  · rw [if_neg hi15]
    rw [Nat.testBit_two_pow_sub_one]
    by_cases hi256 : i < 256
    · have hlt241 : i - 15 < 256 - 15 := by omega
      rw [decide_eq_true hlt241]
      simp
    · have hnbit : n.testBit i = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have hmodbit : (n % 2 ^ 15).testBit i = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 15))
            (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have hnot241 : ¬ i - 15 < 256 - 15 := by omega
      rw [decide_eq_false hnot241, hnbit, hmodbit]

private theorem wordOfInt_sint16_neg_toNat (m : Nat) (hmhi : m < EVM.twoPow 16) :
    (EVM.wordOfInt ((m : Int) - (EVM.twoPow 16 : Int))).toNat =
      UInt256.size - (EVM.twoPow 16 - m) := by
  have hneg : ((m : Int) - (EVM.twoPow 16 : Int)) < 0 := by
    norm_num [EVM.twoPow] at hmhi ⊢
    omega
  have hnatAbs : ((m : Int) - (EVM.twoPow 16 : Int)).natAbs = EVM.twoPow 16 - m := by
    norm_num [EVM.twoPow] at hmhi ⊢
    omega
  have hdiffPos : EVM.twoPow 16 - m ≠ 0 := by
    norm_num [EVM.twoPow] at hmhi ⊢
    omega
  have hdiffLt : EVM.twoPow 16 - m < EVM.wordModulus := by
    norm_num [EVM.wordModulus, EVM.twoPow] at hmhi ⊢
    omega
  unfold EVM.wordOfInt
  rw [if_pos hneg]
  rw [hnatAbs, Nat.mod_eq_of_lt hdiffLt, if_neg hdiffPos]
  change (UInt256.ofNat (EVM.wordModulus - (EVM.twoPow 16 - m))).toNat = _
  rw [ulit_toNat']
  · simp [EVM.wordModulus, EVM.twoPow, UInt256.size]
  · norm_num [EVM.wordModulus, EVM.twoPow, UInt256.size] at hmhi ⊢
    omega

private theorem wordOfInt_sint16Value_eq_signextend_one (w : UInt256) :
    EVM.wordOfInt (tickBitmapSint16Value w) = UInt256.signextend ⟨1⟩ w := by
  apply u256_inj
  rw [signextend_one_norm]
  unfold tickBitmapSint16Value
  let m := w.toNat % EVM.twoPow 16
  have hmdef : m = w.toNat % EVM.twoPow 16 := rfl
  have hmhi : m < EVM.twoPow 16 := by
    rw [hmdef]
    exact Nat.mod_lt _ (by norm_num [EVM.twoPow])
  have hwlt : w.toNat < UInt256.size := by
    simp [UInt256.toNat]
  by_cases h : m < EVM.twoPow 15
  · have hzero : UInt256.land w (UInt256.ofNat (2 ^ 15)) = ⟨0⟩ := by
      apply signextend_one_sign_bit_zero
      rwa [← hmdef]
    rw [if_pos hzero]
    have hval :
        (let m := w.toNat % EVM.twoPow 16
         if m < EVM.twoPow 15 then (m : Int) else (m : Int) - (EVM.twoPow 16 : Int)) =
          (m : Int) := by
      dsimp
      have h' : w.toNat % EVM.twoPow 16 < EVM.twoPow 15 := by rwa [← hmdef]
      rw [if_pos h']
      omega
    rw [hval]
    have hword : (EVM.wordOfInt (m : Int)).toNat = m := by
      unfold EVM.wordOfInt
      rw [if_neg (by omega)]
      unfold EVM.word EVM.uintN UInt256.toNat
      change m % EVM.twoPow 256 = m
      apply Nat.mod_eq_of_lt
      norm_num [EVM.twoPow] at hmhi ⊢
      omega
    rw [hword]
    rw [u256_land_toNat]
    rw [show (UInt256.ofNat (2 ^ 15 - 1)).toNat = 2 ^ 15 - 1 by
      exact ulit_toNat' _ (by norm_num [UInt256.size])]
    change m = Nat.land w.toNat (2 ^ 15 - 1) % UInt256.size
    rw [nat_land_mask_eq_mod]
    have hmdef' : m = w.toNat % 2 ^ 16 := by simpa [EVM.twoPow] using hmdef
    have hmod15 : w.toNat % 2 ^ 15 = m := by
      have hmod16 : w.toNat % 2 ^ 16 = m := hmdef'.symm
      rw [← Nat.mod_mod_of_dvd (a := w.toNat) (show 2 ^ 15 ∣ 2 ^ 16 by norm_num)]
      rw [hmod16]
      exact Nat.mod_eq_of_lt (by simpa [EVM.twoPow] using h)
    rw [hmod15]
    rw [Nat.mod_eq_of_lt (by
      norm_num [EVM.twoPow, UInt256.size] at hmhi ⊢
      omega)]
  · have hne : UInt256.land w (UInt256.ofNat (2 ^ 15)) ≠ ⟨0⟩ := by
      apply signextend_one_sign_bit_ne_zero
      rwa [← hmdef]
    rw [if_neg hne]
    have hval :
        (let m := w.toNat % EVM.twoPow 16
         if m < EVM.twoPow 15 then (m : Int) else (m : Int) - (EVM.twoPow 16 : Int)) =
          (m : Int) - (EVM.twoPow 16 : Int) := by
      dsimp
      have h' : ¬ w.toNat % EVM.twoPow 16 < EVM.twoPow 15 := by
        intro hh
        exact h (by rwa [hmdef])
      rw [if_neg h']
      omega
    rw [hval]
    have hword := wordOfInt_sint16_neg_toNat m hmhi
    rw [hword]
    rw [u256_lor_toNat]
    rw [show (UInt256.ofNat (UInt256.size - 2 ^ 15)).toNat = UInt256.size - 2 ^ 15 by
      exact ulit_toNat' _ (by norm_num [UInt256.size])]
    have hlor := nat_lor_high_mask_15 w.toNat (by simpa [UInt256.size] using hwlt)
    change UInt256.size - (EVM.twoPow 16 - m) =
      (Nat.lor w.toNat (2 ^ 256 - 2 ^ 15)) % UInt256.size
    rw [hlor]
    have hmdef' : m = w.toNat % 2 ^ 16 := by simpa [EVM.twoPow] using hmdef
    have hmod15 : w.toNat % 2 ^ 15 = m - 2 ^ 15 := by
      have hge : 2 ^ 15 ≤ m := by
        have hnot : ¬ m < 2 ^ 15 := by simpa [EVM.twoPow] using h
        omega
      have hmhi' : m < 2 ^ 16 := by simpa [EVM.twoPow] using hmhi
      have hmod16 : w.toNat % 2 ^ 16 = m := hmdef'.symm
      rw [← Nat.mod_mod_of_dvd (a := w.toNat) (show 2 ^ 15 ∣ 2 ^ 16 by norm_num)]
      rw [hmod16]
      rw [Nat.mod_eq_sub_mod hge]
      rw [Nat.mod_eq_of_lt (by omega : m - 2 ^ 15 < 2 ^ 15)]
    rw [hmod15]
    norm_num [UInt256.size, EVM.twoPow] at h hmhi ⊢
    omega

theorem tickBitmapArgKeyWord (I : ExecutionEnv) :
    keyValueToWord (tickBitmapArgKey I) = tickBitmapArgCleanWord I := by
  unfold tickBitmapArgKey tickBitmapArgCleanWord tickBitmapArgWord keyValueToWord
  exact wordOfInt_sint16Value_eq_signextend_one (calldataWord I.calldata 4)

theorem decodeScalarWordsWithMode_int16_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05 [int16] bytes 0 =
      some [Value.int (tickBitmapSint16Value (ABI.bytesToWord (bytes.take 32)))] := by
  simp only [decodeScalarWordsWithMode?]
  unfold decodeScalarWordWithMode? readWord? readBytes? int16 int16Int tickBitmapSint16Value
  simp only [List.drop_zero]
  rw [if_pos hlen0]
  simp only [Option.bind, bind]
  unfold decodeABIWord?
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  rfl

theorem decodeScalarWordsWithMode_int16_none_short {bytes : List UInt8}
    (hshort : bytes.length < 32) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05 [int16] bytes 0 = none := by
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ (bytes.take 32).length = 32 := by
    rw [List.length_take]
    omega
  unfold decodeScalarWordWithMode? readWord? readBytes? int16 int16Int
  simp only [List.drop_zero]
  rw [if_neg htake0n]
  simp only [Option.bind, bind]

theorem uniswapV3PoolTickBitmapDecodeOk {v : PoolImmutables} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode
      (tickbitmapTransition.params.map Param.name)
      (transitionSignature tickbitmapTransition).paramTypes I.calldata = some (tickBitmapStore I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      calldataWord I.calldata 4 :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  rw [show (config v).abiDecodeMode = DecodeMode.legacySolc05 from rfl]
  rw [decodeCalldataWithMode_legacyScalarWords_eq
    (names := tickbitmapTransition.params.map Param.name)
    (types := (transitionSignature tickbitmapTransition).paramTypes) (cd := I.calldata)]
  · rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
    change (match decodeScalarWordsWithMode? DecodeMode.legacySolc05 [int16]
        (I.calldata.toList.drop 4) 0 with
      | some values => decodeCalldata.insertValues ["arg0"] values ∅
      | none => none) = some (tickBitmapStore I)
    rw [decodeScalarWordsWithMode_int16_ok (bytes := I.calldata.toList.drop 4) htake4]
    change decodeCalldata.insertValues ["arg0"]
        [Value.int
          (tickBitmapSint16Value (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)))] ∅ =
      some (tickBitmapStore I)
    simp [decodeCalldata.insertValues, tickBitmapStore, tickBitmapArgValue, tickBitmapArgWord]
    rw [hword4]
  · native_decide

theorem uniswapV3PoolTickBitmapDecodeShort {v : PoolImmutables} {I : ExecutionEnv}
    (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode (config v).abiDecodeMode
      (tickbitmapTransition.params.map Param.name)
      (transitionSignature tickbitmapTransition).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [show (config v).abiDecodeMode = DecodeMode.legacySolc05 from rfl]
  rw [decodeCalldataWithMode_legacyScalarWords_eq
    (names := tickbitmapTransition.params.map Param.name)
    (types := (transitionSignature tickbitmapTransition).paramTypes) (cd := I.calldata)]
  · by_cases hsz4 : I.calldata.size < 4
    · rw [if_pos (by rw [htlen]; omega : I.calldata.toList.length < 4)]
    · rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
      change (match decodeScalarWordsWithMode? DecodeMode.legacySolc05 [int16]
          (I.calldata.toList.drop 4) 0 with
        | some values => decodeCalldata.insertValues ["arg0"] values ∅
        | none => none) = none
      rw [decodeScalarWordsWithMode_int16_none_short
        (bytes := I.calldata.toList.drop 4) (by rw [List.length_drop, htlen]; omega)]
  · native_decide

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolDispatch_tickBitmap {v : PoolImmutables} {cd : ByteArray}
    (hsel : (uniswapV3PoolSelBytes 12 == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some tickbitmapTransition := by
  apply dispatchMsg_eq_some_of_split
    (pre := [burnTransition, collectTransition v, collectprotocolTransition v, factoryTransition v,
      feeTransition v, feegrowthglobal0X128Transition, feegrowthglobal1X128Transition,
      flashTransition v, increaseobservationcardinalitynextTransition v, initializeTransition,
      liquidityTransition, maxliquiditypertickTransition v, mintTransition v, observationsTransition,
      observeTransition v, positionsTransition, protocolfeesTransition, setfeeprotocolTransition v,
      slot0Transition, snapshotcumulativesinsideTransition v, swapTransition v])
    (post := [tickspacingTransition v, ticksTransition, token0Transition v, token1Transition v])
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, burnSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 17) (j := 12)
          (by native_decide) hsel
    · rw [selectorOf, collectSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 10) (j := 12)
          (by native_decide) hsel
    · rw [selectorOf, collectProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 15) (j := 12)
          (by native_decide) hsel
    · rw [selectorOf, factorySelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 19) (j := 12)
          (by native_decide) hsel
    · rw [selectorOf, feeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 22) (j := 12)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal0X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 23) (j := 12)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal1X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 8) (j := 12)
          (by native_decide) hsel
    · rw [selectorOf, flashSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 9) (j := 12)
          (by native_decide) hsel
    · rw [selectorOf, increaseObservationCardinalityNextSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 5) (j := 12)
          (by native_decide) hsel
    · rw [selectorOf, initializeSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 25) (j := 12)
          (by native_decide) hsel
    · rw [selectorOf, liquiditySelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 2) (j := 12)
          (by native_decide) hsel
    · rw [selectorOf, maxLiquidityPerTickSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 13) (j := 12)
          (by native_decide) hsel
    · rw [selectorOf, mintSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 7) (j := 12)
          (by native_decide) hsel
    · rw [selectorOf, observationsSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 4) (j := 12)
          (by native_decide) hsel
    · rw [selectorOf, observeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 16) (j := 12)
          (by native_decide) hsel
    · rw [selectorOf, positionsSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 11) (j := 12)
          (by native_decide) hsel
    · rw [selectorOf, protocolFeesSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 3) (j := 12)
          (by native_decide) hsel
    · rw [selectorOf, setFeeProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 14) (j := 12)
          (by native_decide) hsel
    · rw [selectorOf, slot0SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 6) (j := 12)
          (by native_decide) hsel
    · rw [selectorOf, snapshotCumulativesInsideSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 18) (j := 12)
          (by native_decide) hsel
    · rw [selectorOf, swapSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 1) (j := 12)
          (by native_decide) hsel
  · rw [selectorOf, tickBitmapSelectorBytes]
    simpa [uniswapV3PoolSelBytes] using hsel

theorem tickBitmapStore_arg0 (I : ExecutionEnv) :
    Std.HashMap.get? (tickBitmapStore I) "arg0" = some (tickBitmapArgValue I) := by
  simp [tickBitmapStore]

theorem evalExpr_tickBitmap_arg0 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := tickBitmapStore I } evm
      (.var "arg0") = .ok (tickBitmapArgValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [tickBitmapStore_arg0]

def tickBitmapEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "tickBitmap", steps := [.mindex (tickBitmapArgKey I)] }

theorem evalStorageRef_tickBitmap {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalStorageRef (config v) { contract := contract v, locals := tickBitmapStore I } evm
      (tickBitmapRef (.var "arg0")) = .ok (tickBitmapEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, tickBitmapRef,
    tickBitmapEvaledRef, evalExpr_tickBitmap_arg0, tickBitmapArgValue, tickBitmapArgKey,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalExpr_tickBitmap_storage {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := tickBitmapStore I } evm
      (.storage (tickBitmapRef (.var "arg0"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (tickBitmapStorageSlot I)).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint256Int)
    (slot := tickBitmapRef (.var "arg0"))
    (er := tickBitmapEvaledRef I)
    (loc := loc (tickBitmapStorageSlot I) ⟨0, by decide⟩ ⟨32, by decide⟩
      (by decide) (.int uint256Int))
    (hbase := by simp [tickBitmapStore, tickBitmapRef])
    (her := evalStorageRef_tickBitmap evm I)
    (hty := by
      simp [storageTypeAt?, tickBitmapEvaledRef, contract, storageDecls, uint256St,
        storageTypeStep?])
    (hloc := by
      funext evm'
      simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, tickBitmapEvaledRef,
        tickBitmapStorageSlot, loc])]
  simpa [loc, uint256Loc] using storageLocLoad_uint256 evm (tickBitmapStorageSlot I)

theorem uniswapV3PoolTickBitmapSourceBody {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (tickBitmapStore I) tickbitmapTransition.body
      (.returned { contract := contract v, locals := tickBitmapStore I }
        (initState cA gh bl σ σ₀ g A I)
        (some [Value.int (Int.ofNat (tickBitmapWord σ I).toNat)])) := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (tickBitmapStore I)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [.storage (tickBitmapRef (.var "arg0"))] ] _
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true (by simp [initState, hwv]))).returns (by
      simpa [initState, tickBitmapWord, tickBitmapStorageSlot, solcSlotWord] using
        evalExpr_tickBitmap_storage (v := v) (initState cA gh bl σ σ₀ g A I) I)

theorem uniswapV3PoolTickBitmapValueTransport {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    some [Value.int (Int.ofNat (tickBitmapWord σ_solm I).toNat)] =
      some [Value.int (Int.ofNat (tickBitmapWord σ_evm I).toNat)] := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner
    (tickBitmapStorageSlot I) (⟨0⟩ : UInt256)
  dsimp [tickBitmapWord, solcSlotWord]
  rw [← hslot]

private theorem uniswapV3PoolTickBitmapGetterPatchDisjoint1 {v : PoolImmutables}
    {pc : UInt256} (hlo : 8154 ≤ pc.toNat) (hhi : pc.toNat + 1 ≤ 8174) :
    ∀ p ∈ patches v, pc.toNat + 1 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

private theorem uniswapV3PoolTickBitmapGetterPatchDisjoint2 {v : PoolImmutables}
    {pc : UInt256} (hlo : 8154 ≤ pc.toNat) (hhi : pc.toNat + 2 ≤ 8174) :
    ∀ p ∈ patches v, pc.toNat + 2 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

private theorem uniswapV3PoolTickBitmapDecodePatchedPush1 {v : PoolImmutables}
    {code : ByteArray} {pc n : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hwin : pc.toNat + 2 ≤ uniswapV3PoolBytecode.size)
    (hdisj : ∀ p ∈ patches v, pc.toNat + 2 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat)
    (hgetTemplate : uniswapV3PoolBytecode.get? pc.toNat = some 0x60)
    (hval : uInt256OfByteArray
        (uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 1)) = n) :
    decode code pc = some (.Push .PUSH1, some (n, 1)) := by
  have hsize := uniswapV3PoolPatchedSize hpatch
  have htemplate64 : uniswapV3PoolBytecode.size < 2 ^ 64 := by native_decide
  have hget : code.get? pc.toNat = uniswapV3PoolBytecode.get? pc.toNat := by
    apply get?_eq_of_extract_one
    · rw [hsize]
      omega
    · omega
    · exact patchRuntime_extract_eq (start := pc.toNat) (stop := pc.toNat + 1)
        (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
        (by omega) (by omega)
        (fun p hp => by
          rcases hdisj p hp with hbefore | hafter
          · exact Or.inl (by omega)
          · exact Or.inr hafter)
        hpatch
  have hextract :
      code.extract' pc.toNat.succ (pc.toNat.succ + 1) =
        uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 1) := by
    unfold ByteArray.extract'
    have hguard :
        (decide (pc.toNat.succ < 2 ^ 64) && decide (pc.toNat.succ + 1 < 2 ^ 64)) =
          true := by
      rw [Bool.and_eq_true]
      constructor <;> rw [decide_eq_true_eq] <;> omega
    rw [if_pos hguard, if_pos hguard]
    exact patchRuntime_extract_eq (start := pc.toNat.succ) (stop := pc.toNat.succ + 1)
      (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
      (by omega) (by omega)
      (fun p hp => by
        rcases hdisj p hp with hbefore | hafter
        · exact Or.inl hbefore
        · exact Or.inr (by omega))
      hpatch
  have hgetSome : code.get? pc.toNat = some 0x60 := by
    rw [hget, hgetTemplate]
  have hparse : (some (0x60 : UInt8) >>= parseInstr) = some (.Push .PUSH1) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH1,
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 1)), 1)) =
    some (Operation.Push Operation.POp.PUSH1, some (n, 1))
  rw [hextract, hval]

private theorem uniswapV3PoolPatchPreservesJumpDest8154 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨8154⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched8154 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨8154⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest8154

theorem uniswapV3PoolTickBitmapGetterWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcSingleMappingGetterWf code ⟨8154⟩ ⟨6⟩ := by
  dsimp [solcSingleMappingGetterWf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8154⟩) (byte := 0x5b)
      (op := .JUMPDEST) hpatch (by native_decide)
      (uniswapV3PoolTickBitmapGetterPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · exact uniswapV3PoolTickBitmapDecodePatchedPush1 (pc := ⟨8155⟩) (n := ⟨6⟩)
      hpatch (by native_decide)
      (uniswapV3PoolTickBitmapGetterPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  · exact uniswapV3PoolTickBitmapDecodePatchedPush1 (pc := ⟨8157⟩) (n := ⟨32⟩)
      hpatch (by native_decide)
      (uniswapV3PoolTickBitmapGetterPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8159⟩) (byte := 0x52)
      (op := .MSTORE) hpatch (by native_decide)
      (uniswapV3PoolTickBitmapGetterPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · exact uniswapV3PoolTickBitmapDecodePatchedPush1 (pc := ⟨8160⟩) (n := ⟨0⟩)
      hpatch (by native_decide)
      (uniswapV3PoolTickBitmapGetterPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8162⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide)
      (uniswapV3PoolTickBitmapGetterPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8163⟩) (byte := 0x81)
      (op := .DUP2) hpatch (by native_decide)
      (uniswapV3PoolTickBitmapGetterPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8164⟩) (byte := 0x52)
      (op := .MSTORE) hpatch (by native_decide)
      (uniswapV3PoolTickBitmapGetterPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · exact uniswapV3PoolTickBitmapDecodePatchedPush1 (pc := ⟨8165⟩) (n := ⟨64⟩)
      hpatch (by native_decide)
      (uniswapV3PoolTickBitmapGetterPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8167⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide)
      (uniswapV3PoolTickBitmapGetterPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8168⟩) (byte := 0x20)
      (op := .KECCAK256) hpatch (by native_decide)
      (uniswapV3PoolTickBitmapGetterPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8169⟩) (byte := 0x54)
      (op := .SLOAD) hpatch (by native_decide)
      (uniswapV3PoolTickBitmapGetterPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8170⟩) (byte := 0x81)
      (op := .DUP2) hpatch (by native_decide)
      (uniswapV3PoolTickBitmapGetterPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8171⟩) (byte := 0x56)
      (op := .JUMP) hpatch (by native_decide)
      (uniswapV3PoolTickBitmapGetterPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)

theorem uniswapV3PoolTickBitmapReturnWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcReturnWordFromMemWf code ⟨1118⟩ := by
  dsimp [solcReturnWordFromMemWf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide

theorem tickBitmapStorageSlot_eq_solcMappingSlot (I : ExecutionEnv) :
    tickBitmapStorageSlot I = solcMappingSlot ⟨6⟩ (tickBitmapArgCleanWord I) := by
  unfold tickBitmapStorageSlot tickBitmapSlot mapSlot solcMappingSlot
  rw [tickBitmapArgKeyWord I]

private def tickBitmapStSignextend (s : State) (res : UInt256) (t : List UInt256) :
    State :=
  { s with
      machineState.stack := res :: t,
      machineState.gasAvailable := s.machineState.gasAvailable.subNat 5
      machineState.pc := s.machineState.pc + ⟨1⟩
      machineState.execLength := s.machineState.execLength + 1 }

private theorem tickBitmapSignextendXstep {code : ByteArray} {s : State} {pc a b : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pc)
    (hdec : decode code pc = some (.SIGNEXTEND, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s =
      if s.machineState.gasAvailable.toNat < 5 then .error .OutOfGass
      else .ok (tickBitmapStSignextend s (UInt256.signextend a b) t, .none) := by
  have hdecS : decode s.executionEnv.code s.machineState.pc = some (.SIGNEXTEND, .none) := by
    rw [hcode, hpc]
    exact hdec
  have hstep := step_signextend s hdecS
  have hnoOverflow : ¬ 1024 ≤ t.length := by omega
  simpa [hcode, hstk, GasConstants.Glow, tickBitmapStSignextend, hnoOverflow] using hstep

private theorem tickBitmapRDSignextend {code : ByteArray} {ee : ExecutionEnv}
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
  · have st := tickBitmapSignextendXstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 5
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨tickBitmapStSignextend s (UInt256.signextend a b) t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega,
        by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [tickBitmapStSignextend]; exact hcode
      · simp only [tickBitmapStSignextend]; rw [hpc]
      · rfl
      · simp only [tickBitmapStSignextend]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [tickBitmapStSignextend]; exact hmem
      · simp only [tickBitmapStSignextend]; exact haw
      · simp only [tickBitmapStSignextend]; exact hrdata
      · simp only [tickBitmapStSignextend]; exact hacc
      · exact hee
      · exact hworld

theorem uniswapV3PoolTickBitmapReachEntry {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 12 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1446⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := uniswapV3PoolReachSelector32
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hword : solcSelectorWord I = uniswapV3PoolSelNat 12 := by
    simpa [uniswapV3PoolSelBytes, uniswapV3PoolSelNat] using
      solcSelectorWord_eq_of_beq I hsz 0x53 0x39 0xc2 0x96
        (uniswapV3PoolSelNat 12) (by native_decide) hsel
  have hgt32 : UInt256.gt (armSelNat code ⟨32⟩) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h239 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨239⟩) hpatch h32 hgt32
  have hgt239 : UInt256.gt (armSelNat code ⟨239⟩) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h250 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨250⟩) hpatch h239 hgt239
  have hgt250 : UInt256.gt (armSelNat code ⟨250⟩) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h261 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨261⟩) hpatch h250 hgt250
  have hmiss9 : (uniswapV3PoolSelBytes 9 == I.calldata.extract 0 4) = false :=
    uniswapV3PoolSelectorMissOfHit I (by native_decide) hsel
  have h272 := uniswapV3PoolSelectorArmMissToOf (i := 9) (next := ⟨272⟩)
    hpatch hsz hmiss9 h261
  have hmiss10 : (uniswapV3PoolSelBytes 10 == I.calldata.extract 0 4) = false :=
    uniswapV3PoolSelectorMissOfHit I (by native_decide) hsel
  have h283 := uniswapV3PoolSelectorArmMissToOf (i := 10) (next := ⟨283⟩)
    hpatch hsz hmiss10 h272
  have hmiss11 : (uniswapV3PoolSelBytes 11 == I.calldata.extract 0 4) = false :=
    uniswapV3PoolSelectorMissOfHit I (by native_decide) hsel
  have h294 := uniswapV3PoolSelectorArmMissToOf (i := 11) (next := ⟨294⟩)
    hpatch hsz hmiss11 h283
  have h1446 := uniswapV3PoolSelectorArmHitTo (i := 12) (target := ⟨1446⟩)
    hpatch hsz hsel h294
  exact ⟨_, _, h1446⟩

private theorem uniswapV3PoolTickBitmapDecodedReachRoutine {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {de ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨1468⟩ (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8154⟩ (tickBitmapArgCleanWord ee :: ret :: R)
      mem aw rdata acc k' C' := by
  have rd1469 : RD code ee g s0 ⟨1469⟩ (de :: ⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1) (C + 1) := by
    simpa using h.jumpdest
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd1470 : RD code ee g s0 ⟨1470⟩ (⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1 + 1) (C + 1 + 2) := by
    simpa using rd1469.pop
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd1471 : RD code ee g s0 ⟨1471⟩ (tickBitmapArgWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1) (C + 1 + 2 + 3) := by
    simpa [tickBitmapArgWord, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using (rd1470.calldataload
        (by
          rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
          native_decide)
        (by evm_ov))
  have rd1473 : RD code ee g s0 ⟨1473⟩ (⟨1⟩ :: tickBitmapArgWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1) (C + 1 + 2 + 3 + 3) := by
    simpa using rd1471.push1 ⟨1⟩
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd1474 : RD code ee g s0 ⟨1474⟩ (tickBitmapArgCleanWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1) (C + 1 + 2 + 3 + 3 + 5) := by
    simpa [tickBitmapArgCleanWord] using
      (tickBitmapRDSignextend rd1473
        (by
          rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
          native_decide)
        (by evm_ov))
  have rd1477 : RD code ee g s0 ⟨1477⟩ (⟨8154⟩ :: tickBitmapArgCleanWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1 + 1)
        (C + 1 + 2 + 3 + 3 + 5 + 3) := by
    simpa using rd1474.push2 ⟨8154⟩
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  exact ⟨_, _, rd1477.jump
    (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide)
    (uniswapV3PoolJumpDestPatched8154 hpatch)
    (by evm_ov)⟩

set_option maxHeartbeats 3000000 in
private theorem uniswapV3PoolTickBitmapExternalLenOk {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1446⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1468⟩
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨1118⟩ ::
        [solcSelectorWord I])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact RD.solcExternalStaticArgsLenOk (need := ⟨32⟩)
    (entry := ⟨1446⟩) (ret := ⟨1118⟩) (decoded := ⟨1468⟩) hreach
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide))
    (solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)

set_option maxHeartbeats 2000000 in
private theorem uniswapV3PoolTickBitmapDecodedToLoaded {v : PoolImmutables}
    {code : ByteArray} {cA gh bl σ σ₀ A I} {g : Sat256} {de : UInt256} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (rdDecoded : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1468⟩
      (de :: ⟨4⟩ :: ⟨1118⟩ :: [solcSelectorWord I])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1118⟩
      (tickBitmapWord σ I :: ⟨1118⟩ :: [solcSelectorWord I])
      (solcMappingHashMem ⟨6⟩ (tickBitmapArgCleanWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rdRoutine⟩ :=
    uniswapV3PoolTickBitmapDecodedReachRoutine hpatch rdDecoded
      (by simp only [List.length_singleton]; omega)
  obtain ⟨_, _, rdLoaded0⟩ := RD.solcSingleMappingGetter (baseSlot := ⟨6⟩)
    (key := tickBitmapArgCleanWord I) (ret := ⟨1118⟩) (R := [solcSelectorWord I])
    rdRoutine (uniswapV3PoolTickBitmapGetterWf hpatch)
    (uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide))
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by
    simpa [tickBitmapWord, tickBitmapStorageSlot_eq_solcMappingSlot I] using rdLoaded0⟩

private theorem uniswapV3PoolTickBitmapLoadedToReturn {v : PoolImmutables}
    {code : ByteArray} {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (rdLoaded : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1118⟩
      (tickBitmapWord σ I :: ⟨1118⟩ :: [solcSelectorWord I])
      (solcMappingHashMem ⟨6⟩ (tickBitmapArgCleanWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (tickBitmapWord σ I)) := by
  exact RD.solcReturnWordFromMem rdLoaded
    (uniswapV3PoolTickBitmapReturnWf hpatch)
    (solcMappingHashMem_mload64 ⟨6⟩ (tickBitmapArgCleanWord I))
    (by rfl)
    (solcScratchReturnMem_mload64 (tickBitmapWord σ I)
      (solcMappingHashMem_size ⟨6⟩ (tickBitmapArgCleanWord I))
      (solcMappingHashMem_read64 ⟨6⟩ (tickBitmapArgCleanWord I)))
    (solcScratchReturnMem_read128 (tickBitmapWord σ I)
      (solcMappingHashMem_size ⟨6⟩ (tickBitmapArgCleanWord I)))
    (by simp only [List.length_singleton]; omega)

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolTickBitmapEvm {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 12 == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (tickBitmapWord σ I)) := by
  have hreach := uniswapV3PoolTickBitmapReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  have hdecoded := uniswapV3PoolTickBitmapExternalLenOk hpatch hreach hsz36 hsize
  obtain ⟨_, _, rdDecoded⟩ := hdecoded
  obtain ⟨_, _, rdLoaded⟩ := uniswapV3PoolTickBitmapDecodedToLoaded hpatch rdDecoded
  exact uniswapV3PoolTickBitmapLoadedToReturn hpatch rdLoaded

theorem uniswapV3PoolTickBitmapEvmDecodeShort {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 12 == I.calldata.extract 0 4) = true)
    (hshort : I.calldata.size < 36) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have hreach := uniswapV3PoolTickBitmapReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by
      rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      omega) hsize]
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  exact RD.solcExternalStaticArgsShortReverts (need := ⟨32⟩)
    (entry := ⟨1446⟩) (ret := ⟨1118⟩) (decoded := ⟨1468⟩) hreach
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    hlt

theorem uniswapV3PoolTickBitmapBodyCore {v : PoolImmutables}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsel : (uniswapV3PoolSelBytes 12 == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch := uniswapV3PoolDispatch_tickBitmap (v := v) (cd := I.calldata) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := uniswapV3PoolTickBitmapDecodeOk (v := v) (I := I) hsz36
    have hbody := uniswapV3PoolTickBitmapSourceBody (v := v) (cA := cA)
      (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hwv
    have hvalue := uniswapV3PoolTickBitmapValueTransport (σ_evm := σ_evm)
      (σ_solm := σ_solm) (I := I) hAccounts
    have hrd := uniswapV3PoolTickBitmapEvm (v := v) (code := code) (cA := cA)
      (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel hsz36
    exact hrd.reEquivExecutionTransport hcode hdispatch hdecode hbody hvalue hAccounts
      (returnEquiv_of_encode (uint256ReturnEncoding (tickBitmapWord σ_evm I)))
  · have hshort : I.calldata.size < 36 := by omega
    have hdecode := uniswapV3PoolTickBitmapDecodeShort (v := v) (I := I) hshort
    have hrd := uniswapV3PoolTickBitmapEvmDecodeShort (v := v) (code := code) (cA := cA)
      (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel hshort
    exact hrd.reEquivDecodingFailed hcode hdispatch hdecode

end Benchmarks.UniswapV3Pool
