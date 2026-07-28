import Benchmarks.UniswapV3Pool.BurnPositionUpdateRevert

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

private theorem toBytesBE_eq_reverse_LE (w : UInt256) :
    EVM.Word.toBytesBE w = (EVM.Word.toBytesLEWithSizeProof w).1.reverse := by
  unfold EVM.Word.toBytesBE EVM.Word.toBytesLEWithSizeProof
  simp [toBytesBigEndian, List.reverse_append]

private theorem shiftLeft96_toNat_of_lt_160 (w : UInt256)
    (hw : w.toNat < 2 ^ (160 : Nat)) :
    (UInt256.shiftLeft w ⟨96⟩).toNat = w.toNat * 2 ^ (96 : Nat) := by
  have hprod : w.toNat * 2 ^ (96 : Nat) < UInt256.size := by
    change w.toNat * 2 ^ (96 : Nat) < 2 ^ (256 : Nat)
    nlinarith [hw,
      show (2 : Nat) ^ (256 : Nat) = 2 ^ (160 : Nat) * 2 ^ (96 : Nat) by
        norm_num [← Nat.pow_add]]
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ (⟨96⟩ : UInt256).val ≥ 256)]
  unfold UInt256.toNat
  rw [Fin.shiftLeft_val]
  rw [show (⟨96⟩ : UInt256).val.val = 96 by decide]
  rw [Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt hprod

private theorem shiftLeft96_LE_drop12_eq_take20 (w : UInt256)
    (hw : w.toNat < 2 ^ (160 : Nat)) :
    (EVM.Word.toBytesLEWithSizeProof (UInt256.shiftLeft w ⟨96⟩)).1.drop 12 =
      (EVM.Word.toBytesLEWithSizeProof w).1.take 20 := by
  apply fromBytes'_inj_of_length
  · rw [List.length_drop,
      (EVM.Word.toBytesLEWithSizeProof (UInt256.shiftLeft w ⟨96⟩)).2,
      List.length_take, (EVM.Word.toBytesLEWithSizeProof w).2]
    norm_num
  · rw [fromBytes'_drop_wordLE, fromBytes'_take_wordLE, shiftLeft96_toNat_of_lt_160 _ hw]
    rw [show 256 ^ (12 : Nat) = 2 ^ (96 : Nat) by
      norm_num [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
    rw [show 256 ^ (20 : Nat) = 2 ^ (160 : Nat) by norm_num]
    rw [show w.toNat * 2 ^ (96 : Nat) = 2 ^ (96 : Nat) * w.toNat by ring]
    rw [Nat.mul_div_right _ (by positivity : 0 < 2 ^ (96 : Nat))]
    rw [Nat.mod_eq_of_lt hw]

private theorem sourceWord_toNat_lt_160 (I : ExecutionEnv) :
    (EVM.word I.source).toNat < 2 ^ (160 : Nat) := by
  unfold EVM.word EVM.uintN UInt256.toNat
  change (Fin.ofNat UInt256.size ↑I.source).val < 2 ^ (160 : Nat)
  rw [Fin.val_ofNat]
  rw [Nat.mod_eq_of_lt]
  · exact I.source.2
  · exact lt_trans I.source.2 (by norm_num [UInt256.size, AccountAddress.size])

private theorem ownerPackedWord_eq_shift (I : ExecutionEnv) :
    burnPositionKeyOwnerPackedWord I = UInt256.shiftLeft (EVM.word I.source) ⟨96⟩ := by
  apply u256_inj
  unfold burnPositionKeyOwnerPackedWord
  rw [u256_land_toNat]
  have hlnot : (UInt256.lnot (⟨79228162514264337593543950335⟩ : UInt256)).toNat =
      2 ^ (256 : Nat) - 2 ^ (96 : Nat) := by
    native_decide
  rw [hlnot]
  have hsource : (UInt256.ofNat ↑I.source).toNat < 2 ^ (160 : Nat) := by
    unfold UInt256.ofNat UInt256.toNat
    change (Fin.ofNat UInt256.size ↑I.source).val < 2 ^ (160 : Nat)
    rw [Fin.val_ofNat]
    rw [Nat.mod_eq_of_lt]
    · exact I.source.2
    · exact lt_trans I.source.2 (by norm_num [UInt256.size, AccountAddress.size])
  have hshift : (UInt256.shiftLeft (UInt256.ofNat ↑I.source) ⟨96⟩).toNat =
      (UInt256.ofNat ↑I.source).toNat * 2 ^ (96 : Nat) :=
    shiftLeft96_toNat_of_lt_160 _ hsource
  rw [hshift]
  let x := (UInt256.ofNat ↑I.source).toNat * 2 ^ (96 : Nat)
  have hcomm : (2 ^ (256 : Nat) - 2 ^ (96 : Nat)).land x =
      x.land (2 ^ (256 : Nat) - 2 ^ (96 : Nat)) :=
    Nat.land_comm _ _
  change (2 ^ (256 : Nat) - 2 ^ (96 : Nat)).land x % UInt256.size =
    (UInt256.shiftLeft (EVM.word ↑I.source) ⟨96⟩).toNat
  rw [hcomm]
  subst x
  rw [natLandClearLow ((UInt256.ofNat ↑I.source).toNat * 2 ^ (96 : Nat)) 96
    (by norm_num)]
  · rw [show (UInt256.ofNat ↑I.source).toNat * 2 ^ (96 : Nat) =
        2 ^ (96 : Nat) * (UInt256.ofNat ↑I.source).toNat by ring]
    rw [Nat.mul_div_right _ (by positivity : 0 < 2 ^ (96 : Nat))]
    rw [Nat.mod_eq_of_lt]
    · change (UInt256.ofNat ↑I.source).toNat * 2 ^ (96 : Nat) =
        (UInt256.shiftLeft (UInt256.ofNat ↑I.source) ⟨96⟩).toNat
      rw [hshift]
    · have hprod : (UInt256.ofNat ↑I.source).toNat * 2 ^ (96 : Nat) < UInt256.size := by
        change (UInt256.ofNat ↑I.source).toNat * 2 ^ (96 : Nat) < 2 ^ (256 : Nat)
        nlinarith [hsource,
          show (2 : Nat) ^ (256 : Nat) = 2 ^ (160 : Nat) * 2 ^ (96 : Nat) by
            norm_num [← Nat.pow_add]]
      exact hprod
  · have hprod : (UInt256.ofNat ↑I.source).toNat * 2 ^ (96 : Nat) < UInt256.size := by
      change (UInt256.ofNat ↑I.source).toNat * 2 ^ (96 : Nat) < 2 ^ (256 : Nat)
      nlinarith [hsource,
        show (2 : Nat) ^ (256 : Nat) = 2 ^ (160 : Nat) * 2 ^ (96 : Nat) by
          norm_num [← Nat.pow_add]]
    exact hprod

private theorem ownerPacked_toBytesBE_take20 (I : ExecutionEnv) :
    (EVM.Word.toBytesBE (burnPositionKeyOwnerPackedWord I)).take 20 =
      (EVM.word I.source).toBytesBE.drop 12 := by
  rw [ownerPackedWord_eq_shift]
  rw [toBytesBE_eq_reverse_LE, toBytesBE_eq_reverse_LE]
  rw [List.take_reverse, List.drop_reverse]
  rw [(EVM.Word.toBytesLEWithSizeProof (UInt256.shiftLeft (EVM.word ↑I.source) ⟨96⟩)).2]
  rw [(EVM.Word.toBytesLEWithSizeProof (EVM.word ↑I.source)).2]
  norm_num
  exact shiftLeft96_LE_drop12_eq_take20 _ (sourceWord_toNat_lt_160 I)

private theorem nat_mul_pow232_mod_pow256 (n : Nat) :
    n * 2 ^ (232 : Nat) % 2 ^ (256 : Nat) =
      (n % 2 ^ (24 : Nat)) * 2 ^ (232 : Nat) := by
  have hdecomp : n = n / 2 ^ (24 : Nat) * 2 ^ (24 : Nat) + n % 2 ^ (24 : Nat) := by
    rw [show n / 2 ^ (24 : Nat) * 2 ^ (24 : Nat) =
      2 ^ (24 : Nat) * (n / 2 ^ (24 : Nat)) by ring]
    exact (Nat.div_add_mod n (2 ^ (24 : Nat))).symm
  calc
    n * 2 ^ (232 : Nat) % 2 ^ (256 : Nat)
        = ((n / 2 ^ (24 : Nat) * 2 ^ (24 : Nat) + n % 2 ^ (24 : Nat)) *
            2 ^ (232 : Nat)) % 2 ^ (256 : Nat) := by
          rw [← hdecomp]
    _ = (n / 2 ^ (24 : Nat) * 2 ^ (256 : Nat) +
            (n % 2 ^ (24 : Nat)) * 2 ^ (232 : Nat)) % 2 ^ (256 : Nat) := by
          ring_nf
    _ = ((n % 2 ^ (24 : Nat)) * 2 ^ (232 : Nat)) % 2 ^ (256 : Nat) := by
          rw [show n / 2 ^ (24 : Nat) * 2 ^ (256 : Nat) +
                (n % 2 ^ (24 : Nat)) * 2 ^ (232 : Nat) =
              2 ^ (256 : Nat) * (n / 2 ^ (24 : Nat)) +
                (n % 2 ^ (24 : Nat)) * 2 ^ (232 : Nat) by ring]
          rw [Nat.mul_add_mod_self_left]
    _ = (n % 2 ^ (24 : Nat)) * 2 ^ (232 : Nat) := by
          rw [Nat.mod_eq_of_lt]
          have hmod : n % 2 ^ (24 : Nat) < 2 ^ (24 : Nat) :=
            Nat.mod_lt _ (by positivity)
          nlinarith [
            show (2 : Nat) ^ (256 : Nat) = 2 ^ (24 : Nat) * 2 ^ (232 : Nat) by
              norm_num [← Nat.pow_add]]

private theorem shiftLeft232_toNat (w : UInt256) :
    (UInt256.shiftLeft w ⟨232⟩).toNat =
      (w.toNat % 2 ^ (24 : Nat)) * 2 ^ (232 : Nat) := by
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ (⟨232⟩ : UInt256).val ≥ 256)]
  unfold UInt256.toNat
  rw [Fin.shiftLeft_val, Nat.shiftLeft_eq]
  exact nat_mul_pow232_mod_pow256 w.val.val

private theorem shiftLeft232_LE_drop29_eq_take3 (w : UInt256) :
    (EVM.Word.toBytesLEWithSizeProof (UInt256.shiftLeft w ⟨232⟩)).1.drop 29 =
      (EVM.Word.toBytesLEWithSizeProof w).1.take 3 := by
  apply fromBytes'_inj_of_length
  · rw [List.length_drop,
      (EVM.Word.toBytesLEWithSizeProof (UInt256.shiftLeft w ⟨232⟩)).2,
      List.length_take, (EVM.Word.toBytesLEWithSizeProof w).2]
    norm_num
  · rw [fromBytes'_drop_wordLE, fromBytes'_take_wordLE, shiftLeft232_toNat]
    rw [show 256 ^ (29 : Nat) = 2 ^ (232 : Nat) by
      norm_num [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
    rw [show 256 ^ (3 : Nat) = 2 ^ (24 : Nat) by norm_num]
    rw [show w.toNat % 2 ^ (24 : Nat) * 2 ^ (232 : Nat) =
        2 ^ (232 : Nat) * (w.toNat % 2 ^ (24 : Nat)) by ring]
    rw [Nat.mul_div_right _ (by positivity : 0 < 2 ^ (232 : Nat))]

private theorem shiftLeft232_toBytesBE_take3 (w : UInt256) :
    (EVM.Word.toBytesBE (UInt256.shiftLeft w ⟨232⟩)).take 3 =
      (EVM.Word.toBytesBE w).drop 29 := by
  rw [toBytesBE_eq_reverse_LE, toBytesBE_eq_reverse_LE]
  rw [List.take_reverse, List.drop_reverse]
  rw [(EVM.Word.toBytesLEWithSizeProof (UInt256.shiftLeft w ⟨232⟩)).2]
  rw [(EVM.Word.toBytesLEWithSizeProof w).2]
  norm_num
  exact shiftLeft232_LE_drop29_eq_take3 w

private theorem lowerPacked_toBytesBE_take3 (I : ExecutionEnv) :
    (EVM.Word.toBytesBE (burnPositionKeyLowerPackedWord I)).take 3 =
      (EVM.wordOfInt (tickSpacingSint24Value (burnTickLowerWord I))).toBytesBE.drop 29 := by
  unfold burnPositionKeyLowerPackedWord burnTickLowerCleanWord
  rw [signextend_two_tickSpacing_idempotent (UInt256.signextend ⟨2⟩ (burnTickLowerWord I))]
  rw [signextend_two_tickSpacing_idempotent (burnTickLowerWord I)]
  rw [← wordOfInt_sint24Value_eq_signextend_two (burnTickLowerWord I)]
  exact shiftLeft232_toBytesBE_take3 _

private theorem upperPacked_toBytesBE_take3 (I : ExecutionEnv) :
    (EVM.Word.toBytesBE (burnPositionKeyUpperPackedWord I)).take 3 =
      (EVM.wordOfInt (tickSpacingSint24Value (burnTickUpperWord I))).toBytesBE.drop 29 := by
  unfold burnPositionKeyUpperPackedWord burnTickUpperCleanWord
  rw [signextend_two_tickSpacing_idempotent (UInt256.signextend ⟨2⟩ (burnTickUpperWord I))]
  rw [signextend_two_tickSpacing_idempotent (burnTickUpperWord I)]
  rw [← wordOfInt_sint24Value_eq_signextend_two (burnTickUpperWord I)]
  exact shiftLeft232_toBytesBE_take3 _

private theorem word_toByteArray_extract0_eq_take (word : UInt256) (n : Nat) :
    (UInt256.toByteArray word).extract 0 n =
      ByteArray.mk ((EVM.Word.toBytesBE word).take n).toArray := by
  rw [toByteArray_eq_toBytesBE]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.data_extract, Array.toList_extract]
  rw [List.extract_eq_take_drop, List.drop_zero]
  simp

private theorem owner_toByteArray_extract0_20 (I : ExecutionEnv) :
    (UInt256.toByteArray (burnPositionKeyOwnerPackedWord I)).extract 0 20 =
      ByteArray.mk ((EVM.word I.source).toBytesBE.drop 12).toArray := by
  rw [word_toByteArray_extract0_eq_take, ownerPacked_toBytesBE_take20]

private theorem lower_toByteArray_extract0_3 (I : ExecutionEnv) :
    (UInt256.toByteArray (burnPositionKeyLowerPackedWord I)).extract 0 3 =
      ByteArray.mk
        ((EVM.wordOfInt (tickSpacingSint24Value (burnTickLowerWord I))).toBytesBE.drop 29).toArray := by
  rw [word_toByteArray_extract0_eq_take, lowerPacked_toBytesBE_take3]

private theorem upper_toByteArray_extract0_3 (I : ExecutionEnv) :
    (UInt256.toByteArray (burnPositionKeyUpperPackedWord I)).extract 0 3 =
      ByteArray.mk
        ((EVM.wordOfInt (tickSpacingSint24Value (burnTickUpperWord I))).toBytesBE.drop 29).toArray := by
  rw [word_toByteArray_extract0_eq_take, upperPacked_toBytesBE_take3]

private theorem burnPositionKeyMem0_size (σ : AccountMap) (I : ExecutionEnv) :
    (burnPositionKeyMem0 σ I).size = 544 := by
  unfold burnPositionKeyMem0
  rw [writeWord_size]
  · rw [burnModifyPositionSlot0Mem_size σ I]
    native_decide
  · rw [burnModifyPositionSlot0Mem_size σ I]
    native_decide

private theorem burnPositionKeyMem1_size (σ : AccountMap) (I : ExecutionEnv) :
    (burnPositionKeyMem1 σ I).size = 564 := by
  unfold burnPositionKeyMem1
  rw [writeWord_size]
  · rw [burnPositionKeyMem0_size σ I]
    native_decide
  · rw [burnPositionKeyMem0_size σ I]
    native_decide

private theorem burnPositionKeyMem2_read512_20 (σ : AccountMap) (I : ExecutionEnv) :
    (burnPositionKeyMem2 σ I).readWithPadding 512 20 =
      (UInt256.toByteArray (burnPositionKeyOwnerPackedWord I)).extract 0 20 := by
  unfold burnPositionKeyMem2
  rw [writeWord_read_preserved_len]
  · unfold burnPositionKeyMem1
    rw [writeWord_read_preserved_len]
    · unfold burnPositionKeyMem0
      simpa using writeWord_read_window (burnModifyPositionSlot0Mem σ I) 512 0 20
        (burnPositionKeyOwnerPackedWord I) (by norm_num) (by norm_num) (by norm_num)
        (by rw [burnModifyPositionSlot0Mem_size σ I]; native_decide)
    · rw [burnPositionKeyMem0_size σ I]
      native_decide
    · exact Or.inl ⟨by norm_num, by rw [burnPositionKeyMem0_size σ I]; omega⟩
    · norm_num
    · norm_num
  · rw [burnPositionKeyMem1_size σ I]
    native_decide
  · exact Or.inl ⟨by norm_num, by rw [burnPositionKeyMem1_size σ I]; omega⟩
  · norm_num
  · norm_num

private theorem burnPositionKeyMem2_read532_3 (σ : AccountMap) (I : ExecutionEnv) :
    (burnPositionKeyMem2 σ I).readWithPadding 532 3 =
      (UInt256.toByteArray (burnPositionKeyLowerPackedWord I)).extract 0 3 := by
  unfold burnPositionKeyMem2
  rw [writeWord_read_preserved_len]
  · unfold burnPositionKeyMem1
    simpa using writeWord_read_window (burnPositionKeyMem0 σ I) 532 0 3
      (burnPositionKeyLowerPackedWord I) (by norm_num) (by norm_num) (by norm_num)
      (by rw [burnPositionKeyMem0_size σ I]; native_decide)
  · rw [burnPositionKeyMem1_size σ I]
    native_decide
  · exact Or.inl ⟨by norm_num, by rw [burnPositionKeyMem1_size σ I]; omega⟩
  · norm_num
  · norm_num

private theorem burnPositionKeyMem2_read535_3 (σ : AccountMap) (I : ExecutionEnv) :
    (burnPositionKeyMem2 σ I).readWithPadding 535 3 =
      (UInt256.toByteArray (burnPositionKeyUpperPackedWord I)).extract 0 3 := by
  unfold burnPositionKeyMem2
  simpa using writeWord_read_window (burnPositionKeyMem1 σ I) 535 0 3
    (burnPositionKeyUpperPackedWord I) (by norm_num) (by norm_num) (by norm_num)
    (by rw [burnPositionKeyMem1_size σ I]; native_decide)

private theorem byteArray_mk_append (xs ys : List UInt8) :
    ByteArray.mk xs.toArray ++ ByteArray.mk ys.toArray =
      ByteArray.mk (xs ++ ys).toArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.data_append, Array.toList_append]

private theorem byteArray_mk_append3 (xs ys zs : List UInt8) :
    ByteArray.mk xs.toArray ++ (ByteArray.mk ys.toArray ++ ByteArray.mk zs.toArray) =
      ByteArray.mk (xs ++ ys ++ zs).toArray := by
  rw [byteArray_mk_append, byteArray_mk_append]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [List.append_assoc]

theorem burnPositionKeyPackedHashMem_read512_26
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnPositionKeyPackedHashMem σ I).readWithPadding 512 26 =
      burnPositionKeyPackedBytes I := by
  unfold burnPositionKeyPackedHashMem
  rw [writeWord_read_preserved_len]
  · unfold burnPositionKeyMem3
    rw [writeWord_read_preserved_len]
    · rw [byteArray_readWithPadding_split _ 512 20 6]
      · rw [byteArray_readWithPadding_split _ 532 3 3]
        · rw [burnPositionKeyMem2_read512_20, burnPositionKeyMem2_read532_3,
            burnPositionKeyMem2_read535_3]
          rw [owner_toByteArray_extract0_20, lower_toByteArray_extract0_3,
            upper_toByteArray_extract0_3]
          unfold burnPositionKeyPackedBytes burnPositionKeyPackedList
          rw [byteArray_mk_append3]
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · rw [burnPositionKeyMem2_size σ I]
          omega
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · rw [burnPositionKeyMem2_size σ I]
        omega
    · rw [burnPositionKeyMem2_size σ I]
      native_decide
    · exact Or.inr ⟨by norm_num, by rw [burnPositionKeyMem2_size σ I]; omega⟩
    · norm_num
    · norm_num
  · rw [burnPositionKeyMem3_size σ I]
    native_decide
  · exact Or.inr ⟨by norm_num, by rw [burnPositionKeyMem3_size σ I]; omega⟩
  · norm_num
  · norm_num

theorem burnPositionKeyHashWord_eq (σ : AccountMap) (I : ExecutionEnv) :
    burnPositionKeyHashWord σ I =
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (burnPositionKeyPackedBytes I))) := by
  unfold burnPositionKeyHashWord
  rw [burnPositionKeyPackedHashMem_read512_26]

theorem burnPositionKeyValue_keyValueToWord (I : ExecutionEnv) :
    keyValueToWord
        (KeyValue.fixedBytes bytes32Width (ffi.KEC (burnPositionKeyPackedBytes I)).toList) =
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (burnPositionKeyPackedBytes I))) := by
  have hkey := keyValueToWord_fixedBytes32 (uInt256OfByteArray
    (ffi.KEC (burnPositionKeyPackedBytes I)))
  rw [toBytesBE_keccak_uInt256OfByteArray (burnPositionKeyPackedBytes I)] at hkey
  rw [uInt256OfByteArray_eq] at hkey
  simpa [bytes32Width] using hkey

theorem burnPositionBaseSlotWord_eq_positionsBase
    (σ : AccountMap) (I : ExecutionEnv) :
    burnPositionBaseSlotWord σ I =
      positionsBase
        (KeyValue.fixedBytes bytes32Width (ffi.KEC (burnPositionKeyPackedBytes I)).toList) := by
  unfold burnPositionBaseSlotWord positionsBase mapSlot solcMappingSlot
  rw [burnPositionKeyHashWord_eq σ I, burnPositionKeyValue_keyValueToWord I]

abbrev burnPositionKeyKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (ffi.KEC (burnPositionKeyPackedBytes I)).toList

abbrev burnPositionUpdateArgValues (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) : List Value :=
  [ burnPositionKeyValue I,
    burnLiquidityDeltaValue I,
    .int (Int.ofNat feeGrowthInside0X128.toNat),
    .int (Int.ofNat feeGrowthInside1X128.toNat) ]

abbrev burnPositionUpdateStore (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) : Store :=
  ((((∅ : Store)
    |>.insert "feeGrowthInside1X128" (.int (Int.ofNat feeGrowthInside1X128.toNat)))
    |>.insert "feeGrowthInside0X128" (.int (Int.ofNat feeGrowthInside0X128.toNat)))
    |>.insert "liquidityDelta" (burnLiquidityDeltaValue I))
    |>.insert "positionKey" (burnPositionKeyValue I)

abbrev burnPositionUpdateFrame (v : PoolImmutables) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) : Frame :=
  { contract := contract v,
    locals := burnPositionUpdateStore I feeGrowthInside0X128 feeGrowthInside1X128 }

def burnPositionUpdateEvaledBaseRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "positions", steps := [.mindex (burnPositionKeyKey I)] }

def burnPositionUpdateEvaledRef (I : ExecutionEnv) (field : Ident) : EvaledStorageRef :=
  { base := "positions", steps := [.mindex (burnPositionKeyKey I), .field field] }

theorem burnPositionUpdate_bindParams (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    bindParams? positionUpdateFunction.params
        (burnPositionUpdateArgValues I feeGrowthInside0X128 feeGrowthInside1X128) =
      some (burnPositionUpdateStore I feeGrowthInside0X128 feeGrowthInside1X128) := by
  rfl

theorem burnPositionUpdateStore_positionKey (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    (burnPositionUpdateStore I feeGrowthInside0X128 feeGrowthInside1X128).get?
        "positionKey" =
      some (burnPositionKeyValue I) := by
  rw [burnPositionUpdateStore]
  exact store_get_self
    ((((∅ : Store)
      |>.insert "feeGrowthInside1X128" (.int (Int.ofNat feeGrowthInside1X128.toNat)))
      |>.insert "feeGrowthInside0X128" (.int (Int.ofNat feeGrowthInside0X128.toNat)))
      |>.insert "liquidityDelta" (burnLiquidityDeltaValue I))
    "positionKey" (burnPositionKeyValue I)

theorem burnPositionUpdateStore_liquidityDelta (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    (burnPositionUpdateStore I feeGrowthInside0X128 feeGrowthInside1X128).get?
        "liquidityDelta" =
      some (burnLiquidityDeltaValue I) := by
  rw [burnPositionUpdateStore]
  rw [store_get_ne
    ((((∅ : Store)
      |>.insert "feeGrowthInside1X128" (.int (Int.ofNat feeGrowthInside1X128.toNat)))
      |>.insert "feeGrowthInside0X128" (.int (Int.ofNat feeGrowthInside0X128.toNat)))
      |>.insert "liquidityDelta" (burnLiquidityDeltaValue I))
    (k := "positionKey") (a := "liquidityDelta") (burnPositionKeyValue I)
    (by native_decide)]
  exact store_get_self
    (((∅ : Store)
      |>.insert "feeGrowthInside1X128" (.int (Int.ofNat feeGrowthInside1X128.toNat)))
      |>.insert "feeGrowthInside0X128" (.int (Int.ofNat feeGrowthInside0X128.toNat)))
    "liquidityDelta" (burnLiquidityDeltaValue I)

theorem burnPositionUpdateStore_positions (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    (burnPositionUpdateStore I feeGrowthInside0X128 feeGrowthInside1X128).get?
        "positions" = none := by
  rw [burnPositionUpdateStore]
  rw [store_get_ne4 (∅ : Store)
    (k1 := "feeGrowthInside1X128") (k2 := "feeGrowthInside0X128")
    (k3 := "liquidityDelta") (k4 := "positionKey") (a := "positions")
    (.int (Int.ofNat feeGrowthInside1X128.toNat))
    (.int (Int.ofNat feeGrowthInside0X128.toNat))
    (burnLiquidityDeltaValue I) (burnPositionKeyValue I)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)]
  simp

theorem burnPositionUpdate_evalStorageRef_positions {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    evalStorageRef (config v)
      (burnPositionUpdateFrame v I feeGrowthInside0X128 feeGrowthInside1X128) evm
      (positionsRef (.var "positionKey")) =
        .ok (burnPositionUpdateEvaledBaseRef I) := by
  have hlen :
      (ffi.KEC (burnPositionKeyPackedBytes I)).toList.length =
        bytes32Width.val + 1 := by
    rw [byteArray_toList_eq, Array.length_toList]
    change (ffi.KEC (burnPositionKeyPackedBytes I)).size = bytes32Width.val + 1
    rw [keccak_size]
    simp [bytes32Width]
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, positionsRef,
    evalExpr?, burnPositionUpdateEvaledBaseRef, burnPositionUpdateFrame,
    burnPositionKeyValue, burnPositionKeyKey,
    valueToKey?, hlen, bytes32Width, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem burnPositionUpdate_resolvePositionRef {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    resolveStorageRef? (config v)
      (burnPositionUpdateFrame v I feeGrowthInside0X128 feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I) (positionsRef (.var "positionKey")) =
        .ok (burnPositionUpdateEvaledBaseRef I, positionInfoStructTy) := by
  rw [resolveStorageRef?]
  change
    (match
      (burnPositionUpdateStore I feeGrowthInside0X128 feeGrowthInside1X128).get?
        "positions" with
    | some (.storageRef er ty) =>
        evalStorageRefFrom? (config v)
          (burnPositionUpdateFrame v I feeGrowthInside0X128 feeGrowthInside1X128)
          (initState cA gh bl σ σ₀ g A I) er ty (positionsRef (.var "positionKey")).steps
    | _ =>
        match
          evalStorageRef (config v)
            (burnPositionUpdateFrame v I feeGrowthInside0X128 feeGrowthInside1X128)
            (initState cA gh bl σ σ₀ g A I) (positionsRef (.var "positionKey")) with
        | .ok er => do
            let ty <- EvalResult.ofOption .storageError
              (storageTypeAt?
                (burnPositionUpdateFrame v I feeGrowthInside0X128 feeGrowthInside1X128).contract.storage
                er)
            pure (er, ty)
        | .revert => .revert
        | .error e => .error e) =
      .ok (burnPositionUpdateEvaledBaseRef I, positionInfoStructTy)
  rw [burnPositionUpdateStore_positions]
  rw [burnPositionUpdate_evalStorageRef_positions (v := v)
    (initState cA gh bl σ σ₀ g A I) I feeGrowthInside0X128 feeGrowthInside1X128]
  simp [burnPositionUpdateEvaledBaseRef, burnPositionKeyKey, contract, storageDecls,
    storageTypeAt?, storageTypeStep?, positionInfoStructTy, EvalResult.ofOption,
    EvalResult.bind, bind, pure]

theorem positionsStorageLocLoad_liquidity_at (evm : EVM.State) (base : UInt256) :
    storageLocLoad evm
        (loc base ⟨0, by decide⟩ ⟨16, by decide⟩ (by decide)
          (.int uint128Int)) =
      .int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner base)
        uint128Mask).toNat) := by
  rw [← show UInt256.ofNat (2 ^ (8 * 16) - 1) = uint128Mask by native_decide]
  simpa [loc, uint128Int] using
    storageLocLoad_uint_offset0 evm base (16 : Fin 33) ⟨128, by decide⟩
      (hbound := by decide) (by decide)

theorem burnPositionUpdate_sourceLiquidityLoad_zero
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) = ⟨0⟩) :
    storageLocLoad (initState cA gh bl σ σ₀ g A I)
        (loc (positionsBase (burnPositionKeyKey I)) ⟨0, by decide⟩ ⟨16, by decide⟩
          (by decide) (.int uint128Int)) =
      .int 0 := by
  have hmask : burnPositionUpdateSlot0Mask = uint128Mask := by native_decide
  have hword :
      UInt256.land (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))
          uint128Mask = ⟨0⟩ := by
    simpa [burnPositionUpdateSlot0Packed, hmask, u256_land_comm] using hliq
  rw [positionsStorageLocLoad_liquidity_at]
  simp [initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    hword]

theorem burnPositionUpdate_sourceLiquidityLoad
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    storageLocLoad (initState cA gh bl σ σ₀ g A I)
        (loc (positionsBase (burnPositionKeyKey I)) ⟨0, by decide⟩ ⟨16, by decide⟩
          (by decide) (.int uint128Int)) =
      .int (Int.ofNat (burnPositionUpdateSlot0Packed
        (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))).toNat) := by
  have hmask : burnPositionUpdateSlot0Mask = uint128Mask := by native_decide
  rw [positionsStorageLocLoad_liquidity_at]
  simp [initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    burnPositionUpdateSlot0Packed, hmask, u256_land_comm]

theorem burnPositionUpdateStorageLocLoad_feeGrowthInside0Last
    (evm : EVM.State) (base : UInt256) :
    storageLocLoad evm
        (loc (base + ⟨1⟩) ⟨0, by decide⟩ ⟨32, by decide⟩
          (by decide) (.int uint256Int)) =
      .int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (base + ⟨1⟩)).toNat) := by
  simpa [loc, uint256Loc] using storageLocLoad_uint256 evm (base + ⟨1⟩)

theorem burnPositionUpdateStorageLocLoad_feeGrowthInside1Last
    (evm : EVM.State) (base : UInt256) :
    storageLocLoad evm
        (loc (base + ⟨2⟩) ⟨0, by decide⟩ ⟨32, by decide⟩
          (by decide) (.int uint256Int)) =
      .int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (base + ⟨2⟩)).toNat) := by
  simpa [loc, uint256Loc] using storageLocLoad_uint256 evm (base + ⟨2⟩)

abbrev burnPositionUpdateAfterPositionFrame (v : PoolImmutables) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) : Frame :=
  { contract := contract v,
    locals :=
      (burnPositionUpdateStore I feeGrowthInside0X128 feeGrowthInside1X128).insert
        "position" (.storageRef (burnPositionUpdateEvaledBaseRef I) positionInfoStructTy) }

theorem burnPositionUpdateAfterPosition_liquidityDelta (v : PoolImmutables)
    (I : ExecutionEnv) (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    (burnPositionUpdateAfterPositionFrame v I feeGrowthInside0X128 feeGrowthInside1X128).locals.get?
        "liquidityDelta" =
      some (burnLiquidityDeltaValue I) := by
  rw [burnPositionUpdateAfterPositionFrame]
  rw [store_get_ne
    (burnPositionUpdateStore I feeGrowthInside0X128 feeGrowthInside1X128)
    (k := "position") (a := "liquidityDelta")
    (.storageRef (burnPositionUpdateEvaledBaseRef I) positionInfoStructTy)
    (by native_decide)]
  exact burnPositionUpdateStore_liquidityDelta I feeGrowthInside0X128 feeGrowthInside1X128

theorem burnPositionUpdateAfterPosition_position (v : PoolImmutables)
    (I : ExecutionEnv) (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    (burnPositionUpdateAfterPositionFrame v I feeGrowthInside0X128 feeGrowthInside1X128).locals.get?
        "position" =
      some (.storageRef (burnPositionUpdateEvaledBaseRef I) positionInfoStructTy) := by
  rw [burnPositionUpdateAfterPositionFrame]
  exact store_get_self
    (burnPositionUpdateStore I feeGrowthInside0X128 feeGrowthInside1X128)
    "position" (.storageRef (burnPositionUpdateEvaledBaseRef I) positionInfoStructTy)

theorem burnPositionUpdate_evalLiquidityDeltaEqZero {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (hzero : burnAmountCleanWord I = ⟨0⟩) :
    evalExpr? (config v)
      (burnPositionUpdateAfterPositionFrame v I feeGrowthInside0X128 feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I)
      (eqE (.var "liquidityDelta") (.intLit 0)) = .ok (.bool true) := by
  simp only [eqE, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnPositionUpdateAfterPosition_liquidityDelta (v := v)]
  simp [EvalResult.ofOption, burnLiquidityDeltaValue, hzero, evalBinaryOp?]

theorem burnPositionUpdate_evalLiquidityDeltaEqZeroFalse {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩) :
    evalExpr? (config v)
      (burnPositionUpdateAfterPositionFrame v I feeGrowthInside0X128 feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I)
      (eqE (.var "liquidityDelta") (.intLit 0)) = .ok (.bool false) := by
  simp only [eqE, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnPositionUpdateAfterPosition_liquidityDelta (v := v)]
  simp [EvalResult.ofOption, burnLiquidityDeltaValue, evalBinaryOp?]
  have hnat : (burnAmountCleanWord I).toNat ≠ 0 := by
    intro h
    exact hnonzero (uint256_toNat_eq_zero h)
  omega

theorem burnPositionUpdate_evalPositionLiquidityZero {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) = ⟨0⟩) :
    evalExpr? (config v)
      (burnPositionUpdateAfterPositionFrame v I feeGrowthInside0X128 feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I)
      (.field (.var "position") "liquidity") = .ok (.int 0) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [burnPositionUpdateAfterPosition_position (v := v)]
  simp only [EvalResult.ofOption]
  rw [show storageTypeStep? positionInfoStructTy (.field "liquidity") = some uint128St by
    simp [storageTypeStep?, positionInfoStructTy, uint128St]]
  change
    readStorage? (config v) (initState cA gh bl σ σ₀ g A I)
      (burnPositionUpdateEvaledRef I "liquidity") uint128St =
        .ok (.int 0)
  rw [show uint128St = .elem (.int uint128Int) by rfl]
  rw [readStorage?_elem
    (er := burnPositionUpdateEvaledRef I "liquidity")
    (t := .int uint128Int)
    (loc := loc (positionsBase (burnPositionKeyKey I)) ⟨0, by decide⟩
      ⟨16, by decide⟩ (by decide) (.int uint128Int))]
  · exact congrArg EvalResult.ok (burnPositionUpdate_sourceLiquidityLoad_zero
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hliq)
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnPositionUpdateEvaledRef, burnPositionKeyKey, loc]

theorem burnPositionUpdate_evalPositionLiquidityGtZeroFalse {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) = ⟨0⟩) :
    evalExpr? (config v)
      (burnPositionUpdateAfterPositionFrame v I feeGrowthInside0X128 feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I)
      (gtE (.field (.var "position") "liquidity") (.intLit 0)) =
        .ok (.bool false) := by
  have hfield := burnPositionUpdate_evalPositionLiquidityZero
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128 hliq
  simp [gtE, evalExpr?, hfield, evalBinaryOp?, EvalResult.bind, bind, pure]

theorem uniswapV3PoolPositionUpdateSourceLiquidityZeroReverts
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) = ⟨0⟩) :
    ExecFuncBody (config v)
      (burnPositionUpdateFrame v I feeGrowthInside0X128 feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I) positionUpdateFunction.body .reverted := by
  change ExecFuncBody (config v)
      (burnPositionUpdateFrame v I feeGrowthInside0X128 feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I)
      [ .letStorage "position" (positionsRef (.var "positionKey")),
        Stmt.ite (eqE (.var "liquidityDelta") (.intLit 0))
          [ .require (gtE (.field (.var "position") "liquidity") (.intLit 0)),
            .letDecl "liquidityNext" (some uint128)
              (.field (.var "position") "liquidity") ]
          [ .internalCall "liquidityAddDelta"
              [.field (.var "position") "liquidity", .var "liquidityDelta"]
              "liquidityNext" ],
        .letDecl "tokensOwed0" (some uint128)
          (uint128Wrap
            (divE
              (mulE
                (wordSub (.var "feeGrowthInside0X128")
                  (.field (.var "position") "feeGrowthInside0LastX128"))
                (.field (.var "position") "liquidity"))
              fixedPoint128Q128)),
        .letDecl "tokensOwed1" (some uint128)
          (uint128Wrap
            (divE
              (mulE
                (wordSub (.var "feeGrowthInside1X128")
                  (.field (.var "position") "feeGrowthInside1LastX128"))
                (.field (.var "position") "liquidity"))
              fixedPoint128Q128)),
        Stmt.ite (neE (.var "liquidityDelta") (.intLit 0))
          [ .assign .storage { base := "position", steps := [.field "liquidity"] }
              (.var "liquidityNext") ]
          [],
        .assign .storage { base := "position", steps := [.field "feeGrowthInside0LastX128"] }
          (.var "feeGrowthInside0X128"),
        .assign .storage { base := "position", steps := [.field "feeGrowthInside1LastX128"] }
          (.var "feeGrowthInside1X128"),
        Stmt.ite (orE (gtE (.var "tokensOwed0") (.intLit 0))
            (gtE (.var "tokensOwed1") (.intLit 0)))
          [ .assign .storage { base := "position", steps := [.field "tokensOwed0"] }
              (addE (.field (.var "position") "tokensOwed0") (.var "tokensOwed0")),
            .assign .storage { base := "position", steps := [.field "tokensOwed1"] }
              (addE (.field (.var "position") "tokensOwed1") (.var "tokensOwed1")) ]
          [] ] .reverted
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage
    (burnPositionUpdate_resolvePositionRef (v := v) (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      feeGrowthInside0X128 feeGrowthInside1X128)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue
    (burnPositionUpdate_evalLiquidityDeltaEqZero (v := v) (cA := cA)
      (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) feeGrowthInside0X128 feeGrowthInside1X128 hzero) ?_)
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (burnPositionUpdate_evalPositionLiquidityGtZeroFalse (v := v) (cA := cA)
      (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) feeGrowthInside0X128 feeGrowthInside1X128 hliq))

abbrev burnPositionUpdateValueArgValues (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value) : List Value :=
  [ burnPositionKeyValue I,
    burnLiquidityDeltaValue I,
    feeGrowthInside0X128,
    feeGrowthInside1X128 ]

abbrev burnPositionUpdateValueStore (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value) : Store :=
  ((((∅ : Store)
    |>.insert "feeGrowthInside1X128" feeGrowthInside1X128)
    |>.insert "feeGrowthInside0X128" feeGrowthInside0X128)
    |>.insert "liquidityDelta" (burnLiquidityDeltaValue I))
    |>.insert "positionKey" (burnPositionKeyValue I)

abbrev burnPositionUpdateValueFrame (v : PoolImmutables) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value) : Frame :=
  { contract := contract v,
    locals := burnPositionUpdateValueStore I feeGrowthInside0X128 feeGrowthInside1X128 }

theorem burnPositionUpdateValue_bindParams (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value) :
    bindParams? positionUpdateFunction.params
        (burnPositionUpdateValueArgValues I feeGrowthInside0X128 feeGrowthInside1X128) =
      some (burnPositionUpdateValueStore I feeGrowthInside0X128 feeGrowthInside1X128) := by
  rfl

theorem burnPositionUpdateValueStore_liquidityDelta (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value) :
    (burnPositionUpdateValueStore I feeGrowthInside0X128 feeGrowthInside1X128).get?
        "liquidityDelta" =
      some (burnLiquidityDeltaValue I) := by
  rw [burnPositionUpdateValueStore]
  rw [store_get_ne
    ((((∅ : Store)
      |>.insert "feeGrowthInside1X128" feeGrowthInside1X128)
      |>.insert "feeGrowthInside0X128" feeGrowthInside0X128)
      |>.insert "liquidityDelta" (burnLiquidityDeltaValue I))
    (k := "positionKey") (a := "liquidityDelta") (burnPositionKeyValue I)
    (by native_decide)]
  exact store_get_self
    (((∅ : Store)
      |>.insert "feeGrowthInside1X128" feeGrowthInside1X128)
      |>.insert "feeGrowthInside0X128" feeGrowthInside0X128)
    "liquidityDelta" (burnLiquidityDeltaValue I)

theorem burnPositionUpdateValueStore_feeGrowthInside0X128 (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value) :
    (burnPositionUpdateValueStore I feeGrowthInside0X128 feeGrowthInside1X128).get?
        "feeGrowthInside0X128" =
      some feeGrowthInside0X128 := by
  rw [burnPositionUpdateValueStore]
  rw [store_get_ne2
    (((∅ : Store).insert "feeGrowthInside1X128" feeGrowthInside1X128)
      |>.insert "feeGrowthInside0X128" feeGrowthInside0X128)
    (k1 := "liquidityDelta") (k2 := "positionKey")
    (a := "feeGrowthInside0X128") (burnLiquidityDeltaValue I) (burnPositionKeyValue I)
    (by native_decide) (by native_decide)]
  exact store_get_self ((∅ : Store).insert "feeGrowthInside1X128" feeGrowthInside1X128)
    "feeGrowthInside0X128" feeGrowthInside0X128

theorem burnPositionUpdateValueStore_feeGrowthInside1X128 (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value) :
    (burnPositionUpdateValueStore I feeGrowthInside0X128 feeGrowthInside1X128).get?
        "feeGrowthInside1X128" =
      some feeGrowthInside1X128 := by
  rw [burnPositionUpdateValueStore]
  rw [store_get_ne3
    ((∅ : Store).insert "feeGrowthInside1X128" feeGrowthInside1X128)
    (k1 := "feeGrowthInside0X128") (k2 := "liquidityDelta") (k3 := "positionKey")
    (a := "feeGrowthInside1X128") feeGrowthInside0X128 (burnLiquidityDeltaValue I)
    (burnPositionKeyValue I) (by native_decide) (by native_decide) (by native_decide)]
  exact store_get_self (∅ : Store) "feeGrowthInside1X128" feeGrowthInside1X128

theorem burnPositionUpdateValueStore_positions (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value) :
    (burnPositionUpdateValueStore I feeGrowthInside0X128 feeGrowthInside1X128).get?
        "positions" = none := by
  rw [burnPositionUpdateValueStore]
  rw [store_get_ne4 (∅ : Store)
    (k1 := "feeGrowthInside1X128") (k2 := "feeGrowthInside0X128")
    (k3 := "liquidityDelta") (k4 := "positionKey") (a := "positions")
    feeGrowthInside1X128 feeGrowthInside0X128
    (burnLiquidityDeltaValue I) (burnPositionKeyValue I)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)]
  simp

theorem burnPositionUpdateValue_evalStorageRef_positions {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value) :
    evalStorageRef (config v)
      (burnPositionUpdateValueFrame v I feeGrowthInside0X128 feeGrowthInside1X128) evm
      (positionsRef (.var "positionKey")) =
        .ok (burnPositionUpdateEvaledBaseRef I) := by
  have hlen :
      (ffi.KEC (burnPositionKeyPackedBytes I)).toList.length =
        bytes32Width.val + 1 := by
    rw [byteArray_toList_eq, Array.length_toList]
    change (ffi.KEC (burnPositionKeyPackedBytes I)).size = bytes32Width.val + 1
    rw [keccak_size]
    simp [bytes32Width]
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, positionsRef,
    evalExpr?, burnPositionUpdateEvaledBaseRef, burnPositionUpdateValueFrame,
    burnPositionKeyValue, burnPositionKeyKey,
    valueToKey?, hlen, bytes32Width, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem burnPositionUpdateValue_resolvePositionRef {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value) :
    resolveStorageRef? (config v)
      (burnPositionUpdateValueFrame v I feeGrowthInside0X128 feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I) (positionsRef (.var "positionKey")) =
        .ok (burnPositionUpdateEvaledBaseRef I, positionInfoStructTy) := by
  rw [resolveStorageRef?]
  change
    (match
      (burnPositionUpdateValueStore I feeGrowthInside0X128 feeGrowthInside1X128).get?
        "positions" with
    | some (.storageRef er ty) =>
        evalStorageRefFrom? (config v)
          (burnPositionUpdateValueFrame v I feeGrowthInside0X128 feeGrowthInside1X128)
          (initState cA gh bl σ σ₀ g A I) er ty (positionsRef (.var "positionKey")).steps
    | _ =>
        match
          evalStorageRef (config v)
            (burnPositionUpdateValueFrame v I feeGrowthInside0X128 feeGrowthInside1X128)
            (initState cA gh bl σ σ₀ g A I) (positionsRef (.var "positionKey")) with
        | .ok er => do
            let ty <- EvalResult.ofOption .storageError
              (storageTypeAt?
                (burnPositionUpdateValueFrame v I feeGrowthInside0X128 feeGrowthInside1X128).contract.storage
                er)
            pure (er, ty)
        | .revert => .revert
        | .error e => .error e) =
      .ok (burnPositionUpdateEvaledBaseRef I, positionInfoStructTy)
  rw [burnPositionUpdateValueStore_positions]
  rw [burnPositionUpdateValue_evalStorageRef_positions (v := v)
    (initState cA gh bl σ σ₀ g A I) I feeGrowthInside0X128 feeGrowthInside1X128]
  simp [burnPositionUpdateEvaledBaseRef, burnPositionKeyKey, contract, storageDecls,
    storageTypeAt?, storageTypeStep?, positionInfoStructTy, EvalResult.ofOption,
    EvalResult.bind, bind, pure]

abbrev burnPositionUpdateValueAfterPositionFrame (v : PoolImmutables) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value) : Frame :=
  { contract := contract v,
    locals :=
      (burnPositionUpdateValueStore I feeGrowthInside0X128 feeGrowthInside1X128).insert
        "position" (.storageRef (burnPositionUpdateEvaledBaseRef I) positionInfoStructTy) }

theorem burnPositionUpdateValueAfterPosition_liquidityDelta (v : PoolImmutables)
    (I : ExecutionEnv) (feeGrowthInside0X128 feeGrowthInside1X128 : Value) :
    (burnPositionUpdateValueAfterPositionFrame v I feeGrowthInside0X128
        feeGrowthInside1X128).locals.get? "liquidityDelta" =
      some (burnLiquidityDeltaValue I) := by
  rw [burnPositionUpdateValueAfterPositionFrame]
  rw [store_get_ne
    (burnPositionUpdateValueStore I feeGrowthInside0X128 feeGrowthInside1X128)
    (k := "position") (a := "liquidityDelta")
    (.storageRef (burnPositionUpdateEvaledBaseRef I) positionInfoStructTy)
    (by native_decide)]
  exact burnPositionUpdateValueStore_liquidityDelta I feeGrowthInside0X128
    feeGrowthInside1X128

theorem burnPositionUpdateValueAfterPosition_position (v : PoolImmutables)
    (I : ExecutionEnv) (feeGrowthInside0X128 feeGrowthInside1X128 : Value) :
    (burnPositionUpdateValueAfterPositionFrame v I feeGrowthInside0X128
        feeGrowthInside1X128).locals.get? "position" =
      some (.storageRef (burnPositionUpdateEvaledBaseRef I) positionInfoStructTy) := by
  rw [burnPositionUpdateValueAfterPositionFrame]
  exact store_get_self
    (burnPositionUpdateValueStore I feeGrowthInside0X128 feeGrowthInside1X128)
    "position" (.storageRef (burnPositionUpdateEvaledBaseRef I) positionInfoStructTy)

theorem burnPositionUpdateValue_evalLiquidityDeltaEqZero {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value)
    (hzero : burnAmountCleanWord I = ⟨0⟩) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterPositionFrame v I feeGrowthInside0X128
        feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I)
      (eqE (.var "liquidityDelta") (.intLit 0)) = .ok (.bool true) := by
  simp only [eqE, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnPositionUpdateValueAfterPosition_liquidityDelta (v := v)]
  simp [EvalResult.ofOption, burnLiquidityDeltaValue, hzero, evalBinaryOp?]

theorem burnPositionUpdateValue_evalLiquidityDeltaEqZeroFalse {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value)
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterPositionFrame v I feeGrowthInside0X128
        feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I)
      (eqE (.var "liquidityDelta") (.intLit 0)) = .ok (.bool false) := by
  simp only [eqE, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnPositionUpdateValueAfterPosition_liquidityDelta (v := v)]
  simp [EvalResult.ofOption, burnLiquidityDeltaValue, evalBinaryOp?]
  have hnat : (burnAmountCleanWord I).toNat ≠ 0 := by
    intro h
    exact hnonzero (uint256_toNat_eq_zero h)
  omega

theorem burnPositionUpdateValue_evalPositionLiquidityZero {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) = ⟨0⟩) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterPositionFrame v I feeGrowthInside0X128
        feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I)
      (.field (.var "position") "liquidity") = .ok (.int 0) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [burnPositionUpdateValueAfterPosition_position (v := v)]
  simp only [EvalResult.ofOption]
  rw [show storageTypeStep? positionInfoStructTy (.field "liquidity") = some uint128St by
    simp [storageTypeStep?, positionInfoStructTy, uint128St]]
  change
    readStorage? (config v) (initState cA gh bl σ σ₀ g A I)
      (burnPositionUpdateEvaledRef I "liquidity") uint128St =
        .ok (.int 0)
  rw [show uint128St = .elem (.int uint128Int) by rfl]
  rw [readStorage?_elem
    (er := burnPositionUpdateEvaledRef I "liquidity")
    (t := .int uint128Int)
    (loc := loc (positionsBase (burnPositionKeyKey I)) ⟨0, by decide⟩
      ⟨16, by decide⟩ (by decide) (.int uint128Int))]
  · exact congrArg EvalResult.ok (burnPositionUpdate_sourceLiquidityLoad_zero
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hliq)
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnPositionUpdateEvaledRef, burnPositionKeyKey, loc]

theorem burnPositionUpdateValue_evalPositionLiquidityGtZeroFalse {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) = ⟨0⟩) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterPositionFrame v I feeGrowthInside0X128
        feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I)
      (gtE (.field (.var "position") "liquidity") (.intLit 0)) =
        .ok (.bool false) := by
  have hfield := burnPositionUpdateValue_evalPositionLiquidityZero
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128 hliq
  simp [gtE, evalExpr?, hfield, evalBinaryOp?, EvalResult.bind, bind, pure]

abbrev burnPositionUpdateValueAfterLiquidityNextFrame (v : PoolImmutables)
    (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value) : Frame :=
  { contract := contract v,
    locals := (burnPositionUpdateValueAfterPositionFrame v I feeGrowthInside0X128
      feeGrowthInside1X128).locals.insert "liquidityNext"
        (.int (Int.ofNat (burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))).toNat)) }

theorem burnPositionUpdateValue_evalPositionLiquidity {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterPositionFrame v I feeGrowthInside0X128
        feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I)
      (.field (.var "position") "liquidity") =
        .ok (.int (Int.ofNat (burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))).toNat)) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [burnPositionUpdateValueAfterPosition_position (v := v)]
  simp only [EvalResult.ofOption]
  rw [show storageTypeStep? positionInfoStructTy (.field "liquidity") = some uint128St by
    simp [storageTypeStep?, positionInfoStructTy, uint128St]]
  change
    readStorage? (config v) (initState cA gh bl σ σ₀ g A I)
      (burnPositionUpdateEvaledRef I "liquidity") uint128St =
        .ok (.int (Int.ofNat (burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))).toNat))
  rw [show uint128St = .elem (.int uint128Int) by rfl]
  rw [readStorage?_elem
    (er := burnPositionUpdateEvaledRef I "liquidity")
    (t := .int uint128Int)
    (loc := loc (positionsBase (burnPositionKeyKey I)) ⟨0, by decide⟩
      ⟨16, by decide⟩ (by decide) (.int uint128Int))]
  · exact congrArg EvalResult.ok (burnPositionUpdate_sourceLiquidityLoad
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g))
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnPositionUpdateEvaledRef, burnPositionKeyKey, loc]

theorem burnPositionUpdateValue_evalPositionLiquidityGtZeroTrue {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) ≠ ⟨0⟩) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterPositionFrame v I feeGrowthInside0X128
        feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I)
      (gtE (.field (.var "position") "liquidity") (.intLit 0)) =
        .ok (.bool true) := by
  have hfield := burnPositionUpdateValue_evalPositionLiquidity
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128
  have hnat_ne :
      (burnPositionUpdateSlot0Packed
        (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))).toNat ≠ 0 := by
    intro hnat
    exact hliq (uint256_toNat_eq_zero hnat)
  have hposNat :
      0 < (burnPositionUpdateSlot0Packed
        (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))).toNat :=
    Nat.pos_of_ne_zero hnat_ne
  simp [gtE, evalExpr?, hfield, evalBinaryOp?, hposNat, EvalResult.bind, bind, pure]

theorem uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroPrefixValue
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value)
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) ≠ ⟨0⟩) :
    ExecBlock (config v)
      (burnPositionUpdateValueFrame v I feeGrowthInside0X128 feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I)
      [ .letStorage "position" (positionsRef (.var "positionKey")),
        Stmt.ite (eqE (.var "liquidityDelta") (.intLit 0))
          [ .require (gtE (.field (.var "position") "liquidity") (.intLit 0)),
            .letDecl "liquidityNext" (some uint128)
              (.field (.var "position") "liquidity") ]
          [ .internalCall "liquidityAddDelta"
              [.field (.var "position") "liquidity", .var "liquidityDelta"]
              "liquidityNext" ]]
      (ExecResult.ok
        (burnPositionUpdateValueAfterLiquidityNextFrame v σ I feeGrowthInside0X128
          feeGrowthInside1X128)
        (initState cA gh bl σ σ₀ g A I)) := by
  refine ExecBlock.consNormal (ExecStmt.letStorage
    (burnPositionUpdateValue_resolvePositionRef (v := v) (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      feeGrowthInside0X128 feeGrowthInside1X128)) ?_
  refine ExecBlock.consNormal (ExecStmt.iteTrue
    (burnPositionUpdateValue_evalLiquidityDeltaEqZero (v := v) (cA := cA)
      (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) feeGrowthInside0X128 feeGrowthInside1X128 hzero) ?_) ExecBlock.nil
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (burnPositionUpdateValue_evalPositionLiquidityGtZeroTrue (v := v)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128 hliq)) ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl
    (burnPositionUpdateValue_evalPositionLiquidity (v := v)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128)) ExecBlock.nil

theorem burnPositionUpdateValueAfterLiquidityNext_position (v : PoolImmutables)
    (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value) :
    (burnPositionUpdateValueAfterLiquidityNextFrame v σ I feeGrowthInside0X128
        feeGrowthInside1X128).locals.get? "position" =
      some (.storageRef (burnPositionUpdateEvaledBaseRef I) positionInfoStructTy) := by
  rw [burnPositionUpdateValueAfterLiquidityNextFrame]
  rw [store_get_ne (burnPositionUpdateValueAfterPositionFrame v I feeGrowthInside0X128
    feeGrowthInside1X128).locals (k := "liquidityNext") (a := "position")
    (.int (Int.ofNat (burnPositionUpdateSlot0Packed
      (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))).toNat))
    (by native_decide)]
  exact burnPositionUpdateValueAfterPosition_position v I feeGrowthInside0X128
    feeGrowthInside1X128

theorem burnPositionUpdateValue_evalFeeGrowthInside0LastAfterLiquidityNext
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterLiquidityNextFrame v σ I feeGrowthInside0X128
        feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I)
      (.field (.var "position") "feeGrowthInside0LastX128") =
        .ok (.int (Int.ofNat
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨1⟩)).toNat)) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [burnPositionUpdateValueAfterLiquidityNext_position (v := v) (σ := σ)]
  simp only [EvalResult.ofOption]
  rw [show storageTypeStep? positionInfoStructTy (.field "feeGrowthInside0LastX128") =
      some uint256St by simp [storageTypeStep?, positionInfoStructTy, uint256St]]
  change
    readStorage? (config v) (initState cA gh bl σ σ₀ g A I)
      (burnPositionUpdateEvaledRef I "feeGrowthInside0LastX128") uint256St =
        .ok (.int (Int.ofNat
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨1⟩)).toNat))
  rw [show uint256St = .elem (.int uint256Int) by rfl]
  rw [readStorage?_elem
    (er := burnPositionUpdateEvaledRef I "feeGrowthInside0LastX128")
    (t := .int uint256Int)
    (loc := loc (positionsBase (burnPositionKeyKey I) + ⟨1⟩) ⟨0, by decide⟩
      ⟨32, by decide⟩ (by decide) (.int uint256Int))]
  · simpa [initState, solcSlotWord] using
      burnPositionUpdateStorageLocLoad_feeGrowthInside0Last
        (initState cA gh bl σ σ₀ g A I) (positionsBase (burnPositionKeyKey I))
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnPositionUpdateEvaledRef, burnPositionKeyKey, loc]

theorem burnPositionUpdateValue_evalFeeGrowthInside1LastAfterLiquidityNext
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterLiquidityNextFrame v σ I feeGrowthInside0X128
        feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I)
      (.field (.var "position") "feeGrowthInside1LastX128") =
        .ok (.int (Int.ofNat
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨2⟩)).toNat)) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [burnPositionUpdateValueAfterLiquidityNext_position (v := v) (σ := σ)]
  simp only [EvalResult.ofOption]
  rw [show storageTypeStep? positionInfoStructTy (.field "feeGrowthInside1LastX128") =
      some uint256St by simp [storageTypeStep?, positionInfoStructTy, uint256St]]
  change
    readStorage? (config v) (initState cA gh bl σ σ₀ g A I)
      (burnPositionUpdateEvaledRef I "feeGrowthInside1LastX128") uint256St =
        .ok (.int (Int.ofNat
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨2⟩)).toNat))
  rw [show uint256St = .elem (.int uint256Int) by rfl]
  rw [readStorage?_elem
    (er := burnPositionUpdateEvaledRef I "feeGrowthInside1LastX128")
    (t := .int uint256Int)
    (loc := loc (positionsBase (burnPositionKeyKey I) + ⟨2⟩) ⟨0, by decide⟩
      ⟨32, by decide⟩ (by decide) (.int uint256Int))]
  · simpa [initState, solcSlotWord] using
      burnPositionUpdateStorageLocLoad_feeGrowthInside1Last
        (initState cA gh bl σ σ₀ g A I) (positionsBase (burnPositionKeyKey I))
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnPositionUpdateEvaledRef, burnPositionKeyKey, loc]

theorem uniswapV3PoolPositionUpdateSourceLiquidityZeroRevertsValue
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value)
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) = ⟨0⟩) :
    ExecFuncBody (config v)
      (burnPositionUpdateValueFrame v I feeGrowthInside0X128 feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I) positionUpdateFunction.body .reverted := by
  change ExecFuncBody (config v)
      (burnPositionUpdateValueFrame v I feeGrowthInside0X128 feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I)
      [ .letStorage "position" (positionsRef (.var "positionKey")),
        Stmt.ite (eqE (.var "liquidityDelta") (.intLit 0))
          [ .require (gtE (.field (.var "position") "liquidity") (.intLit 0)),
            .letDecl "liquidityNext" (some uint128)
              (.field (.var "position") "liquidity") ]
          [ .internalCall "liquidityAddDelta"
              [.field (.var "position") "liquidity", .var "liquidityDelta"]
              "liquidityNext" ],
        .letDecl "tokensOwed0" (some uint128)
          (uint128Wrap
            (divE
              (mulE
                (wordSub (.var "feeGrowthInside0X128")
                  (.field (.var "position") "feeGrowthInside0LastX128"))
                (.field (.var "position") "liquidity"))
              fixedPoint128Q128)),
        .letDecl "tokensOwed1" (some uint128)
          (uint128Wrap
            (divE
              (mulE
                (wordSub (.var "feeGrowthInside1X128")
                  (.field (.var "position") "feeGrowthInside1LastX128"))
                (.field (.var "position") "liquidity"))
              fixedPoint128Q128)),
        Stmt.ite (neE (.var "liquidityDelta") (.intLit 0))
          [ .assign .storage { base := "position", steps := [.field "liquidity"] }
              (.var "liquidityNext") ]
          [],
        .assign .storage { base := "position", steps := [.field "feeGrowthInside0LastX128"] }
          (.var "feeGrowthInside0X128"),
        .assign .storage { base := "position", steps := [.field "feeGrowthInside1LastX128"] }
          (.var "feeGrowthInside1X128"),
        Stmt.ite (orE (gtE (.var "tokensOwed0") (.intLit 0))
            (gtE (.var "tokensOwed1") (.intLit 0)))
          [ .assign .storage { base := "position", steps := [.field "tokensOwed0"] }
              (addE (.field (.var "position") "tokensOwed0") (.var "tokensOwed0")),
            .assign .storage { base := "position", steps := [.field "tokensOwed1"] }
              (addE (.field (.var "position") "tokensOwed1") (.var "tokensOwed1")) ]
          [] ] .reverted
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage
    (burnPositionUpdateValue_resolvePositionRef (v := v) (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      feeGrowthInside0X128 feeGrowthInside1X128)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue
    (burnPositionUpdateValue_evalLiquidityDeltaEqZero (v := v) (cA := cA)
      (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) feeGrowthInside0X128 feeGrowthInside1X128 hzero) ?_)
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (burnPositionUpdateValue_evalPositionLiquidityGtZeroFalse (v := v) (cA := cA)
      (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) feeGrowthInside0X128 feeGrowthInside1X128 hliq))

abbrev burnTickGetLowerKey (I : ExecutionEnv) : KeyValue :=
  .int (tickSpacingSint24Value (burnTickLowerWord I))

abbrev burnTickGetUpperKey (I : ExecutionEnv) : KeyValue :=
  .int (tickSpacingSint24Value (burnTickUpperWord I))

abbrev burnTickGetLowerBaseSlot (I : ExecutionEnv) : UInt256 :=
  ticksBase (burnTickGetLowerKey I)

abbrev burnTickGetUpperBaseSlot (I : ExecutionEnv) : UInt256 :=
  ticksBase (burnTickGetUpperKey I)

def burnTickGetLowerEvaledBaseRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ticks", steps := [.mindex (burnTickGetLowerKey I)] }

def burnTickGetUpperEvaledBaseRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ticks", steps := [.mindex (burnTickGetUpperKey I)] }

def burnTickGetLowerEvaledRef (I : ExecutionEnv) (field : Ident) : EvaledStorageRef :=
  { base := "ticks", steps := [.mindex (burnTickGetLowerKey I), .field field] }

def burnTickGetUpperEvaledRef (I : ExecutionEnv) (field : Ident) : EvaledStorageRef :=
  { base := "ticks", steps := [.mindex (burnTickGetUpperKey I), .field field] }

abbrev burnTickGetLowerFeeGrowthOutside0Word (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  solcSlotWord σ I (burnTickGetLowerBaseSlot I + ⟨1⟩)

abbrev burnTickGetLowerFeeGrowthOutside1Word (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  solcSlotWord σ I (burnTickGetLowerBaseSlot I + ⟨2⟩)

abbrev burnTickGetUpperFeeGrowthOutside0Word (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  solcSlotWord σ I (burnTickGetUpperBaseSlot I + ⟨1⟩)

abbrev burnTickGetUpperFeeGrowthOutside1Word (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  solcSlotWord σ I (burnTickGetUpperBaseSlot I + ⟨2⟩)

abbrev burnTickGetFeeGrowthInsideArgValues (σ : AccountMap) (I : ExecutionEnv) :
    List Value :=
  [ burnTickLowerValue I,
    burnTickUpperValue I,
    burnSlot0TickValue σ I,
    burnFeeGrowthGlobal0Value σ I,
    burnFeeGrowthGlobal1Value σ I ]

abbrev burnTickGetFeeGrowthInsideStore (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (((((∅ : Store)
    |>.insert "feeGrowthGlobal1X128" (burnFeeGrowthGlobal1Value σ I))
    |>.insert "feeGrowthGlobal0X128" (burnFeeGrowthGlobal0Value σ I))
    |>.insert "tickCurrent" (burnSlot0TickValue σ I))
    |>.insert "tickUpper" (burnTickUpperValue I))
    |>.insert "tickLower" (burnTickLowerValue I)

abbrev burnTickGetFeeGrowthInsideFrame (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := burnTickGetFeeGrowthInsideStore σ I }

theorem burnTickGetFeeGrowthInside_bindParams (σ : AccountMap) (I : ExecutionEnv) :
    bindParams? tickGetFeeGrowthInsideFunction.params
        (burnTickGetFeeGrowthInsideArgValues σ I) =
      some (burnTickGetFeeGrowthInsideStore σ I) := by
  rfl

theorem burnTickGetStore_tickLower (σ : AccountMap) (I : ExecutionEnv) :
    (burnTickGetFeeGrowthInsideStore σ I).get? "tickLower" =
      some (burnTickLowerValue I) := by
  rw [burnTickGetFeeGrowthInsideStore]
  exact store_get_self
    ((((∅ : Store)
      |>.insert "feeGrowthGlobal1X128" (burnFeeGrowthGlobal1Value σ I))
      |>.insert "feeGrowthGlobal0X128" (burnFeeGrowthGlobal0Value σ I))
      |>.insert "tickCurrent" (burnSlot0TickValue σ I)
      |>.insert "tickUpper" (burnTickUpperValue I))
    "tickLower" (burnTickLowerValue I)

theorem burnTickGetStore_tickUpper (σ : AccountMap) (I : ExecutionEnv) :
    (burnTickGetFeeGrowthInsideStore σ I).get? "tickUpper" =
      some (burnTickUpperValue I) := by
  rw [burnTickGetFeeGrowthInsideStore]
  rw [store_get_ne
    ((((∅ : Store)
      |>.insert "feeGrowthGlobal1X128" (burnFeeGrowthGlobal1Value σ I))
      |>.insert "feeGrowthGlobal0X128" (burnFeeGrowthGlobal0Value σ I))
      |>.insert "tickCurrent" (burnSlot0TickValue σ I)
      |>.insert "tickUpper" (burnTickUpperValue I))
    (k := "tickLower") (a := "tickUpper") (burnTickLowerValue I)
    (by native_decide)]
  exact store_get_self
    (((∅ : Store)
      |>.insert "feeGrowthGlobal1X128" (burnFeeGrowthGlobal1Value σ I))
      |>.insert "feeGrowthGlobal0X128" (burnFeeGrowthGlobal0Value σ I)
      |>.insert "tickCurrent" (burnSlot0TickValue σ I))
    "tickUpper" (burnTickUpperValue I)

theorem burnTickGet_evalStorageRef_lower {v : PoolImmutables}
    (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv) :
    evalStorageRef (config v) (burnTickGetFeeGrowthInsideFrame v σ I) evm
      (ticksRef (.var "tickLower")) =
        .ok (burnTickGetLowerEvaledBaseRef I) := by
  simp only [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, ticksRef,
    burnTickGetFeeGrowthInsideFrame, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnTickGetStore_tickLower]
  simp [burnTickGetLowerEvaledBaseRef, burnTickGetLowerKey, burnTickLowerValue,
    valueToKey?, EvalResult.ofOption]

theorem burnTickGet_evalStorageRef_upper {v : PoolImmutables}
    (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv) :
    evalStorageRef (config v) (burnTickGetFeeGrowthInsideFrame v σ I) evm
      (ticksRef (.var "tickUpper")) =
        .ok (burnTickGetUpperEvaledBaseRef I) := by
  simp only [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, ticksRef,
    burnTickGetFeeGrowthInsideFrame, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnTickGetStore_tickUpper]
  simp [burnTickGetUpperEvaledBaseRef, burnTickGetUpperKey, burnTickUpperValue,
    valueToKey?, EvalResult.ofOption]

theorem burnTickGetStore_ticks (σ : AccountMap) (I : ExecutionEnv) :
    (burnTickGetFeeGrowthInsideStore σ I).get? "ticks" = none := by
  rw [burnTickGetFeeGrowthInsideStore]
  rw [store_get_ne5 (∅ : Store)
    (k1 := "feeGrowthGlobal1X128") (k2 := "feeGrowthGlobal0X128")
    (k3 := "tickCurrent") (k4 := "tickUpper") (k5 := "tickLower") (a := "ticks")
    (burnFeeGrowthGlobal1Value σ I) (burnFeeGrowthGlobal0Value σ I)
    (burnSlot0TickValue σ I) (burnTickUpperValue I) (burnTickLowerValue I)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)]
  simp

theorem burnTickGet_resolveLowerRef {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    resolveStorageRef? (config v) (burnTickGetFeeGrowthInsideFrame v σ I)
      (initState cA gh bl σ σ₀ g A I) (ticksRef (.var "tickLower")) =
        .ok (burnTickGetLowerEvaledBaseRef I, tickInfoStructTy) := by
  apply resolveStorageRef?_ok
  · exact burnTickGetStore_ticks σ I
  · exact burnTickGet_evalStorageRef_lower (v := v) (initState cA gh bl σ σ₀ g A I) σ I
  · simp [burnTickGetLowerEvaledBaseRef, contract, storageDecls, storageTypeAt?,
      storageTypeStep?, tickInfoStructTy]

theorem burnTickGet_resolveUpperRef {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    resolveStorageRef? (config v) (burnTickGetFeeGrowthInsideFrame v σ I)
      (initState cA gh bl σ σ₀ g A I) (ticksRef (.var "tickUpper")) =
        .ok (burnTickGetUpperEvaledBaseRef I, tickInfoStructTy) := by
  apply resolveStorageRef?_ok
  · exact burnTickGetStore_ticks σ I
  · exact burnTickGet_evalStorageRef_upper (v := v) (initState cA gh bl σ σ₀ g A I) σ I
  · simp [burnTickGetUpperEvaledBaseRef, contract, storageDecls, storageTypeAt?,
      storageTypeStep?, tickInfoStructTy]

abbrev burnWordSubInt (x y : Int) : Int :=
  (x - y) % (2 ^ 256 : Int)

theorem evalExpr_wordSub_int {v : PoolImmutables} {frame : Frame} {evm : EVM.State}
    {e₁ e₂ : Expr} {x y : Int}
    (h₁ : evalExpr? (config v) frame evm e₁ = .ok (.int x))
    (h₂ : evalExpr? (config v) frame evm e₂ = .ok (.int y)) :
    evalExpr? (config v) frame evm (wordSub e₁ e₂) =
      .ok (.int (burnWordSubInt x y)) := by
  simp only [wordSub, modE, subE, uint256Modulus, evalExpr?, EvalResult.bind, bind, pure]
  rw [h₁, h₂]
  simp [evalBinaryOp?, burnWordSubInt]

theorem ticksStorageLocLoad_feeGrowthOutside0_at (evm : EVM.State) (base : UInt256) :
    storageLocLoad evm
        (loc (base + ⟨1⟩) ⟨0, by decide⟩ ⟨32, by decide⟩
          (by decide) (.int uint256Int)) =
      .int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (base + ⟨1⟩)).toNat) := by
  simpa [loc, uint256Loc] using storageLocLoad_uint256 evm (base + ⟨1⟩)

theorem ticksStorageLocLoad_feeGrowthOutside1_at (evm : EVM.State) (base : UInt256) :
    storageLocLoad evm
        (loc (base + ⟨2⟩) ⟨0, by decide⟩ ⟨32, by decide⟩
          (by decide) (.int uint256Int)) =
      .int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (base + ⟨2⟩)).toNat) := by
  simpa [loc, uint256Loc] using storageLocLoad_uint256 evm (base + ⟨2⟩)

abbrev burnTickGetLowerFeeGrowthOutside0Int (σ : AccountMap) (I : ExecutionEnv) :
    Int :=
  Int.ofNat (burnTickGetLowerFeeGrowthOutside0Word σ I).toNat

abbrev burnTickGetLowerFeeGrowthOutside1Int (σ : AccountMap) (I : ExecutionEnv) :
    Int :=
  Int.ofNat (burnTickGetLowerFeeGrowthOutside1Word σ I).toNat

abbrev burnTickGetUpperFeeGrowthOutside0Int (σ : AccountMap) (I : ExecutionEnv) :
    Int :=
  Int.ofNat (burnTickGetUpperFeeGrowthOutside0Word σ I).toNat

abbrev burnTickGetUpperFeeGrowthOutside1Int (σ : AccountMap) (I : ExecutionEnv) :
    Int :=
  Int.ofNat (burnTickGetUpperFeeGrowthOutside1Word σ I).toNat

abbrev burnTickGetFeeGrowthGlobal0Int (σ : AccountMap) (I : ExecutionEnv) : Int :=
  Int.ofNat (solcSlotWord σ I ⟨1⟩).toNat

abbrev burnTickGetFeeGrowthGlobal1Int (σ : AccountMap) (I : ExecutionEnv) : Int :=
  Int.ofNat (solcSlotWord σ I ⟨2⟩).toNat

abbrev burnTickGetBelow0Int (σ : AccountMap) (I : ExecutionEnv) : Int :=
  if tickSpacingSint24Value (slot0TickRawWord σ I) >=
      tickSpacingSint24Value (burnTickLowerWord I) then
    burnTickGetLowerFeeGrowthOutside0Int σ I
  else
    burnWordSubInt (burnTickGetFeeGrowthGlobal0Int σ I)
      (burnTickGetLowerFeeGrowthOutside0Int σ I)

abbrev burnTickGetBelow1Int (σ : AccountMap) (I : ExecutionEnv) : Int :=
  if tickSpacingSint24Value (slot0TickRawWord σ I) >=
      tickSpacingSint24Value (burnTickLowerWord I) then
    burnTickGetLowerFeeGrowthOutside1Int σ I
  else
    burnWordSubInt (burnTickGetFeeGrowthGlobal1Int σ I)
      (burnTickGetLowerFeeGrowthOutside1Int σ I)

abbrev burnTickGetAbove0Int (σ : AccountMap) (I : ExecutionEnv) : Int :=
  if tickSpacingSint24Value (slot0TickRawWord σ I) <
      tickSpacingSint24Value (burnTickUpperWord I) then
    burnTickGetUpperFeeGrowthOutside0Int σ I
  else
    burnWordSubInt (burnTickGetFeeGrowthGlobal0Int σ I)
      (burnTickGetUpperFeeGrowthOutside0Int σ I)

abbrev burnTickGetAbove1Int (σ : AccountMap) (I : ExecutionEnv) : Int :=
  if tickSpacingSint24Value (slot0TickRawWord σ I) <
      tickSpacingSint24Value (burnTickUpperWord I) then
    burnTickGetUpperFeeGrowthOutside1Int σ I
  else
    burnWordSubInt (burnTickGetFeeGrowthGlobal1Int σ I)
      (burnTickGetUpperFeeGrowthOutside1Int σ I)

abbrev burnTickGetInside0Int (σ : AccountMap) (I : ExecutionEnv) : Int :=
  burnWordSubInt
    (burnWordSubInt (burnTickGetFeeGrowthGlobal0Int σ I) (burnTickGetBelow0Int σ I))
    (burnTickGetAbove0Int σ I)

abbrev burnTickGetInside1Int (σ : AccountMap) (I : ExecutionEnv) : Int :=
  burnWordSubInt
    (burnWordSubInt (burnTickGetFeeGrowthGlobal1Int σ I) (burnTickGetBelow1Int σ I))
    (burnTickGetAbove1Int σ I)

abbrev burnTickGetBelow0Value (σ : AccountMap) (I : ExecutionEnv) : Value :=
  .int (burnTickGetBelow0Int σ I)

abbrev burnTickGetBelow1Value (σ : AccountMap) (I : ExecutionEnv) : Value :=
  .int (burnTickGetBelow1Int σ I)

abbrev burnTickGetAbove0Value (σ : AccountMap) (I : ExecutionEnv) : Value :=
  .int (burnTickGetAbove0Int σ I)

abbrev burnTickGetAbove1Value (σ : AccountMap) (I : ExecutionEnv) : Value :=
  .int (burnTickGetAbove1Int σ I)

abbrev burnTickGetInside0Value (σ : AccountMap) (I : ExecutionEnv) : Value :=
  .int (burnTickGetInside0Int σ I)

abbrev burnTickGetInside1Value (σ : AccountMap) (I : ExecutionEnv) : Value :=
  .int (burnTickGetInside1Int σ I)

abbrev burnTickGetAfterLowerFrame (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnTickGetFeeGrowthInsideStore σ I).insert "lower"
      (.storageRef (burnTickGetLowerEvaledBaseRef I) tickInfoStructTy) }

abbrev burnTickGetAfterUpperFrame (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnTickGetAfterLowerFrame v σ I).locals.insert "upper"
      (.storageRef (burnTickGetUpperEvaledBaseRef I) tickInfoStructTy) }

abbrev burnTickGetAfterBelow0Frame (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnTickGetAfterUpperFrame v σ I).locals.insert "feeGrowthBelow0X128"
      (burnTickGetBelow0Value σ I) }

abbrev burnTickGetAfterBelow1Frame (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnTickGetAfterBelow0Frame v σ I).locals.insert "feeGrowthBelow1X128"
      (burnTickGetBelow1Value σ I) }

abbrev burnTickGetAfterAbove0Frame (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnTickGetAfterBelow1Frame v σ I).locals.insert "feeGrowthAbove0X128"
      (burnTickGetAbove0Value σ I) }

abbrev burnTickGetAfterAbove1Frame (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnTickGetAfterAbove0Frame v σ I).locals.insert "feeGrowthAbove1X128"
      (burnTickGetAbove1Value σ I) }

theorem burnTickGetAfterLower_tickUpper (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterLowerFrame v σ I).locals.get? "tickUpper" =
      some (burnTickUpperValue I) := by
  rw [burnTickGetAfterLowerFrame]
  rw [store_get_ne (burnTickGetFeeGrowthInsideStore σ I)
    (k := "lower") (a := "tickUpper")
    (.storageRef (burnTickGetLowerEvaledBaseRef I) tickInfoStructTy)
    (by native_decide)]
  exact burnTickGetStore_tickUpper σ I

theorem burnTickGetAfterLower_ticks (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterLowerFrame v σ I).locals.get? "ticks" = none := by
  rw [burnTickGetAfterLowerFrame]
  rw [store_get_ne (burnTickGetFeeGrowthInsideStore σ I)
    (k := "lower") (a := "ticks")
    (.storageRef (burnTickGetLowerEvaledBaseRef I) tickInfoStructTy)
    (by native_decide)]
  exact burnTickGetStore_ticks σ I

theorem burnTickGetAfterLower_evalStorageRef_upper {v : PoolImmutables}
    (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv) :
    evalStorageRef (config v) (burnTickGetAfterLowerFrame v σ I) evm
      (ticksRef (.var "tickUpper")) =
        .ok (burnTickGetUpperEvaledBaseRef I) := by
  simp only [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, ticksRef,
    burnTickGetAfterLowerFrame, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnTickGetAfterLower_tickUpper v σ I]
  simp [burnTickGetUpperEvaledBaseRef, burnTickGetUpperKey, burnTickUpperValue,
    valueToKey?, EvalResult.ofOption]

theorem burnTickGetAfterLower_resolveUpperRef {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    resolveStorageRef? (config v) (burnTickGetAfterLowerFrame v σ I)
      (initState cA gh bl σ σ₀ g A I) (ticksRef (.var "tickUpper")) =
        .ok (burnTickGetUpperEvaledBaseRef I, tickInfoStructTy) := by
  apply resolveStorageRef?_ok
  · exact burnTickGetAfterLower_ticks v σ I
  · exact burnTickGetAfterLower_evalStorageRef_upper (v := v)
      (initState cA gh bl σ σ₀ g A I) σ I
  · simp [burnTickGetUpperEvaledBaseRef, contract, storageDecls, storageTypeAt?,
      storageTypeStep?, tickInfoStructTy]

theorem burnTickGetAfterUpper_lower (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterUpperFrame v σ I).locals.get? "lower" =
      some (.storageRef (burnTickGetLowerEvaledBaseRef I) tickInfoStructTy) := by
  rw [burnTickGetAfterUpperFrame]
  rw [store_get_ne (burnTickGetAfterLowerFrame v σ I).locals
    (k := "upper") (a := "lower")
    (.storageRef (burnTickGetUpperEvaledBaseRef I) tickInfoStructTy)
    (by native_decide)]
  rw [burnTickGetAfterLowerFrame]
  exact store_get_self (burnTickGetFeeGrowthInsideStore σ I)
    "lower" (.storageRef (burnTickGetLowerEvaledBaseRef I) tickInfoStructTy)

theorem burnTickGetAfterUpper_upper (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterUpperFrame v σ I).locals.get? "upper" =
      some (.storageRef (burnTickGetUpperEvaledBaseRef I) tickInfoStructTy) := by
  rw [burnTickGetAfterUpperFrame]
  exact store_get_self (burnTickGetAfterLowerFrame v σ I).locals
    "upper" (.storageRef (burnTickGetUpperEvaledBaseRef I) tickInfoStructTy)

theorem burnTickGetAfterUpper_tickLower (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterUpperFrame v σ I).locals.get? "tickLower" =
      some (burnTickLowerValue I) := by
  rw [burnTickGetAfterUpperFrame]
  rw [store_get_ne (burnTickGetAfterLowerFrame v σ I).locals
    (k := "upper") (a := "tickLower")
    (.storageRef (burnTickGetUpperEvaledBaseRef I) tickInfoStructTy)
    (by native_decide)]
  rw [burnTickGetAfterLowerFrame]
  rw [store_get_ne (burnTickGetFeeGrowthInsideStore σ I)
    (k := "lower") (a := "tickLower")
    (.storageRef (burnTickGetLowerEvaledBaseRef I) tickInfoStructTy)
    (by native_decide)]
  exact burnTickGetStore_tickLower σ I

theorem burnTickGetAfterUpper_tickUpper (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterUpperFrame v σ I).locals.get? "tickUpper" =
      some (burnTickUpperValue I) := by
  rw [burnTickGetAfterUpperFrame]
  rw [store_get_ne (burnTickGetAfterLowerFrame v σ I).locals
    (k := "upper") (a := "tickUpper")
    (.storageRef (burnTickGetUpperEvaledBaseRef I) tickInfoStructTy)
    (by native_decide)]
  exact burnTickGetAfterLower_tickUpper v σ I

theorem burnTickGetAfterUpper_tickCurrent (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterUpperFrame v σ I).locals.get? "tickCurrent" =
      some (burnSlot0TickValue σ I) := by
  rw [burnTickGetAfterUpperFrame]
  rw [store_get_ne (burnTickGetAfterLowerFrame v σ I).locals
    (k := "upper") (a := "tickCurrent")
    (.storageRef (burnTickGetUpperEvaledBaseRef I) tickInfoStructTy)
    (by native_decide)]
  rw [burnTickGetAfterLowerFrame]
  rw [store_get_ne (burnTickGetFeeGrowthInsideStore σ I)
    (k := "lower") (a := "tickCurrent")
    (.storageRef (burnTickGetLowerEvaledBaseRef I) tickInfoStructTy)
    (by native_decide)]
  rw [burnTickGetFeeGrowthInsideStore]
  rw [store_get_ne2
    (((∅ : Store)
      |>.insert "feeGrowthGlobal1X128" (burnFeeGrowthGlobal1Value σ I))
      |>.insert "feeGrowthGlobal0X128" (burnFeeGrowthGlobal0Value σ I)
      |>.insert "tickCurrent" (burnSlot0TickValue σ I))
    (k1 := "tickUpper") (k2 := "tickLower") (a := "tickCurrent")
    (burnTickUpperValue I) (burnTickLowerValue I)
    (by native_decide) (by native_decide)]
  exact store_get_self
    (((∅ : Store)
      |>.insert "feeGrowthGlobal1X128" (burnFeeGrowthGlobal1Value σ I))
      |>.insert "feeGrowthGlobal0X128" (burnFeeGrowthGlobal0Value σ I))
    "tickCurrent" (burnSlot0TickValue σ I)

theorem burnTickGet_evalCurrentGeLower {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? (config v) (burnTickGetAfterUpperFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (geE (.var "tickCurrent") (.var "tickLower")) =
        .ok (.bool (tickSpacingSint24Value (slot0TickRawWord σ I) >=
          tickSpacingSint24Value (burnTickLowerWord I))) := by
  simp only [geE, evalExpr?, EvalResult.bind, bind]
  rw [burnTickGetAfterUpper_tickCurrent v σ I, burnTickGetAfterUpper_tickLower v σ I]
  simp [EvalResult.ofOption, burnSlot0TickValue, burnTickLowerValue, wordToElem, int24Int,
    tickSpacingSint24Value, evalBinaryOp?]

theorem burnTickGet_evalCurrentLtUpper {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? (config v) (burnTickGetAfterBelow1Frame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (ltE (.var "tickCurrent") (.var "tickUpper")) =
        .ok (.bool (tickSpacingSint24Value (slot0TickRawWord σ I) <
          tickSpacingSint24Value (burnTickUpperWord I))) := by
  simp only [ltE, evalExpr?, EvalResult.bind, bind]
  rw [show (burnTickGetAfterBelow1Frame v σ I).locals.get? "tickCurrent" =
      some (burnSlot0TickValue σ I) by
    rw [burnTickGetAfterBelow1Frame, burnTickGetAfterBelow0Frame]
    rw [store_get_ne (burnTickGetAfterBelow0Frame v σ I).locals
      (k := "feeGrowthBelow1X128") (a := "tickCurrent") (burnTickGetBelow1Value σ I)
      (by native_decide)]
    rw [store_get_ne (burnTickGetAfterUpperFrame v σ I).locals
      (k := "feeGrowthBelow0X128") (a := "tickCurrent") (burnTickGetBelow0Value σ I)
      (by native_decide)]
    exact burnTickGetAfterUpper_tickCurrent v σ I]
  rw [show (burnTickGetAfterBelow1Frame v σ I).locals.get? "tickUpper" =
      some (burnTickUpperValue I) by
    rw [burnTickGetAfterBelow1Frame, burnTickGetAfterBelow0Frame]
    rw [store_get_ne (burnTickGetAfterBelow0Frame v σ I).locals
      (k := "feeGrowthBelow1X128") (a := "tickUpper") (burnTickGetBelow1Value σ I)
      (by native_decide)]
    rw [store_get_ne (burnTickGetAfterUpperFrame v σ I).locals
      (k := "feeGrowthBelow0X128") (a := "tickUpper") (burnTickGetBelow0Value σ I)
      (by native_decide)]
    exact burnTickGetAfterUpper_tickUpper v σ I]
  simp [EvalResult.ofOption, burnSlot0TickValue, burnTickUpperValue, wordToElem, int24Int,
    tickSpacingSint24Value, evalBinaryOp?]

theorem burnTickGet_evalLowerFeeGrowthOutside0 {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} {frame : Frame}
    (hlower : frame.locals.get? "lower" =
      some (.storageRef (burnTickGetLowerEvaledBaseRef I) tickInfoStructTy)) :
    evalExpr? (config v) frame (initState cA gh bl σ σ₀ g A I)
      (.field (.var "lower") "feeGrowthOutside0X128") =
        .ok (.int (burnTickGetLowerFeeGrowthOutside0Int σ I)) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [hlower]
  simp only [EvalResult.ofOption]
  rw [show storageTypeStep? tickInfoStructTy (.field "feeGrowthOutside0X128") =
      some uint256St by simp [storageTypeStep?, tickInfoStructTy, uint256St]]
  change
    readStorage? (config v) (initState cA gh bl σ σ₀ g A I)
      (burnTickGetLowerEvaledRef I "feeGrowthOutside0X128") uint256St =
        .ok (.int (burnTickGetLowerFeeGrowthOutside0Int σ I))
  rw [show uint256St = .elem (.int uint256Int) by rfl]
  rw [readStorage?_elem
    (er := burnTickGetLowerEvaledRef I "feeGrowthOutside0X128")
    (t := .int uint256Int)
    (loc := loc (burnTickGetLowerBaseSlot I + ⟨1⟩) ⟨0, by decide⟩ ⟨32, by decide⟩
      (by decide) (.int uint256Int))]
  · simpa [initState, burnTickGetLowerFeeGrowthOutside0Int,
      burnTickGetLowerFeeGrowthOutside0Word, burnTickGetLowerBaseSlot, solcSlotWord] using
      ticksStorageLocLoad_feeGrowthOutside0_at (initState cA gh bl σ σ₀ g A I)
        (burnTickGetLowerBaseSlot I)
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnTickGetLowerEvaledRef, burnTickGetLowerKey, burnTickGetLowerBaseSlot, loc]

theorem burnTickGet_evalLowerFeeGrowthOutside1 {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} {frame : Frame}
    (hlower : frame.locals.get? "lower" =
      some (.storageRef (burnTickGetLowerEvaledBaseRef I) tickInfoStructTy)) :
    evalExpr? (config v) frame (initState cA gh bl σ σ₀ g A I)
      (.field (.var "lower") "feeGrowthOutside1X128") =
        .ok (.int (burnTickGetLowerFeeGrowthOutside1Int σ I)) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [hlower]
  simp only [EvalResult.ofOption]
  rw [show storageTypeStep? tickInfoStructTy (.field "feeGrowthOutside1X128") =
      some uint256St by simp [storageTypeStep?, tickInfoStructTy, uint256St]]
  change
    readStorage? (config v) (initState cA gh bl σ σ₀ g A I)
      (burnTickGetLowerEvaledRef I "feeGrowthOutside1X128") uint256St =
        .ok (.int (burnTickGetLowerFeeGrowthOutside1Int σ I))
  rw [show uint256St = .elem (.int uint256Int) by rfl]
  rw [readStorage?_elem
    (er := burnTickGetLowerEvaledRef I "feeGrowthOutside1X128")
    (t := .int uint256Int)
    (loc := loc (burnTickGetLowerBaseSlot I + ⟨2⟩) ⟨0, by decide⟩ ⟨32, by decide⟩
      (by decide) (.int uint256Int))]
  · simpa [initState, burnTickGetLowerFeeGrowthOutside1Int,
      burnTickGetLowerFeeGrowthOutside1Word, burnTickGetLowerBaseSlot, solcSlotWord] using
      ticksStorageLocLoad_feeGrowthOutside1_at (initState cA gh bl σ σ₀ g A I)
        (burnTickGetLowerBaseSlot I)
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnTickGetLowerEvaledRef, burnTickGetLowerKey, burnTickGetLowerBaseSlot, loc]

theorem burnTickGet_evalUpperFeeGrowthOutside0 {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} {frame : Frame}
    (hupper : frame.locals.get? "upper" =
      some (.storageRef (burnTickGetUpperEvaledBaseRef I) tickInfoStructTy)) :
    evalExpr? (config v) frame (initState cA gh bl σ σ₀ g A I)
      (.field (.var "upper") "feeGrowthOutside0X128") =
        .ok (.int (burnTickGetUpperFeeGrowthOutside0Int σ I)) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [hupper]
  simp only [EvalResult.ofOption]
  rw [show storageTypeStep? tickInfoStructTy (.field "feeGrowthOutside0X128") =
      some uint256St by simp [storageTypeStep?, tickInfoStructTy, uint256St]]
  change
    readStorage? (config v) (initState cA gh bl σ σ₀ g A I)
      (burnTickGetUpperEvaledRef I "feeGrowthOutside0X128") uint256St =
        .ok (.int (burnTickGetUpperFeeGrowthOutside0Int σ I))
  rw [show uint256St = .elem (.int uint256Int) by rfl]
  rw [readStorage?_elem
    (er := burnTickGetUpperEvaledRef I "feeGrowthOutside0X128")
    (t := .int uint256Int)
    (loc := loc (burnTickGetUpperBaseSlot I + ⟨1⟩) ⟨0, by decide⟩ ⟨32, by decide⟩
      (by decide) (.int uint256Int))]
  · simpa [initState, burnTickGetUpperFeeGrowthOutside0Int,
      burnTickGetUpperFeeGrowthOutside0Word, burnTickGetUpperBaseSlot, solcSlotWord] using
      ticksStorageLocLoad_feeGrowthOutside0_at (initState cA gh bl σ σ₀ g A I)
        (burnTickGetUpperBaseSlot I)
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnTickGetUpperEvaledRef, burnTickGetUpperKey, burnTickGetUpperBaseSlot, loc]

theorem burnTickGet_evalUpperFeeGrowthOutside1 {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} {frame : Frame}
    (hupper : frame.locals.get? "upper" =
      some (.storageRef (burnTickGetUpperEvaledBaseRef I) tickInfoStructTy)) :
    evalExpr? (config v) frame (initState cA gh bl σ σ₀ g A I)
      (.field (.var "upper") "feeGrowthOutside1X128") =
        .ok (.int (burnTickGetUpperFeeGrowthOutside1Int σ I)) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [hupper]
  simp only [EvalResult.ofOption]
  rw [show storageTypeStep? tickInfoStructTy (.field "feeGrowthOutside1X128") =
      some uint256St by simp [storageTypeStep?, tickInfoStructTy, uint256St]]
  change
    readStorage? (config v) (initState cA gh bl σ σ₀ g A I)
      (burnTickGetUpperEvaledRef I "feeGrowthOutside1X128") uint256St =
        .ok (.int (burnTickGetUpperFeeGrowthOutside1Int σ I))
  rw [show uint256St = .elem (.int uint256Int) by rfl]
  rw [readStorage?_elem
    (er := burnTickGetUpperEvaledRef I "feeGrowthOutside1X128")
    (t := .int uint256Int)
    (loc := loc (burnTickGetUpperBaseSlot I + ⟨2⟩) ⟨0, by decide⟩ ⟨32, by decide⟩
      (by decide) (.int uint256Int))]
  · simpa [initState, burnTickGetUpperFeeGrowthOutside1Int,
      burnTickGetUpperFeeGrowthOutside1Word, burnTickGetUpperBaseSlot, solcSlotWord] using
      ticksStorageLocLoad_feeGrowthOutside1_at (initState cA gh bl σ σ₀ g A I)
        (burnTickGetUpperBaseSlot I)
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnTickGetUpperEvaledRef, burnTickGetUpperKey, burnTickGetUpperBaseSlot, loc]

end Benchmarks.UniswapV3Pool
