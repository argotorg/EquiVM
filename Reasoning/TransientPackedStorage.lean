import Reasoning.TransientStorage
import Reasoning.PackedStorage

/-! Direct transient-storage counterparts for packed scalar fields. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace Reasoning.Theory

theorem transientLocLoad_uint48_offset0 (evm : EVM.State) (slot : UInt256) :
    transientLocLoad evm (packedUInt48Loc slot ⟨0, by decide⟩ (by decide)) =
      .int (Int.ofNat (UInt256.land
        (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)
        uint48Mask).toNat) := by
  simpa [packedUInt48Loc, uint48Mask] using
    transientLocLoad_uint_offset0 evm slot ⟨6, by decide⟩ ⟨48, by decide⟩
      (hbound := by decide) (by decide) (by decide)

theorem transientLocLoad_uint48_offset6 (evm : EVM.State) (slot : UInt256) :
    transientLocLoad evm (packedUInt48Loc slot ⟨6, by decide⟩ (by decide)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.ofNat (256 ^ 6)))
        uint48Mask).toNat) := by
  simpa [packedUInt48Loc, uint48Mask] using
    transientLocLoad_uint_offset evm slot ⟨6, by decide⟩ ⟨6, by decide⟩ ⟨48, by decide⟩
      (hbound := by decide) (by decide) (by decide) (by decide)

theorem transientLocLoad_uint48_offset20 (evm : EVM.State) (slot : UInt256) :
    transientLocLoad evm (packedUInt48Loc slot ⟨20, by decide⟩ (by decide)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.ofNat (256 ^ 20)))
        uint48Mask).toNat) := by
  simpa [packedUInt48Loc, uint48Mask] using
    transientLocLoad_uint_offset evm slot ⟨20, by decide⟩ ⟨6, by decide⟩ ⟨48, by decide⟩
      (hbound := by decide) (by decide) (by decide) (by decide)

theorem transientLocLoad_uint48_offset26 (evm : EVM.State) (slot : UInt256) :
    transientLocLoad evm (packedUInt48Loc slot ⟨26, by decide⟩ (by decide)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.ofNat (256 ^ 26)))
        uint48Mask).toNat) := by
  simpa [packedUInt48Loc, uint48Mask] using
    transientLocLoad_uint_offset evm slot ⟨26, by decide⟩ ⟨6, by decide⟩ ⟨48, by decide⟩
      (hbound := by decide) (by decide) (by decide) (by decide)


theorem transientLocStore_uint48_offset0_word (evm : EVM.State) (slot data : UInt256) :
    transientLocStore evm (packedUInt48Loc slot ⟨0, by decide⟩ (by decide))
        (.int (Int.ofNat data.toNat % packedUInt48Modulus)) =
      some (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
        (setUint48Offset0Word (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)
          data)) := by
  unfold transientLocStore storageLocWriteWord packedUInt48Loc
  simp only [valueToWord, wordOfInt_emod_uint48, bind, Option.bind]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (6 : Fin 33).val _ ++
        List.drop ((0 : Fin 32).val + (6 : Fin 33).val) _) =
      (setUint48Offset0Word (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)
        data).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (6 : Fin 33).val = 6 from rfl,
    List.take_zero, List.nil_append]
  rw [fromBytes'_append]
  rw [fromBytes'_take_wordLE_land_mask _ 6 (by norm_num)]
  rw [fromBytes'_drop_wordLE]
  have hlen6 :
      ((EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint48Mask)).1.take 6).length =
        6 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint48Mask)).2]
    norm_num
  rw [hlen6]
  rw [show 2 ^ (8 * 6) = (2 : Nat) ^ 48 by norm_num]
  rw [show 256 ^ 6 = (2 : Nat) ^ 48 by norm_num]
  rw [setUint48Offset0Word_toNat]
  have hclean : UInt256.land (UInt256.land data uint48Mask)
      (UInt256.ofNat (2 ^ 48 - 1)) = UInt256.land data uint48Mask := by
    simpa [uint48Mask] using uint48Mask_clean data
  rw [hclean]
  ring


theorem transientLocStore_uint48_offset6_word (evm : EVM.State) (slot data : UInt256) :
    transientLocStore evm (packedUInt48Loc slot ⟨6, by decide⟩ (by decide))
        (.int (Int.ofNat data.toNat % packedUInt48Modulus)) =
      some (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
        (setUint48Offset6Word (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)
          data)) := by
  unfold transientLocStore storageLocWriteWord packedUInt48Loc
  simp only [valueToWord, wordOfInt_emod_uint48, bind, Option.bind]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (6 : Fin 32).val _ ++ List.take (6 : Fin 33).val _ ++
        List.drop ((6 : Fin 32).val + (6 : Fin 33).val) _) =
      (setUint48Offset6Word (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)
        data).toNat
  rw [show (6 : Fin 32).val = 6 from rfl, show (6 : Fin 33).val = 6 from rfl]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE_land_mask _ 6 (by norm_num),
    fromBytes'_drop_wordLE]
  have hlenOld6 :
      ((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1.take 6).length = 6 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).2]
    norm_num
  have hlenVal6 :
      ((EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint48Mask)).1.take 6).length =
        6 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint48Mask)).2]
    norm_num
  rw [List.length_append, hlenOld6, hlenVal6]
  rw [show 2 ^ (8 * 6) = (2 : Nat) ^ 48 by norm_num]
  rw [show 256 ^ 6 = (2 : Nat) ^ 48 by norm_num]
  rw [show 256 ^ 12 = (2 : Nat) ^ 96 by norm_num]
  rw [setUint48Offset6Word_toNat]
  have hclean : UInt256.land (UInt256.land data uint48Mask)
      (UInt256.ofNat (2 ^ 48 - 1)) = UInt256.land data uint48Mask := by
    simpa [uint48Mask] using uint48Mask_clean data
  rw [hclean]
  ring


theorem clearTransientStorage_uint256_zero {layout : StorageLayout} {evm : EVM.State}
    {er : EvaledStorageRef} {slot : UInt256}
    (hloc : layout er = some (.leaf (uint256Loc slot))) :
    transientSolidityClearStorage? layout evm er packedUInt256StorageType =
      .ok (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot ⟨0⟩) := by
  simp only [transientSolidityClearStorage?, packedUInt256StorageType, transientSolidityLeafLoc?, hloc,
    EvalResult.ofOption, EvalResult.bind, bind]
  change EvalResult.ofOption EvalError.storageError
      (transientLocStore evm (uint256Loc slot) (.int (Int.ofNat (⟨0⟩ : UInt256).toNat))) =
    .ok (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot ⟨0⟩)
  rw [transientLocStore_uint256 evm slot (⟨0⟩ : UInt256)]
  rfl

theorem transientLocStore_addr_zero (evm : EVM.State) (slot : UInt256) :
    transientLocStore evm (addressOffset0Loc slot) (.int 0) =
      some (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
        (setAddressOffset0Word (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot) ⟨0⟩)) :=
          by
  unfold transientLocStore storageLocWriteWord addressOffset0Loc
  simp only [valueToWord, Reasoning.Theory.wordOfInt_zero, bind, Option.bind]
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (20 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (20 : Fin 33).val) _) =
        (setAddressOffset0Word
          (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot) (⟨0⟩ : UInt256)).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (20 : Fin 33).val = 20 from rfl,
    List.take_zero, List.nil_append]
  rw [fromBytes'_append, fromBytes'_take20_wordLE_solcAddrMask, fromBytes'_drop_wordLE]
  have hclean : (UInt256.land (⟨0⟩ : UInt256) solcAddrMask).toNat = (0 : Nat) := by
    decide
  rw [hclean]
  have hlen20 :
      ((EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).1.take 20).length = 20 := by
    rw [List.length_take, hvlen]
    norm_num
  rw [hlen20]
  rw [show 2 ^ (8 * 20) = 2 ^ 160 by norm_num]
  rw [show 256 ^ 20 = 2 ^ 160 by norm_num]
  rw [setAddressOffset0Word_toNat _ _ (by decide)]
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]
  ring

theorem clearTransientStorage_addr_zero {layout : StorageLayout} {evm : EVM.State}
    {er : EvaledStorageRef} {slot : UInt256}
    (hloc : layout er = some (.leaf (addressOffset0Loc slot))) :
    transientSolidityClearStorage? layout evm er packedAddressStorageType =
      .ok (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
        (setAddressOffset0Word (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot) ⟨0⟩)) :=
          by
  simp only [transientSolidityClearStorage?, packedAddressStorageType, transientSolidityLeafLoc?, hloc,
    EvalResult.ofOption, EvalResult.bind, bind]
  change EvalResult.ofOption EvalError.storageError
      (transientLocStore evm (addressOffset0Loc slot) (.int (Int.ofNat (⟨0⟩ : UInt256).toNat))) =
    .ok (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
      (setAddressOffset0Word (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot) ⟨0⟩))
  rw [show (Int.ofNat (⟨0⟩ : UInt256).toNat) = 0 from rfl]
  rw [transientLocStore_addr_zero]
  rfl


theorem transientLocStore_uint48_offset20_zero (evm : EVM.State) (slot : UInt256) :
    transientLocStore evm (packedUInt48Loc slot ⟨20, by decide⟩ (by decide)) (.int 0) =
      some (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
        (clearUint48Offset20Word
          (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot))) := by
  unfold transientLocStore storageLocWriteWord packedUInt48Loc
  simp only [valueToWord, Reasoning.Theory.wordOfInt_zero, bind, Option.bind]
  congr 2
  apply u256_inj
  let old := Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot
  show fromBytes'
      (List.take (20 : Fin 32).val _ ++ List.take (6 : Fin 33).val _ ++
        List.drop ((20 : Fin 32).val + (6 : Fin 33).val) _) =
      (clearUint48Offset20Word old).toNat
  rw [show (20 : Fin 32).val = 20 from rfl, show (6 : Fin 33).val = 6 from rfl]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  have hlenOld20 :
      ((EVM.Word.toBytesLEWithSizeProof old).1.take 20).length = 20 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof old).2]
    norm_num
  have hlenZero6 :
      ((EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).1.take 6).length = 6 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).2]
    norm_num
  rw [List.length_append, hlenOld20, hlenZero6]
  rw [show 256 ^ 20 = (2 : Nat) ^ 160 by norm_num]
  rw [show 256 ^ 6 = (2 : Nat) ^ 48 by norm_num]
  rw [show 256 ^ 26 = (2 : Nat) ^ 208 by norm_num]
  unfold clearUint48Offset20Word
  have hsumLt : old.toNat % 2 ^ 160 + old.toNat / 2 ^ 208 * 2 ^ 208 < UInt256.size := by
    have hlow : old.toNat % 2 ^ 160 < 2 ^ 160 := Nat.mod_lt _ (by norm_num)
    have hhigh : old.toNat / 2 ^ 208 < 2 ^ 48 := by
      apply Nat.div_lt_of_lt_mul
      rw [show 2 ^ 208 * 2 ^ 48 = (2 : Nat) ^ 256 by norm_num]
      change old.val.val < UInt256.size
      exact old.val.isLt
    have hlowLe : old.toNat % 2 ^ 160 ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hlow
    have hhighLe : old.toNat / 2 ^ 208 ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hhigh
    have hhighTerm : old.toNat / 2 ^ 208 * 2 ^ 208 ≤ (2 ^ 48 - 1) * 2 ^ 208 :=
      Nat.mul_le_mul_right _ hhighLe
    have hmax : (2 ^ 160 - 1) + (2 ^ 48 - 1) * 2 ^ 208 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  rw [UInt256.toNat_ofNat_of_lt hsumLt]
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]
  ring_nf
  rfl

theorem transientLocStore_uint48_offset26_zero (evm : EVM.State) (slot : UInt256) :
    transientLocStore evm (packedUInt48Loc slot ⟨26, by decide⟩ (by decide)) (.int 0) =
      some (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
        (clearUint48Offset26Word
          (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot))) := by
  unfold transientLocStore storageLocWriteWord packedUInt48Loc
  simp only [valueToWord, Reasoning.Theory.wordOfInt_zero, bind, Option.bind]
  congr 2
  apply u256_inj
  let old := Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot
  show fromBytes'
      (List.take (26 : Fin 32).val _ ++ List.take (6 : Fin 33).val _ ++
        List.drop ((26 : Fin 32).val + (6 : Fin 33).val) _) =
      (clearUint48Offset26Word old).toNat
  rw [show (26 : Fin 32).val = 26 from rfl, show (6 : Fin 33).val = 6 from rfl]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  have hlenOld26 :
      ((EVM.Word.toBytesLEWithSizeProof old).1.take 26).length = 26 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof old).2]
    norm_num
  have hlenZero6 :
      ((EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).1.take 6).length = 6 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).2]
    norm_num
  rw [List.length_append, hlenOld26, hlenZero6]
  rw [show 256 ^ 26 = (2 : Nat) ^ 208 by norm_num]
  rw [show 256 ^ 6 = (2 : Nat) ^ 48 by norm_num]
  rw [show 2 ^ (8 * (26 + 6)) = (2 : Nat) ^ 256 by norm_num]
  rw [show 256 ^ (26 + 6) = (2 : Nat) ^ 256 by norm_num]
  unfold clearUint48Offset26Word
  have hsumLt : old.toNat % 2 ^ 208 < UInt256.size := by
    exact lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num [UInt256.size])
  rw [UInt256.toNat_ofNat_of_lt hsumLt]
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]
  have hdiv : old.toNat / 2 ^ 256 = 0 := by
    exact Nat.div_eq_of_lt (by
      change old.val.val < 2 ^ 256
      exact old.val.isLt)
  dsimp [old]
  ring_nf
  have hdiv' :
      (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot).toNat /
          115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        0 := by
    simpa [old] using hdiv
  rw [hdiv']
  simp


theorem transientLocStore_uint48_offset26_word (evm : EVM.State) (slot data : UInt256) :
    transientLocStore evm (packedUInt48Loc slot ⟨26, by decide⟩ (by decide))
        (.int (Int.ofNat data.toNat % packedUInt48Modulus)) =
      some (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
        (setUint48Offset26Word
          (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot) data)) := by
  unfold transientLocStore storageLocWriteWord packedUInt48Loc
  simp only [valueToWord, wordOfInt_emod_uint48, bind, Option.bind]
  congr 2
  apply u256_inj
  let old := Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot
  show fromBytes'
      (List.take (26 : Fin 32).val _ ++ List.take (6 : Fin 33).val _ ++
        List.drop ((26 : Fin 32).val + (6 : Fin 33).val) _) =
      (setUint48Offset26Word old data).toNat
  rw [show (26 : Fin 32).val = 26 from rfl, show (6 : Fin 33).val = 6 from rfl]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE_land_mask _ 6 (by norm_num),
    fromBytes'_drop_wordLE]
  have hlenOld26 :
      ((EVM.Word.toBytesLEWithSizeProof old).1.take 26).length = 26 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof old).2]
    norm_num
  have hlenData6 :
      ((EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint48Mask)).1.take 6).length =
        6 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint48Mask)).2]
    norm_num
  rw [List.length_append, hlenOld26, hlenData6]
  rw [show 2 ^ (8 * 26) = (2 : Nat) ^ 208 by norm_num]
  rw [show 2 ^ (8 * 6) = (2 : Nat) ^ 48 by norm_num]
  rw [show 2 ^ (8 * (26 + 6)) = (2 : Nat) ^ 256 by norm_num]
  rw [show 256 ^ (26 + 6) = (2 : Nat) ^ 256 by norm_num]
  rw [setUint48Offset26Word_toNat]
  have hclean : UInt256.land (UInt256.land data uint48Mask)
      (UInt256.ofNat (2 ^ 48 - 1)) = UInt256.land data uint48Mask := by
    simpa [uint48Mask] using uint48Mask_clean data
  rw [hclean]
  have hdiv : old.toNat / 2 ^ 256 = 0 := by
    exact Nat.div_eq_of_lt (by
      change old.val.val < 2 ^ 256
      exact old.val.isLt)
  dsimp [old]
  ring_nf
  have hdiv' :
      (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot).toNat /
          115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        0 := by
    simpa [old] using hdiv
  rw [hdiv']
  simp

theorem transientLocStore_uint48_offset20_word (evm : EVM.State) (slot data : UInt256) :
    transientLocStore evm (packedUInt48Loc slot ⟨20, by decide⟩ (by decide))
        (.int (Int.ofNat data.toNat % packedUInt48Modulus)) =
      some (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
        (setUint48Offset20Word
          (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot) data)) := by
  unfold transientLocStore storageLocWriteWord packedUInt48Loc
  simp only [valueToWord, wordOfInt_emod_uint48, bind, Option.bind]
  congr 2
  apply u256_inj
  let old := Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot
  show fromBytes'
      (List.take (20 : Fin 32).val _ ++ List.take (6 : Fin 33).val _ ++
        List.drop ((20 : Fin 32).val + (6 : Fin 33).val) _) =
      (setUint48Offset20Word old data).toNat
  rw [show (20 : Fin 32).val = 20 from rfl, show (6 : Fin 33).val = 6 from rfl]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE_land_mask _ 6 (by norm_num),
    fromBytes'_drop_wordLE]
  have hlenOld20 :
      ((EVM.Word.toBytesLEWithSizeProof old).1.take 20).length = 20 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof old).2]
    norm_num
  have hlenData6 :
      ((EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint48Mask)).1.take 6).length =
        6 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint48Mask)).2]
    norm_num
  rw [List.length_append, hlenOld20, hlenData6]
  rw [show 2 ^ (8 * 20) = (2 : Nat) ^ 160 by norm_num]
  rw [show 2 ^ (8 * 6) = (2 : Nat) ^ 48 by norm_num]
  rw [show 2 ^ (8 * (20 + 6)) = (2 : Nat) ^ 208 by norm_num]
  rw [show 256 ^ (20 + 6) = (2 : Nat) ^ 208 by norm_num]
  rw [setUint48Offset20Word_toNat]
  have hclean : UInt256.land (UInt256.land data uint48Mask)
      (UInt256.ofNat (2 ^ 48 - 1)) = UInt256.land data uint48Mask := by
    simpa [uint48Mask] using uint48Mask_clean data
  rw [hclean]
  dsimp [old]
  ring_nf


theorem clearTransientStorage_uint48_offset20_zero {layout : StorageLayout} {evm : EVM.State}
    {er : EvaledStorageRef} {slot : UInt256}
    (hloc :
      layout er = some (.leaf (packedUInt48Loc slot ⟨20, by decide⟩ (by decide)))) :
    transientSolidityClearStorage? layout evm er packedUInt48StorageType =
      .ok (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
        (clearUint48Offset20Word
          (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot))) := by
  simp only [transientSolidityClearStorage?, packedUInt48StorageType, transientSolidityLeafLoc?, hloc,
    EvalResult.ofOption, EvalResult.bind, bind]
  change EvalResult.ofOption EvalError.storageError
      (transientLocStore evm (packedUInt48Loc slot ⟨20, by decide⟩ (by decide)) (.int 0)) =
    .ok (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
      (clearUint48Offset20Word
        (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)))
  rw [transientLocStore_uint48_offset20_zero]
  rfl

theorem clearTransientStorage_uint48_offset26_zero {layout : StorageLayout} {evm : EVM.State}
    {er : EvaledStorageRef} {slot : UInt256}
    (hloc :
      layout er = some (.leaf (packedUInt48Loc slot ⟨26, by decide⟩ (by decide)))) :
    transientSolidityClearStorage? layout evm er packedUInt48StorageType =
      .ok (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
        (clearUint48Offset26Word
          (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot))) := by
  simp only [transientSolidityClearStorage?, packedUInt48StorageType, transientSolidityLeafLoc?, hloc,
    EvalResult.ofOption, EvalResult.bind, bind]
  change EvalResult.ofOption EvalError.storageError
      (transientLocStore evm (packedUInt48Loc slot ⟨26, by decide⟩ (by decide)) (.int 0)) =
    .ok (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
      (clearUint48Offset26Word
        (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)))
  rw [transientLocStore_uint48_offset26_zero]
  rfl


theorem transientLocStore_bool_offset1 (evm : EVM.State) (slot : UInt256) (value : Bool) :
    transientLocStore evm (packedBoolLocAt slot 1) (.bool value) =
      some (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
        (setBoolOffset1Word (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot) value))
          := by
  unfold transientLocStore storageLocWriteWord packedBoolLocAt
  simp only [valueToWord, bind, Option.bind]
  congr 2
  apply u256_inj
  change fromBytes'
    ((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1.take 1 ++
      (EVM.Word.toBytesLEWithSizeProof value.toUInt256).1.take 1 ++
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1.drop 2) = _
  rw [fromBytes'_append, fromBytes'_append, fromBytes'_take_wordLE,
    fromBytes'_take_wordLE, fromBytes'_drop_wordLE, setBoolOffset1Word_toNat]
  simp only [List.length_append, List.length_take,
    (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).2,
    (EVM.Word.toBytesLEWithSizeProof value.toUInt256).2]
  cases value <;> simp [Bool.toUInt256, Nat.mul_comm] <;> decide


theorem transientLocStore_bool_true_offset20 (evm : EVM.State) (slot : UInt256) :
    transientLocStore evm (packedBoolLocAt slot 20) (.bool true) =
      some (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
        (setBoolTrueOffset20Word (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot))) := by
  unfold transientLocStore storageLocWriteWord packedBoolLocAt
  simp only [valueToWord, bind, Option.bind]
  congr 2
  apply u256_inj
  change fromBytes'
    ((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1.take 20 ++
      (EVM.Word.toBytesLEWithSizeProof true.toUInt256).1.take 1 ++
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1.drop 21) = _
  rw [fromBytes'_append, fromBytes'_append, fromBytes'_take_wordLE,
    fromBytes'_take_wordLE, fromBytes'_drop_wordLE, setBoolTrueOffset20Word_toNat]
  simp only [List.length_append, List.length_take,
    (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).2,
    (EVM.Word.toBytesLEWithSizeProof true.toUInt256).2]
  change _ % 2 ^ 160 + 2 ^ 160 * 1 + 2 ^ 168 * (_ / 2 ^ 168) = _
  omega


end Reasoning.Theory
