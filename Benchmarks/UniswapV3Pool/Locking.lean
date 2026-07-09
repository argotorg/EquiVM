import Benchmarks.UniswapV3Pool.Slot0

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

abbrev slot0UnlockedLoc : StorageLoc :=
  loc ⟨0⟩ ⟨30, by decide⟩ ⟨1, by decide⟩ (by decide) .bool

abbrev slot0UnlockedClearMask : UInt256 :=
  UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat (2 ^ 8 - 1)) ⟨240⟩)

abbrev slot0UnlockedTrueSlotWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat
    ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 240 +
      2 ^ 240 +
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 248 *
          2 ^ 248)

abbrev slot0AfterUnlockState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (slot0UnlockedTrueSlotWord evm)

theorem slot0UnlockedClearMask_toNat :
    slot0UnlockedClearMask.toNat = 2 ^ 256 - 2 ^ 248 + (2 ^ 240 - 1) := by
  native_decide

theorem slot0UnlockedTrueSlotWord_nat_lt (evm : EVM.State) :
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 240 +
        2 ^ 240 +
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 248 *
            2 ^ 248 <
      UInt256.size := by
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  have hlow : w.toNat % 2 ^ 240 ≤ 2 ^ 240 - 1 :=
    Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
  have hhighLt : w.toNat / 2 ^ 248 < 2 ^ 8 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 248 * 2 ^ 8 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change w.val.val < UInt256.size
    exact w.val.isLt
  have hhigh : w.toNat / 2 ^ 248 ≤ 2 ^ 8 - 1 := Nat.le_pred_of_lt hhighLt
  have hmax : (2 ^ 240 - 1) + 2 ^ 240 + (2 ^ 8 - 1) * 2 ^ 248 <
      UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  dsimp [w] at hlow hhigh
  omega

theorem natLandClearSlot0UnlockedByte (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n (2 ^ 256 - 2 ^ 248 + (2 ^ 240 - 1)) =
      n % 2 ^ 240 + (n / 2 ^ 248) * 2 ^ 248 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& (2 ^ 256 - 2 ^ 248 + (2 ^ 240 - 1))).testBit i =
    (n % 2 ^ 240 + n / 2 ^ 248 * 2 ^ 248).testBit i
  rw [Nat.testBit_and]
  rw [show n % 2 ^ 240 + (n / 2 ^ 248) * 2 ^ 248 =
      2 ^ 248 * (n / 2 ^ 248) + n % 2 ^ 240 by ring]
  rw [Nat.testBit_two_pow_mul_add (a := n / 2 ^ 248)
    (b_lt := lt_trans (Nat.mod_lt _ (by positivity : 0 < 2 ^ 240))
      (by norm_num : 2 ^ 240 < 2 ^ 248))]
  rw [show 2 ^ 256 - 2 ^ 248 + (2 ^ 240 - 1) =
      2 ^ 248 * (2 ^ 8 - 1) + (2 ^ 240 - 1) by norm_num [Nat.pow_add]]
  have hmaskLow : 2 ^ 240 - 1 < 2 ^ 248 := by norm_num
  rw [Nat.testBit_two_pow_mul_add (a := 2 ^ 8 - 1) (b_lt := hmaskLow)]
  by_cases hi248 : i < 248
  · simp [hi248]
    change (n.testBit i && (2 ^ 240 - 1).testBit i) = (n % 2 ^ 240).testBit i
    by_cases hi240 : i < 240
    · have hmask : (2 ^ 240 - 1).testBit i = true := by
        rw [Nat.testBit_two_pow_sub_one]
        exact decide_eq_true hi240
      have hmod : (n % 2 ^ 240).testBit i = n.testBit i := by
        rw [Nat.testBit_mod_two_pow]
        simp [hi240]
      rw [hmask, hmod]
      simp
    · have hmask : (2 ^ 240 - 1).testBit i = false := by
        rw [Nat.testBit_two_pow_sub_one]
        exact decide_eq_false hi240
      have hmod : (n % 2 ^ 240).testBit i = false := by
        rw [Nat.testBit_mod_two_pow]
        simp [hi240]
      rw [hmask, hmod]
      simp
  · have h248le : 248 ≤ i := Nat.le_of_not_gt hi248
    simp [hi248]
    change (n.testBit i && (2 ^ 8 - 1).testBit (i - 248)) =
      (n / 2 ^ 248).testBit (i - 248)
    by_cases hi256 : i < 256
    · have hsub8 : i - 248 < 8 := by omega
      have hdiv := divPow_testBit n 248 i h248le
      have hmask : (2 ^ 8 - 1).testBit (i - 248) = true := by
        rw [Nat.testBit_two_pow_sub_one]
        exact decide_eq_true hsub8
      rw [hdiv, hmask]
      simp
    · have hsub8 : ¬ i - 248 < 8 := by omega
      have hnbit : n.testBit i = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega : 256 ≤ i)))
      have hdivfalse : (n / 2 ^ 248).testBit (i - 248) = false := by
        rw [divPow_testBit n 248 i h248le, hnbit]
      have hmask : (2 ^ 8 - 1).testBit (i - 248) = false := by
        rw [Nat.testBit_two_pow_sub_one]
        exact decide_eq_false hsub8
      rw [hmask, hdivfalse]
      simp

theorem storageLocStore_slot0Unlocked_false (evm : EVM.State) :
    storageLocStore evm slot0UnlockedLoc (.bool false) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
          slot0UnlockedClearMask)) := by
  unfold storageLocStore storageLocWriteWord slot0UnlockedLoc loc
  simp only [valueToWord, Bool.toUInt256_false, bind, Option.bind]
  congr 2
  apply u256_inj
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner { val := 0 }
  show fromBytes'
      ((List.take 30 ↑(EVM.Word.toBytesLEWithSizeProof w) ++
          List.take 1 ↑(EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0))) ++
        List.drop (30 + 1) ↑(EVM.Word.toBytesLEWithSizeProof w)) =
    (UInt256.land w slot0UnlockedClearMask).toNat
  rw [show List.take 1 ↑(EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0)) =
      ([0] : List UInt8) by
    native_decide]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  rw [u256_land_toNat, slot0UnlockedClearMask_toNat]
  rw [natLandClearSlot0UnlockedByte w.toNat w.val.isLt]
  have hsumLt :
      w.toNat % 2 ^ 240 + w.toNat / 2 ^ 248 * 2 ^ 248 < UInt256.size := by
    rw [← natLandClearSlot0UnlockedByte w.toNat w.val.isLt]
    exact lt_of_le_of_lt (nat_land_le_right _ _) (by norm_num [UInt256.size])
  rw [Nat.mod_eq_of_lt hsumLt]
  have hlen30 : (List.take 30 (EVM.Word.toBytesLEWithSizeProof w).1).length = 30 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof w).2]
    norm_num
  have hlen31 : (List.take 30 (EVM.Word.toBytesLEWithSizeProof w).1 ++ [0]).length = 31 := by
    rw [List.length_append, hlen30]
    norm_num
  rw [hlen30]
  rw [hlen31]
  simp [fromBytes']
  ring

theorem natLorSlot0UnlockedByte (n byte : Nat) (hbyte : byte < 2 ^ 8) :
    Nat.lor (n % 2 ^ 240 + n / 2 ^ 248 * 2 ^ 248) (byte * 2 ^ 240) =
      n % 2 ^ 240 + byte * 2 ^ 240 + n / 2 ^ 248 * 2 ^ 248 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change ((n % 2 ^ 240 + n / 2 ^ 248 * 2 ^ 248) ||| (byte * 2 ^ 240)).testBit i =
    (n % 2 ^ 240 + byte * 2 ^ 240 + n / 2 ^ 248 * 2 ^ 248).testBit i
  rw [Nat.testBit_or]
  rw [show n % 2 ^ 240 + n / 2 ^ 248 * 2 ^ 248 =
      2 ^ 248 * (n / 2 ^ 248) + n % 2 ^ 240 by ring]
  rw [Nat.testBit_two_pow_mul_add (a := n / 2 ^ 248)
    (b_lt := lt_trans (Nat.mod_lt _ (show 0 < 2 ^ 240 by norm_num))
      (by norm_num : 2 ^ 240 < 2 ^ 248))]
  rw [show n % 2 ^ 240 + byte * 2 ^ 240 + n / 2 ^ 248 * 2 ^ 248 =
      2 ^ 248 * (n / 2 ^ 248) + (2 ^ 240 * byte + n % 2 ^ 240) by ring]
  have hmid : 2 ^ 240 * byte + n % 2 ^ 240 < 2 ^ 248 := by
    have hlow : n % 2 ^ 240 ≤ 2 ^ 240 - 1 :=
      Nat.le_pred_of_lt (Nat.mod_lt _ (show 0 < 2 ^ 240 by norm_num))
    have hbytele : byte ≤ 2 ^ 8 - 1 := Nat.le_pred_of_lt hbyte
    have hmax : 2 ^ 240 * (2 ^ 8 - 1) + (2 ^ 240 - 1) < 2 ^ 248 := by
      norm_num [Nat.pow_add]
    nlinarith
  rw [Nat.testBit_two_pow_mul_add (a := n / 2 ^ 248) (b_lt := hmid)]
  rw [Nat.testBit_two_pow_mul_add (a := byte)
    (b_lt := Nat.mod_lt _ (show 0 < 2 ^ 240 by norm_num))]
  rw [show byte * 2 ^ 240 = 2 ^ 240 * byte + 0 by ring]
  rw [Nat.testBit_two_pow_mul_add (a := byte) (b_lt := show 0 < 2 ^ 240 by norm_num)]
  by_cases hi240 : i < 240
  · simp [hi240]
  · have h240le : 240 ≤ i := Nat.le_of_not_gt hi240
    have hlowfalse : (n % 2 ^ 240).testBit i = false := by
      exact Nat.testBit_lt_two_pow
        (lt_of_lt_of_le (Nat.mod_lt _ (show 0 < 2 ^ 240 by norm_num))
          (Nat.pow_le_pow_right (by norm_num) h240le))
    by_cases hi248 : i < 248
    · simp [hi240, hi248]
      intro hlowtrue
      have hlowfalse' :
          (n % 1766847064778384329583297500742918515827483896875618958121606201292619776).testBit i =
            false := by
        simpa using hlowfalse
      rw [hlowfalse'] at hlowtrue
      cases hlowtrue
    · have hbytefalse : byte.testBit (i - 240) = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hbyte (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hi240, hi248]
      intro hbytetrue
      rw [hbytefalse] at hbytetrue
      cases hbytetrue

theorem natLorSlot0UnlockedTrueByte (n : Nat) :
    Nat.lor (n % 2 ^ 240 + n / 2 ^ 248 * 2 ^ 248) (2 ^ 240) =
      n % 2 ^ 240 + 2 ^ 240 + n / 2 ^ 248 * 2 ^ 248 := by
  simpa using natLorSlot0UnlockedByte n 1 (by norm_num : 1 < 2 ^ 8)

theorem slot0UnlockedTrueSlotWord_eq_of_accountMapEquiv
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ evm.accountMap) (hEnv : evm.executionEnv = I) :
    UInt256.lor
        (UInt256.shiftLeft ⟨1⟩ ⟨240⟩)
        (UInt256.land slot0UnlockedClearMask (codeOwnerStorageWord I σ ⟨0⟩)) =
      slot0UnlockedTrueSlotWord evm := by
  have hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ =
        codeOwnerStorageWord I σ ⟨0⟩ := by
    have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ (⟨0⟩ : UInt256)
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      codeOwnerStorageWord, hEnv] using hslot.symm
  have hclearLt :
      (codeOwnerStorageWord I σ ⟨0⟩).toNat % 2 ^ 240 +
          (codeOwnerStorageWord I σ ⟨0⟩).toNat / 2 ^ 248 * 2 ^ 248 <
        UInt256.size := by
    rw [← natLandClearSlot0UnlockedByte
      (codeOwnerStorageWord I σ ⟨0⟩).toNat (codeOwnerStorageWord I σ ⟨0⟩).val.isLt]
    exact lt_of_le_of_lt (nat_land_le_right _ _) (by norm_num [UInt256.size])
  have htrueLt :
      (codeOwnerStorageWord I σ ⟨0⟩).toNat % 2 ^ 240 + 2 ^ 240 +
          (codeOwnerStorageWord I σ ⟨0⟩).toNat / 2 ^ 248 * 2 ^ 248 <
        UInt256.size := by
    let w := codeOwnerStorageWord I σ ⟨0⟩
    have hlow : w.toNat % 2 ^ 240 ≤ 2 ^ 240 - 1 :=
      Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
    have hhighLt : w.toNat / 2 ^ 248 < 2 ^ 8 := by
      apply Nat.div_lt_of_lt_mul
      rw [show 2 ^ 248 * 2 ^ 8 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
      change w.val.val < UInt256.size
      exact w.val.isLt
    have hhigh : w.toNat / 2 ^ 248 ≤ 2 ^ 8 - 1 := Nat.le_pred_of_lt hhighLt
    have hmax : (2 ^ 240 - 1) + 2 ^ 240 + (2 ^ 8 - 1) * 2 ^ 248 <
        UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    dsimp [w] at hlow hhigh
    omega
  apply u256_inj
  rw [slot0UnlockedTrueSlotWord, hload, u256_lor_toNat, u256_land_toNat]
  rw [slot0UnlockedClearMask_toNat]
  rw [nat_land_comm, natLandClearSlot0UnlockedByte]
  rw [Nat.mod_eq_of_lt hclearLt]
  rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨240⟩).toNat = 2 ^ 240 by
    native_decide]
  rw [nat_lor_comm, natLorSlot0UnlockedTrueByte]
  rw [Nat.mod_eq_of_lt htrueLt]
  exact (ulit_toNat' _ htrueLt).symm
  exact (codeOwnerStorageWord I σ ⟨0⟩).val.isLt

theorem storageLocStore_slot0Unlocked_true (evm : EVM.State) :
    storageLocStore evm slot0UnlockedLoc (.bool true) =
      some (slot0AfterUnlockState evm) := by
  unfold storageLocStore storageLocWriteWord slot0UnlockedLoc loc
  simp only [valueToWord, Bool.toUInt256_true, bind, Option.bind]
  congr 2
  apply u256_inj
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner { val := 0 }
  show fromBytes'
      ((List.take 30 ↑(EVM.Word.toBytesLEWithSizeProof w) ++
          List.take 1 ↑(EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 1))) ++
        List.drop (30 + 1) ↑(EVM.Word.toBytesLEWithSizeProof w)) =
    (slot0UnlockedTrueSlotWord evm).toNat
  rw [show List.take 1 ↑(EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 1)) =
      ([1] : List UInt8) by
    native_decide]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  rw [show 256 ^ (30 : Nat) = 2 ^ 240 by norm_num [Nat.pow_add]]
  rw [show 256 ^ (31 : Nat) = 2 ^ 248 by norm_num [Nat.pow_add]]
  have hlen30 : (List.take 30 (EVM.Word.toBytesLEWithSizeProof w).1).length = 30 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof w).2]
    norm_num
  have hlen31 : (List.take 30 (EVM.Word.toBytesLEWithSizeProof w).1 ++ [1]).length = 31 := by
    rw [List.length_append, hlen30]
    norm_num
  rw [hlen30, hlen31]
  rw [show (slot0UnlockedTrueSlotWord evm).toNat =
      w.toNat % 2 ^ 240 + 2 ^ 240 + w.toNat / 2 ^ 248 * 2 ^ 248 by
    dsimp [slot0UnlockedTrueSlotWord, w]
    exact ulit_toNat' _ (slot0UnlockedTrueSlotWord_nat_lt evm)]
  simp [fromBytes']
  ring

end Benchmarks.UniswapV3Pool
