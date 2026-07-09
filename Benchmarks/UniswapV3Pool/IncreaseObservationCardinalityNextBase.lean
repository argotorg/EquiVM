import Benchmarks.UniswapV3Pool.Common
import Benchmarks.UniswapV3Pool.Locking
import Benchmarks.UniswapV3Pool.NoDelegateCall

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

abbrev increaseObservationCardinalityNextUint16Mask : UInt256 := UInt256.ofNat (2 ^ 16 - 1)

abbrev increaseObservationCardinalityNextUint8Mask : UInt256 := UInt256.ofNat (2 ^ 8 - 1)

abbrev increaseObservationCardinalityNextUnlockedShift : UInt256 :=
  UInt256.shiftLeft ⟨1⟩ ⟨240⟩

abbrev increaseObservationCardinalityNextUnlockedByte (σ : AccountMap)
    (I : ExecutionEnv) : UInt256 :=
  UInt256.land increaseObservationCardinalityNextUint8Mask
    (UInt256.div (solcSlotWord σ I ⟨0⟩) increaseObservationCardinalityNextUnlockedShift)

abbrev increaseObservationCardinalityNextUnlockedClearMask : UInt256 :=
  UInt256.lnot (UInt256.shiftLeft increaseObservationCardinalityNextUint8Mask ⟨240⟩)

abbrev increaseObservationCardinalityNextLockedSlotWord (σ : AccountMap)
    (I : ExecutionEnv) : UInt256 :=
  UInt256.land increaseObservationCardinalityNextUnlockedClearMask (solcSlotWord σ I ⟨0⟩)

abbrev increaseObservationCardinalityNextArgWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (calldataWord I.calldata 4) increaseObservationCardinalityNextUint16Mask

abbrev increaseObservationCardinalityNextArgValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (increaseObservationCardinalityNextArgWord I).toNat)

abbrev increaseObservationCardinalityNextOldWord (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  slot0ObservationCardinalityNextWord σ I

abbrev increaseObservationCardinalityNextOldValue (σ : AccountMap) (I : ExecutionEnv) :
    Value :=
  .int (Int.ofNat (increaseObservationCardinalityNextOldWord σ I).toNat)

abbrev increaseObservationCardinalityNextStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "observationCardinalityNext"
    (increaseObservationCardinalityNextArgValue I)

abbrev increaseObservationCardinalityNextStoreWithOld (σ : AccountMap)
    (I : ExecutionEnv) : Store :=
  (increaseObservationCardinalityNextStore I).insert "observationCardinalityNextOld"
    (increaseObservationCardinalityNextOldValue σ I)

abbrev increaseObservationCardinalityNextStoreWithOldNew (σ : AccountMap)
    (I : ExecutionEnv) : Store :=
  (increaseObservationCardinalityNextStoreWithOld σ I).insert
    "observationCardinalityNextNew" (increaseObservationCardinalityNextArgValue I)

abbrev increaseObservationCardinalityNextStoreWithOldNewNoGrow (σ : AccountMap)
    (I : ExecutionEnv) : Store :=
  (increaseObservationCardinalityNextStoreWithOldNew σ I).insert
    "observationCardinalityNextNew" (increaseObservationCardinalityNextOldValue σ I)

abbrev increaseObservationCardinalityNextUnlockedLoc : StorageLoc :=
  loc ⟨0⟩ ⟨30, by decide⟩ ⟨1, by decide⟩ (by decide) .bool

abbrev increaseObservationCardinalityNextObservationCardinalityNextLoc : StorageLoc :=
  loc ⟨0⟩ ⟨27, by decide⟩ ⟨2, by decide⟩ (by decide) (.int uint16Int)

abbrev increaseObservationCardinalityNextNoGrowSlotWord (evm : EVM.State)
    (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat
    (fromBytes'
      ((List.take 27
          (EVM.Word.toBytesLEWithSizeProof
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)).1 ++
        List.take 2
          (EVM.Word.toBytesLEWithSizeProof
            (increaseObservationCardinalityNextOldWord evm.accountMap I)).1) ++
        List.drop (27 + 2)
          (EVM.Word.toBytesLEWithSizeProof
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)).1))

abbrev increaseObservationCardinalityNextAfterNoGrowObsNextState (evm : EVM.State)
    (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (increaseObservationCardinalityNextNoGrowSlotWord evm I)

abbrev increaseObservationCardinalityNextEvmNoGrowObsNextSlotWord
    (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.land
      (codeOwnerStorageWord I σ ⟨0⟩)
      (UInt256.lnot (UInt256.shiftLeft (⟨65535⟩ : UInt256) ⟨216⟩)))
    (UInt256.mul
      (UInt256.land (increaseObservationCardinalityNextOldWord σ I) (⟨65535⟩ : UInt256))
      (UInt256.shiftLeft ⟨1⟩ ⟨216⟩))

abbrev increaseObservationCardinalityNextEvmUnlockedTrueSlotWord
    (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.shiftLeft ⟨1⟩ ⟨240⟩)
    (UInt256.land slot0UnlockedClearMask (codeOwnerStorageWord I σ ⟨0⟩))

theorem increaseObservationCardinalityNextUint16Mask_toNat :
    increaseObservationCardinalityNextUint16Mask.toNat = 2 ^ 16 - 1 := by
  exact ulit_toNat' _ (by norm_num [UInt256.size])

theorem increaseObservationCardinalityNextUint16Mask_decode (w : UInt256) :
    (UInt256.land w increaseObservationCardinalityNextUint16Mask).toNat =
      w.toNat % EVM.twoPow 16 := by
  rw [u256_land_toNat, increaseObservationCardinalityNextUint16Mask_toNat,
    nat_land_mask_eq_mod]
  exact Nat.mod_eq_of_lt (by
    exact lt_trans (Nat.mod_lt _ (by norm_num [EVM.twoPow]))
      (by norm_num [EVM.twoPow, UInt256.size]))

theorem decodeScalarWordWithMode_uint16_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWordWithMode? DecodeMode.legacySolc05 uint16 bytes start =
      some
        (.int (Int.ofNat
          (UInt256.land (ABI.bytesToWord ((bytes.drop start).take 32))
            increaseObservationCardinalityNextUint16Mask).toNat),
          start + 32) := by
  simp only [decodeScalarWordWithMode?]
  unfold readWord? readBytes? uint16 uint16Int
  rw [if_pos hlen]
  simp only [bind, Option.bind]
  unfold decodeABIWord?
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  rw [increaseObservationCardinalityNextUint16Mask_decode]
  rfl

theorem decodeScalarWordsWithMode_uint16_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05 [uint16] bytes 0 =
      some
        [ .int (Int.ofNat
            (UInt256.land (ABI.bytesToWord (bytes.take 32))
              increaseObservationCardinalityNextUint16Mask).toNat) ] := by
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint16_ok (bytes := bytes) (start := 0) (by simpa using hlen0)]
  simp only [List.drop_zero, bind, Option.bind]

theorem decodeScalarWordsWithMode_uint16_none_short {bytes : List UInt8}
    (hshort : bytes.length < 32) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05 [uint16] bytes 0 = none := by
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ (bytes.take 32).length = 32 := by
    rw [List.length_take]
    omega
  unfold decodeScalarWordWithMode? readWord? readBytes? uint16 uint16Int
  simp only [List.drop_zero]
  rw [if_neg htake0n]
  simp only [Option.bind, bind]

theorem increaseObservationCardinalityNextUnlockedByte_eq_slot0UnlockedRawWord
    (σ : AccountMap) (I : ExecutionEnv) :
    increaseObservationCardinalityNextUnlockedByte σ I = slot0UnlockedRawWord σ I := by
  have hshift : increaseObservationCardinalityNextUnlockedShift = slot0ShiftBytes 30 := by
    native_decide
  simp [increaseObservationCardinalityNextUnlockedByte, slot0UnlockedRawWord,
    increaseObservationCardinalityNextUnlockedShift, slot0ShiftBytes, slot0SlotWord,
    increaseObservationCardinalityNextUint8Mask, slot0Uint8Mask, hshift, u256_land_comm]

theorem uniswapV3PoolIncreaseObservationCardinalityNextEvalUnlocked {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? (config v)
      { contract := contract v, locals := increaseObservationCardinalityNextStore I }
      (initState cA gh bl σ σ₀ g A I) (.storage (slot0F "unlocked")) =
      .ok (wordToElem .bool (increaseObservationCardinalityNextUnlockedByte σ I)) := by
  rw [evalExpr_storage_scalar
    (t := .bool)
    (slot := slot0F "unlocked")
    (er := { base := "slot0", steps := [.field "unlocked"] })
    (loc := increaseObservationCardinalityNextUnlockedLoc)
    (hbase := by simp [slot0F, increaseObservationCardinalityNextStore])
    (her := by
      simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind])
    (hty := by
      simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy, boolSt])
    (hloc := by
      funext evm
      simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
        increaseObservationCardinalityNextUnlockedLoc, loc])]
  simpa [increaseObservationCardinalityNextUnlockedByte_eq_slot0UnlockedRawWord] using
    slot0StorageLocLoad_unlocked (initState cA gh bl σ σ₀ g A I)

theorem increaseObservationCardinalityNextUnlockedByte_wordToElem_false
    {σ : AccountMap} {I : ExecutionEnv}
    (hzero : increaseObservationCardinalityNextUnlockedByte σ I = ⟨0⟩) :
    wordToElem .bool (increaseObservationCardinalityNextUnlockedByte σ I) = .bool false := by
  simp [wordToElem, hzero]

theorem increaseObservationCardinalityNextUnlockedByte_wordToElem_true
    {σ : AccountMap} {I : ExecutionEnv}
    (hnz : increaseObservationCardinalityNextUnlockedByte σ I ≠ ⟨0⟩) :
    wordToElem .bool (increaseObservationCardinalityNextUnlockedByte σ I) = .bool true := by
  have hbeq : ((increaseObservationCardinalityNextUnlockedByte σ I).val == 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro hval
    apply hnz
    apply u256_inj
    simpa [UInt256.toNat] using hval
  simp [wordToElem, hbeq]

theorem increaseObservationCardinalityNextUnlockedByte_transport
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    increaseObservationCardinalityNextUnlockedByte σ_solm I =
      increaseObservationCardinalityNextUnlockedByte σ_evm I := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ (⟨0⟩ : UInt256)
  dsimp [increaseObservationCardinalityNextUnlockedByte, solcSlotWord]
  rw [← hslot]

theorem increaseObservationCardinalityNextLockedSlotWord_transport
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    increaseObservationCardinalityNextLockedSlotWord σ_solm I =
      increaseObservationCardinalityNextLockedSlotWord σ_evm I := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ (⟨0⟩ : UInt256)
  dsimp [increaseObservationCardinalityNextLockedSlotWord, solcSlotWord]
  rw [← hslot]

theorem increaseObservationCardinalityNextOldWord_transport
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    increaseObservationCardinalityNextOldWord σ_solm I =
      increaseObservationCardinalityNextOldWord σ_evm I := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ (⟨0⟩ : UInt256)
  dsimp [increaseObservationCardinalityNextOldWord, slot0ObservationCardinalityNextWord,
    slot0SlotWord, solcSlotWord]
  rw [← hslot]

theorem increaseObservationCardinalityNextStorageLoad_codeOwner_eq
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ evm.accountMap) (hEnv : evm.executionEnv = I) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ =
      codeOwnerStorageWord I σ ⟨0⟩ := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ (⟨0⟩ : UInt256)
  simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    codeOwnerStorageWord, hEnv] using hslot.symm

theorem increaseObservationCardinalityNextNoGrowClearMask_toNat :
    (UInt256.lnot (UInt256.shiftLeft (⟨65535⟩ : UInt256) ⟨216⟩)).toNat =
      2 ^ 256 - 2 ^ 232 + (2 ^ 216 - 1) := by
  native_decide

theorem natLandClearObservationCardinalityNextBytes (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n (2 ^ 256 - 2 ^ 232 + (2 ^ 216 - 1)) =
      n % 2 ^ 216 + (n / 2 ^ 232) * 2 ^ 232 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& (2 ^ 256 - 2 ^ 232 + (2 ^ 216 - 1))).testBit i =
    (n % 2 ^ 216 + n / 2 ^ 232 * 2 ^ 232).testBit i
  rw [Nat.testBit_and]
  rw [show n % 2 ^ 216 + (n / 2 ^ 232) * 2 ^ 232 =
      2 ^ 232 * (n / 2 ^ 232) + n % 2 ^ 216 by ring]
  rw [Nat.testBit_two_pow_mul_add (a := n / 2 ^ 232)
    (b_lt := lt_trans (Nat.mod_lt _ (show 0 < 2 ^ 216 by norm_num))
      (by norm_num : 2 ^ 216 < 2 ^ 232))]
  rw [show 2 ^ 256 - 2 ^ 232 + (2 ^ 216 - 1) =
      2 ^ 232 * (2 ^ 24 - 1) + (2 ^ 216 - 1) by norm_num [Nat.pow_add]]
  have hmaskLow : 2 ^ 216 - 1 < 2 ^ 232 := by norm_num
  rw [Nat.testBit_two_pow_mul_add (a := 2 ^ 24 - 1) (b_lt := hmaskLow)]
  by_cases hi232 : i < 232
  · simp [hi232]
    change (n.testBit i && (2 ^ 216 - 1).testBit i) = (n % 2 ^ 216).testBit i
    by_cases hi216 : i < 216
    · have hmask : (2 ^ 216 - 1).testBit i = true := by
        rw [Nat.testBit_two_pow_sub_one]
        exact decide_eq_true hi216
      have hmod : (n % 2 ^ 216).testBit i = n.testBit i := by
        rw [Nat.testBit_mod_two_pow]
        simp [hi216]
      rw [hmask, hmod]
      simp
    · have hmask : (2 ^ 216 - 1).testBit i = false := by
        rw [Nat.testBit_two_pow_sub_one]
        exact decide_eq_false hi216
      have hmod : (n % 2 ^ 216).testBit i = false := by
        rw [Nat.testBit_mod_two_pow]
        simp [hi216]
      rw [hmask, hmod]
      simp
  · have h232le : 232 ≤ i := Nat.le_of_not_gt hi232
    simp [hi232]
    change (n.testBit i && (2 ^ 24 - 1).testBit (i - 232)) =
      (n / 2 ^ 232).testBit (i - 232)
    by_cases hi256 : i < 256
    · have hsub24 : i - 232 < 24 := by omega
      have hdiv := divPow_testBit n 232 i h232le
      have hmask : (2 ^ 24 - 1).testBit (i - 232) = true := by
        rw [Nat.testBit_two_pow_sub_one]
        exact decide_eq_true hsub24
      rw [hdiv, hmask]
      simp
    · have hsub24 : ¬ i - 232 < 24 := by omega
      have hnbit : n.testBit i = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega : 256 ≤ i)))
      have hdivfalse : (n / 2 ^ 232).testBit (i - 232) = false := by
        rw [divPow_testBit n 232 i h232le, hnbit]
      have hmask : (2 ^ 24 - 1).testBit (i - 232) = false := by
        rw [Nat.testBit_two_pow_sub_one]
        exact decide_eq_false hsub24
      rw [hmask, hdivfalse]
      simp

private theorem nat_lor_packed_uint16_byte216 (n field : Nat)
    (hfield : field < 2 ^ 16) :
    Nat.lor (n % 2 ^ 216 + n / 2 ^ 232 * 2 ^ 232) (field * 2 ^ 216) =
      n % 2 ^ 216 + field * 2 ^ 216 + n / 2 ^ 232 * 2 ^ 232 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change ((n % 2 ^ 216 + n / 2 ^ 232 * 2 ^ 232) ||| (field * 2 ^ 216)).testBit i =
    (n % 2 ^ 216 + field * 2 ^ 216 + n / 2 ^ 232 * 2 ^ 232).testBit i
  rw [Nat.testBit_or]
  rw [show n % 2 ^ 216 + n / 2 ^ 232 * 2 ^ 232 =
      2 ^ 232 * (n / 2 ^ 232) + n % 2 ^ 216 by ring]
  rw [Nat.testBit_two_pow_mul_add (a := n / 2 ^ 232)
    (b_lt := lt_trans (Nat.mod_lt _ (show 0 < 2 ^ 216 by norm_num))
      (by norm_num : 2 ^ 216 < 2 ^ 232))]
  rw [show n % 2 ^ 216 + field * 2 ^ 216 + n / 2 ^ 232 * 2 ^ 232 =
      2 ^ 232 * (n / 2 ^ 232) + (2 ^ 216 * field + n % 2 ^ 216) by ring]
  have hmid : 2 ^ 216 * field + n % 2 ^ 216 < 2 ^ 232 := by
    have hlow : n % 2 ^ 216 ≤ 2 ^ 216 - 1 :=
      Nat.le_pred_of_lt (Nat.mod_lt _ (show 0 < 2 ^ 216 by norm_num))
    have hfieldle : field ≤ 2 ^ 16 - 1 := Nat.le_pred_of_lt hfield
    have hmax : 2 ^ 216 * (2 ^ 16 - 1) + (2 ^ 216 - 1) < 2 ^ 232 := by
      norm_num [Nat.pow_add]
    nlinarith
  rw [Nat.testBit_two_pow_mul_add (a := n / 2 ^ 232) (b_lt := hmid)]
  rw [Nat.testBit_two_pow_mul_add (a := field)
    (b_lt := Nat.mod_lt _ (show 0 < 2 ^ 216 by norm_num))]
  rw [show field * 2 ^ 216 = 2 ^ 216 * field + 0 by ring]
  rw [Nat.testBit_two_pow_mul_add (a := field) (b_lt := show 0 < 2 ^ 216 by norm_num)]
  by_cases hi216 : i < 216
  · simp [hi216]
  · have h216le : 216 ≤ i := Nat.le_of_not_gt hi216
    have hlowfalse : (n % 2 ^ 216).testBit i = false := by
      exact Nat.testBit_lt_two_pow
        (lt_of_lt_of_le (Nat.mod_lt _ (show 0 < 2 ^ 216 by norm_num))
          (Nat.pow_le_pow_right (by norm_num) h216le))
    by_cases hi232 : i < 232
    · simp [hi216, hi232]
      intro hlowtrue
      have hlowfalse' :
          (n % 105312291668557186697918027683670432318895095400549111254310977536).testBit i =
            false := by
        simpa using hlowfalse
      rw [hlowfalse'] at hlowtrue
      cases hlowtrue
    · have hfieldfalse : field.testBit (i - 216) = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hfield (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hi216, hi232]
      intro hfieldtrue
      rw [hfieldfalse] at hfieldtrue
      cases hfieldtrue

private theorem nat_lor_packed_byte240 (n byte : Nat) (hbyte : byte < 2 ^ 8) :
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

private theorem nat_lor_packed_true_byte240 (n : Nat) :
    Nat.lor (n % 2 ^ 240 + n / 2 ^ 248 * 2 ^ 248) (2 ^ 240) =
      n % 2 ^ 240 + 2 ^ 240 + n / 2 ^ 248 * 2 ^ 248 := by
  simpa using nat_lor_packed_byte240 n 1 (by norm_num : 1 < 2 ^ 8)

theorem increaseObservationCardinalityNextNoGrowSlotWord_nat_lt
    (evm : EVM.State) (I : ExecutionEnv) :
    fromBytes'
        ((List.take 27
            (EVM.Word.toBytesLEWithSizeProof
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)).1 ++
          List.take 2
            (EVM.Word.toBytesLEWithSizeProof
              (increaseObservationCardinalityNextOldWord evm.accountMap I)).1) ++
          List.drop (27 + 2)
            (EVM.Word.toBytesLEWithSizeProof
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)).1) <
      UInt256.size := by
  let bs :=
        ((List.take 27
            (EVM.Word.toBytesLEWithSizeProof
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)).1 ++
          List.take 2
            (EVM.Word.toBytesLEWithSizeProof
              (increaseObservationCardinalityNextOldWord evm.accountMap I)).1) ++
          List.drop (27 + 2)
            (EVM.Word.toBytesLEWithSizeProof
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)).1)
  have hlen : bs.length = 32 := by
    simp [bs, List.length_take, List.length_drop,
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)).2,
      (EVM.Word.toBytesLEWithSizeProof
        (increaseObservationCardinalityNextOldWord evm.accountMap I)).2]
  apply lt_of_lt_of_le (b := 2 ^ (8 * bs.length))
  · simpa [bs] using (EVM.fromBytes'_le (bs := bs))
  · rw [hlen]
    norm_num [UInt256.size]

theorem increaseObservationCardinalityNextEvmNoGrowObsNextSlotWord_eq
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ evm.accountMap) (hEnv : evm.executionEnv = I) :
    increaseObservationCardinalityNextEvmNoGrowObsNextSlotWord σ I =
      increaseObservationCardinalityNextNoGrowSlotWord evm I := by
  have hload := increaseObservationCardinalityNextStorageLoad_codeOwner_eq
    (evm := evm) (σ := σ) (I := I) hAccounts hEnv
  have holdEq :
      increaseObservationCardinalityNextOldWord evm.accountMap I =
        increaseObservationCardinalityNextOldWord σ I := by
    exact increaseObservationCardinalityNextOldWord_transport
      (σ_evm := σ) (σ_solm := evm.accountMap) hAccounts
  have holdLt :
      (increaseObservationCardinalityNextOldWord σ I).toNat < 2 ^ 16 := by
    simpa [increaseObservationCardinalityNextOldWord] using
      slot0Uint16Mask_bound (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 27))
  have hclearLt :
      (codeOwnerStorageWord I σ ⟨0⟩).toNat % 2 ^ 216 +
          (codeOwnerStorageWord I σ ⟨0⟩).toNat / 2 ^ 232 * 2 ^ 232 <
        UInt256.size := by
    rw [← natLandClearObservationCardinalityNextBytes
      (codeOwnerStorageWord I σ ⟨0⟩).toNat (codeOwnerStorageWord I σ ⟨0⟩).val.isLt]
    exact lt_of_le_of_lt (nat_land_le_right _ _) (by norm_num [UInt256.size])
  have hpackedLt :
      (codeOwnerStorageWord I σ ⟨0⟩).toNat % 2 ^ 216 +
          (increaseObservationCardinalityNextOldWord σ I).toNat * 2 ^ 216 +
            (codeOwnerStorageWord I σ ⟨0⟩).toNat / 2 ^ 232 * 2 ^ 232 <
        UInt256.size := by
    have hlow : (codeOwnerStorageWord I σ ⟨0⟩).toNat % 2 ^ 216 ≤ 2 ^ 216 - 1 :=
      Nat.le_pred_of_lt (Nat.mod_lt _ (show 0 < 2 ^ 216 by norm_num))
    have holdLe :
        (increaseObservationCardinalityNextOldWord σ I).toNat ≤ 2 ^ 16 - 1 :=
      Nat.le_pred_of_lt holdLt
    have hhighLt : (codeOwnerStorageWord I σ ⟨0⟩).toNat / 2 ^ 232 < 2 ^ 24 := by
      apply Nat.div_lt_of_lt_mul
      rw [show 2 ^ 232 * 2 ^ 24 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
      change (codeOwnerStorageWord I σ ⟨0⟩).val.val < UInt256.size
      exact (codeOwnerStorageWord I σ ⟨0⟩).val.isLt
    have hhighLe : (codeOwnerStorageWord I σ ⟨0⟩).toNat / 2 ^ 232 ≤ 2 ^ 24 - 1 :=
      Nat.le_pred_of_lt hhighLt
    have hmax :
        (2 ^ 216 - 1) + (2 ^ 16 - 1) * 2 ^ 216 +
            (2 ^ 24 - 1) * 2 ^ 232 <
          UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    nlinarith
  have hmulLt :
      (increaseObservationCardinalityNextOldWord σ I).toNat * 2 ^ 216 < UInt256.size := by
    exact lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_right holdLt (by norm_num : 0 < 2 ^ 216))
      (by norm_num [UInt256.size])
  have hmulMod :
      (increaseObservationCardinalityNextOldWord σ I).toNat * 2 ^ 216 % UInt256.size =
        (increaseObservationCardinalityNextOldWord σ I).toNat * 2 ^ 216 :=
    Nat.mod_eq_of_lt hmulLt
  have hsourceWordLt :
      fromBytes'
          ((List.take 27
              (EVM.Word.toBytesLEWithSizeProof (codeOwnerStorageWord I σ ⟨0⟩)).1 ++
            List.take 2
              (EVM.Word.toBytesLEWithSizeProof
                (increaseObservationCardinalityNextOldWord σ I)).1) ++
            List.drop (27 + 2)
              (EVM.Word.toBytesLEWithSizeProof (codeOwnerStorageWord I σ ⟨0⟩)).1) <
        UInt256.size := by
    let bs :=
          ((List.take 27
              (EVM.Word.toBytesLEWithSizeProof (codeOwnerStorageWord I σ ⟨0⟩)).1 ++
            List.take 2
              (EVM.Word.toBytesLEWithSizeProof
                (increaseObservationCardinalityNextOldWord σ I)).1) ++
            List.drop (27 + 2)
              (EVM.Word.toBytesLEWithSizeProof (codeOwnerStorageWord I σ ⟨0⟩)).1)
    have hlen : bs.length = 32 := by
      simp [bs, List.length_take, List.length_drop,
        (EVM.Word.toBytesLEWithSizeProof (codeOwnerStorageWord I σ ⟨0⟩)).2,
        (EVM.Word.toBytesLEWithSizeProof
          (increaseObservationCardinalityNextOldWord σ I)).2]
    apply lt_of_lt_of_le (b := 2 ^ (8 * bs.length))
    · simpa [bs] using (EVM.fromBytes'_le (bs := bs))
    · rw [hlen]
      norm_num [UInt256.size]
  apply u256_inj
  rw [increaseObservationCardinalityNextEvmNoGrowObsNextSlotWord,
    increaseObservationCardinalityNextNoGrowSlotWord]
  rw [hload, holdEq]
  rw [u256_lor_toNat, u256_land_toNat, u256_mul_toNat]
  rw [increaseObservationCardinalityNextNoGrowClearMask_toNat]
  rw [natLandClearObservationCardinalityNextBytes]
  rw [Nat.mod_eq_of_lt hclearLt]
  rw [u256_land_toNat]
  rw [show (⟨65535⟩ : UInt256).toNat = 2 ^ 16 - 1 by native_decide]
  rw [nat_land_mask_eq_mod]
  rw [Nat.mod_eq_of_lt holdLt]
  rw [Nat.mod_eq_of_lt (lt_trans holdLt (by norm_num [UInt256.size]))]
  rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨216⟩).toNat = 2 ^ 216 by
    native_decide]
  rw [hmulMod]
  rw [nat_lor_packed_uint16_byte216 _ _ holdLt]
  rw [Nat.mod_eq_of_lt hpackedLt]
  rw [ulit_toNat' _ hsourceWordLt]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  have hlen27 :
      (List.take 27 (EVM.Word.toBytesLEWithSizeProof (codeOwnerStorageWord I σ ⟨0⟩)).1).length =
        27 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof
      (codeOwnerStorageWord I σ ⟨0⟩)).2]
    norm_num
  have hlen29 :
      (List.take 27 (EVM.Word.toBytesLEWithSizeProof (codeOwnerStorageWord I σ ⟨0⟩)).1 ++
          List.take 2
            (EVM.Word.toBytesLEWithSizeProof
              (increaseObservationCardinalityNextOldWord σ I)).1).length =
        29 := by
    rw [List.length_append, hlen27, List.length_take,
      (EVM.Word.toBytesLEWithSizeProof
        (increaseObservationCardinalityNextOldWord σ I)).2]
    norm_num
  rw [hlen27, hlen29]
  rw [show 256 ^ (27 : Nat) = 2 ^ 216 by norm_num [Nat.pow_add]]
  rw [show 256 ^ (29 : Nat) = 2 ^ 232 by norm_num [Nat.pow_add]]
  rw [show 256 ^ (2 : Nat) = 2 ^ 16 by norm_num]
  rw [Nat.mod_eq_of_lt holdLt]
  ring
  exact (codeOwnerStorageWord I σ ⟨0⟩).val.isLt

theorem increaseObservationCardinalityNextEvmUnlockedTrueSlotWord_eq
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ evm.accountMap) (hEnv : evm.executionEnv = I) :
    increaseObservationCardinalityNextEvmUnlockedTrueSlotWord σ I =
      slot0UnlockedTrueSlotWord evm := by
  have hload := increaseObservationCardinalityNextStorageLoad_codeOwner_eq
    (evm := evm) (σ := σ) (I := I) hAccounts hEnv
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
  rw [increaseObservationCardinalityNextEvmUnlockedTrueSlotWord, slot0UnlockedTrueSlotWord]
  rw [hload]
  rw [u256_lor_toNat, u256_land_toNat]
  rw [slot0UnlockedClearMask_toNat]
  rw [nat_land_comm]
  rw [natLandClearSlot0UnlockedByte]
  rw [Nat.mod_eq_of_lt hclearLt]
  rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨240⟩).toNat = 2 ^ 240 by
    native_decide]
  rw [nat_lor_comm]
  rw [nat_lor_packed_true_byte240]
  rw [Nat.mod_eq_of_lt htrueLt]
  exact (ulit_toNat' _ htrueLt).symm
  exact (codeOwnerStorageWord I σ ⟨0⟩).val.isLt

theorem increaseObservationCardinalityNextFinalNoGrowAccountMapEquiv
    {evmOwner : EVM.State} {σOwnerEvm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σOwnerEvm evmOwner.accountMap)
    (hEnv : evmOwner.executionEnv = I) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σOwnerEvm ⟨0⟩
          (increaseObservationCardinalityNextEvmNoGrowObsNextSlotWord σOwnerEvm I))
        ⟨0⟩
        (increaseObservationCardinalityNextEvmUnlockedTrueSlotWord
          (sstoreAccountMap I.codeOwner σOwnerEvm ⟨0⟩
            (increaseObservationCardinalityNextEvmNoGrowObsNextSlotWord σOwnerEvm I)) I))
      (slot0AfterUnlockState
        (increaseObservationCardinalityNextAfterNoGrowObsNextState evmOwner I)).accountMap := by
  have hfirstWord := increaseObservationCardinalityNextEvmNoGrowObsNextSlotWord_eq
    (evm := evmOwner) (σ := σOwnerEvm) (I := I) hAccounts hEnv
  have hFirstAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σOwnerEvm ⟨0⟩
          (increaseObservationCardinalityNextEvmNoGrowObsNextSlotWord σOwnerEvm I))
        (increaseObservationCardinalityNextAfterNoGrowObsNextState evmOwner I).accountMap := by
    rw [hfirstWord]
    simpa [increaseObservationCardinalityNextAfterNoGrowObsNextState,
      storageStore_accountMap, hEnv] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
        (increaseObservationCardinalityNextNoGrowSlotWord evmOwner I) hAccounts
  have hFirstEnv :
      (increaseObservationCardinalityNextAfterNoGrowObsNextState evmOwner I).executionEnv = I := by
    simp [increaseObservationCardinalityNextAfterNoGrowObsNextState,
      storageStore_executionEnv, hEnv]
  have hsecondWord := increaseObservationCardinalityNextEvmUnlockedTrueSlotWord_eq
    (evm := increaseObservationCardinalityNextAfterNoGrowObsNextState evmOwner I)
    (σ := sstoreAccountMap I.codeOwner σOwnerEvm ⟨0⟩
      (increaseObservationCardinalityNextEvmNoGrowObsNextSlotWord σOwnerEvm I))
    (I := I) hFirstAccounts hFirstEnv
  rw [hsecondWord]
  simpa [slot0AfterUnlockState, storageStore_accountMap, hFirstEnv] using
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
      (slot0UnlockedTrueSlotWord
        (increaseObservationCardinalityNextAfterNoGrowObsNextState evmOwner I))
      hFirstAccounts

theorem increaseObservationCardinalityNextStoreWithOldNew_old
    (σ : AccountMap) (I : ExecutionEnv) :
    (increaseObservationCardinalityNextStoreWithOldNew σ I).get?
        "observationCardinalityNextOld" =
      some (increaseObservationCardinalityNextOldValue σ I) := by
  rw [increaseObservationCardinalityNextStoreWithOldNew]
  rw [store_get_ne (increaseObservationCardinalityNextStoreWithOld σ I)
    (increaseObservationCardinalityNextArgValue I) (by decide)]
  rw [increaseObservationCardinalityNextStoreWithOld, store_get_self]

theorem increaseObservationCardinalityNextStoreWithOld_param
    (σ : AccountMap) (I : ExecutionEnv) :
    (increaseObservationCardinalityNextStoreWithOld σ I).get?
        "observationCardinalityNext" =
      some (increaseObservationCardinalityNextArgValue I) := by
  rw [increaseObservationCardinalityNextStoreWithOld]
  rw [store_get_ne (increaseObservationCardinalityNextStore I)
    (increaseObservationCardinalityNextOldValue σ I) (by decide)]
  rw [increaseObservationCardinalityNextStore, store_get_self]

theorem increaseObservationCardinalityNextStoreWithOldNew_new
    (σ : AccountMap) (I : ExecutionEnv) :
    (increaseObservationCardinalityNextStoreWithOldNew σ I).get?
        "observationCardinalityNextNew" =
      some (increaseObservationCardinalityNextArgValue I) := by
  rw [increaseObservationCardinalityNextStoreWithOldNew, store_get_self]

theorem increaseObservationCardinalityNextStoreWithOldNewNoGrow_new
    (σ : AccountMap) (I : ExecutionEnv) :
    (increaseObservationCardinalityNextStoreWithOldNewNoGrow σ I).get?
        "observationCardinalityNextNew" =
      some (increaseObservationCardinalityNextOldValue σ I) := by
  rw [increaseObservationCardinalityNextStoreWithOldNewNoGrow, store_get_self]

theorem evalExpr_increaseObservationCardinalityNext_oldStorage {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExpr? (config v)
        { contract := contract v, locals := increaseObservationCardinalityNextStore I }
        evm (.storage (slot0F "observationCardinalityNext")) =
      .ok (increaseObservationCardinalityNextOldValue evm.accountMap I) := by
  rw [evalExpr_storage_scalar
    (t := .int uint16Int)
    (slot := slot0F "observationCardinalityNext")
    (er := { base := "slot0", steps := [.field "observationCardinalityNext"] })
    (loc := increaseObservationCardinalityNextObservationCardinalityNextLoc)
    (hbase := by simp [slot0F, increaseObservationCardinalityNextStore])
    (her := by
      simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind])
    (hty := by
      simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy,
        uint16St])
    (hloc := by
      funext evm
      simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
        increaseObservationCardinalityNextObservationCardinalityNextLoc, loc])]
  simpa [increaseObservationCardinalityNextOldValue, increaseObservationCardinalityNextOldWord,
    slot0ObservationCardinalityNextWord, slot0SlotWord, solcSlotWord, howner] using
    slot0StorageLocLoad_observationCardinalityNext evm

theorem evalExpr_increaseObservationCardinalityNext_param_withOld {v : PoolImmutables}
    (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv) :
    evalExpr? (config v)
        { contract := contract v, locals := increaseObservationCardinalityNextStoreWithOld σ I }
        evm (.var "observationCardinalityNext") =
      .ok (increaseObservationCardinalityNextArgValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [increaseObservationCardinalityNextStoreWithOld_param]

theorem evalExpr_increaseObservationCardinalityNext_old_withOldNew
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv) :
    evalExpr? (config v)
        { contract := contract v, locals := increaseObservationCardinalityNextStoreWithOldNew σ I }
        evm (.var "observationCardinalityNextOld") =
      .ok (increaseObservationCardinalityNextOldValue σ I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [increaseObservationCardinalityNextStoreWithOldNew_old]

theorem evalExpr_increaseObservationCardinalityNext_new_withOldNew
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv) :
    evalExpr? (config v)
        { contract := contract v, locals := increaseObservationCardinalityNextStoreWithOldNew σ I }
        evm (.var "observationCardinalityNextNew") =
      .ok (increaseObservationCardinalityNextArgValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [increaseObservationCardinalityNextStoreWithOldNew_new]

theorem evalExpr_increaseObservationCardinalityNext_new_withOldNewNoGrow
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv) :
    evalExpr? (config v)
        { contract := contract v,
          locals := increaseObservationCardinalityNextStoreWithOldNewNoGrow σ I }
        evm (.var "observationCardinalityNextNew") =
      .ok (increaseObservationCardinalityNextOldValue σ I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [increaseObservationCardinalityNextStoreWithOldNewNoGrow_new]

theorem assignStorageRef_increaseObservationCardinalityNext_noGrowLocal
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv) :
    assignStorageRef? (config v)
        { contract := contract v, locals := increaseObservationCardinalityNextStoreWithOldNew σ I }
        evm .localVar (varRef "observationCardinalityNextNew")
        (increaseObservationCardinalityNextOldValue σ I) =
      .ok
        ({ contract := contract v,
           locals := increaseObservationCardinalityNextStoreWithOldNewNoGrow σ I },
          evm) := by
  simp [assignStorageRef?, varRef, updateLocalPath?, EvalResult.bind, bind, pure,
    increaseObservationCardinalityNextStoreWithOldNewNoGrow]

theorem assignStorageRef_increaseObservationCardinalityNext_unlocked_true
    {v : PoolImmutables} (evm : EVM.State) (L : Store)
    (hbase : "slot0" ∉ L) :
    assignStorageRef? (config v)
        { contract := contract v, locals := L }
        evm .storage (slot0F "unlocked") (.bool true) =
      .ok ({ contract := contract v, locals := L }, slot0AfterUnlockState evm) := by
  apply assignStorageRef_storage_scalar_value
      (er := { base := "slot0", steps := [.field "unlocked"] })
      (ty := .elem .bool)
      (loc := increaseObservationCardinalityNextUnlockedLoc)
  · simpa [slot0F] using hbase
  · simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind]
  · simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy, boolSt]
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      increaseObservationCardinalityNextUnlockedLoc, loc]
  · trivial
  · simpa [increaseObservationCardinalityNextUnlockedLoc, slot0UnlockedLoc] using
      storageLocStore_slot0Unlocked_true evm

theorem storageLocStore_increaseObservationCardinalityNext_noGrowObsNext
    (evm : EVM.State) (I : ExecutionEnv) :
    storageLocStore evm increaseObservationCardinalityNextObservationCardinalityNextLoc
        (increaseObservationCardinalityNextOldValue evm.accountMap I) =
      some (increaseObservationCardinalityNextAfterNoGrowObsNextState evm I) := by
  unfold storageLocStore storageLocWriteWord
    increaseObservationCardinalityNextObservationCardinalityNextLoc loc
    increaseObservationCardinalityNextAfterNoGrowObsNextState
    increaseObservationCardinalityNextNoGrowSlotWord
    increaseObservationCardinalityNextOldValue
  simp only [valueToWord, bind, Option.bind]
  rw [show EVM.wordOfInt (Int.ofNat (increaseObservationCardinalityNextOldWord evm.accountMap I).toNat) =
      increaseObservationCardinalityNextOldWord evm.accountMap I by
    exact wordOfInt_ofNat_toNat _]
  apply congrArg some
  apply congrArg (fun w : UInt256 =>
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ w)
  apply u256_inj
  rw [ulit_toNat']
  · rfl
  · let bs :=
        ((List.take 27
            (EVM.Word.toBytesLEWithSizeProof
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)).1 ++
          List.take 2
            (EVM.Word.toBytesLEWithSizeProof
              (increaseObservationCardinalityNextOldWord evm.accountMap I)).1) ++
          List.drop (27 + 2)
            (EVM.Word.toBytesLEWithSizeProof
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)).1)
    have hlen : bs.length = 32 := by
      simp [bs, List.length_take, List.length_drop,
        (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)).2,
        (EVM.Word.toBytesLEWithSizeProof
          (increaseObservationCardinalityNextOldWord evm.accountMap I)).2]
    apply lt_of_lt_of_le (b := 2 ^ (8 * bs.length))
    · simpa [bs] using (EVM.fromBytes'_le (bs := bs))
    · rw [hlen]
      norm_num [UInt256.size]

theorem assignStorageRef_increaseObservationCardinalityNext_noGrowObsNext
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? (config v)
        { contract := contract v,
          locals := increaseObservationCardinalityNextStoreWithOldNewNoGrow evm.accountMap I }
        evm .storage (slot0F "observationCardinalityNext")
        (increaseObservationCardinalityNextOldValue evm.accountMap I) =
      .ok
        ({ contract := contract v,
           locals := increaseObservationCardinalityNextStoreWithOldNewNoGrow evm.accountMap I },
          increaseObservationCardinalityNextAfterNoGrowObsNextState evm I) := by
  apply assignStorageRef_storage_scalar_value
      (er := { base := "slot0", steps := [.field "observationCardinalityNext"] })
      (ty := .elem (.int uint16Int))
      (loc := increaseObservationCardinalityNextObservationCardinalityNextLoc)
  · simp [slot0F, increaseObservationCardinalityNextStoreWithOldNewNoGrow,
      increaseObservationCardinalityNextStoreWithOldNew,
      increaseObservationCardinalityNextStoreWithOld,
      increaseObservationCardinalityNextStore]
  · simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind]
  · simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy, uint16St]
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      increaseObservationCardinalityNextObservationCardinalityNextLoc, loc]
  · trivial
  · exact storageLocStore_increaseObservationCardinalityNext_noGrowObsNext evm I

theorem evalExpr_increaseObservationCardinalityNext_oldGtZero_false {v : PoolImmutables}
    (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (hzero : increaseObservationCardinalityNextOldWord σ I = ⟨0⟩) :
    evalExpr? (config v)
        { contract := contract v, locals := increaseObservationCardinalityNextStoreWithOldNew σ I }
        evm (gtE (.var "observationCardinalityNextOld") (.intLit 0)) =
      .ok (.bool false) := by
  simp only [gtE, evalExpr?, evalExpr_increaseObservationCardinalityNext_old_withOldNew,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  simp [hzero]

theorem evalExpr_increaseObservationCardinalityNext_oldGtZero_true {v : PoolImmutables}
    (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (hnz : increaseObservationCardinalityNextOldWord σ I ≠ ⟨0⟩) :
    evalExpr? (config v)
        { contract := contract v, locals := increaseObservationCardinalityNextStoreWithOldNew σ I }
        evm (gtE (.var "observationCardinalityNextOld") (.intLit 0)) =
      .ok (.bool true) := by
  simp only [gtE, evalExpr?, evalExpr_increaseObservationCardinalityNext_old_withOldNew,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  have hpos : 0 < (increaseObservationCardinalityNextOldWord σ I).toNat := by
    exact Nat.pos_of_ne_zero (by
      intro hz
      apply hnz
      apply u256_inj
      simpa using hz)
  simpa [increaseObservationCardinalityNextOldValue] using hpos

theorem evalExpr_increaseObservationCardinalityNext_newLeOld_true {v : PoolImmutables}
    (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (hnewLe : UInt256.gt (increaseObservationCardinalityNextArgWord I)
        (increaseObservationCardinalityNextOldWord σ I) = ⟨0⟩) :
    evalExpr? (config v)
        { contract := contract v, locals := increaseObservationCardinalityNextStoreWithOldNew σ I }
        evm (leE (.var "observationCardinalityNextNew")
          (.var "observationCardinalityNextOld")) =
      .ok (.bool true) := by
  simp only [leE, evalExpr?, evalExpr_increaseObservationCardinalityNext_new_withOldNew,
    evalExpr_increaseObservationCardinalityNext_old_withOldNew, EvalResult.bind, bind,
    evalBinaryOp?]
  have hleNat :
      (increaseObservationCardinalityNextArgWord I).toNat ≤
        (increaseObservationCardinalityNextOldWord σ I).toNat := by
    by_contra hnot
    have hlt :
        (increaseObservationCardinalityNextOldWord σ I).toNat <
          (increaseObservationCardinalityNextArgWord I).toNat := by
      omega
    have hgt : UInt256.gt (increaseObservationCardinalityNextArgWord I)
        (increaseObservationCardinalityNextOldWord σ I) = ⟨1⟩ := by
      exact ugt_one hlt
    rw [hgt] at hnewLe
    exact (by native_decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hnewLe
  simpa [increaseObservationCardinalityNextArgValue,
    increaseObservationCardinalityNextOldValue] using hleNat

theorem uniswapV3PoolIncreaseObservationCardinalityNextSourceNoGrowPrefix
    {v : PoolImmutables} {evm : EVM.State} {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (holdNonzero : increaseObservationCardinalityNextOldWord evm.accountMap I ≠ ⟨0⟩)
    (hnewLe : UInt256.gt (increaseObservationCardinalityNextArgWord I)
        (increaseObservationCardinalityNextOldWord evm.accountMap I) = ⟨0⟩) :
    ExecBlock (config v)
      { contract := contract v, locals := increaseObservationCardinalityNextStore I } evm
      [ .letDecl "observationCardinalityNextOld" (some uint16)
          (.storage (slot0F "observationCardinalityNext")),
        .letDecl "observationCardinalityNextNew" (some uint16)
          (.var "observationCardinalityNext"),
        .require (gtE (.var "observationCardinalityNextOld") (.intLit 0)),
        Stmt.ite (leE (.var "observationCardinalityNextNew")
            (.var "observationCardinalityNextOld"))
          [ .assign .localVar (varRef "observationCardinalityNextNew")
              (.var "observationCardinalityNextOld") ]
          [ .letDecl "i" (some uint16) (.var "observationCardinalityNextOld"),
            .while (ltE (.var "i") (.var "observationCardinalityNextNew"))
              [ .assign .storage (observationsRawF (.var "i") "blockTimestamp") (.intLit 1),
                .assign .localVar (varRef "i") (addE (.var "i") (.intLit 1)) ] ] ]
      (.ok
        { contract := contract v,
          locals := increaseObservationCardinalityNextStoreWithOldNewNoGrow evm.accountMap I }
        evm) := by
  refine ExecBlock.consNormal
    (ExecStmt.letDecl
      (evalExpr_increaseObservationCardinalityNext_oldStorage (v := v) evm I howner)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl
      (evalExpr_increaseObservationCardinalityNext_param_withOld
        (v := v) evm evm.accountMap I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_increaseObservationCardinalityNext_oldGtZero_true
        (v := v) evm evm.accountMap I holdNonzero)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (evalExpr_increaseObservationCardinalityNext_newLeOld_true
        (v := v) evm evm.accountMap I hnewLe) ?_) ExecBlock.nil
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_increaseObservationCardinalityNext_old_withOldNew
        (v := v) evm evm.accountMap I)
      (assignStorageRef_increaseObservationCardinalityNext_noGrowLocal
        (v := v) evm evm.accountMap I))
    ExecBlock.nil

theorem uniswapV3PoolIncreaseObservationCardinalityNextSourceNoGrowReturns
    {v : PoolImmutables} {evm : EVM.State} {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (holdNonzero : increaseObservationCardinalityNextOldWord evm.accountMap I ≠ ⟨0⟩)
    (hnewLe : UInt256.gt (increaseObservationCardinalityNextArgWord I)
        (increaseObservationCardinalityNextOldWord evm.accountMap I) = ⟨0⟩) :
    ExecBlock (config v)
      { contract := contract v, locals := increaseObservationCardinalityNextStore I } evm
      [ .letDecl "observationCardinalityNextOld" (some uint16)
          (.storage (slot0F "observationCardinalityNext")),
        .letDecl "observationCardinalityNextNew" (some uint16)
          (.var "observationCardinalityNext"),
        .require (gtE (.var "observationCardinalityNextOld") (.intLit 0)),
        Stmt.ite (leE (.var "observationCardinalityNextNew")
            (.var "observationCardinalityNextOld"))
          [ .assign .localVar (varRef "observationCardinalityNextNew")
              (.var "observationCardinalityNextOld") ]
          [ .letDecl "i" (some uint16) (.var "observationCardinalityNextOld"),
            .while (ltE (.var "i") (.var "observationCardinalityNextNew"))
              [ .assign .storage (observationsRawF (.var "i") "blockTimestamp") (.intLit 1),
                .assign .localVar (varRef "i") (addE (.var "i") (.intLit 1)) ] ],
        .assign .storage (slot0F "observationCardinalityNext")
          (.var "observationCardinalityNextNew"),
        .assign .storage (slot0F "unlocked") (.boolLit true) ]
      (.ok
        { contract := contract v,
          locals := increaseObservationCardinalityNextStoreWithOldNewNoGrow evm.accountMap I }
        (slot0AfterUnlockState
          (increaseObservationCardinalityNextAfterNoGrowObsNextState evm I))) := by
  have hprefix :=
    uniswapV3PoolIncreaseObservationCardinalityNextSourceNoGrowPrefix
      (v := v) (evm := evm) (I := I) howner holdNonzero hnewLe
  have htail :
      ExecBlock (config v)
        { contract := contract v,
          locals := increaseObservationCardinalityNextStoreWithOldNewNoGrow evm.accountMap I }
        evm
        [ .assign .storage (slot0F "observationCardinalityNext")
            (.var "observationCardinalityNextNew"),
          .assign .storage (slot0F "unlocked") (.boolLit true) ]
        (.ok
          { contract := contract v,
            locals := increaseObservationCardinalityNextStoreWithOldNewNoGrow evm.accountMap I }
          (slot0AfterUnlockState
            (increaseObservationCardinalityNextAfterNoGrowObsNextState evm I))) := by
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (evalExpr_increaseObservationCardinalityNext_new_withOldNewNoGrow
          (v := v) evm evm.accountMap I)
        (assignStorageRef_increaseObservationCardinalityNext_noGrowObsNext
          (v := v) evm I)) ?_
    exact ExecBlock.consNormal
      (ExecStmt.assign (by simp [evalExpr?, pure])
        (assignStorageRef_increaseObservationCardinalityNext_unlocked_true
          (v := v) (increaseObservationCardinalityNextAfterNoGrowObsNextState evm I)
          (increaseObservationCardinalityNextStoreWithOldNewNoGrow evm.accountMap I)
          (by
            simp [increaseObservationCardinalityNextStoreWithOldNewNoGrow,
              increaseObservationCardinalityNextStoreWithOldNew,
              increaseObservationCardinalityNextStoreWithOld,
              increaseObservationCardinalityNextStore])))
      ExecBlock.nil
  simpa using execBlock_append hprefix htail

theorem uniswapV3PoolIncreaseObservationCardinalityNextSourceOldZeroReverts
    {v : PoolImmutables} {evm : EVM.State} {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hzero : increaseObservationCardinalityNextOldWord evm.accountMap I = ⟨0⟩) :
    ExecBlock (config v)
      { contract := contract v, locals := increaseObservationCardinalityNextStore I } evm
      [ .letDecl "observationCardinalityNextOld" (some uint16)
          (.storage (slot0F "observationCardinalityNext")),
        .letDecl "observationCardinalityNextNew" (some uint16)
          (.var "observationCardinalityNext"),
        .require (gtE (.var "observationCardinalityNextOld") (.intLit 0)),
        Stmt.ite (leE (.var "observationCardinalityNextNew")
            (.var "observationCardinalityNextOld"))
          [ .assign .localVar (varRef "observationCardinalityNextNew")
              (.var "observationCardinalityNextOld") ]
          [ .letDecl "i" (some uint16) (.var "observationCardinalityNextOld"),
            .while (ltE (.var "i") (.var "observationCardinalityNextNew"))
              [ .assign .storage (observationsRawF (.var "i") "blockTimestamp") (.intLit 1),
                .assign .localVar (varRef "i") (addE (.var "i") (.intLit 1)) ] ],
        .assign .storage (slot0F "observationCardinalityNext")
          (.var "observationCardinalityNextNew"),
        .assign .storage (slot0F "unlocked") (.boolLit true) ] .reverted := by
  refine ExecBlock.consNormal
    (ExecStmt.letDecl
      (evalExpr_increaseObservationCardinalityNext_oldStorage (v := v) evm I howner)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl
      (evalExpr_increaseObservationCardinalityNext_param_withOld
        (v := v) evm evm.accountMap I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_increaseObservationCardinalityNext_oldGtZero_false
        (v := v) evm evm.accountMap I hzero))

theorem uniswapV3PoolIncreaseObservationCardinalityNextSourceLockedReverts
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlocked : increaseObservationCardinalityNextUnlockedByte σ I = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (increaseObservationCardinalityNextStore I)
      (increaseobservationcardinalitynextTransition v).body .reverted := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (increaseObservationCardinalityNextStore I)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.storage (slot0F "unlocked")),
        .assign .storage (slot0F "unlocked") (.boolLit false),
        .require (.binary .eq (.env .this) (addrLit v.original)),
        .letDecl "observationCardinalityNextOld" (some uint16)
          (.storage (slot0F "observationCardinalityNext")),
        .letDecl "observationCardinalityNextNew" (some uint16)
          (.var "observationCardinalityNext"),
        .require (gtE (.var "observationCardinalityNextOld") (.intLit 0)),
        Stmt.ite (leE (.var "observationCardinalityNextNew")
            (.var "observationCardinalityNextOld"))
          [ .assign .localVar (varRef "observationCardinalityNextNew")
              (.var "observationCardinalityNextOld") ]
          [ .letDecl "i" (some uint16) (.var "observationCardinalityNextOld"),
            .while (ltE (.var "i") (.var "observationCardinalityNextNew"))
              [ .assign .storage (observationsRawF (.var "i") "blockTimestamp") (.intLit 1),
                .assign .localVar (varRef "i") (addE (.var "i") (.intLit 1)) ] ],
        .assign .storage (slot0F "observationCardinalityNext")
          (.var "observationCardinalityNextNew"),
        .assign .storage (slot0F "unlocked") (.boolLit true) ] .reverted
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
      simp [initState, hwv]))) <|
      ExecBlock.consRevert (ExecStmt.requireFalse (by
        rw [uniswapV3PoolIncreaseObservationCardinalityNextEvalUnlocked]
        exact congrArg EvalResult.ok
          (increaseObservationCardinalityNextUnlockedByte_wordToElem_false hlocked)))

theorem uniswapV3PoolIncreaseObservationCardinalityNextSourceLockPrefixExact
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hunlocked : increaseObservationCardinalityNextUnlockedByte σ I ≠ ⟨0⟩) :
    ExecBlock (config v)
      { contract := contract v, locals := increaseObservationCardinalityNextStore I }
      (initState cA gh bl σ σ₀ g A I)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.storage (slot0F "unlocked")),
        .assign .storage (slot0F "unlocked") (.boolLit false) ]
      (.ok { contract := contract v, locals := increaseObservationCardinalityNextStore I }
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (increaseObservationCardinalityNextLockedSlotWord σ I))) := by
  refine nonpayableRequireAssignStorageBlock
    (cfg := config v)
    (solm := { contract := contract v, locals := increaseObservationCardinalityNextStore I })
    (evm := initState cA gh bl σ σ₀ g A I)
    (evm' := Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
      (increaseObservationCardinalityNextLockedSlotWord σ I))
    (guard := .storage (slot0F "unlocked")) (rhs := .boolLit false)
    (ref := slot0F "unlocked") (value := .bool false)
    (by simp [initState, hwv]) ?_ ?_ ?_
  · rw [uniswapV3PoolIncreaseObservationCardinalityNextEvalUnlocked]
    exact congrArg EvalResult.ok
      (increaseObservationCardinalityNextUnlockedByte_wordToElem_true hunlocked)
  · simp [evalExpr?, pure]
  · apply assignStorageRef_storage_scalar_value
      (er := { base := "slot0", steps := [.field "unlocked"] })
      (ty := .elem .bool)
      (loc := increaseObservationCardinalityNextUnlockedLoc)
    · simp [slot0F, increaseObservationCardinalityNextStore]
    · simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind]
    · simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy, boolSt]
    · funext evm
      simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
        increaseObservationCardinalityNextUnlockedLoc, loc]
    · trivial
    · simpa [initState, increaseObservationCardinalityNextLockedSlotWord, solcSlotWord,
        increaseObservationCardinalityNextUnlockedLoc, slot0UnlockedLoc,
        increaseObservationCardinalityNextUnlockedClearMask, slot0UnlockedClearMask,
        u256_land_comm] using
        storageLocStore_slot0Unlocked_false (initState cA gh bl σ σ₀ g A I)

theorem uniswapV3PoolIncreaseObservationCardinalityNextDecodeOk {v : PoolImmutables}
    {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode
      ((increaseobservationcardinalitynextTransition v).params.map Param.name)
      (transitionSignature (increaseobservationcardinalitynextTransition v)).paramTypes
      I.calldata = some (increaseObservationCardinalityNextStore I) := by
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
    (names := (increaseobservationcardinalitynextTransition v).params.map Param.name)
    (types := (transitionSignature (increaseobservationcardinalitynextTransition v)).paramTypes)
    (cd := I.calldata)]
  · rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
    change (match decodeScalarWordsWithMode? DecodeMode.legacySolc05 [uint16]
        (I.calldata.toList.drop 4) 0 with
      | some values => decodeCalldata.insertValues ["observationCardinalityNext"] values ∅
      | none => none) = some (increaseObservationCardinalityNextStore I)
    rw [decodeScalarWordsWithMode_uint16_ok (bytes := I.calldata.toList.drop 4) htake4]
    simp [decodeCalldata.insertValues, increaseObservationCardinalityNextStore,
      increaseObservationCardinalityNextArgValue, increaseObservationCardinalityNextArgWord]
    rw [hword4]
  · simp [increaseobservationcardinalitynextTransition, transitionSignature,
      isABIScalarWordType, uint16]

theorem uniswapV3PoolIncreaseObservationCardinalityNextDecodeShort {v : PoolImmutables}
    {I : ExecutionEnv} (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode (config v).abiDecodeMode
      ((increaseobservationcardinalitynextTransition v).params.map Param.name)
      (transitionSignature (increaseobservationcardinalitynextTransition v)).paramTypes
      I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [show (config v).abiDecodeMode = DecodeMode.legacySolc05 from rfl]
  rw [decodeCalldataWithMode_legacyScalarWords_eq
    (names := (increaseobservationcardinalitynextTransition v).params.map Param.name)
    (types := (transitionSignature (increaseobservationcardinalitynextTransition v)).paramTypes)
    (cd := I.calldata)]
  · by_cases hsz4 : I.calldata.size < 4
    · rw [if_pos (by rw [htlen]; omega : I.calldata.toList.length < 4)]
    · rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
      change (match decodeScalarWordsWithMode? DecodeMode.legacySolc05 [uint16]
          (I.calldata.toList.drop 4) 0 with
        | some values => decodeCalldata.insertValues ["observationCardinalityNext"] values ∅
        | none => none) = none
      rw [decodeScalarWordsWithMode_uint16_none_short
        (bytes := I.calldata.toList.drop 4) (by rw [List.length_drop, htlen]; omega)]
  · simp [increaseobservationcardinalitynextTransition, transitionSignature,
      isABIScalarWordType, uint16]

theorem uniswapV3PoolDispatch_increaseObservationCardinalityNext {v : PoolImmutables}
    {cd : ByteArray}
    (hsel : (uniswapV3PoolSelBytes 5 == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some (increaseobservationcardinalitynextTransition v) := by
  apply dispatchMsg_eq_some_of_split
    (pre := [burnTransition, collectTransition v, collectprotocolTransition v,
      factoryTransition v, feeTransition v, feegrowthglobal0X128Transition,
      feegrowthglobal1X128Transition, flashTransition v])
    (post := [initializeTransition, liquidityTransition, maxliquiditypertickTransition v,
      mintTransition v, observationsTransition, observeTransition v, positionsTransition,
      protocolfeesTransition, setfeeprotocolTransition v, slot0Transition,
      snapshotcumulativesinsideTransition v, swapTransition v, tickbitmapTransition,
      tickspacingTransition v, ticksTransition, token0Transition v, token1Transition v])
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, burnSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 17) (j := 5)
          (by native_decide) hsel
    · rw [selectorOf, collectSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 10) (j := 5)
          (by native_decide) hsel
    · rw [selectorOf, collectProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 15) (j := 5)
          (by native_decide) hsel
    · rw [selectorOf, factorySelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 19) (j := 5)
          (by native_decide) hsel
    · rw [selectorOf, feeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 22) (j := 5)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal0X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 23) (j := 5)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal1X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 8) (j := 5)
          (by native_decide) hsel
    · rw [selectorOf, flashSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 9) (j := 5)
          (by native_decide) hsel
  · rw [selectorOf, increaseObservationCardinalityNextSelectorBytes v]
    simpa [uniswapV3PoolSelBytes] using hsel

theorem uniswapV3PoolIncreaseObservationCardinalityNextReachEntry {v : PoolImmutables}
    {code : ByteArray} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 5 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨824⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := uniswapV3PoolReachSelector32
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hword : solcSelectorWord I = uniswapV3PoolSelNat 5 := by
    simpa [uniswapV3PoolSelBytes, uniswapV3PoolSelNat] using
      solcSelectorWord_eq_of_beq I hsz 0x32 0x14 0x8f 0x67
        (uniswapV3PoolSelNat 5) (by native_decide) hsel
  have hgt32 : UInt256.gt (armSelNat code ⟨32⟩) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h239 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨239⟩) hpatch h32 hgt32
  have hgt239 : UInt256.gt (armSelNat code ⟨239⟩) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h348 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨348⟩) hpatch h239 hgt239
  have hgt348 : UInt256.gt (armSelNat code ⟨348⟩) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h359 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨359⟩) hpatch h348 hgt348
  have hmiss3 : (uniswapV3PoolSelBytes 3 == I.calldata.extract 0 4) = false :=
    uniswapV3PoolSelectorMissOfHit I (by native_decide) hsel
  have h370 := uniswapV3PoolSelectorArmMissToOf (i := 3) (next := ⟨370⟩)
    hpatch hsz hmiss3 h359
  have hmiss4 : (uniswapV3PoolSelBytes 4 == I.calldata.extract 0 4) = false :=
    uniswapV3PoolSelectorMissOfHit I (by native_decide) hsel
  have h381 := uniswapV3PoolSelectorArmMissToOf (i := 4) (next := ⟨381⟩)
    hpatch hsz hmiss4 h370
  have h824 := uniswapV3PoolSelectorArmHitTo (i := 5) (target := ⟨824⟩)
    hpatch hsz hsel h381
  exact ⟨_, _, h824⟩

end Benchmarks.UniswapV3Pool
