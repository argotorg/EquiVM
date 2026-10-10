import Benchmarks.UniswapV3.Pool.PackedStorage
import Benchmarks.UniswapV3.Pool.SignedWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3.Pool

def slot0FieldWord (offset size : Nat) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (solcSlotWordAt ⟨0⟩ σ I) (UInt256.ofNat (256 ^ offset)))
    (UInt256.ofNat (256 ^ size - 1))

theorem evalSlot0UIntField (name : Ident) (offset : Fin 32) (size : Fin 33)
    (width : ABI.BitWidth) (locals imms : Store) (evm : EVM.State)
    (hbase : locals.get? "slot0" = none)
    (htype : storageTypeAt? contract.storage ⟨"slot0", [.field name]⟩ =
      some (.elem (.int (.uint width))))
    (hbound : offset.val + size.val - 1 < 32)
    (hloc : storageBackend.locate? ⟨"slot0", [.field name]⟩ = some (.leaf
      { slot := ⟨0⟩, offset := offset, size := size, hbound := hbound, type := .int (.uint width) }))
    (hwidth : width.val = 8 * size.val) (hoff : 8 * offset.val < 256) (hsize : 8 * size.val ≤ 256) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"slot0", [.field name]⟩) =
      .ok (.int (Int.ofNat (slot0FieldWord offset.val size.val evm.accountMap evm.executionEnv).toNat)) := by
  apply evalExpr_storage_scalar_value hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, EvalResult.bind, bind, pure])
    htype poolStorageBackend_eq hloc
  rw [storageLocLoad_uint_offset _ _ _ _ _ hwidth hoff hsize,
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv ⟨0⟩ rfl]
  rfl

def slot0TickValue (σ : AccountMap) (I : ExecutionEnv) : Int :=
  normalizeInt (.sint ⟨24, by decide⟩)
    (Int.ofNat (UInt256.div (solcSlotWordAt ⟨0⟩ σ I) (UInt256.ofNat (2 ^ 160))).toNat)

theorem evalSlot0Tick (locals imms : Store) (evm : EVM.State)
    (hbase : locals.get? "slot0" = none) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"slot0", [.field "tick"]⟩) =
      .ok (.int (slot0TickValue evm.accountMap evm.executionEnv)) := by
  apply evalExpr_storage_scalar_value (t := .int (.sint ⟨24, by decide⟩))
    (er := ⟨"slot0", [.field "tick"]⟩)
    (loc := { slot := ⟨0⟩, offset := 20, size := 3,
              type := .int (.sint ⟨24, by decide⟩), hbound := by decide }) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, EvalResult.bind, bind, pure])
    (by dsimp only; decide +kernel) poolStorageBackend_eq rfl
  rw [storageLocLoad_elem_offset _ _ _ _ _ (by decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv ⟨0⟩ rfl]
  simp only [wordToElem, normalizeSint_mask ⟨24, by decide⟩ _
    (UInt256.ofNat (256 ^ (3 : Fin 33).val - 1)) (by native_decide)]
  rfl

theorem evalSlot0Unlocked (locals imms : Store) (evm : EVM.State)
    (hbase : locals.get? "slot0" = none) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"slot0", [.field "unlocked"]⟩) =
      .ok (wordToElem .bool (slot0FieldWord 30 1 evm.accountMap evm.executionEnv)) := by
  apply evalExpr_storage_scalar_value (t := .bool)
    (er := ⟨"slot0", [.field "unlocked"]⟩)
    (loc := { slot := ⟨0⟩, offset := 30, size := 1, type := .bool, hbound := by decide }) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, EvalResult.bind, bind, pure])
    (by dsimp only; decide +kernel) poolStorageBackend_eq rfl
  rw [storageLocLoad_elem_offset _ _ _ _ _ (by decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv ⟨0⟩ rfl]
  rfl

theorem evalSlot0SqrtPriceX96 (locals imms : Store) (evm : EVM.State)
    (hbase : locals.get? "slot0" = none) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"slot0", [.field "sqrtPriceX96"]⟩) =
      .ok (.int (Int.ofNat (slot0FieldWord 0 20 evm.accountMap evm.executionEnv).toNat)) := by
  exact evalSlot0UIntField "sqrtPriceX96" 0 20 ⟨160, by decide⟩ locals imms evm hbase
    (by decide +kernel) (by decide) rfl rfl (by decide) (by decide)

theorem evalSlot0ObservationIndex (locals imms : Store) (evm : EVM.State)
    (hbase : locals.get? "slot0" = none) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"slot0", [.field "observationIndex"]⟩) =
      .ok (.int (Int.ofNat (slot0FieldWord 23 2 evm.accountMap evm.executionEnv).toNat)) := by
  exact evalSlot0UIntField "observationIndex" 23 2 ⟨16, by decide⟩ locals imms evm hbase
    (by decide +kernel) (by decide) rfl rfl (by decide) (by decide)

theorem evalSlot0ObservationCardinality (locals imms : Store) (evm : EVM.State)
    (hbase : locals.get? "slot0" = none) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"slot0", [.field "observationCardinality"]⟩) =
      .ok (.int (Int.ofNat (slot0FieldWord 25 2 evm.accountMap evm.executionEnv).toNat)) := by
  exact evalSlot0UIntField "observationCardinality" 25 2 ⟨16, by decide⟩ locals imms evm hbase
    (by decide +kernel) (by decide) rfl rfl (by decide) (by decide)

theorem evalSlot0ObservationCardinalityNext (locals imms : Store) (evm : EVM.State)
    (hbase : locals.get? "slot0" = none) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"slot0", [.field "observationCardinalityNext"]⟩) =
      .ok (.int (Int.ofNat (slot0FieldWord 27 2 evm.accountMap evm.executionEnv).toNat)) := by
  exact evalSlot0UIntField "observationCardinalityNext" 27 2 ⟨16, by decide⟩ locals imms evm hbase
    (by decide +kernel) (by decide) rfl rfl (by decide) (by decide)

theorem evalSlot0FeeProtocol (locals imms : Store) (evm : EVM.State)
    (hbase : locals.get? "slot0" = none) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"slot0", [.field "feeProtocol"]⟩) =
      .ok (.int (Int.ofNat (slot0FieldWord 29 1 evm.accountMap evm.executionEnv).toNat)) := by
  exact evalSlot0UIntField "feeProtocol" 29 1 ⟨8, by decide⟩ locals imms evm hbase
    (by decide +kernel) (by decide) rfl rfl (by decide) (by decide)

def slot0UnlockedWord (old : UInt256) (value : Bool) : UInt256 :=
  UInt256.lor
    (UInt256.land old (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) ⟨240⟩)))
    (UInt256.shiftLeft value.toUInt256 ⟨240⟩)

theorem slot0UnlockedWord_toNat (old : UInt256) (value : Bool) :
    (slot0UnlockedWord old value).toNat =
      old.toNat % 2 ^ 240 + value.toNat * 2 ^ 240 + old.toNat / 2 ^ 248 * 2 ^ 248 := by
  exact packedMaskedWord_toNat old _ _ 240 8 value.toNat (by decide)
    (by native_decide) (by cases value <;> decide) (by cases value <;> decide)

theorem slot0UnlockedWord_false (old : UInt256) :
    slot0UnlockedWord old false =
      UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) ⟨240⟩)) old := by
  simp only [slot0UnlockedWord, Bool.toUInt256_false]
  rw [show UInt256.shiftLeft (UInt256.ofNat 0) ⟨240⟩ = ⟨0⟩ by decide, u256_lor_zero,
    u256_land_comm]

def storeSlot0Unlocked (evm : EVM.State) (value : Bool) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (slot0UnlockedWord (EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) value)

theorem storageLocStore_slot0Unlocked (evm : EVM.State) (value : Bool) :
    storageLocStore evm
      { slot := ⟨0⟩, offset := 30, size := 1, type := .bool, hbound := by decide }
      (.bool value) = some (storeSlot0Unlocked evm value) := by
  apply storageLocStore_packed_of_toNat evm _ _ value.toUInt256 _ rfl rfl
  rw [slot0UnlockedWord_toNat]
  cases value <;> simp [Bool.toUInt256, Bool.toNat, Nat.mul_comm] <;> decide +kernel

theorem assignSlot0Unlocked (evm : EVM.State) (locals imms : Store) (value : Bool)
    (hbase : locals.get? "slot0" = none) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms }
      evm .storage ⟨"slot0", [.field "unlocked"]⟩ (.bool value) =
      .ok ({ contract := contract, locals := locals, immutables := imms },
        storeSlot0Unlocked evm value) := by
  apply assignStorageRef_storage_scalar_value (ty := .elem .bool)
    (er := ⟨"slot0", [.field "unlocked"]⟩)
    (loc := { slot := ⟨0⟩, offset := 30, size := 1, type := .bool, hbound := by decide }) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, EvalResult.bind, bind, pure])
    (by dsimp only; decide +kernel) poolStorageBackend_eq rfl (Or.inl ⟨.bool, rfl⟩)
  exact storageLocStore_slot0Unlocked evm value

theorem slot0FieldWord_unlocked_evm (σ : AccountMap) (I : ExecutionEnv) :
    slot0FieldWord 30 1 σ I =
      UInt256.land (UInt256.ofNat 255)
        (UInt256.div (solcSlotWordAt ⟨0⟩ σ I)
          (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240))) := by
  rw [slot0FieldWord, u256_land_comm]
  rw [show UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240) =
    UInt256.ofNat (256 ^ 30) by native_decide]
  rfl

theorem storeSlot0Unlocked_accountMap (evm : EVM.State) (value : Bool) :
    (storeSlot0Unlocked evm value).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨0⟩
        (slot0UnlockedWord (solcSlotWordAt ⟨0⟩ evm.accountMap evm.executionEnv) value) := by
  rw [storeSlot0Unlocked, storageStore_accountMap,
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv ⟨0⟩ rfl]

theorem storeSlot0Unlocked_executionEnv (evm : EVM.State) (value : Bool) :
    (storeSlot0Unlocked evm value).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

theorem storeSlot0Unlocked_originalAccounts (evm : EVM.State) (value : Bool) :
    (storeSlot0Unlocked evm value).σ₀ = evm.σ₀ := storageStore_σ₀ _ _ _ _

def slot0FeeProtocolWord (old value : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land old
      (UInt256.ofNat 115790329291997763829805189145943027211779609632852660590886017564236060819455))
    (UInt256.mul (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 232))
      (UInt256.land (UInt256.ofNat 255) value))

theorem slot0FeeProtocolWord_toNat (old value : UInt256) :
    (slot0FeeProtocolWord old value).toNat =
      old.toNat % 2 ^ 232 + (value.toNat % 256) * 2 ^ 232 +
        old.toNat / 2 ^ 240 * 2 ^ 240 := by
  have hfield : (UInt256.land (UInt256.ofNat 255) value).toNat = value.toNat % 256 := by
    rw [uland_toNat]
    change Nat.land (2 ^ 8 - 1) value.toNat = _
    rw [nat_land_comm, nat_land_mask_eq_mod]
    rfl
  have hsmall : value.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  have hshift : (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 232)).toNat = 2 ^ 232 := by
    native_decide
  apply packedMaskedWord_toNat old _ _ 232 8 (value.toNat % 256) (by decide)
    (by native_decide) _ hsmall
  change ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 232)) *
    UInt256.land (UInt256.ofNat 255) value).toNat = _
  rw [umul_toNat _ _ (by rw [hshift, hfield]; change _ < 2 ^ 256; omega), hshift, hfield,
    Nat.mul_comm]

def storeSlot0FeeProtocol (evm : EVM.State) (value : UInt256) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (slot0FeeProtocolWord (EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) value)

theorem storageLocStore_slot0FeeProtocol (evm : EVM.State) (value : UInt256) :
    storageLocStore evm
      { slot := ⟨0⟩, offset := 29, size := 1, type := .int (.uint ⟨8, by decide⟩),
        hbound := by decide }
      (.int (Int.ofNat value.toNat)) = some (storeSlot0FeeProtocol evm value) := by
  apply storageLocStore_packed_of_toNat evm _ _ value _
    (by simp only [valueToWord, wordOfInt_ofNat_toNat, pure]) rfl
  rw [slot0FeeProtocolWord_toNat]
  simp [Nat.mul_comm]

theorem assignSlot0FeeProtocol (evm : EVM.State) (locals imms : Store) (value : UInt256)
    (hbase : locals.get? "slot0" = none) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms }
      evm .storage ⟨"slot0", [.field "feeProtocol"]⟩ (.int (Int.ofNat value.toNat)) =
      .ok ({ contract := contract, locals := locals, immutables := imms },
        storeSlot0FeeProtocol evm value) := by
  apply assignStorageRef_storage_scalar_value (ty := .elem (.int (.uint ⟨8, by decide⟩)))
    (er := ⟨"slot0", [.field "feeProtocol"]⟩)
    (loc := { slot := ⟨0⟩, offset := 29, size := 1,
              type := .int (.uint ⟨8, by decide⟩), hbound := by decide }) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, EvalResult.bind, bind, pure])
    (by dsimp only; decide +kernel) poolStorageBackend_eq rfl (Or.inl ⟨_, rfl⟩)
  exact storageLocStore_slot0FeeProtocol evm value

theorem slot0UnlockedWord_true (old : UInt256) :
    slot0UnlockedWord old true =
      UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240))
        (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 240))) old) := by
  simp only [slot0UnlockedWord, Bool.toUInt256_true]
  rw [u256_lor_comm, u256_land_comm]
  rfl

theorem storeSlot0FeeProtocol_accountMap (evm : EVM.State) (value : UInt256) :
    (storeSlot0FeeProtocol evm value).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨0⟩
        (slot0FeeProtocolWord (solcSlotWordAt ⟨0⟩ evm.accountMap evm.executionEnv) value) := by
  rw [storeSlot0FeeProtocol, storageStore_accountMap,
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv ⟨0⟩ rfl]

theorem storeSlot0FeeProtocol_executionEnv (evm : EVM.State) (value : UInt256) :
    (storeSlot0FeeProtocol evm value).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

end Benchmarks.UniswapV3.Pool
