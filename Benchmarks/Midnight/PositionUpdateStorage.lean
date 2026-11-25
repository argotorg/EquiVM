import Benchmarks.Midnight.Uint128HighStore
import Benchmarks.Midnight.PositionViewSourceBase

/-! Ordered position writes, retaining reads after earlier writes without slot-disjointness assumptions. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def storeLow128 (evm : EVM.State) (slot value : UInt256) : EVM.State :=
  Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot
    (setUint128LowWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) value)

def storeHigh128 (evm : EVM.State) (slot value : UInt256) : EVM.State :=
  Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot
    (setUint128HighWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) value)

def storeLow128Accounts (σ : AccountMap) (I : ExecutionEnv) (slot value : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner σ slot (setUint128LowWord (solcSlotWordAt slot σ I) value)

def storeHigh128Accounts (σ : AccountMap) (I : ExecutionEnv) (slot value : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner σ slot (setUint128HighWord (solcSlotWordAt slot σ I) value)

@[simp] theorem storeLow128_env (evm : EVM.State) (slot value : UInt256) :
    (storeLow128 evm slot value).executionEnv = evm.executionEnv := storageStore_executionEnv ..

@[simp] theorem storeHigh128_env (evm : EVM.State) (slot value : UInt256) :
    (storeHigh128 evm slot value).executionEnv = evm.executionEnv := storageStore_executionEnv ..

theorem storeHigh128_low (evm : EVM.State) (slot value : UInt256) :
    storeHigh128 evm slot (low128 value) = storeHigh128 evm slot value := by
  have hs : UInt256.shiftLeft (low128 value) (UInt256.ofNat 128) =
      UInt256.shiftLeft value (UInt256.ofNat 128) := by
    apply u256_inj
    simp only [shiftLeft128_toNat, low128_toNat, Nat.mod_mod]
  simp only [storeHigh128, setUint128HighWord, hs]

@[simp] theorem storeLow128_accounts (evm : EVM.State) (slot value : UInt256) :
    (storeLow128 evm slot value).accountMap =
      storeLow128Accounts evm.accountMap evm.executionEnv slot value := by
  rw [storeLow128, storageStore_accountMap,
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv slot rfl]
  rfl

@[simp] theorem storeHigh128_accounts (evm : EVM.State) (slot value : UInt256) :
    (storeHigh128 evm slot value).accountMap =
      storeHigh128Accounts evm.accountMap evm.executionEnv slot value := by
  rw [storeHigh128, storageStore_accountMap,
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv slot rfl]
  rfl

def positionFieldStore (evm : EVM.State) (id user : UInt256) (i : Fin 4) (value : UInt256) : EVM.State :=
  if i.val % 2 = 0 then storeLow128 evm (positionFieldSlot id user i) value
  else storeHigh128 evm (positionFieldSlot id user i) value

theorem positionField_store (evm : EVM.State) (id user : UInt256) (i : Fin 4) (value : UInt256) :
    storageLocStore evm (positionFieldLoc id user i) (.int value.toNat) =
      some (positionFieldStore evm id user i value) := by
  rcases i with ⟨i, hi⟩
  interval_cases i <;> dsimp only [positionFieldLoc, positionFieldStore, positionFieldSlot] <;>
    norm_num only
  · exact storageLocStore_uint128_low_word ..
  · exact storageLocStore_uint128_high_word ..
  · exact storageLocStore_uint128_low_word ..
  · exact storageLocStore_uint128_high_word ..

theorem assignPositionAliasField {frame : Frame} {evm : EVM.State} {id user : UInt256}
    (i : Fin 4) (value : UInt256) (hcanon : user.toNat < EVM.addressModulus)
    (hget : frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType)) :
    assignStorageRef? config frame evm .storage { base := "_position", steps :=
      [.field (positionFieldName i)] } (.int value.toNat) =
      .ok (frame, positionFieldStore evm id user i value) :=
  assignStorageAliasField hget (positionField_type i) rfl
    (positionField_layout id user i hcanon) (positionField_store evm id user i value)

def positionUpdateState (evm : EVM.State) (id user credit pending : UInt256) : EVM.State :=
  let evm1 := storeLow128 evm (positionSlot id user) credit
  let evm2 := storeLow128 evm1 (positionSlot id user + ⟨1⟩) (marketLossWord evm1 id)
  let evm3 := storeHigh128 evm2 (positionSlot id user) pending
  storeHigh128 evm3 (positionSlot id user + ⟨1⟩) (UInt256.ofNat evm.executionEnv.header.timestamp)

def positionUpdateAccounts (σ : AccountMap) (I : ExecutionEnv) (id user credit pending : UInt256) : AccountMap :=
  let σ1 := storeLow128Accounts σ I (positionSlot id user) credit
  let σ2 := storeLow128Accounts σ1 I (positionSlot id user + ⟨1⟩)
    (UInt256.shiftRight (solcSlotWordAt (solcMappingSlot ⟨1⟩ id) σ1 I) (UInt256.ofNat 128))
  let σ3 := storeHigh128Accounts σ2 I (positionSlot id user) pending
  storeHigh128Accounts σ3 I (positionSlot id user + ⟨1⟩) (UInt256.ofNat I.header.timestamp)

@[simp] theorem positionUpdateState_env (evm : EVM.State) (id user credit pending : UInt256) :
    (positionUpdateState evm id user credit pending).executionEnv = evm.executionEnv := by
  simp [positionUpdateState]

theorem positionUpdateState_accounts (evm : EVM.State) (id user credit pending : UInt256) :
    (positionUpdateState evm id user credit pending).accountMap =
      positionUpdateAccounts evm.accountMap evm.executionEnv id user credit pending := by
  have hl := storageLoad_codeOwner_eq_solcSlotWordAt
    (storeLow128 evm (positionSlot id user) credit) evm.executionEnv (solcMappingSlot ⟨1⟩ id) (by simp)
  simp only [storeLow128_env, storeLow128_accounts] at hl
  simp only [positionUpdateState, storeHigh128_accounts, storeLow128_accounts,
    storeLow128_env, storeHigh128_env, positionUpdateAccounts, marketLossWord, hl]

def marketFeeCreditWord (evm : EVM.State) (id : UInt256) : UInt256 :=
  UInt256.shiftRight (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
    (solcMappingSlot ⟨1⟩ id + ⟨1⟩)) (UInt256.ofNat 128)

def positionUpdateFeeState (evm : EVM.State) (id fee : UInt256) : EVM.State :=
  storeHigh128 evm (solcMappingSlot ⟨1⟩ id + ⟨1⟩) (marketFeeCreditWord evm id + fee)

end Benchmarks.Midnight
