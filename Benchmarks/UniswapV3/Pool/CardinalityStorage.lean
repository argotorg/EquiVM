import Benchmarks.UniswapV3.Pool.Slot0Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def slot0CardinalityNextWord (old value : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 216))))
    (UInt256.mul value (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 216)))

theorem slot0CardinalityNextWord_toNat (old value : UInt256) (hfit : value.toNat < 2 ^ 16) :
    (slot0CardinalityNextWord old value).toNat =
      old.toNat % 2 ^ 216 + value.toNat * 2 ^ 216 + old.toNat / 2 ^ 232 * 2 ^ 232 := by
  have hshift : (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 216)).toNat = 2 ^ 216 := by decide +kernel
  apply packedMaskedWord_toNat old _ _ 216 16 value.toNat (by decide) (by decide +kernel) ?_ hfit
  change (value * UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 216)).toNat = _
  rw [umul_toNat _ _ (by rw [hshift]; change _ < 2 ^ 256; omega), hshift]

def storeSlot0CardinalityNext (evm : EVM.State) (value : UInt256) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (slot0CardinalityNextWord (EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) value)

theorem storageLocStore_slot0CardinalityNext (evm : EVM.State) (value : UInt256)
    (hfit : value.toNat < 2 ^ 16) :
    storageLocStore evm
      { slot := ⟨0⟩, offset := 27, size := 2, type := .int (.uint ⟨16, by decide⟩), hbound := by decide }
      (.int (Int.ofNat value.toNat)) = some (storeSlot0CardinalityNext evm value) := by
  apply storageLocStore_packed_of_toNat evm _ _ value _
    (by simp only [valueToWord, wordOfInt_ofNat_toNat, pure]) rfl
  rw [slot0CardinalityNextWord_toNat _ _ hfit]
  change _ = (EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 216 +
    2 ^ 216 * (value.toNat % 2 ^ 16) +
    2 ^ 232 * ((EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 232)
  rw [Nat.mod_eq_of_lt hfit]
  simp only [Nat.mul_comm]

theorem assignSlot0CardinalityNext (evm : EVM.State) (locals imms : Store) (value : UInt256)
    (hbase : locals.get? "slot0" = none) (hfit : value.toNat < 2 ^ 16) :
    assignStorageRef? config {contract := contract, locals := locals, immutables := imms} evm .storage
      ⟨"slot0", [.field "observationCardinalityNext"]⟩ (.int (Int.ofNat value.toNat)) =
      .ok ({contract := contract, locals := locals, immutables := imms}, storeSlot0CardinalityNext evm value) := by
  apply assignStorageRef_storage_scalar_value (ty := .elem (.int (.uint ⟨16, by decide⟩)))
    (er := ⟨"slot0", [.field "observationCardinalityNext"]⟩)
    (loc := {slot := ⟨0⟩, offset := 27, size := 2, type := .int (.uint ⟨16, by decide⟩), hbound := by decide})
    hbase (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, EvalResult.bind, bind, pure])
    rfl poolStorageBackend_eq rfl (Or.inl ⟨_, rfl⟩)
  exact storageLocStore_slot0CardinalityNext evm value hfit

theorem storeSlot0CardinalityNext_accountMap (evm : EVM.State) (value : UInt256) :
    (storeSlot0CardinalityNext evm value).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨0⟩
        (slot0CardinalityNextWord (solcSlotWordAt ⟨0⟩ evm.accountMap evm.executionEnv) value) := by
  rw [storeSlot0CardinalityNext, storageStore_accountMap,
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv ⟨0⟩ rfl]

theorem storeSlot0CardinalityNext_executionEnv (evm : EVM.State) (value : UInt256) :
    (storeSlot0CardinalityNext evm value).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

theorem storeSlot0CardinalityNext_originalAccounts (evm : EVM.State) (value : UInt256) :
    (storeSlot0CardinalityNext evm value).σ₀ = evm.σ₀ := storageStore_σ₀ _ _ _ _

theorem slot0CardinalityNext_lt (σ : AccountMap) (I : ExecutionEnv) :
    (slot0FieldWord 27 2 σ I).toNat < 2 ^ 16 :=
  u256LandMaskToNatLtOfToNat _ _ (by decide)

theorem slot0CardinalityNext_evm (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.land (UInt256.ofNat 65535)
      (UInt256.div (solcSlotWordAt ⟨0⟩ σ I)
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 216))) = slot0FieldWord 27 2 σ I := by
  rw [slot0FieldWord, u256_land_comm]
  rw [show UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 216) =
    UInt256.ofNat (256 ^ 27) by decide +kernel]
  rfl

end Benchmarks.UniswapV3.Pool
