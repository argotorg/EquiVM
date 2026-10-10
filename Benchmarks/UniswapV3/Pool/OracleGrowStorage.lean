import Benchmarks.UniswapV3.Pool.ObservationStorage
import Benchmarks.UniswapV3.Pool.PackedStorage
import Benchmarks.UniswapV3.Pool.SourceExpressions
import Benchmarks.UniswapV3.Pool.Calls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def observationTimestampOne (old : UInt256) : UInt256 :=
  UInt256.lor ⟨1⟩ (UInt256.land (UInt256.lnot (UInt256.ofNat (2 ^ 32 - 1))) old)

def storeObservationTimestampOne (evm : EVM.State) (index : UInt256) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner (observationSlot index)
    (observationTimestampOne (EVM.storageLoad evm evm.executionEnv.codeOwner (observationSlot index)))

theorem storageLocStore_observationTimestampOne (evm : EVM.State) (index : UInt256) :
    storageLocStore evm
      { slot := observationSlot index, offset := 0, size := 4, hbound := by decide,
        type := .int (.uint ⟨32, by decide⟩) } (.int 1) =
      some (storeObservationTimestampOne evm index) := by
  apply storageLocStore_packed_of_toNat evm _ _ ⟨1⟩ _ rfl rfl
  unfold observationTimestampOne
  rw [u256_land_comm, u256_lor_comm]
  have h := packedMaskedWord_toNat (EVM.storageLoad evm evm.executionEnv.codeOwner (observationSlot index))
    (UInt256.lnot (UInt256.ofNat (2 ^ 32 - 1))) ⟨1⟩ 0 32 1 (by decide)
    (by decide +kernel) (by decide) (by decide)
  simpa [Nat.mul_comm] using h

theorem assignObservationTimestampOne (locals imms : Store) (evm : EVM.State)
    (name : Ident) (index : UInt256)
    (hbase : locals.get? "observations" = none)
    (hget : locals.get? name = some (.int (Int.ofNat index.toNat))) (hin : index.toNat < 65535) :
    assignStorageRef? config {contract := contract, locals := locals, immutables := imms} evm .storage
      ⟨"observations", [.aindex (.var name), .field "blockTimestamp"]⟩ (.int 1) =
      .ok ({contract := contract, locals := locals, immutables := imms}, storeObservationTimestampOne evm index) := by
  apply assignStorageRef_storage_scalar_value (ty := .elem (.int (.uint ⟨32, by decide⟩)))
    hbase (evalStorageRef_aindex_field_ok (evalExpr_var_get hget) rfl
      (by rw [observationArrayBounds, if_pos hin])) rfl poolStorageBackend_eq ?_
    (Or.inl ⟨_, rfl⟩) (storageLocStore_observationTimestampOne evm index)
  change some (StorageAddr.leaf
    { slot := (⟨8⟩ : UInt256) + UInt256.ofNat ((keyValueToWord (.int (Int.ofNat index.toNat))).toNat / 1),
      offset := 0, size := 4, hbound := by decide, type := .int (.uint ⟨32, by decide⟩) }) = _
  simp only [keyValueToWord_uint256, Nat.div_one, u256_ofNat_toNat, observationSlot,
    show UInt256.ofNat 8 = (⟨8⟩ : UInt256) from rfl, u256_add_comm]

def oracleGrowState (evm : EVM.State) (start : Nat) : Nat → EVM.State
  | 0 => evm
  | count + 1 => oracleGrowState (storeObservationTimestampOne evm (UInt256.ofNat start)) (start + 1) count

theorem storeObservationTimestampOne_executionEnv (evm : EVM.State) (index : UInt256) :
    (storeObservationTimestampOne evm index).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

theorem oracleGrowState_executionEnv (evm : EVM.State) (start count : Nat) :
    (oracleGrowState evm start count).executionEnv = evm.executionEnv := by
  induction count generalizing evm start with
  | zero => rfl
  | succ count ih => rw [oracleGrowState, ih, storeObservationTimestampOne_executionEnv]

theorem oracleGrowState_originalAccounts (evm : EVM.State) (start count : Nat) :
    (oracleGrowState evm start count).σ₀ = evm.σ₀ := by
  induction count generalizing evm start with
  | zero => rfl
  | succ count ih =>
      rw [oracleGrowState, ih]
      exact storageStore_σ₀ _ _ _ _

theorem SourceState.storeObservationTimestampOne {s0 ee σ evm} (hs : SourceState s0 ee σ evm)
    (index : UInt256) :
    SourceState s0 ee
      (sstoreAccountMap ee.codeOwner σ (observationSlot index)
        (observationTimestampOne (solcSlotWordAt (observationSlot index) σ ee)))
      (storeObservationTimestampOne evm index) := by
  simpa only [Benchmarks.UniswapV3.Pool.storeObservationTimestampOne, hs.env, solcSlotWordAt] using
    hs.readModifyWrite (observationSlot index) observationTimestampOne

end Benchmarks.UniswapV3.Pool
