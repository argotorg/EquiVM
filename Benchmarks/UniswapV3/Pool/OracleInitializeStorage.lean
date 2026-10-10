import Benchmarks.UniswapV3.Pool.PackedPrefix
import Benchmarks.UniswapV3.Pool.OracleObservationStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleInitializeWord (time : UInt256) : UInt256 := UInt256.ofNat (time.toNat + 2 ^ 248)

def oracleInitializeState (evm : EVM.State) (time : UInt256) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ (oracleInitializeWord time)

def oracleInitializeValue (time : UInt256) : Value :=
  .struct "Observation" [("blockTimestamp", .int (Int.ofNat time.toNat)),
    ("tickCumulative", .int 0), ("secondsPerLiquidityCumulativeX128", .int 0),
    ("initialized", .bool true)]

def oracleInitializeTimeLoc : StorageLoc :=
  {slot := ⟨8⟩, offset := 0, size := 4, type := .int (.uint ⟨32, by decide⟩), hbound := by decide}

def oracleInitializeTickLoc : StorageLoc :=
  {slot := ⟨8⟩, offset := 4, size := 7, type := .int (.sint ⟨56, by decide⟩), hbound := by decide}

def oracleInitializeSecondsLoc : StorageLoc :=
  {slot := ⟨8⟩, offset := 11, size := 20, type := .int (.uint ⟨160, by decide⟩), hbound := by decide}

def oracleInitializeFlagLoc : StorageLoc :=
  {slot := ⟨8⟩, offset := 31, size := 1, type := .bool, hbound := by decide}

theorem oracleInitializeWord_toNat (time : UInt256) (ht : time.toNat < 2 ^ 32) :
    (oracleInitializeWord time).toNat = time.toNat + 2 ^ 248 := by
  apply UInt256.toNat_ofNat_of_lt
  change _ < 2 ^ 256
  omega

-- LIBRARY CANDIDATE: a scalar field in an absent account has no effect.
theorem storageLocStore_absent (evm : EVM.State) (loc : StorageLoc) (value : Value)
    (word : UInt256) (hvalue : valueToWord value = some word)
    (hmissing : evm.accountMap.get? evm.executionEnv.codeOwner = none) :
    storageLocStore evm loc value = some evm := by
  unfold storageLocStore
  simp only [hvalue, bind, Option.bind, pure]
  exact congrArg some (storageStore_absent evm evm.executionEnv.codeOwner hmissing loc.slot _)

theorem oracleInitializeFields (evm e0 e1 e2 e3 : EVM.State) (time : UInt256)
    (h0 : storageLocStore evm oracleInitializeTimeLoc (.int (Int.ofNat time.toNat)) = some e0)
    (h1 : storageLocStore e0 oracleInitializeTickLoc (.int 0) = some e1)
    (h2 : storageLocStore e1 oracleInitializeSecondsLoc (.int 0) = some e2)
    (h3 : storageLocStore e2 oracleInitializeFlagLoc (.bool true) = some e3) :
    solidityWriteStorage? storageBackend.locate? evm
      ⟨"observations", [.aindex (.int 0)]⟩ observationStorageType (oracleInitializeValue time) =
      .ok e3 := by
  have hl0 : storageBackend.locate?
      ⟨"observations", [.aindex (.int 0), .field "blockTimestamp"]⟩ =
      some (.leaf oracleInitializeTimeLoc) := rfl
  have hl1 : storageBackend.locate?
      ⟨"observations", [.aindex (.int 0), .field "tickCumulative"]⟩ =
      some (.leaf oracleInitializeTickLoc) := rfl
  have hl2 : storageBackend.locate?
      ⟨"observations", [.aindex (.int 0), .field "secondsPerLiquidityCumulativeX128"]⟩ =
      some (.leaf oracleInitializeSecondsLoc) := rfl
  have hl3 : storageBackend.locate?
      ⟨"observations", [.aindex (.int 0), .field "initialized"]⟩ =
      some (.leaf oracleInitializeFlagLoc) := rfl
  simp only [observationStorageType, oracleInitializeValue, solidityWriteStorage?,
    solidityWriteFields?, ↓reduceIte, List.cons_append, List.nil_append,
    solidityLeafLoc?_of_leaf hl0, solidityLeafLoc?_of_leaf hl1,
    solidityLeafLoc?_of_leaf hl2, solidityLeafLoc?_of_leaf hl3,
    h0, h1, h2, h3, EvalResult.ofOption, bind, EvalResult.bind]

theorem oracleInitializeWrite (evm : EVM.State) (time : UInt256) (ht : time.toNat < 2 ^ 32) :
    solidityWriteStorage? storageBackend.locate? evm
      ⟨"observations", [.aindex (.int 0)]⟩ observationStorageType (oracleInitializeValue time) =
      .ok (oracleInitializeState evm time) := by
  cases ha : evm.accountMap.get? evm.executionEnv.codeOwner with
  | none =>
    have hs0 := storageLocStore_absent evm oracleInitializeTimeLoc (.int (Int.ofNat time.toNat)) time
      (by simp only [valueToWord, wordOfInt_ofNat_toNat, pure]) ha
    have hs1 := storageLocStore_absent evm oracleInitializeTickLoc (.int 0) ⟨0⟩ rfl ha
    have hs2 := storageLocStore_absent evm oracleInitializeSecondsLoc (.int 0) ⟨0⟩ rfl ha
    have hs3 := storageLocStore_absent evm oracleInitializeFlagLoc (.bool true) ⟨1⟩ rfl ha
    rw [oracleInitializeState, storageStore_absent evm _ ha]
    exact oracleInitializeFields evm evm evm evm evm time hs0 hs1 hs2 hs3
  | some acc =>
    let old := EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩
    let e0 := EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ (packedPrefixWord old time 32)
    let e1 := EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ (packedPrefixWord old time 88)
    let e2 := EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ (packedPrefixWord old time 248)
    have ht88 : time.toNat < 2 ^ 88 := lt_of_lt_of_le ht (by decide)
    have ht248 : time.toNat < 2 ^ 248 := lt_of_lt_of_le ht (by decide)
    have h0 : storageLocStore evm oracleInitializeTimeLoc (.int (Int.ofNat time.toNat)) = some e0 := by
      apply storageLocStore_packed_of_toNat evm _ _ time _
        (by simp only [valueToWord, wordOfInt_ofNat_toNat, pure]) rfl
      rw [packedPrefixWord_toNat old time 32 (by decide) ht]
      change _ = old.toNat % 1 + 1 * (time.toNat % 2 ^ 32) + 2 ^ 32 * (old.toNat / 2 ^ 32)
      rw [Nat.mod_one, Nat.mod_eq_of_lt ht]
      omega
    have h1 : storageLocStore e0 oracleInitializeTickLoc (.int 0) = some e1 := by
      have hs : storageLocStore e0 oracleInitializeTickLoc (.int 0) =
          some (EVM.storageStore e0 e0.executionEnv.codeOwner ⟨8⟩ (packedPrefixWord old time 88)) := by
        apply storageLocStore_packed_of_toNat e0 _ _ ⟨0⟩ _ rfl rfl
        rw [packedPrefixWord_toNat old time 88 (by decide) ht88]
        change _ = (EVM.storageLoad e0 e0.executionEnv.codeOwner ⟨8⟩).toNat % 2 ^ 32 +
          2 ^ 32 * 0 + 2 ^ 88 * ((EVM.storageLoad e0 e0.executionEnv.codeOwner ⟨8⟩).toNat / 2 ^ 88)
        dsimp only [e0]
        rw [storageStore_executionEnv, storageLoad_storageStore_same_present evm _ ha,
          packedPrefixWord_mod old time 32 (by decide) ht,
          packedPrefixWord_div old time 32 88 (by decide) (by decide) ht]
        omega
      simpa only [e0, storageStore_executionEnv, storageStore_overwrite] using hs
    have h2 : storageLocStore e1 oracleInitializeSecondsLoc (.int 0) = some e2 := by
      have hs : storageLocStore e1 oracleInitializeSecondsLoc (.int 0) =
          some (EVM.storageStore e1 e1.executionEnv.codeOwner ⟨8⟩ (packedPrefixWord old time 248)) := by
        apply storageLocStore_packed_of_toNat e1 _ _ ⟨0⟩ _ rfl rfl
        rw [packedPrefixWord_toNat old time 248 (by decide) ht248]
        change _ = (EVM.storageLoad e1 e1.executionEnv.codeOwner ⟨8⟩).toNat % 2 ^ 88 +
          2 ^ 88 * 0 + 2 ^ 248 * ((EVM.storageLoad e1 e1.executionEnv.codeOwner ⟨8⟩).toNat / 2 ^ 248)
        dsimp only [e1]
        rw [storageStore_executionEnv, storageLoad_storageStore_same_present evm _ ha,
          packedPrefixWord_mod old time 88 (by decide) ht88,
          packedPrefixWord_div old time 88 248 (by decide) (by decide) ht88]
        omega
      simpa only [e1, storageStore_executionEnv, storageStore_overwrite] using hs
    have h3 : storageLocStore e2 oracleInitializeFlagLoc (.bool true) =
        some (oracleInitializeState evm time) := by
      have hs : storageLocStore e2 oracleInitializeFlagLoc (.bool true) =
          some (EVM.storageStore e2 e2.executionEnv.codeOwner ⟨8⟩ (oracleInitializeWord time)) := by
        apply storageLocStore_packed_of_toNat e2 _ _ ⟨1⟩ _ rfl rfl
        rw [oracleInitializeWord_toNat time ht]
        change _ = (EVM.storageLoad e2 e2.executionEnv.codeOwner ⟨8⟩).toNat % 2 ^ 248 +
          2 ^ 248 * 1 + 2 ^ 256 * ((EVM.storageLoad e2 e2.executionEnv.codeOwner ⟨8⟩).toNat / 2 ^ 256)
        dsimp only [e2]
        rw [storageStore_executionEnv, storageLoad_storageStore_same_present evm _ ha,
          packedPrefixWord_mod old time 248 (by decide) ht248]
        have hbound : (packedPrefixWord old time 248).toNat < 2 ^ 256 :=
          (packedPrefixWord old time 248).val.isLt
        rw [Nat.div_eq_of_lt hbound]
        omega
      simpa only [e2, storageStore_executionEnv, storageStore_overwrite] using hs
    exact oracleInitializeFields evm e0 e1 e2 _ time h0 h1 h2 h3

end Benchmarks.UniswapV3.Pool
