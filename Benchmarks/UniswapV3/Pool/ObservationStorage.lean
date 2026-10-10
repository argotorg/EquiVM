import Benchmarks.UniswapV3.Pool.ArrayStorage
import Benchmarks.UniswapV3.Pool.SignedWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3.Pool

def observationSlot (index : UInt256) : UInt256 := index + UInt256.ofNat 8

def observationFieldWord (index : UInt256) (offset size : Nat)
    (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (solcSlotWordAt (observationSlot index) σ I)
    (UInt256.ofNat (256 ^ offset))) (UInt256.ofNat (256 ^ size - 1))

def observationTickValue (index : UInt256) (σ : AccountMap) (I : ExecutionEnv) : Int :=
  normalizeInt (.sint ⟨56, by decide⟩) (Int.ofNat
    (UInt256.div (solcSlotWordAt (observationSlot index) σ I) (UInt256.ofNat (2 ^ 32))).toNat)

theorem observationArrayBounds (evm : EVM.State) (index : UInt256) :
    arrayIndexInBounds? config evm contract.storage "observations" [] (.int (Int.ofNat index.toNat)) =
      if index.toNat < 65535 then .ok () else .revert := by
  change (if 0 ≤ Int.ofNat index.toNat ∧ Int.ofNat index.toNat < (65535 : Int)
    then EvalResult.ok () else .revert) = _
  simp only [Int.ofNat_eq_natCast]
  by_cases h : index.toNat < 65535
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem evalObservationField (name : Ident) (ty : ABI.ElemType) (loc : StorageLoc)
    (locals imms : Store) (evm : EVM.State) (index : UInt256)
    (hbase : locals.get? "observations" = none)
    (hindex : locals.get? "arg0" = some (.int (Int.ofNat index.toNat))) (hin : index.toNat < 65535)
    (htype : storageTypeAt? contract.storage
      ⟨"observations", [.aindex (.int (Int.ofNat index.toNat)), .field name]⟩ = some (.elem ty))
    (hloc : storageBackend.locate?
      ⟨"observations", [.aindex (.int (Int.ofNat index.toNat)), .field name]⟩ = some (.leaf loc)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"observations", [.aindex (.var "arg0"), .field name]⟩) =
      .ok (storageLocLoad evm loc) := by
  have hb : arrayIndexInBounds? config evm contract.storage "observations" []
      (.int (Int.ofNat index.toNat)) = .ok () := by rw [observationArrayBounds, if_pos hin]
  have heval : evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.var "arg0") = .ok (.int (Int.ofNat index.toNat)) := by
    simp only [evalExpr?, hindex, EvalResult.ofOption]
  exact evalExpr_storage_scalar hbase
    (evalStorageRef_aindex_field_ok heval rfl hb)
    htype poolStorageBackend_eq hloc

theorem evalObservationFieldOutOfBounds (name : Ident) (locals imms : Store)
    (evm : EVM.State) (index : UInt256)
    (hbase : locals.get? "observations" = none)
    (hindex : locals.get? "arg0" = some (.int (Int.ofNat index.toNat)))
    (hout : ¬ index.toNat < 65535) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"observations", [.aindex (.var "arg0"), .field name]⟩) = .revert := by
  have hb : arrayIndexInBounds? config evm contract.storage "observations" []
      (.int (Int.ofNat index.toNat)) = .revert := by rw [observationArrayBounds, if_neg hout]
  have heval : evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.var "arg0") = .ok (.int (Int.ofNat index.toNat)) := by
    simp only [evalExpr?, hindex, EvalResult.ofOption]
  exact evalExpr_storage_ref_revert hbase
    (evalStorageRef_aindex_field_revert heval rfl hb)

theorem evalObservationBlockTimestamp (locals imms : Store) (evm : EVM.State) (index : UInt256)
    (hbase : locals.get? "observations" = none)
    (hindex : locals.get? "arg0" = some (.int (Int.ofNat index.toNat))) (hin : index.toNat < 65535) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"observations", [.aindex (.var "arg0"), .field "blockTimestamp"]⟩) =
      .ok (.int (Int.ofNat (observationFieldWord index 0 4 evm.accountMap evm.executionEnv).toNat)) := by
  rw [evalObservationField "blockTimestamp" (.int (.uint ⟨32, by decide⟩))
    { slot := observationSlot index, offset := 0, size := 4, hbound := by decide, type := .int (.uint ⟨32, by decide⟩) }
    locals imms evm index hbase hindex hin rfl (by
      change some (StorageAddr.leaf { slot := (⟨8⟩ : UInt256) + UInt256.ofNat ((keyValueToWord (.int (Int.ofNat index.toNat))).toNat / 1), offset := 0, size := 4, hbound := by decide, type := .int (.uint ⟨32, by decide⟩) }) = _
      simp only [keyValueToWord_uint256, Nat.div_one, u256_ofNat_toNat, observationSlot,
        show UInt256.ofNat 8 = (⟨8⟩ : UInt256) from rfl, u256_add_comm])]
  rw [storageLocLoad_uint_offset _ _ _ _ _ rfl (by decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  rfl

theorem evalObservationTickCumulative (locals imms : Store) (evm : EVM.State) (index : UInt256)
    (hbase : locals.get? "observations" = none)
    (hindex : locals.get? "arg0" = some (.int (Int.ofNat index.toNat))) (hin : index.toNat < 65535) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"observations", [.aindex (.var "arg0"), .field "tickCumulative"]⟩) =
      .ok (.int (observationTickValue index evm.accountMap evm.executionEnv)) := by
  rw [evalObservationField "tickCumulative" (.int (.sint ⟨56, by decide⟩))
    { slot := observationSlot index, offset := 4, size := 7, hbound := by decide, type := .int (.sint ⟨56, by decide⟩) }
    locals imms evm index hbase hindex hin rfl (by
      change some (StorageAddr.leaf { slot := (⟨8⟩ : UInt256) + UInt256.ofNat ((keyValueToWord (.int (Int.ofNat index.toNat))).toNat / 1), offset := 4, size := 7, hbound := by decide, type := .int (.sint ⟨56, by decide⟩) }) = _
      simp only [keyValueToWord_uint256, Nat.div_one, u256_ofNat_toNat, observationSlot,
        show UInt256.ofNat 8 = (⟨8⟩ : UInt256) from rfl, u256_add_comm])]
  rw [storageLocLoad_elem_offset _ _ _ _ _ (by decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  simp only [wordToElem, normalizeSint_mask ⟨56, by decide⟩ _
    (UInt256.ofNat (256 ^ (7 : Fin 33).val - 1)) (by native_decide)]
  rfl

theorem evalObservationSecondsPerLiquidityCumulativeX128 (locals imms : Store) (evm : EVM.State) (index : UInt256)
    (hbase : locals.get? "observations" = none)
    (hindex : locals.get? "arg0" = some (.int (Int.ofNat index.toNat))) (hin : index.toNat < 65535) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"observations", [.aindex (.var "arg0"), .field "secondsPerLiquidityCumulativeX128"]⟩) =
      .ok (.int (Int.ofNat (observationFieldWord index 11 20 evm.accountMap evm.executionEnv).toNat)) := by
  rw [evalObservationField "secondsPerLiquidityCumulativeX128" (.int (.uint ⟨160, by decide⟩))
    { slot := observationSlot index, offset := 11, size := 20, hbound := by decide, type := .int (.uint ⟨160, by decide⟩) }
    locals imms evm index hbase hindex hin rfl (by
      change some (StorageAddr.leaf { slot := (⟨8⟩ : UInt256) + UInt256.ofNat ((keyValueToWord (.int (Int.ofNat index.toNat))).toNat / 1), offset := 11, size := 20, hbound := by decide, type := .int (.uint ⟨160, by decide⟩) }) = _
      simp only [keyValueToWord_uint256, Nat.div_one, u256_ofNat_toNat, observationSlot,
        show UInt256.ofNat 8 = (⟨8⟩ : UInt256) from rfl, u256_add_comm])]
  rw [storageLocLoad_uint_offset _ _ _ _ _ rfl (by decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  rfl

theorem evalObservationInitialized (locals imms : Store) (evm : EVM.State) (index : UInt256)
    (hbase : locals.get? "observations" = none)
    (hindex : locals.get? "arg0" = some (.int (Int.ofNat index.toNat))) (hin : index.toNat < 65535) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"observations", [.aindex (.var "arg0"), .field "initialized"]⟩) =
      .ok (wordToElem .bool (observationFieldWord index 31 1 evm.accountMap evm.executionEnv)) := by
  rw [evalObservationField "initialized" (.bool)
    { slot := observationSlot index, offset := 31, size := 1, hbound := by decide, type := .bool }
    locals imms evm index hbase hindex hin rfl (by
      change some (StorageAddr.leaf { slot := (⟨8⟩ : UInt256) + UInt256.ofNat ((keyValueToWord (.int (Int.ofNat index.toNat))).toNat / 1), offset := 31, size := 1, hbound := by decide, type := .bool }) = _
      simp only [keyValueToWord_uint256, Nat.div_one, u256_ofNat_toNat, observationSlot,
        show UInt256.ofNat 8 = (⟨8⟩ : UInt256) from rfl, u256_add_comm])]
  rw [storageLocLoad_elem_offset _ _ _ _ _ (by decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  rfl

end Benchmarks.UniswapV3.Pool
