import Benchmarks.Morpho.MetaMorphoV1_1.PackedDeletion
import Benchmarks.Morpho.MetaMorphoV1_1.MappingStructs

/-! Packed mapping deletes for cap and market-removal revocations. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

theorem clearFieldWord_high192 (old : UInt256) :
    clearFieldWord old 24 8 = UInt256.land (UInt256.ofNat (2 ^ 192 - 1)) old := by
  have hdiv : old.toNat / 256 ^ (24 + 8) = 0 := Nat.div_eq_of_lt old.val.isLt
  have hp : 256 ^ 24 = (2 : Nat) ^ 192 := by decide
  apply u256_inj
  rw [clearFieldWord, hdiv, Nat.zero_mul, Nat.add_zero,
    UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (by decide)),
    hp, u256_land_comm, u256_land_toNat, ulit_toNat' _ (by decide), nat_land_mask_eq_mod]
  exact (Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (by decide))).symm

theorem deleteStorage_pendingCap (evm : EVM.State) (locals imms : Store)
    (bs : List UInt8) (w : UInt256) (hlen : bs.length = 32)
    (hbase : locals.get? "pendingCap" = none)
    (hget : locals.get? "id" = some (.fixedBytes abiBytes32Width bs))
    (hkey : keyValueToWord (.fixedBytes abiBytes32Width bs) = w) :
    deleteStorage? config { contract := contract, locals := locals, immutables := imms }
      evm ⟨"pendingCap", [.mindex (.var "id")]⟩ =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (solcMappingSlot ⟨16⟩ w)
        ⟨0⟩) := by
  have hr := resolveStorageRef?_ok (cfg := config) (evm := evm)
    (solm := { contract := contract, locals := locals, immutables := imms })
    (slot := ⟨"pendingCap", [.mindex (.var "id")]⟩)
    (er := ⟨"pendingCap", [.mindex (.fixedBytes abiBytes32Width bs)]⟩) hbase
    (by simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hget,
      valueToKey_bytes32_of_length hlen, EvalResult.ofOption, bind, pure, EvalResult.bind])
    (show storageTypeAt? contract.storage
      ⟨"pendingCap", [.mindex (.fixedBytes abiBytes32Width bs)]⟩ = some
      (.struct "PendingUint192" [("value", .elem (.int (.uint ⟨192, by decide⟩))),
        ("validAt", .elem (.int (.uint ⟨64, by decide⟩)))]) from rfl)
  simp only [deleteStorage?, usesTransientStorage_of_resolveStorageRef hr,
    Bool.false_eq_true, ↓reduceIte, hr, bind, EvalResult.bind]
  change solidityClearStorage? _ evm
    ⟨"pendingCap", [.mindex (.fixedBytes abiBytes32Width bs)]⟩ (.struct "PendingUint192" _) = _
  rw [solidityClearStorage?, solidityClearFields?]
  rw [clearStorage_field
    ⟨solcMappingSlot ⟨16⟩ w, 0, 24, by decide, none, .int (.uint ⟨192, by decide⟩)⟩
    (by change some (StorageAddr.leaf
          ⟨solcMappingSlot ⟨16⟩ (keyValueToWord (.fixedBytes abiBytes32Width bs)),
            0, 24, by decide, none, .int (.uint ⟨192, by decide⟩)⟩) = _
        rw [hkey]) rfl]
  simp only [bind, EvalResult.bind]
  rw [solidityClearFields?]
  rw [clearStorage_field
    ⟨solcMappingSlot ⟨16⟩ w, 24, 8, by decide, none, .int (.uint ⟨64, by decide⟩)⟩
    (by change some (StorageAddr.leaf
          ⟨solcMappingSlot ⟨16⟩ (keyValueToWord (.fixedBytes abiBytes32Width bs)),
            24, 8, by decide, none, .int (.uint ⟨64, by decide⟩)⟩) = _
        rw [hkey]) rfl]
  simp only [bind, EvalResult.bind, solidityClearFields?]
  change EvalResult.ok (clearFieldState
    (clearFieldState evm (solcMappingSlot ⟨16⟩ w) 0 24) (solcMappingSlot ⟨16⟩ w) 24 8) = _
  rw [clearFieldState_append, clearFieldState_all]

theorem deleteStorage_configRemovableAt (evm : EVM.State) (locals imms : Store)
    (bs : List UInt8) (w : UInt256) (hlen : bs.length = 32)
    (hbase : locals.get? "config" = none)
    (hget : locals.get? "id" = some (.fixedBytes abiBytes32Width bs))
    (hkey : keyValueToWord (.fixedBytes abiBytes32Width bs) = w) :
    deleteStorage? config { contract := contract, locals := locals, immutables := imms }
      evm ⟨"config", [.mindex (.var "id"), .field "removableAt"]⟩ =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (solcMappingSlot ⟨13⟩ w)
        (UInt256.land (UInt256.ofNat (2 ^ 192 - 1))
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨13⟩ w)))) := by
  have hr := resolveStorageRef?_ok (cfg := config) (evm := evm)
    (solm := { contract := contract, locals := locals, immutables := imms })
    (slot := ⟨"config", [.mindex (.var "id"), .field "removableAt"]⟩)
    (er := ⟨"config", [.mindex (.fixedBytes abiBytes32Width bs), .field "removableAt"]⟩)
    hbase (evalStorageRef_bytes32Field "config" "id" "removableAt" bs hlen hget)
    (show storageTypeAt? contract.storage
      ⟨"config", [.mindex (.fixedBytes abiBytes32Width bs), .field "removableAt"]⟩ =
      some (.elem (.int (.uint ⟨64, by decide⟩))) from rfl)
  simp only [deleteStorage?, usesTransientStorage_of_resolveStorageRef hr,
    Bool.false_eq_true, ↓reduceIte, hr, bind, EvalResult.bind]
  change solidityClearStorage? _ evm
    ⟨"config", [.mindex (.fixedBytes abiBytes32Width bs), .field "removableAt"]⟩
    (.elem (.int (.uint ⟨64, by decide⟩))) = _
  rw [clearStorage_field
    ⟨solcMappingSlot ⟨13⟩ w, 24, 8, by decide, none, .int (.uint ⟨64, by decide⟩)⟩
    (by change some (StorageAddr.leaf
          ⟨solcMappingSlot ⟨13⟩ (keyValueToWord (.fixedBytes abiBytes32Width bs)),
            24, 8, by decide, none, .int (.uint ⟨64, by decide⟩)⟩) = _
        rw [hkey]) rfl]
  change EvalResult.ok (clearFieldState evm (solcMappingSlot ⟨13⟩ w) 24 8) = _
  rw [clearFieldState, clearFieldWord_high192]

end Benchmarks.Morpho.MetaMorphoV1_1
