import Benchmarks.Morpho.MetaMorphoV1_1.MarketRevocationMutation

/-! Deleting the three adjacent fields clears exactly one market-configuration slot. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000

def deletedMarketConfigState (evm : State) (id : UInt256) : State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (solcMappingSlot ⟨13⟩ id) ⟨0⟩

theorem deleteStorage_config {frame : Frame} {evm : State} {id : UInt256}
    (hc : frame.contract = contract) (hbase : frame.locals.get? "config" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id)) :
    deleteStorage? config frame evm ⟨"config", [.mindex (.var "id")]⟩ =
      .ok (deletedMarketConfigState evm id) := by
  have hkey : keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)) = id :=
    keyValueToWord_fixedBytes32 id
  have hr := resolveStorageRef?_ok (cfg := config) (evm := evm) (solm := frame)
    (slot := ⟨"config", [.mindex (.var "id")]⟩)
    (er := ⟨"config", [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))]⟩)
    hbase
    (by simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hid,
      wordBytes32Value, valueToKey_bytes32_of_length (word_toBytesBE_length_32 id),
      EvalResult.ofOption, bind, pure, EvalResult.bind])
    (show storageTypeAt? frame.contract.storage
      ⟨"config", [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))]⟩ = some
      (.struct "MarketConfig" [("cap", .elem (.int (.uint ⟨184, by decide⟩))),
        ("enabled", .elem .bool), ("removableAt", .elem (.int (.uint ⟨64, by decide⟩)))]) from
      by rw [hc]; rfl)
  simp only [deleteStorage?, usesTransientStorage_of_resolveStorageRef hr,
    Bool.false_eq_true, ↓reduceIte, hr, bind, EvalResult.bind]
  change solidityClearStorage? _ evm
    ⟨"config", [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))]⟩
    (.struct "MarketConfig" _) = _
  rw [solidityClearStorage?, solidityClearFields?]
  rw [clearStorage_field
    ⟨solcMappingSlot ⟨13⟩ id, 0, 23, by decide, none, .int (.uint ⟨184, by decide⟩)⟩
    (by change some (StorageAddr.leaf
          ⟨solcMappingSlot ⟨13⟩
            (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))),
            0, 23, by decide, none, .int (.uint ⟨184, by decide⟩)⟩) = _
        rw [hkey]) rfl]
  simp only [bind, EvalResult.bind]
  rw [solidityClearFields?]
  rw [clearStorage_field ⟨solcMappingSlot ⟨13⟩ id, 23, 1, by decide, none, .bool⟩
    (by change some (StorageAddr.leaf
          ⟨solcMappingSlot ⟨13⟩
            (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))),
            23, 1, by decide, none, .bool⟩) = _
        rw [hkey]) rfl]
  simp only [bind, EvalResult.bind]
  rw [solidityClearFields?]
  rw [clearStorage_field
    ⟨solcMappingSlot ⟨13⟩ id, 24, 8, by decide, none, .int (.uint ⟨64, by decide⟩)⟩
    (by change some (StorageAddr.leaf
          ⟨solcMappingSlot ⟨13⟩
            (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))),
            24, 8, by decide, none, .int (.uint ⟨64, by decide⟩)⟩) = _
        rw [hkey]) rfl]
  simp only [bind, EvalResult.bind, solidityClearFields?]
  change EvalResult.ok (clearFieldState (clearFieldState
    (clearFieldState evm (solcMappingSlot ⟨13⟩ id) 0 23)
      (solcMappingSlot ⟨13⟩ id) 23 1) (solcMappingSlot ⟨13⟩ id) 24 8) = _
  rw [clearFieldState_append, clearFieldState_append, clearFieldState_all]
  rfl

end Benchmarks.Morpho.MetaMorphoV1_1
