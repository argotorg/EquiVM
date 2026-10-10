import Benchmarks.UniswapV4PoolManager.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def protocolFeesSlot (currency : AccountAddress) : UInt256 := mappingSlotWord (accountWord currency) ⟨1⟩
def protocolFeesWord (evm : EVM.State) (currency : AccountAddress) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (protocolFeesSlot currency)
def protocolFeesPost (evm : EVM.State) (currency : AccountAddress) (value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (protocolFeesSlot currency) value

theorem protocolFeesLoc (currency : AccountAddress) :
    config.storageBackend.locate? {base := "protocolFeesAccrued", steps := [.mindex (.address currency)]} =
      some (.leaf (uint256Loc (protocolFeesSlot currency))) := by
  have h := protocolFeesAccrued_loc (accountWord currency) (accountWord_canonical currency)
  have hc : AccountAddress.ofNat (accountWord currency).toNat = currency :=
    ((accountWord_eq_iff currency _ (accountWord_canonical currency)).2 rfl).symm
  rw [hc] at h
  exact h

theorem protocolFeesRead {f : Frame} {evm : EVM.State} {e : Expr} {currency : AccountAddress}
    (hf : f.contract = contract) (hb : f.locals.get? "protocolFeesAccrued" = none)
    (he : evalExpr? config f evm e = .ok (.address currency)) :
    evalExpr? config f evm (.storage {base := "protocolFeesAccrued", steps := [.mindex e]}) =
      .ok (.int (Int.ofNat (protocolFeesWord evm currency).toNat)) := by
  apply evalExpr_storage_scalar_value hb (evalMappingRef (base := "protocolFeesAccrued") he rfl)
    (hbackend := rfl) (hloc := protocolFeesLoc currency)
  · rw [hf]; exact protocolFeesAccrued_type currency
  · exact storageLocLoad_uint256 _ _

theorem protocolFeesWrite {f : Frame} {evm : EVM.State} {e : Expr} {currency : AccountAddress}
    (value : UInt256) (hf : f.contract = contract) (hb : f.locals.get? "protocolFeesAccrued" = none)
    (he : evalExpr? config f evm e = .ok (.address currency)) :
    assignStorageRef? config f evm .storage {base := "protocolFeesAccrued", steps := [.mindex e]}
      (.int (Int.ofNat value.toNat)) = .ok (f, protocolFeesPost evm currency value) := by
  apply assignStorageRef_storage_scalar (slot := {base := "protocolFeesAccrued", steps := [.mindex e]})
    hb (evalMappingRef (base := "protocolFeesAccrued") he rfl)
    (hbackend := rfl) (hloc := protocolFeesLoc currency) (hleaf := Or.inl ⟨_, rfl⟩)
  · rw [hf]; exact protocolFeesAccrued_type currency
  · exact storageLocStore_uint256 _ _ _

end Benchmarks.UniswapV4PoolManager
