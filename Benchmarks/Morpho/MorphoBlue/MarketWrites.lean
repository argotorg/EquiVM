import Benchmarks.Morpho.MorphoBlue.Storage
import Benchmarks.Morpho.MorphoBlue.PackedHighStorage
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def setUint128HalfWord (high : Bool) (old value : UInt256) : UInt256 :=
  if high then setUint128HighWord old value else setUint128LowWord old value

theorem storageLocStore_uint128Half (evm : EVM.State) (slot value : UInt256) (high : Bool)
    (hc : value.toNat < 2 ^ 128) :
    storageLocStore evm (uint128HalfLoc slot high) (.int (Int.ofNat value.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint128HalfWord high (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) value)) := by
  cases high
  · exact storageLocStore_uint128Low evm slot value hc
  · exact storageLocStore_uint128High evm slot value hc

def storeMarketField (evm : EVM.State) (id : UInt256) (i : Fin 6) (value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (marketFieldSlot id i)
    (setUint128HalfWord (decide (i.val % 2 = 1))
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (marketFieldSlot id i)) value)

theorem assignMarketField (evm : EVM.State) (locals imms : Store) (key : Expr)
    (id : UInt256) (i : Fin 6) (value : UInt256) (hc : value.toNat < 2 ^ 128)
    (hbase : locals.get? "market" = none)
    (hkey : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm key = .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id))) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms }
      evm .storage ⟨"market", [.mindex key, .field (marketFieldName i)]⟩ (.int (Int.ofNat value.toNat)) =
      .ok ({ contract := contract, locals := locals, immutables := imms }, storeMarketField evm id i value) := by
  apply assignStorageRef_storage_scalar_value hbase
    (er := ⟨"market", [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id)),
      .field (marketFieldName i)]⟩)
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, hkey,
      valueToKey?, word_toBytesBE_length_32, if_pos (by decide : (32 : Nat) = 31 + 1),
      ↓reduceIte, EvalResult.ofOption, pure, bind, EvalResult.bind]
  · fin_cases i <;> rfl
  · rfl
  · exact morphoLayout_marketField id i
  · exact Or.inl ⟨_, rfl⟩
  · exact storageLocStore_uint128Half evm _ value _ hc

def storeMarketFieldAccounts (σ : AccountMap) (I : ExecutionEnv) (id : UInt256) (i : Fin 6)
    (value : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (marketFieldSlot id i)
    (setUint128HalfWord (decide (i.val % 2 = 1)) (solcSlotWordAt (marketFieldSlot id i) σ I) value)

theorem storeMarketField_executionEnv (evm : EVM.State) (id : UInt256) (i : Fin 6) (value : UInt256) :
    (storeMarketField evm id i value).executionEnv = evm.executionEnv := storageStore_executionEnv _ _ _ _

theorem storeMarketField_accounts (evm : EVM.State) (id : UInt256) (i : Fin 6) (value : UInt256) :
    (storeMarketField evm id i value).accountMap =
      storeMarketFieldAccounts evm.accountMap evm.executionEnv id i value := by
  rw [storeMarketField, storageStore_accountMap]
  rfl

theorem storeMarketField_bridge {s0 : State} {I : ExecutionEnv} {σ : AccountMap} {evm : State}
    (hs : SourceState s0 I σ evm) (id : UInt256) (i : Fin 6) (value : UInt256) :
    SourceState s0 I (storeMarketFieldAccounts σ I id i value) (storeMarketField evm id i value) := by
  refine ⟨?_, storeMarketField_executionEnv evm id i value |>.trans hs.env, ?_⟩
  · rw [storeMarketField, storageStore_σ₀]; exact hs.world
  · rw [storeMarketField_accounts, hs.env, ← hs.accounts]

-- The fee-share update writes the full supply-share word in the position mapping.
def storePositionSupplyShares (evm : EVM.State) (id account value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (positionSlot id account) value

theorem assignPositionSupplyShares (evm : EVM.State) (locals imms : Store) (key0 key1 : Expr)
    (id account value : UInt256) (hc : account.toNat < EVM.addressModulus)
    (hbase : locals.get? "position" = none)
    (hkey0 : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm key0 = .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id)))
    (hkey1 : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm key1 = .ok (.address (AccountAddress.ofNat account.toNat))) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms }
      evm .storage ⟨"position", [.mindex key0, .mindex key1, .field "supplyShares"]⟩ (.int (Int.ofNat value.toNat)) =
      .ok ({ contract := contract, locals := locals, immutables := imms }, storePositionSupplyShares evm id account value) := by
  apply assignStorageRef_storage_scalar_value hbase
    (er := ⟨"position", [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id)),
      .mindex (.address (AccountAddress.ofNat account.toNat)), .field "supplyShares"]⟩)
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, hkey0, hkey1,
      valueToKey?, word_toBytesBE_length_32, if_pos (by decide : (32 : Nat) = 31 + 1),
      ↓reduceIte, EvalResult.ofOption, pure, bind, EvalResult.bind]
  · rfl
  · rfl
  · exact morphoLayout_position id account ⟨0, by decide⟩ hc
  · exact Or.inl ⟨_, rfl⟩
  · exact storageLocStore_uint256 evm _ value

theorem storePositionSupplyShares_executionEnv (evm : EVM.State) (id account value : UInt256) :
    (storePositionSupplyShares evm id account value).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

theorem storePositionSupplyShares_bridge {s0 : State} {I : ExecutionEnv} {σ : AccountMap} {evm : State}
    (hs : SourceState s0 I σ evm) (id account value : UInt256) :
    SourceState s0 I (sstoreAccountMap I.codeOwner σ (positionSlot id account) value)
      (storePositionSupplyShares evm id account value) := by
  refine ⟨?_, storePositionSupplyShares_executionEnv evm id account value |>.trans hs.env, ?_⟩
  · rw [storePositionSupplyShares, storageStore_σ₀]; exact hs.world
  · rw [storePositionSupplyShares, storageStore_accountMap, hs.env, ← hs.accounts]

end Benchmarks.Morpho.MorphoBlue
