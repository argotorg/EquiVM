import Benchmarks.Morpho.MorphoBlue.MarketWrites

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def positionPackedField (high : Bool) : Fin 3 := if high then ⟨2, by decide⟩ else ⟨1, by decide⟩

def storePositionPacked (evm : EVM.State) (id account : UInt256) (high : Bool) (value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (positionSlot id account + ⟨1⟩)
    (setUint128HalfWord high (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (positionSlot id account + ⟨1⟩)) value)

theorem assignPositionPacked (evm : EVM.State) (locals imms : Store) (key0 key1 : Expr)
    (id account : UInt256) (high : Bool) (value : UInt256) (hc : value.toNat < 2 ^ 128)
    (ha : account.toNat < EVM.addressModulus) (hbase : locals.get? "position" = none)
    (hkey0 : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm key0 = .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id)))
    (hkey1 : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm key1 = .ok (.address (AccountAddress.ofNat account.toNat))) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms }
      evm .storage ⟨"position", [.mindex key0, .mindex key1, .field (positionFieldName (positionPackedField high))]⟩
      (.int (Int.ofNat value.toNat)) =
      .ok ({ contract := contract, locals := locals, immutables := imms }, storePositionPacked evm id account high value) := by
  apply assignStorageRef_storage_scalar_value hbase
    (er := ⟨"position", [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id)),
      .mindex (.address (AccountAddress.ofNat account.toNat)), .field (positionFieldName (positionPackedField high))]⟩)
    (loc := uint128HalfLoc (positionSlot id account + ⟨1⟩) high)
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, hkey0, hkey1,
      valueToKey?, word_toBytesBE_length_32, if_pos (by decide : (32 : Nat) = 31 + 1),
      ↓reduceIte, EvalResult.ofOption, pure, bind, EvalResult.bind]
  · cases high <;> rfl
  · rfl
  · cases high
    · exact morphoLayout_position id account ⟨1, by decide⟩ ha
    · exact morphoLayout_position id account ⟨2, by decide⟩ ha
  · exact Or.inl ⟨_, rfl⟩
  · exact storageLocStore_uint128Half evm _ value high hc

def storePositionPackedAccounts (σ : AccountMap) (ee : ExecutionEnv)
    (id account : UInt256) (high : Bool) (value : UInt256) : AccountMap :=
  sstoreAccountMap ee.codeOwner σ (positionSlot id account + ⟨1⟩)
    (setUint128HalfWord high (solcSlotWordAt (positionSlot id account + ⟨1⟩) σ ee) value)

theorem storePositionPacked_executionEnv (evm : EVM.State) (id account : UInt256) (high : Bool) (value : UInt256) :
    (storePositionPacked evm id account high value).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

theorem storePositionPacked_bridge {s0 : State} {ee : ExecutionEnv} {σ : AccountMap} {evm : State}
    (hs : SourceState s0 ee σ evm) (id account : UInt256) (high : Bool) (value : UInt256) :
    SourceState s0 ee (storePositionPackedAccounts σ ee id account high value)
      (storePositionPacked evm id account high value) := by
  refine ⟨?_, (storePositionPacked_executionEnv evm id account high value).trans hs.env, ?_⟩
  · rw [storePositionPacked, storageStore_σ₀]; exact hs.world
  · rw [storePositionPacked, storageStore_accountMap]
    change storePositionPackedAccounts σ ee id account high value =
      storePositionPackedAccounts evm.accountMap evm.executionEnv id account high value
    rw [hs.env, ← hs.accounts]

end Benchmarks.Morpho.MorphoBlue
