import Benchmarks.Morpho.MorphoBlue.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: explicit uint128 narrowing equals the low-half word mask.
theorem evalCastUint128 {cfg : Config} {frame : Frame} {evm : EVM.State}
    {e : Expr} {w : UInt256}
    (he : evalExpr? cfg frame evm e = .ok (.int (Int.ofNat w.toNat))) :
    evalExpr? cfg frame evm (.cast e (.elem (.int (.uint ⟨128, by decide⟩)))) =
      .ok (.int (Int.ofNat (halfWord false w).toNat)) := by
  have hw : (halfWord false w).toNat = w.toNat % 2 ^ 128 := by
    change (UInt256.land w uint128Mask).toNat = _
    rw [uland_toNat]
    change Nat.land w.toNat (2 ^ 128 - 1) = _
    exact nat_land_mask_eq_mod _ _
  rw [evalExpr_cast_int he, hw]
  change EvalResult.ok (Value.int (Int.ofNat w.toNat % Int.ofNat (2 ^ 128))) = _
  rfl

def storeMarketLastUpdate (evm : EVM.State) (id value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (marketFieldSlot id 4)
    (setUint128LowWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (marketFieldSlot id 4)) value)

theorem assignMarketLastUpdate (evm : EVM.State) (locals imms : Store) (key : Expr)
    (id value : UInt256) (hc : value.toNat < 2 ^ 128)
    (hbase : locals.get? "market" = none)
    (hkey : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm key = .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id))) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms }
      evm .storage ⟨"market", [.mindex key, .field "lastUpdate"]⟩ (.int (Int.ofNat value.toNat)) =
      .ok ({ contract := contract, locals := locals, immutables := imms },
        storeMarketLastUpdate evm id value) := by
  apply assignStorageRef_storage_scalar_value hbase
    (er := ⟨"market", [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id)),
      .field "lastUpdate"]⟩)
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, hkey,
      valueToKey?, word_toBytesBE_length_32, if_pos (by decide : (32 : Nat) = 31 + 1),
      ↓reduceIte, EvalResult.ofOption, pure, bind, EvalResult.bind]
  · rfl
  · rfl
  · exact morphoLayout_marketField id ⟨4, by decide⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact storageLocStore_uint128Low evm _ value hc

theorem storeMarketLastUpdate_executionEnv (evm : EVM.State) (id value : UInt256) :
    (storeMarketLastUpdate evm id value).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

end Benchmarks.Morpho.MorphoBlue
