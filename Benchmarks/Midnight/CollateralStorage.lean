import Benchmarks.Midnight.PositionStorage
import Benchmarks.Midnight.ArrayStorage

/-! Source storage access for a position's packed collateral array. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def collateralArguments (id user index : UInt256) : Store :=
  (positionArguments id user).insert "index" (.int (Int.ofNat index.toNat))

def collateralRef : StorageRef :=
  { base := "position", steps := [.mindex (.var "id"), .mindex (.var "user"),
      .field "collateral", .aindex (.var "index")] }

def collateralEvaledRef (id user index : UInt256) : EvaledStorageRef :=
  { base := "position", steps := [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)),
      .mindex (.address (AccountAddress.ofNat user.toNat)), .field "collateral",
      .aindex (.int (Int.ofNat index.toNat))] }

theorem evalCollateralRef (evm : EVM.State) (id user index : UInt256) :
    evalStorageRef config (calldataFrame contract (collateralArguments id user index) ∅ evm)
      evm collateralRef =
      if index.toNat < 128 then .ok (collateralEvaledRef id user index) else .revert := by
  have hid : (calldataFrame contract (collateralArguments id user index) ∅ evm).locals.get?
      "id" = some (wordBytes32Value id) := by
    change (((((∅ : Store).insert "id" (wordBytes32Value id)).insert "user"
      (.address (AccountAddress.ofNat user.toNat))).insert "index" (.int (Int.ofNat index.toNat))).insert "__calldata" (.bytes evm.executionEnv.calldata)).get? "id" = _
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_self]
  have huser : (calldataFrame contract (collateralArguments id user index) ∅ evm).locals.get?
      "user" = some (.address (AccountAddress.ofNat user.toNat)) := by
    change (((((∅ : Store).insert "id" (wordBytes32Value id)).insert "user"
      (.address (AccountAddress.ofNat user.toNat))).insert "index" (.int (Int.ofNat index.toNat))).insert "__calldata" (.bytes evm.executionEnv.calldata)).get? "user" = _
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  have hindex : (calldataFrame contract (collateralArguments id user index) ∅ evm).locals.get?
      "index" = some (.int (Int.ofNat index.toNat)) := by
    change (((positionArguments id user).insert "index" (.int (Int.ofNat index.toNat))).insert "__calldata" (.bytes evm.executionEnv.calldata)).get? "index" = _
    rw [store_get_ne _ _ (by decide), store_get_self]
  have hlen : (EVM.Word.toBytesBE id).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size id
  have hty : storageTypeAt?
      (calldataFrame contract (collateralArguments id user index) ∅ evm).contract.storage
      { base := "position", steps := [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)),
        .mindex (.address (AccountAddress.ofNat user.toNat)), .field "collateral"] } =
      some (.array (.elem (.int (.uint ⟨128, by decide⟩))) 128) := rfl
  simp only [collateralRef, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    evalExpr?, hid, huser, hindex, EvalResult.bind, EvalResult.ofOption, valueToKey?,
    wordBytes32Value, pure, bind, hlen, show (abiBytes32Width : Nat) + 1 = 32 from rfl,
    ite_true, List.nil_append, List.cons_append, arrayIndexInBounds?, hty]
  simp only [Int.ofNat_eq_natCast, Int.natCast_nonneg, Nat.cast_lt, true_and]
  by_cases hi : index.toNat < 128 <;> simp only [hi, if_true, if_false] <;> rfl

def collateralLoc (id user index : UInt256) : StorageLoc where
  slot := positionSlot id user + ⟨3⟩ + UInt256.ofNat (index.toNat / 2)
  offset := ⟨16 * (index.toNat % 2), by omega⟩
  size := 16
  hbound := by dsimp; omega
  type := .int (.uint ⟨128, by decide⟩)

def collateralWord (load : UInt256 → UInt256) (id user index : UInt256) : UInt256 :=
  UInt256.land (UInt256.shiftRight
    (load (positionSlot id user + ⟨3⟩ + UInt256.ofNat (index.toNat / 2)))
    (UInt256.ofNat (128 * (index.toNat % 2)))) (UInt256.ofNat (2^128 - 1))

theorem collateralLoc_load (evm : EVM.State) (id user index : UInt256) :
    storageLocLoad evm (collateralLoc id user index) =
      .int (Int.ofNat (collateralWord
        (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner) id user index).toNat) := by
  unfold collateralLoc
  rw [storageLocLoad_uint_offset evm _ _ 16 ⟨128, by decide⟩
    (by decide) (by dsimp; omega) (by decide), div_byteOffset_eq_shiftRight]
  change Value.int (Int.ofNat (UInt256.land (UInt256.shiftRight _
    (UInt256.ofNat (8 * (16 * (index.toNat % 2))))) _).toNat) = _
  rw [show 8 * (16 * (index.toNat % 2)) = 128 * (index.toNat % 2) by omega]
  rfl

end Benchmarks.Midnight
