import Benchmarks.Midnight.PositionStorage
import Benchmarks.Midnight.AliasStorage
import Benchmarks.Midnight.PackedUint128

/-! Position storage aliases and their four packed uint128 fields. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

def positionType : StorageType :=
  match (contract.storage[0]!).ty with
  | .mapping _ (.mapping _ ty) => ty
  | _ => .elem .bool

def positionRef (id user : UInt256) : EvaledStorageRef :=
  { base := "position", steps :=
    [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)),
     .mindex (.address (AccountAddress.ofNat user.toNat))] }

def positionFieldName (i : Fin 4) : Ident :=
  ["credit", "pendingFee", "lastLossFactor", "lastAccrual"][i.val]'i.isLt

def positionFieldSlot (id user : UInt256) (i : Fin 4) : UInt256 :=
  if i.val < 2 then positionSlot id user else positionSlot id user + ⟨1⟩

def positionFieldLoc (id user : UInt256) (i : Fin 4) : StorageLoc := {
  slot := positionFieldSlot id user i
  offset := if i.val % 2 = 0 then 0 else 16
  size := 16
  hbound := by split <;> decide
  type := .int packedUInt128Int }

def positionFieldWord (evm : EVM.State) (id user : UInt256) (i : Fin 4) : UInt256 :=
  let w := Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (positionFieldSlot id user i)
  if i.val % 2 = 0 then UInt256.land w uint128Mask
  else UInt256.shiftRight w (UInt256.ofNat 128)

theorem positionFieldWord_lt (evm : EVM.State) (id user : UInt256) (i : Fin 4) :
    (positionFieldWord evm id user i).toNat < 2 ^ 128 := by
  unfold positionFieldWord
  split
  · exact u256LandMaskToNatLtOfToNat _ _ (by decide)
  · exact shiftRight128_lt _

theorem positionField_type (i : Fin 4) :
    storageTypeStep? positionType (.field (positionFieldName i)) =
      some (.elem (.int packedUInt128Int)) := by
  rcases i with ⟨i, hi⟩
  interval_cases i <;> rfl

theorem positionField_layout (id user : UInt256) (i : Fin 4)
    (hcanon : user.toNat < EVM.addressModulus) :
    midnightStorageLayout { (positionRef id user) with steps :=
      (positionRef id user).steps ++ [.field (positionFieldName i)] } =
      some (.leaf (positionFieldLoc id user i)) := by
  rcases i with ⟨i, hi⟩
  interval_cases i <;>
    change some (StorageAddr.leaf {
      slot := _, offset := _, size := 16, hbound := _, type := .int packedUInt128Int }) = _ <;>
    simp only [abiBytes32Width, keyValueToWord_fixedBytes32,
      keyValueToWord_address_of_canonical user hcanon] <;>
    simp [positionFieldLoc, positionFieldSlot, positionSlot, solcMappingSlot]

theorem positionField_load (evm : EVM.State) (id user : UInt256) (i : Fin 4) :
    storageLocLoad evm (positionFieldLoc id user i) =
      .int (positionFieldWord evm id user i).toNat := by
  rcases i with ⟨i, hi⟩
  interval_cases i <;> dsimp only [positionFieldLoc, positionFieldWord, positionFieldSlot] <;>
    norm_num only
  · exact storageLocLoad_uint_offset0 evm _ 16 ⟨128, by decide⟩ (by decide) (by decide)
  · exact storageLocLoad_uint128_high evm _
  · exact storageLocLoad_uint_offset0 evm _ 16 ⟨128, by decide⟩ (by decide) (by decide)
  · exact storageLocLoad_uint128_high evm _

theorem evalPositionAliasField {frame : Frame} {evm : EVM.State} {id user : UInt256}
    (i : Fin 4) (hcanon : user.toNat < EVM.addressModulus)
    (hget : frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType)) :
    evalExpr? config frame evm (.storage { base := "_position", steps :=
      [.field (positionFieldName i)] }) =
      .ok (.int (positionFieldWord evm id user i).toNat) :=
  evalStorageAliasField hget (positionField_type i) rfl
    (positionField_layout id user i hcanon) (positionField_load evm id user i)

theorem resolvePositionRef {frame : Frame} {evm : EVM.State} {id user : UInt256}
    (hc : frame.contract = contract) (hbase : frame.locals.get? "position" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (huser : frame.locals.get? "user" = some (.address (AccountAddress.ofNat user.toNat))) :
    resolveStorageRef? config frame evm { base := "position", steps :=
      [.mindex (.var "id"), .mindex (.var "user")] } =
      .ok (positionRef id user, positionType) := by
  apply resolveStorageRef?_ok hbase
  · have hlen : (EVM.Word.toBytesBE id).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size id
    simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hid, huser,
      EvalResult.bind, EvalResult.ofOption, valueToKey?, wordBytes32Value, pure, bind,
      hlen, show (abiBytes32Width : Nat) + 1 = 32 from rfl, ite_true]
    rfl
  · rw [hc]; rfl

end Benchmarks.Midnight
