import Benchmarks.CompoundIII.Comet.StaticReturns
import Benchmarks.CompoundIII.Comet.SignedFields

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def userBasicSlot (addr : AccountAddress) : UInt256 :=
  solcMappingSlot ⟨5⟩ (EVM.word addr.val)

def userBasicWord (σ : AccountMap) (I : ExecutionEnv) (addr : AccountAddress) : UInt256 :=
  solcSlotWordAt (userBasicSlot addr) σ I

def userBasicFieldName (i : Fin 4) : Ident :=
  match i.val with
  | 0 => "baseTrackingIndex"
  | 1 => "baseTrackingAccrued"
  | 2 => "assetsIn"
  | _ => "_reserved"

def userBasicFieldOffset (i : Fin 4) : Fin 32 :=
  match i.val with
  | 0 => ⟨13, by decide⟩
  | 1 => ⟨21, by decide⟩
  | 2 => ⟨29, by decide⟩
  | _ => ⟨31, by decide⟩

def userBasicFieldSize (i : Fin 4) : Fin 33 :=
  match i.val with
  | 0 => ⟨8, by decide⟩
  | 1 => ⟨8, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨1, by decide⟩

def userBasicFieldWidth (i : Fin 4) : BitWidth :=
  ⟨8 * (userBasicFieldSize i).val, by rcases i with ⟨i, hi⟩; interval_cases i <;> dsimp only [userBasicFieldSize, userBasicFieldOffset] <;> decide⟩

def userBasicFieldWord (w : UInt256) (i : Fin 4) : UInt256 :=
  packedUint w (userBasicFieldOffset i).val (userBasicFieldSize i).val

def userBasicFieldExpr (i : Fin 4) : Expr :=
  .storage ⟨"userBasic", [.mindex (.var "arg0"), .field (userBasicFieldName i)]⟩

theorem userBasicFieldWords (w : UInt256) :
    userBasicFieldWord w 0 = UInt256.land (UInt256.shiftRight w (UInt256.ofNat 104))
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)) ∧
    userBasicFieldWord w 1 = UInt256.land (UInt256.shiftRight w (UInt256.ofNat 168))
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)) ∧
    userBasicFieldWord w 2 = UInt256.land (UInt256.shiftRight w (UInt256.ofNat 232))
      (UInt256.ofNat 65535) ∧
    userBasicFieldWord w 3 = UInt256.shiftRight w (UInt256.ofNat 248) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change UInt256.land (UInt256.div w (UInt256.ofNat (256 ^ (13 : Fin 32).val))) _ = _
    rw [divBytePow_eq_shift]
    rfl
  · change UInt256.land (UInt256.div w (UInt256.ofNat (256 ^ (21 : Fin 32).val))) _ = _
    rw [divBytePow_eq_shift]
    rfl
  · change UInt256.land (UInt256.div w (UInt256.ofNat (256 ^ (29 : Fin 32).val))) _ = _
    rw [divBytePow_eq_shift]
    rfl
  · change UInt256.land (UInt256.div w (UInt256.ofNat (256 ^ (31 : Fin 32).val))) _ = _
    rw [divBytePow_eq_shift]
    apply u256LandMaskCleanOfToNat (bits := 8) _ _ rfl
    change (UInt256.shiftRight w ⟨248⟩).toNat < 2 ^ 8
    simp [UInt256.shiftRight, UInt256.toNat, Fin.shiftRight_val,
      Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul w.val.isLt

theorem evalUserBasicField (evm : EVM.State) (locals imms : Store)
    (addr : AccountAddress) (i : Fin 4)
    (hlocal : locals.get? "userBasic" = none)
    (harg : locals.get? "arg0" = some (.address addr)) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (userBasicFieldExpr i) =
      .ok (.int (userBasicFieldWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr)) i).toNat) := by
  have hbound : (userBasicFieldOffset i).val + (userBasicFieldSize i).val - 1 < 32 := by
    rcases i with ⟨i, hi⟩; interval_cases i <;> dsimp only [userBasicFieldSize, userBasicFieldOffset] <;> decide
  apply evalExpr_storage_scalar_value (hbackend := rfl)
    (loc := { slot := userBasicSlot addr, offset := userBasicFieldOffset i,
              size := userBasicFieldSize i, hbound := hbound,
              type := .int (.uint (userBasicFieldWidth i)) })
    (er := ⟨"userBasic", [.mindex (.address addr), .field (userBasicFieldName i)]⟩)
    (t := .int (.uint (userBasicFieldWidth i))) hlocal
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, harg,
      valueToKey?, pure, bind, EvalResult.bind, EvalResult.ofOption]
  · change storageTypeAt? contract.storage
      ⟨"userBasic", [.mindex (.address addr), .field (userBasicFieldName i)]⟩ = _
    rcases i with ⟨i, hi⟩; interval_cases i <;> rfl
  · rcases i with ⟨i, hi⟩
    interval_cases i <;>
      simp only [userBasicSlot, userBasicFieldName, userBasicFieldOffset, userBasicFieldSize,
        userBasicFieldWidth, solcMappingSlot, keyValueToWord_address] <;> rfl
  · exact packedUint_load evm (userBasicSlot addr) (userBasicFieldOffset i)
      (userBasicFieldSize i) (userBasicFieldWidth i) rfl

def userBasicScalar (w : UInt256) (i : Fin 4) : ScalarReturn :=
  { type := .int (.uint (userBasicFieldWidth i))
    value := .int (userBasicFieldWord w i).toNat
    word := userBasicFieldWord w i
    encoded := uintWordEncoding (userBasicFieldWidth i) _
      (Nat.ne_of_gt (userBasicFieldWidth i).property.1)
      (packedUint_lt w _ (by omega)) }

def userBasicPrincipalExpr : Expr :=
  .storage ⟨"userBasic", [.mindex (.var "arg0"), .field "principal"]⟩

theorem evalUserBasicPrincipalOf (evm : EVM.State) (locals imms : Store)
    (addr : AccountAddress) (arg : Expr)
    (hlocal : locals.get? "userBasic" = none)
    (harg : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm arg = .ok (.address addr)) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨"userBasic", [.mindex arg, .field "principal"]⟩) =
      .ok (.int (signed104
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr)))) := by
  apply evalExpr_storage_scalar_value (hbackend := rfl)
    (loc := { slot := userBasicSlot addr, offset := 0, size := 13, hbound := by decide,
              type := .int (.sint ⟨104, by decide⟩) })
    (er := ⟨"userBasic", [.mindex (.address addr), .field "principal"]⟩)
    (t := .int (.sint ⟨104, by decide⟩)) hlocal
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, harg,
      valueToKey?, pure, bind, EvalResult.bind, EvalResult.ofOption]
  · rfl
  · simp only [userBasicSlot, solcMappingSlot, keyValueToWord_address]
    rfl
  · exact packedSint_load evm (userBasicSlot addr) 0 13 ⟨104, by decide⟩

theorem evalUserBasicPrincipal (evm : EVM.State) (locals imms : Store)
    (addr : AccountAddress)
    (hlocal : locals.get? "userBasic" = none)
    (harg : locals.get? "arg0" = some (.address addr)) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm userBasicPrincipalExpr =
      .ok (.int (signed104
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr)))) := by
  apply evalUserBasicPrincipalOf evm locals imms addr (.var "arg0") hlocal
  simp only [evalExpr?, harg, EvalResult.ofOption]

def userBasicPrincipalScalar (w : UInt256) : ScalarReturn :=
  { type := .int (.sint ⟨104, by decide⟩)
    value := .int (signed104 w)
    word := UInt256.signextend ⟨12⟩ w
    encoded := sint104WordEncoding w }

def userBasicScalars (w : UInt256) : List ScalarReturn :=
  [userBasicPrincipalScalar w, userBasicScalar w 0, userBasicScalar w 1, userBasicScalar w 2, userBasicScalar w 3]

end Benchmarks.CompoundIII.Comet
