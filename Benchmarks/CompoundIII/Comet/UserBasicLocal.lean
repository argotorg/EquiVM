import Benchmarks.CompoundIII.Comet.UserBasicData

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def userBasicWithAccrued (basic : UserBasicData) (accrued : UInt256) : UserBasicData :=
  { basic with accrued := packedUint accrued 0 8,
               accrued_lt := packedUint_lt accrued 0 (by decide) }

theorem userBasicWithAccrued_eq (basic : UserBasicData) (accrued : UInt256)
    (hfit : accrued.toNat < 2^64) :
    userBasicWithAccrued basic accrued = { basic with accrued := accrued, accrued_lt := hfit } := by
  have hw : packedUint accrued 0 8 = accrued := by
    change UInt256.land (UInt256.div accrued ⟨1⟩) _ = accrued
    rw [word_div_one]
    exact u256LandMaskCleanOfToNat _ _ (bits := 64) rfl hfit
  simp only [userBasicWithAccrued, hw]

-- LIBRARY CANDIDATE: assigning a local aggregate after computing the updated value.
theorem assignLocalPath_frame {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {steps : List StorageRefStep} {old value updated : Value}
    (hget : frame.locals.get? name = some old)
    (hupdate : updateLocalPath? cfg frame evm old steps value = .ok updated) :
    assignStorageRef? cfg frame evm .localVar ⟨name, steps⟩ value =
      .ok ({ frame with locals := frame.locals.insert name updated }, evm) := by
  simp only [assignStorageRef?, hget, hupdate, bind, EvalResult.bind, pure]

theorem evalBasicPrincipal {cfg frame evm expr basic}
    (he : evalExpr? cfg frame evm expr = .ok (userBasicValue basic)) :
    evalExpr? cfg frame evm (.field expr "principal") = .ok (.int (signed104 basic.principal)) := by
  simp only [evalExpr?, he, bind, EvalResult.bind]
  rfl

theorem evalBasicIndex {cfg frame evm expr basic}
    (he : evalExpr? cfg frame evm expr = .ok (userBasicValue basic)) :
    evalExpr? cfg frame evm (.field expr "baseTrackingIndex") = .ok (.int basic.index.toNat) := by
  simp only [evalExpr?, he, bind, EvalResult.bind]
  rfl

theorem evalBasicAccrued {cfg frame evm expr basic}
    (he : evalExpr? cfg frame evm expr = .ok (userBasicValue basic)) :
    evalExpr? cfg frame evm (.field expr "baseTrackingAccrued") =
      .ok (.int basic.accrued.toNat) := by
  simp only [evalExpr?, he, bind, EvalResult.bind]
  rfl

theorem evalBasicAssets {cfg frame evm expr basic}
    (he : evalExpr? cfg frame evm expr = .ok (userBasicValue basic)) :
    evalExpr? cfg frame evm (.field expr "assetsIn") = .ok (.int basic.assets.toNat) := by
  simp only [evalExpr?, he, bind, EvalResult.bind]
  rfl

theorem evalBasicReserved {cfg frame evm expr basic}
    (he : evalExpr? cfg frame evm expr = .ok (userBasicValue basic)) :
    evalExpr? cfg frame evm (.field expr "_reserved") = .ok (.int basic.reserved.toNat) := by
  simp only [evalExpr?, he, bind, EvalResult.bind]
  rfl

theorem assignBasicPrincipal {cfg frame evm name basic} (principal : UInt256)
    (hget : frame.locals.get? name = some (userBasicValue basic)) :
    assignStorageRef? cfg frame evm .localVar ⟨name, [.field "principal"]⟩
      (.int (signed104 principal)) =
    .ok ({ frame with
      locals := frame.locals.insert name
        (userBasicValue { basic with principal := principal }) }, evm) := by
  apply assignLocalPath_frame hget
  simp only [updateLocalPath?, userBasicValue, userBasicValues, lookupField?, lookupAssoc,
    updateField?, updateAssoc, EvalResult.ofOption, bind, EvalResult.bind, pure]
  rfl

theorem assignBasicIndex {cfg frame evm name basic} (index : UInt256) (hb : index.toNat < 2^64)
    (hget : frame.locals.get? name = some (userBasicValue basic)) :
    assignStorageRef? cfg frame evm .localVar ⟨name, [.field "baseTrackingIndex"]⟩
      (.int index.toNat) =
    .ok ({ frame with
      locals := frame.locals.insert name
        (userBasicValue { basic with index := index, index_lt := hb }) }, evm) := by
  apply assignLocalPath_frame hget
  simp only [updateLocalPath?, userBasicValue, userBasicValues, lookupField?, lookupAssoc,
    updateField?, updateAssoc, EvalResult.ofOption, bind, EvalResult.bind, pure]
  rfl

theorem assignBasicAccrued {cfg frame evm name basic} (accrued : UInt256)
    (hb : accrued.toNat < 2^64) (hget : frame.locals.get? name = some (userBasicValue basic)) :
    assignStorageRef? cfg frame evm .localVar ⟨name, [.field "baseTrackingAccrued"]⟩
      (.int accrued.toNat) =
    .ok ({ frame with
      locals := frame.locals.insert name
        (userBasicValue (userBasicWithAccrued basic accrued)) }, evm) := by
  rw [userBasicWithAccrued_eq basic accrued hb]
  apply assignLocalPath_frame hget
  simp only [updateLocalPath?, userBasicValue, userBasicValues, lookupField?, lookupAssoc,
    updateField?, updateAssoc, EvalResult.ofOption, bind, EvalResult.bind, pure]
  rfl

end Benchmarks.CompoundIII.Comet
