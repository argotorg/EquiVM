import Benchmarks.Dss.Clipper.TakeGenericContinuationSource
import Benchmarks.Dss.Clipper.TakeCallbackSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/- The arithmetic branches of `take` retain different dead scratch locals.  These
   lemmas evaluate the callback guard from only its four live bindings, so the source
   proof does not depend on a particular scratch-store layout. -/

private theorem clipperEvalBinaryOpGtIntGeneric (x y : Int) :
    evalBinaryOp? .gt (.int x) (.int y) = .ok (.bool (x > y)) := by
  rfl

private theorem clipperEvalBinaryOpNeAddressGeneric (a b : AccountAddress) :
    evalBinaryOp? .ne (.address a) (.address b) =
      .ok (.bool (!(Value.address a == Value.address b))) := by
  rfl

theorem clipperEvalTakeGenericDataLength
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    {I : ExecutionEnv}
    (hdata : locals.get? "data" = some (clipperTakeDataValue I)) :
    evalExpr? (config v) (Frame.mk (contract v) locals) evm (bytesLength "data") =
      .ok (.int (Int.ofNat (clipperTakeDataBytes I).length)) := by
  simp only [bytesLength, localRef, evalExpr?, readLocalPath?, EvalResult.bind, bind,
    pure]
  rw [hdata]
  change EvalResult.ok
      (Value.int (Int.ofNat (ByteArray.mk (clipperTakeDataBytes I).toArray).size)) =
    EvalResult.ok (Value.int (Int.ofNat (clipperTakeDataBytes I).length))
  rw [show (ByteArray.mk (clipperTakeDataBytes I).toArray).size =
      (clipperTakeDataBytes I).length by
    simp only [ByteArray.size]
    simp]

theorem clipperEvalTakeGenericDataGtZero
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    {I : ExecutionEnv}
    (hdata : locals.get? "data" = some (clipperTakeDataValue I))
    (hpos : 0 < (clipperTakeDataBytes I).length) :
    evalExpr? (config v) (Frame.mk (contract v) locals) evm
      (.binary .gt (bytesLength "data") (.intLit 0)) = .ok (.bool true) := by
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [clipperEvalTakeGenericDataLength hdata]
  simp only [evalExpr?, pure]
  change evalBinaryOp? .gt (.int (Int.ofNat (clipperTakeDataBytes I).length))
      (.int 0) = .ok (.bool true)
  rw [clipperEvalBinaryOpGtIntGeneric]
  exact congrArg (fun b => EvalResult.ok (Value.bool b))
    (decide_eq_true (Int.ofNat_lt_ofNat_of_lt hpos))
  all_goals decide

theorem clipperEvalTakeGenericDataGtZero_false
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    {I : ExecutionEnv}
    (hdata : locals.get? "data" = some (clipperTakeDataValue I))
    (hempty : clipperTakeDataLenWord I = ⟨0⟩) :
    evalExpr? (config v) (Frame.mk (contract v) locals) evm
      (.binary .gt (bytesLength "data") (.intLit 0)) = .ok (.bool false) := by
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [clipperEvalTakeGenericDataLength hdata]
  simp only [evalExpr?, pure]
  change evalBinaryOp? .gt (.int (Int.ofNat (clipperTakeDataBytes I).length))
      (.int 0) = .ok (.bool false)
  rw [clipperEvalBinaryOpGtIntGeneric]
  have hlen : (clipperTakeDataBytes I).length = 0 := by
    simp [clipperTakeDataBytes, hempty]
  rw [hlen]
  rfl
  all_goals decide

theorem clipperEvalTakeGenericWhoNeVat
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    {who : AccountAddress} {b : Bool}
    (hwho : locals.get? "who" = some (.address who))
    (hb : (who != v.vat) = b) :
    evalExpr? (config v) (Frame.mk (contract v) locals) evm
      (.binary .ne (.var "who") (vatExpr v)) = .ok (.bool b) := by
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [clipperEvalTakeGenericVar hwho, clipperEvalVat]
  simp only [EvalResult.bind, bind]
  rw [clipperEvalBinaryOpNeAddressGeneric]
  cases b <;> simp_all
  all_goals decide

theorem clipperEvalTakeGenericWhoNeDog
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    {who dog : AccountAddress} {b : Bool}
    (hwho : locals.get? "who" = some (.address who))
    (hdog : locals.get? "dog_" = some (.address dog))
    (hb : (who != dog) = b) :
    evalExpr? (config v) (Frame.mk (contract v) locals) evm
      (.binary .ne (.var "who") (.var "dog_")) = .ok (.bool b) := by
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [clipperEvalTakeGenericVar hwho, clipperEvalTakeGenericVar hdog]
  simp only [EvalResult.bind, bind]
  rw [clipperEvalBinaryOpNeAddressGeneric]
  cases b <;> simp_all
  all_goals decide

theorem clipperEvalTakeGenericCallbackGuardOfParts
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    {bData bVat bDog : Bool}
    (hdata : evalExpr? (config v) (Frame.mk (contract v) locals) evm
      (.binary .gt (bytesLength "data") (.intLit 0)) = .ok (.bool bData))
    (hvat : evalExpr? (config v) (Frame.mk (contract v) locals) evm
      (.binary .ne (.var "who") (vatExpr v)) = .ok (.bool bVat))
    (hdog : evalExpr? (config v) (Frame.mk (contract v) locals) evm
      (.binary .ne (.var "who") (.var "dog_")) = .ok (.bool bDog)) :
    evalExpr? (config v) (Frame.mk (contract v) locals) evm
      (.binary .and
        (.binary .gt (bytesLength "data") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "who") (vatExpr v))
          (.binary .ne (.var "who") (.var "dog_")))) =
      .ok (.bool (bData && (bVat && bDog))) := by
  rw [evalExpr?]
  simp only [EvalResult.bind, bind, pure]
  rw [hdata, evalExpr?]
  simp only [EvalResult.bind, bind, pure]
  rw [hvat, hdog]
  cases bData <;> cases bVat <;> cases bDog <;> rfl

theorem clipperTakeGenericCallbackGuardTrue
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    {I : ExecutionEnv} {who dog : AccountAddress}
    (hdata : locals.get? "data" = some (clipperTakeDataValue I))
    (hwho : locals.get? "who" = some (.address who))
    (hdog : locals.get? "dog_" = some (.address dog))
    (hpos : 0 < (clipperTakeDataBytes I).length)
    (hwhoVat : who ≠ v.vat) (hwhoDog : who ≠ dog) :
    evalExpr? (config v) (Frame.mk (contract v) locals) evm
      (.binary .and
        (.binary .gt (bytesLength "data") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "who") (vatExpr v))
          (.binary .ne (.var "who") (.var "dog_")))) = .ok (.bool true) := by
  simpa [hwhoVat, hwhoDog] using
    (clipperEvalTakeGenericCallbackGuardOfParts
      (clipperEvalTakeGenericDataGtZero hdata hpos)
      (clipperEvalTakeGenericWhoNeVat (v := v) (b := true) hwho (by simp [hwhoVat]))
      (clipperEvalTakeGenericWhoNeDog (v := v) (b := true) hwho hdog
        (by simp [hwhoDog])))

theorem clipperTakeGenericCallbackGuardFalseWhoVat
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    {I : ExecutionEnv} {who dog : AccountAddress}
    (hdata : locals.get? "data" = some (clipperTakeDataValue I))
    (hwho : locals.get? "who" = some (.address who))
    (hdog : locals.get? "dog_" = some (.address dog))
    (hpos : 0 < (clipperTakeDataBytes I).length)
    (hwhoVat : who = v.vat) :
    evalExpr? (config v) (Frame.mk (contract v) locals) evm
      (.binary .and
        (.binary .gt (bytesLength "data") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "who") (vatExpr v))
          (.binary .ne (.var "who") (.var "dog_")))) = .ok (.bool false) := by
  simpa [hwhoVat] using
    (clipperEvalTakeGenericCallbackGuardOfParts
      (clipperEvalTakeGenericDataGtZero hdata hpos)
      (clipperEvalTakeGenericWhoNeVat (v := v) (b := false) hwho
        (by simp [hwhoVat]))
      (clipperEvalTakeGenericWhoNeDog (v := v) (b := (who != dog)) hwho hdog rfl))

theorem clipperTakeGenericCallbackGuardFalseWhoDog
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    {I : ExecutionEnv} {who dog : AccountAddress}
    (hdata : locals.get? "data" = some (clipperTakeDataValue I))
    (hwho : locals.get? "who" = some (.address who))
    (hdog : locals.get? "dog_" = some (.address dog))
    (hpos : 0 < (clipperTakeDataBytes I).length)
    (hwhoDog : who = dog) :
    evalExpr? (config v) (Frame.mk (contract v) locals) evm
      (.binary .and
        (.binary .gt (bytesLength "data") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "who") (vatExpr v))
          (.binary .ne (.var "who") (.var "dog_")))) = .ok (.bool false) := by
  simpa [hwhoDog] using
    (clipperEvalTakeGenericCallbackGuardOfParts
      (clipperEvalTakeGenericDataGtZero hdata hpos)
      (clipperEvalTakeGenericWhoNeVat (v := v) (b := (who != v.vat)) hwho rfl)
      (clipperEvalTakeGenericWhoNeDog (v := v) (b := false) hwho hdog
        (by simp [hwhoDog])))

theorem clipperTakeGenericCallbackGuardFalseDataEmpty
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    {I : ExecutionEnv} {who dog : AccountAddress}
    (hdata : locals.get? "data" = some (clipperTakeDataValue I))
    (hwho : locals.get? "who" = some (.address who))
    (hdog : locals.get? "dog_" = some (.address dog))
    (hempty : clipperTakeDataLenWord I = ⟨0⟩) :
    evalExpr? (config v) (Frame.mk (contract v) locals) evm
      (.binary .and
        (.binary .gt (bytesLength "data") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "who") (vatExpr v))
          (.binary .ne (.var "who") (.var "dog_")))) = .ok (.bool false) := by
  simpa using
    (clipperEvalTakeGenericCallbackGuardOfParts
      (clipperEvalTakeGenericDataGtZero_false hdata hempty)
      (clipperEvalTakeGenericWhoNeVat (v := v) (b := (who != v.vat)) hwho rfl)
      (clipperEvalTakeGenericWhoNeDog (v := v) (b := (who != dog)) hwho hdog rfl))

end Benchmarks.Dss.Clipper
