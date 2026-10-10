import Benchmarks.UniswapV4PoolManager.TickStorage
import Benchmarks.UniswapV4PoolManager.PoolFeeGrowthStorage
import Benchmarks.UniswapV4PoolManager.Slot0TickSource
import Benchmarks.UniswapV4PoolManager.WordWrappingSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

inductive FeeGrowthRegion where
  | below | above | inside

def feeOutsideField (second : Bool) : TickField :=
  if second then .feeGrowthOutside1 else .feeGrowthOutside0

def poolFeeInsideRegionWord (evm : EVM.State) (id : UInt256) (lower upper : Int)
    (region : FeeGrowthRegion) (second : Bool) : UInt256 :=
  let lo := tickFieldWord evm id lower (feeOutsideField second)
  let hi := tickFieldWord evm id upper (feeOutsideField second)
  match region with
  | .below => UInt256.sub lo hi
  | .above => UInt256.sub hi lo
  | .inside => UInt256.sub (UInt256.sub (poolFeeGrowthWord evm id second) lo) hi

def poolFeeInsideRegionExpr (region : FeeGrowthRegion) (second : Bool) : Expr :=
  let lo := Expr.storage {base := "lower", steps := [.field (feeOutsideField second).name]}
  let hi := Expr.storage {base := "upper", steps := [.field (feeOutsideField second).name]}
  let castSub (a b : Expr) := Expr.cast (.binary .sub a b) (.elem (.int (.uint ⟨256, by decide⟩)))
  match region with
  | .below => castSub lo hi
  | .above => castSub hi lo
  | .inside => castSub (castSub (.storage {base := "self", steps := [.field (poolFeeGrowthName second)]}) lo) hi

theorem poolFeeInsideRegion_eval {f : Frame} {evm : EVM.State} {id : UInt256} {lower upper : Int}
    (hs : f.locals.get? "self" = some (poolRefValue id))
    (hl : f.locals.get? "lower" = some (tickRefValue id lower))
    (hu : f.locals.get? "upper" = some (tickRefValue id upper)) (region : FeeGrowthRegion) (second : Bool) :
    evalExpr? config f evm (poolFeeInsideRegionExpr region second) =
      .ok (.int (Int.ofNat (poolFeeInsideRegionWord evm id lower upper region second).toNat)) := by
  have hlo := tickField_read (evm := evm) hl (feeOutsideField second)
  have hhi := tickField_read (evm := evm) hu (feeOutsideField second)
  cases region
  · exact evalWordSub hlo hhi
  · exact evalWordSub hhi hlo
  · exact evalWordSub (evalWordSub (poolFeeGrowth_read hs second) hlo) hhi

def poolFeeInsideRegionFrame (f : Frame) (evm : EVM.State) (id : UInt256) (lower upper : Int)
    (region : FeeGrowthRegion) : Frame :=
  {f with locals := ((f.locals.insert "feeGrowthInside0X128"
    (.int (Int.ofNat (poolFeeInsideRegionWord evm id lower upper region false).toNat))).insert
    "feeGrowthInside1X128" (.int (Int.ofNat (poolFeeInsideRegionWord evm id lower upper region true).toNat)))}

def poolFeeInsideRegionBody (region : FeeGrowthRegion) : List Stmt :=
  [.assign .localVar {base := "feeGrowthInside0X128"} (poolFeeInsideRegionExpr region false),
   .assign .localVar {base := "feeGrowthInside1X128"} (poolFeeInsideRegionExpr region true)]

theorem poolFeeInsideRegionRun {f : Frame} {evm : EVM.State} {id : UInt256} {lower upper : Int}
    {old0 old1 : Value} (hs : f.locals.get? "self" = some (poolRefValue id))
    (hl : f.locals.get? "lower" = some (tickRefValue id lower))
    (hu : f.locals.get? "upper" = some (tickRefValue id upper))
    (h0 : f.locals.get? "feeGrowthInside0X128" = some old0)
    (h1 : f.locals.get? "feeGrowthInside1X128" = some old1) (region : FeeGrowthRegion) :
    ExecBlock config f evm (poolFeeInsideRegionBody region)
      (.ok (poolFeeInsideRegionFrame f evm id lower upper region) evm) := by
  let f1 : Frame := {f with locals := (f.locals.insert "feeGrowthInside0X128"
    (.int (Int.ofNat (poolFeeInsideRegionWord evm id lower upper region false).toNat)))}
  have e0 := poolFeeInsideRegion_eval (evm := evm) hs hl hu region false
  have a0 : ExecStmt config f evm (poolFeeInsideRegionBody region)[0]! (.ok f1 evm) :=
    ExecStmt.assign e0 (assignLocalValue h0)
  have e1 := poolFeeInsideRegion_eval (f := f1) (evm := evm)
    ((store_get_ne _ _ (by decide : ("feeGrowthInside0X128" == "self") = false)).trans hs)
    ((store_get_ne _ _ (by decide : ("feeGrowthInside0X128" == "lower") = false)).trans hl)
    ((store_get_ne _ _ (by decide : ("feeGrowthInside0X128" == "upper") = false)).trans hu) region true
  exact ExecBlock.consNormal a0 (execBlock_singleton (ExecStmt.assign e1
    (assignLocalValue ((store_get_ne _ _
      (by decide : ("feeGrowthInside0X128" == "feeGrowthInside1X128") = false)).trans h1))))

end Benchmarks.UniswapV4PoolManager
