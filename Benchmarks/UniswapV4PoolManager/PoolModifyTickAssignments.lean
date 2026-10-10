import Benchmarks.UniswapV4PoolManager.PoolModifyValues
import Benchmarks.UniswapV4PoolManager.LocalStruct

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyTickRet (upper : Bool) : Ident := if upper then "__c2" else "__c1"
def poolModifyTickName (upper : Bool) : Ident := if upper then "tickUpper" else "tickLower"
def poolModifyFlipField (upper : Bool) : Ident := if upper then "flippedUpper" else "flippedLower"
def poolModifyGrossField (upper : Bool) : Ident := if upper then "liquidityGrossAfterUpper" else "liquidityGrossAfterLower"

def poolModifyFlipValue (upper flipped fl : Bool) (gl : UInt256) (fu : Bool) (gu : UInt256) : Value :=
  if upper then poolModifyStateValue fl gl flipped gu else poolModifyStateValue flipped gl fu gu
def poolModifyTickValue (upper flipped : Bool) (gross : UInt256) (fl : Bool) (gl : UInt256) (fu : Bool) (gu : UInt256) : Value :=
  if upper then poolModifyStateValue fl gl flipped gross else poolModifyStateValue flipped gross fu gu
def poolModifyTickFrame (f : Frame) (upper flipped : Bool) (gross : UInt256)
    (fl : Bool) (gl : UInt256) (fu : Bool) (gu : UInt256) : Frame :=
  {f with locals := ((f.locals.insert "state" (poolModifyFlipValue upper flipped fl gl fu gu)).insert
    "state" (poolModifyTickValue upper flipped gross fl gl fu gu))}

def poolModifyTickAssignBlock (upper : Bool) : List Stmt :=
  [.assign .localVar {base := "state", steps := [.field (poolModifyFlipField upper)]}
      (.tupleGet (.var (poolModifyTickRet upper)) 0),
   .assign .localVar {base := "state", steps := [.field (poolModifyGrossField upper)]}
      (.tupleGet (.var (poolModifyTickRet upper)) 1)]

theorem poolModifyTickAssignments {f : Frame} {evm : State} {upper flipped fl fu : Bool} {gross gl gu : UInt256}
    (hs : f.locals.get? "state" = some (poolModifyStateValue fl gl fu gu))
    (hr : f.locals.get? (poolModifyTickRet upper) = some (.tuple [.bool flipped, .int (Int.ofNat gross.toNat)])) :
    ExecBlock config f evm (poolModifyTickAssignBlock upper)
      (.ok (poolModifyTickFrame f upper flipped gross fl gl fu gu) evm) := by
  let f1 := {f with locals := f.locals.insert "state" (poolModifyFlipValue upper flipped fl gl fu gu)}
  have he0 := evalTupleProjection (evalLocalValue (cfg := config) (f := f) (evm := evm) hr) (i := 0) rfl
  have h0 : ExecStmt config f evm (poolModifyTickAssignBlock upper)[0]! (.ok f1 evm) :=
    ExecStmt.assign he0 (assignLocalField hs
      (show lookupField? (poolModifyStateValue fl gl fu gu) (poolModifyFlipField upper) =
        some (.bool (if upper then fu else fl)) by cases upper <;> rfl)
      (by cases upper <;> rfl))
  have hr1 : f1.locals.get? (poolModifyTickRet upper) = some (.tuple [.bool flipped, .int (Int.ofNat gross.toNat)]) :=
    (store_get_ne _ _ (by cases upper <;> decide : ("state" == poolModifyTickRet upper) = false)).trans hr
  have he1 := evalTupleProjection (evalLocalValue (cfg := config) (f := f1) (evm := evm) hr1) (i := 1) rfl
  have h1 : ExecStmt config f1 evm (poolModifyTickAssignBlock upper)[1]!
      (.ok (poolModifyTickFrame f upper flipped gross fl gl fu gu) evm) :=
    ExecStmt.assign he1 (assignLocalField (store_get_self _ _ _)
      (show lookupField? (poolModifyFlipValue upper flipped fl gl fu gu) (poolModifyGrossField upper) =
        some (.int (Int.ofNat (if upper then gu else gl).toNat)) by cases upper <;> rfl)
      (by cases upper <;> rfl))
  exact ExecBlock.consNormal h0 (execBlock_singleton h1)

end Benchmarks.UniswapV4PoolManager
