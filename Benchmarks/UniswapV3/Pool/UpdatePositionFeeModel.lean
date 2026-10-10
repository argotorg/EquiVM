import Benchmarks.UniswapV3.Pool.UpdatePositionChangeTrace
import Benchmarks.UniswapV3.Pool.TickFeeHeapTrace
import Benchmarks.UniswapV3.Pool.PositionUpdateModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def updatePositionFeeArgs (a : UpdatePositionArgs) (evm : EVM.State) : TickFeeArgs :=
  {lower := a.lower, upper := a.upper, current := a.current,
    global0 := feeGrowthWord false evm.accountMap evm.executionEnv,
    global1 := feeGrowthWord true evm.accountMap evm.executionEnv}

theorem updatePositionFeeArgs_fits (a : UpdatePositionArgs) (evm : EVM.State) (ha : a.Fits) :
    (updatePositionFeeArgs a evm).Fits := ⟨ha.1, ha.2.1, ha.2.2.2⟩

def updatePositionInside (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (second : Bool) : UInt256 :=
  tickFeeInside (updatePositionFeeArgs a evm) (updatePositionChangedState v a evm).accountMap
    (updatePositionChangedState v a evm).executionEnv second

def updatePositionFeeFrame (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : Frame :=
  let frame := updatePositionChangedFrame v a evm
  let locals := frame.locals.insert "__c7"
    (.tuple [.int (Int.ofNat (updatePositionInside v a evm false).toNat),
      .int (Int.ofNat (updatePositionInside v a evm true).toNat)])
  {frame with locals := locals}

def updatePositionFee0Frame (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : Frame :=
  let frame := updatePositionFeeFrame v a evm
  let locals := frame.locals.insert "feeGrowthInside0X128"
    (.int (Int.ofNat (updatePositionInside v a evm false).toNat))
  {frame with locals := locals}

def updatePositionFee1Frame (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : Frame :=
  let frame := updatePositionFee0Frame v a evm
  let locals := frame.locals.insert "feeGrowthInside1X128"
    (.int (Int.ofNat (updatePositionInside v a evm true).toNat))
  {frame with locals := locals}

def updatePositionFeeExprs : List Expr :=
  [.var "tickLower", .var "tickUpper", .var "tick",
    .var "_feeGrowthGlobal0X128", .var "_feeGrowthGlobal1X128"]

def updatePositionFeeBody : List Stmt :=
  [.internalCall "Tick_getFeeGrowthInside" updatePositionFeeExprs "__c7",
    .letDecl "feeGrowthInside0X128" (some (.elem (.int (.uint ⟨256, by decide⟩))))
      (.tupleGet (.var "__c7") 0),
    .letDecl "feeGrowthInside1X128" (some (.elem (.int (.uint ⟨256, by decide⟩))))
      (.tupleGet (.var "__c7") 1)]

def updatePositionPositionArgs (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : PositionUpdateArgs :=
  {key := updatePositionKey a, delta := a.delta,
    growth0 := updatePositionInside v a evm false, growth1 := updatePositionInside v a evm true}

def updatePositionFlag (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) : Bool :=
  if a.delta = 0 then false else updatePositionFlipped v a evm upper

theorem updatePositionChangedWords_eq (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) :
    updatePositionChangedWords v a evm =
      [(updatePositionFlag v a evm true).toUInt256, (updatePositionFlag v a evm false).toUInt256,
        feeGrowthWord true evm.accountMap evm.executionEnv,
        feeGrowthWord false evm.accountMap evm.executionEnv,
        solcMappingSlot ⟨7⟩ (updatePositionKey a), EVM.wordOfInt a.current, EVM.wordOfInt a.delta,
        EVM.wordOfInt a.upper, EVM.wordOfInt a.lower, EVM.word a.owner.val] := by
  by_cases hz : a.delta = 0
  all_goals simp only [updatePositionChangedWords, updatePositionFlag, updatePositionPrefixWords,
    updatePositionUpdatedWords, updatePositionBitmapWords, hz, if_true, if_false]
  all_goals rfl

theorem updatePositionChangedFrame_eq (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) :
    updatePositionChangedFrame v a evm =
      {contract := contract, locals := (updatePositionChangedFrame v a evm).locals,
        immutables := immStore v} := by
  unfold updatePositionChangedFrame updatePositionBitmapDoneFrame updatePositionBitmapCallFrame
    updatePositionBitmapInputFrame updatePositionBitmapLowerFrame
  split_ifs <;> rfl

macro "update_position_changed_get" : tactic =>
  `(tactic| (simp only [updatePositionFee1Frame, updatePositionFee0Frame, updatePositionFeeFrame,
    updatePositionChangedFrame, updatePositionBitmapDoneFrame, updatePositionBitmapCallFrame,
    updatePositionBitmapInputFrame, updatePositionBitmapLowerFrame, if_true]; (try split_ifs) <;>
    ((try simp only [Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert]); (first | update_position_tick_get | update_position_prefix_get))))

end Benchmarks.UniswapV3.Pool
