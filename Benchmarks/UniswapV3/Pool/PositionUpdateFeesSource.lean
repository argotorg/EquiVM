import Benchmarks.UniswapV3.Pool.PositionUpdateFeeSource
import Benchmarks.UniswapV3.Pool.PositionUpdateLiquiditySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def positionUpdateFee0Frame (imms : Store) (a : PositionUpdateArgs) (evm : EVM.State) : Frame :=
  positionUpdateFeeReadyFrame (positionUpdateLiquidityFrame imms a evm) a evm false

def positionUpdateReadyFrame (imms : Store) (a : PositionUpdateArgs) (evm : EVM.State) : Frame :=
  positionUpdateFeeReadyFrame (positionUpdateFee0Frame imms a evm) a evm true

macro "position_update_ready_get" : tactic =>
  `(tactic| (simp only [positionUpdateReadyFrame, positionUpdateFee0Frame,
    positionUpdateFeeReadyFrame, positionUpdateFeeCallFrame, positionUpdateRawName,
    positionOwedField, positionUpdateGrowthName, PositionUpdateArgs.growth,
    positionUpdateLiquidityFrame, Bool.false_eq_true, if_true, if_false]; split_ifs <;> position_update_get))

theorem positionUpdateFee0Source (imms : Store) (evm : EVM.State) (a : PositionUpdateArgs) :
    ExecBlock config (positionUpdateLiquidityFrame imms a evm) evm
      (positionUpdateFeeBody false) (.ok (positionUpdateFee0Frame imms a evm) evm) := by
  have h := positionUpdateFeeSource (positionUpdateLiquidityFrame imms a evm).locals imms evm
    a false (by position_update_ready_get) (by position_update_ready_get)
  by_cases hz : a.delta = 0
  all_goals
    simpa only [positionUpdateFee0Frame, positionUpdateLiquidityFrame, hz, ↓reduceIte] using h

theorem positionUpdateFee1Source (imms : Store) (evm : EVM.State) (a : PositionUpdateArgs) :
    ExecBlock config (positionUpdateFee0Frame imms a evm) evm
      (positionUpdateFeeBody true) (.ok (positionUpdateReadyFrame imms a evm) evm) := by
  have h := positionUpdateFeeSource (positionUpdateFee0Frame imms a evm).locals imms evm
    a true (by position_update_ready_get) (by position_update_ready_get)
  by_cases hz : a.delta = 0
  all_goals
    simpa only [positionUpdateReadyFrame, positionUpdateFee0Frame,
      positionUpdateFeeReadyFrame, positionUpdateFeeCallFrame, positionUpdateLiquidityFrame,
      hz, ↓reduceIte] using h

theorem positionUpdateFeesSource (imms : Store) (evm : EVM.State)
    (a : PositionUpdateArgs) (hv : positionUpdateLiquidityValid a evm) :
    ExecBlock config (positionUpdateFrame imms a) evm (positionUpdateFunction.body.take 8)
      (.ok (positionUpdateReadyFrame imms a evm) evm) := by
  change ExecBlock config (positionUpdateFrame imms a) evm
    (positionUpdateFunction.body.take 4 ++
      (positionUpdateFeeBody false ++ positionUpdateFeeBody true)) _
  exact execBlock_append_ok (positionUpdateLiquiditySource imms evm a hv)
    (execBlock_append_ok (positionUpdateFee0Source imms evm a) (positionUpdateFee1Source imms evm a))

theorem positionUpdateReadyFrame_eq (imms : Store) (a : PositionUpdateArgs) (evm : EVM.State) :
    positionUpdateReadyFrame imms a evm =
      {contract := contract, locals := (positionUpdateReadyFrame imms a evm).locals,
        immutables := imms} := by
  by_cases hz : a.delta = 0
  all_goals
    simp only [positionUpdateReadyFrame, positionUpdateFee0Frame,
      positionUpdateFeeReadyFrame, positionUpdateFeeCallFrame, positionUpdateLiquidityFrame,
      hz, ↓reduceIte]
  all_goals rfl

end Benchmarks.UniswapV3.Pool
