import Benchmarks.UniswapV3.Pool.UpdatePositionFeeModel
import Benchmarks.UniswapV3.Pool.PositionUpdateStoreModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def updatePositionPositionFrame (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : Frame :=
  resumeAfterInternalCall (updatePositionFee1Frame v a evm) "__c8" none

def updatePositionPositionState (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : EVM.State :=
  positionUpdateFinalState (updatePositionPositionArgs v a evm) (updatePositionChangedState v a evm)

def updatePositionPositionExprs : List Expr :=
  [.var "position", .var "liquidityDelta", .var "feeGrowthInside0X128", .var "feeGrowthInside1X128"]

def updatePositionPositionWords (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : List UInt256 :=
  updatePositionInside v a evm true :: updatePositionInside v a evm false ::
    updatePositionChangedWords v a evm

theorem updatePositionFee1Frame_eq (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) :
    updatePositionFee1Frame v a evm =
      {contract := contract, locals := (updatePositionFee1Frame v a evm).locals,
        immutables := immStore v} := by
  unfold updatePositionFee1Frame updatePositionFee0Frame updatePositionFeeFrame
  rw [updatePositionChangedFrame_eq]

theorem evalUpdatePositionPositionExprs (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm evm' : EVM.State) :
    evalExprs? config (updatePositionFee1Frame v a evm) evm' updatePositionPositionExprs =
      .ok [.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (updatePositionKey a)), .int a.delta,
        .int (Int.ofNat (updatePositionInside v a evm false).toNat),
        .int (Int.ofNat (updatePositionInside v a evm true).toNat)] := by
  have hk : evalExpr? config (updatePositionFee1Frame v a evm) evm' (.var "position") =
      .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (updatePositionKey a))) :=
    evalExpr_var_get (by update_position_changed_get)
  have hd : evalExpr? config (updatePositionFee1Frame v a evm) evm' (.var "liquidityDelta") =
      .ok (.int a.delta) := evalExpr_var_get (by update_position_changed_get)
  have hg0 : evalExpr? config (updatePositionFee1Frame v a evm) evm' (.var "feeGrowthInside0X128") =
      .ok (.int (Int.ofNat (updatePositionInside v a evm false).toNat)) :=
    evalExpr_var_get (by update_position_changed_get)
  have hg1 : evalExpr? config (updatePositionFee1Frame v a evm) evm' (.var "feeGrowthInside1X128") =
      .ok (.int (Int.ofNat (updatePositionInside v a evm true).toNat)) :=
    evalExpr_var_get (by update_position_changed_get)
  simp only [updatePositionPositionExprs, evalExprs?, hk, hd, hg0, hg1,
    bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool
