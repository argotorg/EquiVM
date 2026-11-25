import Benchmarks.Midnight.WithdrawSourceFrame
import Benchmarks.Midnight.BitmapCallSource

variable {fork : Ethereum.Fork}

/-! Source call and storage assignment for a cleared collateral bitmap bit. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def withdrawClearBody : List Stmt :=
  match withdrawCollateralTransition.body[10]! with
  | .ite _ yes _ => yes
  | _ => []

theorem withdrawBitmapSource {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user index assets : UInt256} {token receiver : AccountAddress}
    (hf : WithdrawSourceFrame frame m id user index assets token receiver)
    (hcanon : user.toNat < EVM.addressModulus) (hi : index.toNat < 128)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork config frame evm withdrawClearBody
      (.ok (wordLocal frame "__c2" (bitmapClear (positionBitmapWord evm id user) index))
        (storeHigh128 evm (positionSlot id user + ⟨2⟩)
          (bitmapClear (positionBitmapWord evm id user) index))) := by
  let bitmap := bitmapClear (positionBitmapWord evm id user) index
  have hp : (wordLocal frame "__c2" bitmap).locals.get? "_position" =
      some (.storageRef (positionRef id user) positionType) := by
    rw [wordLocal_get_ne _ _ _ _ (by decide)]; exact hf.position
  refine ExecBlock.consNormal (callBitmapClear (bitmap := positionBitmapWord evm id user)
    (bit := index) hf.contract ?_ (by omega)) ?_
  · simp only [evalExprs?, evalHealthBitmap hcanon hf.position, evalExpr?, hf.index,
      EvalResult.ofOption, EvalResult.bind, bind, pure, positionBitmapWord]
  exact ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm)
    (evalWordLocal (wordLocal_get ..)) (assignPositionBitmap bitmap hcanon hp)) ExecBlock.nil

end Benchmarks.Midnight
