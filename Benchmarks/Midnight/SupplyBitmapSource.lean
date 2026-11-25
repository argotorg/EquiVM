import Benchmarks.Midnight.BitmapCountSource
import Benchmarks.Midnight.PositionBitmapStorage
import Benchmarks.Midnight.InternalCall

variable {fork : Ethereum.Fork}

/-! Source calls and assignment for the newly enabled collateral bitmap. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def supplyNewCollateralBody : List Stmt :=
  match supplyCollateralTransition.body[8]! with
  | .ite _ yes _ => yes
  | _ => []

theorem callBitmapSet {cfg : Config} {frame : Frame} {evm : EVM.State}
    {bitmap bit : UInt256} {args : List Expr} {name : Ident}
    (hc : frame.contract = contract)
    (he : evalExprs? cfg frame evm args = .ok [.int bitmap.toNat, .int bit.toNat])
    (hbit : bit.toNat < 256) :
    ExecStmt fork cfg frame evm (.internalCall "UtilsLib_setBit" args name)
      (.ok (wordLocal frame name (bitmapSet bitmap bit)) evm) := by
  let locals : Store := ((∅ : Store).insert "bit" (.int bit.toNat)).insert
    "bitmap" (.int bitmap.toNat)
  apply internalCallFunctionReturn (callee := bitmapSetFunction) (locals := locals)
    (value := some [.int (bitmapSet bitmap bit).toNat]) he
  · rw [hc]; rfl
  · rfl
  · exact bitmapSetSource (by exact store_get_self _ _ _)
      (by simp only [locals, store_get_ne _ _ (show ("bitmap" == "bit") = false from rfl),
        store_get_self]) hbit

theorem callBitmapCount {cfg : Config} {frame : Frame} {evm : EVM.State}
    {bitmap : UInt256} {args : List Expr} {name : Ident}
    (hc : frame.contract = contract)
    (he : evalExprs? cfg frame evm args = .ok [.int bitmap.toNat])
    (hbitmap : bitmap.toNat < 2^128) :
    ExecStmt fork cfg frame evm (.internalCall "UtilsLib_countBits" args name)
      (.ok (wordLocal frame name (bitmapCount bitmap)) evm) := by
  let locals : Store := (∅ : Store).insert "x" (.int bitmap.toNat)
  obtain ⟨frame', hf⟩ := bitmapCountSource (cfg := cfg) (evm := evm)
    (frame := { frame with locals := locals }) hbitmap (store_get_self _ _ _)
  apply internalCallFunctionReturn (callee := bitmapCountFunction) (locals := locals)
    (calleeStele := frame') (value := some [.int (bitmapCount bitmap).toNat]) he
  · rw [hc]; rfl
  · rfl
  · exact hf

theorem supplyBitmapSetStmt {frame : Frame} {evm : EVM.State} {id user index : UInt256}
    (hc : frame.contract = contract) (hcanon : user.toNat < EVM.addressModulus)
    (hp : frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType))
    (hi : frame.locals.get? "collateralIndex" = some (.int index.toNat)) (hindex : index.toNat < 128) :
    ExecStmt fork config frame evm (supplyNewCollateralBody[2]!)
      (.ok (wordLocal frame "newCollateralBitmap"
        (bitmapSet (positionBitmapWord evm id user) index)) evm) := by
  apply callBitmapSet hc ?_ (by omega)
  simp only [evalExprs?, evalHealthBitmap hcanon hp, evalExpr?, hi, EvalResult.ofOption,
    EvalResult.bind, bind, pure, positionBitmapWord]

def supplyBitmapFrame (frame : Frame) (bitmap : UInt256) : Frame :=
  wordLocal frame "newCollateralBitmap" bitmap

def supplyCountFrame (frame : Frame) (bitmap : UInt256) : Frame :=
  wordLocal (supplyBitmapFrame frame bitmap) "__c3" (bitmapCount bitmap)

theorem supplyBitmapSource {frame : Frame} {evm : EVM.State} {id user index : UInt256}
    {result : ExecResult} (hc : frame.contract = contract)
    (hcanon : user.toNat < EVM.addressModulus)
    (hp : frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType))
    (hi : frame.locals.get? "collateralIndex" = some (.int index.toNat)) (hindex : index.toNat < 128)
    (hperm : evm.executionEnv.perm = true)
    (htail : ExecBlock fork config
      (supplyCountFrame frame (bitmapSet (positionBitmapWord evm id user) index))
      (storeHigh128 evm (positionSlot id user + ⟨2⟩)
        (bitmapSet (positionBitmapWord evm id user) index))
      (supplyNewCollateralBody.drop 5) result) :
    ExecBlock fork config frame evm (supplyNewCollateralBody.drop 2) result := by
  let bitmap := bitmapSet (positionBitmapWord evm id user) index
  have hp' : (supplyBitmapFrame frame bitmap).locals.get? "_position" =
      some (.storageRef (positionRef id user) positionType) := by
    rw [supplyBitmapFrame, wordLocal_get_ne _ _ _ _ (by decide)]
    exact hp
  apply ExecBlock.consNormal (supplyBitmapSetStmt hc hcanon hp hi hindex)
  apply ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm)
    (evalWordLocal (wordLocal_get ..)) (assignPositionBitmap bitmap hcanon hp'))
  apply ExecBlock.consNormal (callBitmapCount (by exact hc) ?_ (low128_lt _)) htail
  simp only [evalExprs?, supplyBitmapFrame, evalExpr?, wordLocal_get,
    EvalResult.ofOption, EvalResult.bind, bind, pure]
  rfl

theorem supplyBitmapStatic {frame : Frame} {evm : EVM.State} {id user index : UInt256}
    (hc : frame.contract = contract) (hcanon : user.toNat < EVM.addressModulus)
    (hp : frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType))
    (hi : frame.locals.get? "collateralIndex" = some (.int index.toNat)) (hindex : index.toNat < 128)
    (hperm : evm.executionEnv.perm = false) :
    ExecBlock fork config frame evm (supplyNewCollateralBody.drop 2) .staticViolation := by
  let bitmap := bitmapSet (positionBitmapWord evm id user) index
  have hp' : (supplyBitmapFrame frame bitmap).locals.get? "_position" =
      some (.storageRef (positionRef id user) positionType) := by
    rw [supplyBitmapFrame, wordLocal_get_ne _ _ _ _ (by decide)]
    exact hp
  apply ExecBlock.consNormal (supplyBitmapSetStmt hc hcanon hp hi hindex)
  exact ExecBlock.consStatic (ExecStmt.assignStatic (evalWordLocal (wordLocal_get ..))
    (assignPositionBitmap bitmap hcanon hp') hperm)

theorem evalSupplyCountGuard (frame : Frame) (evm : EVM.State) (bitmap : UInt256) :
    evalExpr? config (supplyCountFrame frame bitmap) evm
      (.binary .le (.var "__c3") (.intLit 16)) =
      .ok (.bool (decide ((bitmapCount bitmap).toNat ≤ 16))) := by
  simp only [evalExpr?, supplyCountFrame, wordLocal_get, EvalResult.ofOption,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  simp only [show ((bitmapCount bitmap).toNat : Int) ≤ 16 ↔
    (bitmapCount bitmap).toNat ≤ 16 by omega]

end Benchmarks.Midnight
