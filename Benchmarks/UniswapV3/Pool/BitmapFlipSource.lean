import Benchmarks.UniswapV3.Pool.BitmapFlipPrefix
import Benchmarks.UniswapV3.Pool.BitmapStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem bitmapFlipReadyGet (imms : Store) (tick spacing : Int) :
    (bitmapFlipReadyFrame imms tick spacing).locals.get? "wordPos" =
      some (.int (bitmapWordPos (tick.tdiv spacing))) ∧
    (bitmapFlipReadyFrame imms tick spacing).locals.get? "mask" =
      some (.int (Int.ofNat (bitmapFlipMask tick spacing).toNat)) ∧
    (bitmapFlipReadyFrame imms tick spacing).locals.get? "tickBitmap" = none := by
  simp only [bitmapFlipReadyFrame, bitmapFlipBitFrame, bitmapFlipWordFrame,
    bitmapFlipCallFrame, bitmapFlipLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  exact ⟨rfl, rfl, by simp⟩

def bitmapFlipValueExpr : Expr :=
  .binary (.bitXor (.uint ⟨256, by decide⟩))
    (.storage ⟨"tickBitmap", [.mindex (.var "wordPos")]⟩) (.var "mask")

theorem evalBitmapFlipValue (imms : Store) (evm : EVM.State) (tick spacing : Int) :
    evalExpr? config (bitmapFlipReadyFrame imms tick spacing) evm bitmapFlipValueExpr =
      .ok (.int (Int.ofNat (bitmapFlippedWord evm.accountMap evm.executionEnv
        (bitmapWordPos (tick.tdiv spacing)) (bitmapFlipMask tick spacing)).toNat)) := by
  obtain ⟨hw, hm, hb⟩ := bitmapFlipReadyGet imms tick spacing
  apply evalExpr_word_xor
  · exact evalBitmapStorage _ imms evm _ _ hb (evalExpr_var_get hw)
  · exact evalExpr_var_get hm

theorem bitmapFlipAssign (imms : Store) (evm : EVM.State) (tick spacing : Int) :
    assignStorageRef? config (bitmapFlipReadyFrame imms tick spacing) evm .storage
      ⟨"tickBitmap", [.mindex (.var "wordPos")]⟩
      (.int (Int.ofNat (bitmapFlippedWord evm.accountMap evm.executionEnv
        (bitmapWordPos (tick.tdiv spacing)) (bitmapFlipMask tick spacing)).toNat)) =
      .ok (bitmapFlipReadyFrame imms tick spacing,
        flipBitmap evm (bitmapWordPos (tick.tdiv spacing)) (bitmapFlipMask tick spacing)) := by
  obtain ⟨hw, hm, hb⟩ := bitmapFlipReadyGet imms tick spacing
  have ha := assignBitmapStorage _ imms evm (bitmapWordPos (tick.tdiv spacing)) (.var "wordPos")
    (bitmapFlippedWord evm.accountMap evm.executionEnv
      (bitmapWordPos (tick.tdiv spacing)) (bitmapFlipMask tick spacing)) hb (evalExpr_var_get hw)
  simpa only [flipBitmap, bitmapFlippedWord,
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl] using ha

theorem bitmapFlipReturns (imms : Store) (evm : EVM.State) (tick spacing : Int)
    (hn : spacing ≠ 0) (hr : tick.tmod spacing = 0) :
    ExecFuncBody config (bitmapFlipFrame imms tick spacing) evm bitmapFlipFunction.body
      (.returned (bitmapFlipReadyFrame imms tick spacing)
        (flipBitmap evm (bitmapWordPos (tick.tdiv spacing)) (bitmapFlipMask tick spacing)) none) := by
  apply ExecFuncBody.execBlockOK
  rw [← List.take_append_drop 5 bitmapFlipFunction.body]
  apply execBlock_append_ok (bitmapFlipReadySource imms evm tick spacing hn hr)
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalBitmapFlipValue imms evm tick spacing)
      (bitmapFlipAssign imms evm tick spacing)) ExecBlock.nil

theorem bitmapFlipStatic (imms : Store) (evm : EVM.State) (tick spacing : Int)
    (hn : spacing ≠ 0) (hr : tick.tmod spacing = 0) (hperm : evm.executionEnv.perm = false) :
    ExecFuncBody config (bitmapFlipFrame imms tick spacing) evm bitmapFlipFunction.body
      .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  rw [← List.take_append_drop 5 bitmapFlipFunction.body]
  apply execBlock_append_ok (bitmapFlipReadySource imms evm tick spacing hn hr)
  exact ExecBlock.consStatic (ExecStmt.assignStatic (evalBitmapFlipValue imms evm tick spacing)
    (bitmapFlipAssign imms evm tick spacing) hperm)

end Benchmarks.UniswapV3.Pool
