import Benchmarks.UniswapV4PoolManager.TickPositionWords
import Benchmarks.UniswapV4PoolManager.SignedShiftSource
import Benchmarks.UniswapV4PoolManager.ValueLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev tickPositionFunction : FunctionDecl := contract.functions[112]!
theorem tickPosition_lookup : lookupCallable? contract "TickBitmap_position" =
    some tickPositionFunction.toCallable := rfl

def tickPositionExpr : Expr := .cast
  (.binary (.shr (.sint ⟨24, by decide⟩)) (.var "tick") (.intLit 8)) (.elem (.int (.sint ⟨16, by decide⟩)))
def tickPositionBitExpr : Expr := .cast (.var "tick") (.elem (.int (.uint ⟨8, by decide⟩)))

theorem tickPosition_body_eq : tickPositionFunction.body =
    [.return [tickPositionExpr, tickPositionBitExpr]] := rfl

theorem tickPositionBody {f : Frame} {evm : EVM.State} {tick : UInt256}
    (ht : f.locals.get? "tick" = some (.int (EVM.signed tick))) :
    ExecFuncBody config f evm tickPositionFunction.body (.returned f evm (some (tickPositionValues tick))) := by
  have hshift := evalSignedShr (n := 8) ⟨24, by decide⟩ (by decide)
    (evalLocalValue (cfg := config) (evm := evm) ht)
    (show evalExpr? config f evm (.intLit 8) = .ok (.int (Int.ofNat 8)) by simp only [evalExpr?, pure]; rfl)
  rw [normalizeSigned24Word, ← wordSarSigned _ (n := 8) (by decide)] at hshift
  have hpos := evalExpr_cast_int (intType := .sint ⟨16, by decide⟩) hshift
  rw [normalizeSigned16Word] at hpos
  have hbit := evalExpr_cast_int (intType := .uint ⟨8, by decide⟩)
    (evalLocalValue (cfg := config) (evm := evm) ht)
  rw [normalizeUintSignedWord ⟨8, by decide⟩ tick (UInt256.ofNat 255) rfl] at hbit
  rw [tickPosition_body_eq]
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?, tickPositionExpr, tickPositionBitExpr, hpos, hbit,
    bind, EvalResult.bind, pure, tickPositionValues, tickPositionWord, tickPositionBit]

theorem tickPositionCall {f : Frame} {evm : EVM.State} {e : Expr} {tick : UInt256}
    (hf : f.contract = contract) (ht : evalExpr? config f evm e = .ok (.int (EVM.signed tick))) (ret : Ident) :
    ExecStmt config f evm (.internalCall "TickBitmap_position" [e] ret)
      (.ok (valueLocal f ret (.tuple (tickPositionValues tick))) evm) := by
  apply internalCallFunctionReturn (argVals := [.int (EVM.signed tick)])
    (value := some (tickPositionValues tick)) (evalExprs?_singleton ht)
    (by rw [hf]; exact tickPosition_lookup) rfl
  exact tickPositionBody (store_get_self _ _ _)

end Benchmarks.UniswapV4PoolManager
