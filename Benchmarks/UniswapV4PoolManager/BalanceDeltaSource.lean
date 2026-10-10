import Benchmarks.UniswapV4PoolManager.WordSignedShiftSource
import Benchmarks.UniswapV4PoolManager.WordSignedSource
import Benchmarks.UniswapV4PoolManager.CallComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def balanceDeltaWord (amount0 amount1 : UInt256) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft amount0 (UInt256.ofNat 128))
    (UInt256.land (UInt256.ofNat (2^128-1)) amount1)

abbrev balanceDeltaFunction : FunctionDecl := contract.functions[67]!
theorem balanceDelta_lookup : lookupCallable? contract "toBalanceDelta" = some balanceDeltaFunction.toCallable := rfl

theorem balanceDelta_eval {cfg : Config} {f : Frame} {evm : EVM.State} {e0 e1 : Expr} {a b : UInt256}
    (h0 : evalExpr? cfg f evm e0 = .ok (.int (EVM.signed a)))
    (h1 : evalExpr? cfg f evm e1 = .ok (.int (EVM.signed b))) :
    evalExpr? cfg f evm (.binary (.bitOr (.sint ⟨256, by decide⟩))
      (.binary (.shl (.sint ⟨256, by decide⟩)) (.cast e0 (.elem (.int (.sint ⟨256, by decide⟩)))) (.intLit 128))
      (.cast (.cast e1 (.elem (.int (.uint ⟨128, by decide⟩)))) (.elem (.int (.sint ⟨256, by decide⟩))))) =
      .ok (.int (EVM.signed (balanceDeltaWord a b))) := by
  have ha := evalExpr_cast_int (intType := .sint ⟨256, by decide⟩) h0
  rw [normalizeSignedWordOfInt, wordOfInt_signed] at ha
  have hb := evalExpr_cast_int (intType := .sint ⟨256, by decide⟩)
    (evalExpr_cast_int (intType := .uint ⟨128, by decide⟩) h1)
  rw [normalizeUintSignedWord ⟨128, by decide⟩ b (UInt256.ofNat (2^128-1)) rfl, normalizeInt_sint256_word] at hb
  have he := evalSignedWordOr (evalSignedWordShl (n := 128) (by decide) ha
    (show evalExpr? cfg f evm (.intLit 128) = .ok (.int (Int.ofNat 128)) by
      simp only [evalExpr?, pure]; rfl)) hb
  simpa only [u256_land_comm b, balanceDeltaWord] using he

theorem balanceDeltaBody {f : Frame} {evm : EVM.State} {a b : UInt256}
    (h0 : f.locals.get? "_amount0" = some (.int (EVM.signed a)))
    (h1 : f.locals.get? "_amount1" = some (.int (EVM.signed b))) :
    ExecFuncBody config f evm balanceDeltaFunction.body
      (.returned f evm (some [.int (EVM.signed (balanceDeltaWord a b))])) :=
  .execBlockRet (ABlock.start.returns (balanceDelta_eval (evalLocalValue h0) (evalLocalValue h1)))

theorem balanceDeltaCall {f : Frame} {evm : EVM.State} {e0 e1 : Expr} {a b : UInt256}
    (hf : f.contract = contract) (h0 : evalExpr? config f evm e0 = .ok (.int (EVM.signed a)))
    (h1 : evalExpr? config f evm e1 = .ok (.int (EVM.signed b))) (ret : Ident) :
    ExecStmt config f evm (.internalCall "toBalanceDelta" [e0, e1] ret)
      (.ok {f with locals := f.locals.insert ret (.int (EVM.signed (balanceDeltaWord a b)))} evm) := by
  apply internalCallFunctionReturn (argVals := [.int (EVM.signed a), .int (EVM.signed b)])
    (value := some [.int (EVM.signed (balanceDeltaWord a b))])
    (by simp only [evalExprs?, h0, h1, bind, EvalResult.bind, pure])
    (by rw [hf]; exact balanceDelta_lookup) rfl
  exact balanceDeltaBody (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("_amount0" == "_amount1") = false)).trans (store_get_self _ _ _))

end Benchmarks.UniswapV4PoolManager
