import Benchmarks.UniswapV4PoolManager.WordSignextend24
import Benchmarks.UniswapV4PoolManager.NarrowWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def slot0TickWord (packed : UInt256) : UInt256 :=
  UInt256.signextend ⟨2⟩ (UInt256.shiftRight packed ⟨160⟩)

theorem slot0TickWord_canonical (packed : UInt256) : int24Canonical (slot0TickWord packed) :=
  signextend24_canonical _

abbrev slot0TickFunction : FunctionDecl := contract.functions[69]!
theorem slot0Tick_lookup : lookupCallable? contract "Slot0Library_tick" = some slot0TickFunction.toCallable := rfl

theorem slot0TickBody {f : Frame} {evm : EVM.State} {packed : UInt256}
    (hp : f.locals.get? "_packed" = some (wordBytes32Value packed)) :
    ExecFuncBody config f evm slot0TickFunction.body
      (.returned f evm (some [.int (EVM.signed (slot0TickWord packed))])) := by
  have hshift := evalWordShr (n := 160) (by decide)
    (evalCastValue (evalLocalValue (cfg := config) (evm := evm) hp) (castBytes32ToUint256 packed))
    (show evalExpr? config f evm (.intLit 160) = .ok (.int (Int.ofNat 160)) by simp only [evalExpr?, pure]; rfl)
  have hsmall : (UInt256.shiftRight packed (UInt256.ofNat 160)).toNat < 2^255 := by
    rw [wordShiftRightNat _ (by decide)]
    have hp : packed.toNat < 2^256 := packed.val.isLt
    omega
  have hs : EVM.signed (UInt256.shiftRight packed (UInt256.ofNat 160)) =
      Int.ofNat (UInt256.shiftRight packed (UInt256.ofNat 160)).toNat := by
    change (if (UInt256.shiftRight packed (UInt256.ofNat 160)).toNat < 2^255 then _ else _) = _
    rw [if_pos hsmall]
    rfl
  have he := evalExpr_cast_int (intType := .sint ⟨24, by decide⟩) hshift
  rw [← hs, normalizeSigned24Word] at he
  exact .execBlockRet (ABlock.start.returns he)

theorem slot0TickCall {f : Frame} {evm : EVM.State} {e : Expr} {packed : UInt256}
    (hf : f.contract = contract) (he : evalExpr? config f evm e = .ok (wordBytes32Value packed)) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "Slot0Library_tick" [e] retVar)
      (.ok {f with locals := f.locals.insert retVar (.int (EVM.signed (slot0TickWord packed)))} evm) := by
  apply internalCallFunctionReturn (argVals := [wordBytes32Value packed])
    (value := some [.int (EVM.signed (slot0TickWord packed))]) (evalExprs?_singleton he)
    (by rw [hf]; exact slot0Tick_lookup) rfl
  exact slot0TickBody (store_get_self _ _ _)

end Benchmarks.UniswapV4PoolManager
