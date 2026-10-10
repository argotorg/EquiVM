import Benchmarks.UniswapV4PoolManager.WordSignedSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def sqrtPriceClearMask : UInt256 := UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960
def tickClearMask : UInt256 := UInt256.ofNat 115792089237316195423546465081495555268867154031409843925235967201614124548095
def slot0SetSqrtWord (packed price : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land packed sqrtPriceClearMask) (UInt256.shiftLeft price (UInt256.ofNat 0))
def slot0SetTickWord (packed tick : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land packed tickClearMask)
    (UInt256.shiftLeft (UInt256.land tick (UInt256.ofNat (2^24-1))) (UInt256.ofNat 160))

abbrev slot0SetTickFunction : FunctionDecl := contract.functions[58]!
abbrev slot0SetSqrtFunction : FunctionDecl := contract.functions[59]!
theorem slot0SetTick_lookup : lookupCallable? contract "Slot0Library_setTick" = some slot0SetTickFunction.toCallable := rfl
theorem slot0SetSqrt_lookup : lookupCallable? contract "Slot0Library_setSqrtPriceX96" = some slot0SetSqrtFunction.toCallable := rfl

theorem slot0SetSqrtBody {f : Frame} {evm : EVM.State} {packed price : UInt256}
    (hp : f.locals.get? "_packed" = some (wordBytes32Value packed))
    (hv : f.locals.get? "_sqrtPriceX96" = some (.int (Int.ofNat price.toNat))) (hc : price.toNat < 2^160) :
    ExecFuncBody config f evm slot0SetSqrtFunction.body
      (.returned {f with locals := f.locals.insert "cleared" (.int (Int.ofNat (UInt256.land packed sqrtPriceClearMask).toNat))}
        evm (some [wordBytes32Value (slot0SetSqrtWord packed price)])) :=
  wordFieldSetBodyExec sqrtPriceClearMask 0 ⟨160, by decide⟩ "_sqrtPriceX96" (by decide) (by decide) hp hv hc

theorem slot0SetSqrtCall {f : Frame} {evm : EVM.State} {ep es : Expr} {packed price : UInt256}
    (hf : f.contract = contract) (hc : price.toNat < 2^160)
    (hp : evalExpr? config f evm ep = .ok (wordBytes32Value packed))
    (hs : evalExpr? config f evm es = .ok (.int (Int.ofNat price.toNat))) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "Slot0Library_setSqrtPriceX96" [ep, es] retVar)
      (.ok {f with locals := f.locals.insert retVar (wordBytes32Value (slot0SetSqrtWord packed price))} evm) := by
  apply internalCallFunctionReturn (argVals := [wordBytes32Value packed, .int (Int.ofNat price.toNat)])
    (value := some [wordBytes32Value (slot0SetSqrtWord packed price)])
    (by simp only [evalExprs?, hp, hs, bind, EvalResult.bind, pure])
    (by rw [hf]; exact slot0SetSqrt_lookup) rfl
  exact slot0SetSqrtBody (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("_packed" == "_sqrtPriceX96") = false)).trans (store_get_self _ _ _)) hc

theorem slot0SetTickBody {f : Frame} {evm : EVM.State} {packed tick : UInt256}
    (hp : f.locals.get? "_packed" = some (wordBytes32Value packed))
    (hv : f.locals.get? "_tick" = some (.int (EVM.signed tick))) :
    ExecFuncBody config f evm slot0SetTickFunction.body
      (.returned {f with locals := f.locals.insert "cleared" (.int (Int.ofNat (UInt256.land packed tickClearMask).toNat))}
        evm (some [wordBytes32Value (slot0SetTickWord packed tick)])) :=
  wordFieldSetNormalizedBodyExec tickClearMask 160 ⟨24, by decide⟩ "_tick" (by decide) (by decide) hp hv
    (normalizeUintSignedWord ⟨24, by decide⟩ tick (UInt256.ofNat (2^24-1)) rfl)

theorem slot0SetTickCall {f : Frame} {evm : EVM.State} {ep et : Expr} {packed tick : UInt256}
    (hf : f.contract = contract)
    (hp : evalExpr? config f evm ep = .ok (wordBytes32Value packed))
    (ht : evalExpr? config f evm et = .ok (.int (EVM.signed tick))) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "Slot0Library_setTick" [ep, et] retVar)
      (.ok {f with locals := f.locals.insert retVar (wordBytes32Value (slot0SetTickWord packed tick))} evm) := by
  apply internalCallFunctionReturn (argVals := [wordBytes32Value packed, .int (EVM.signed tick)])
    (value := some [wordBytes32Value (slot0SetTickWord packed tick)])
    (by simp only [evalExprs?, hp, ht, bind, EvalResult.bind, pure])
    (by rw [hf]; exact slot0SetTick_lookup) rfl
  exact slot0SetTickBody (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("_packed" == "_tick") = false)).trans (store_get_self _ _ _))

end Benchmarks.UniswapV4PoolManager
