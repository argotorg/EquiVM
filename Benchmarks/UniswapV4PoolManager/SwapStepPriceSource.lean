import Benchmarks.UniswapV4PoolManager.NextPriceSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def swapStepPriceRet (input : Bool) : Ident := if input then "__c4" else "__c9"

def swapStepPriceStmts (ea : Expr) (input : Bool) : List Stmt :=
  [.internalCall (nextPriceName input)
    [.var "sqrtPriceCurrentX96", .var "liquidity", ea, .var "zeroForOne"] (swapStepPriceRet input),
   .assign .localVar {base := "sqrtPriceNextX96"} (.var (swapStepPriceRet input))]

def swapStepPriceFrame (f : Frame) (price liquidity amount : UInt256) (input zeroForOne : Bool) : Frame :=
  {f with locals := ((f.locals.insert (swapStepPriceRet input)
    (.int (Int.ofNat (nextPriceWord price liquidity amount input zeroForOne).toNat))).insert
      "sqrtPriceNextX96" (.int (Int.ofNat (nextPriceWord price liquidity amount input zeroForOne).toNat)))}

theorem swapStepPriceFrame_get (f : Frame) (price liquidity amount : UInt256) (input zeroForOne : Bool)
    (name : Ident) (hn : ("sqrtPriceNextX96" == name) = false) (hr : (swapStepPriceRet input == name) = false) :
    (swapStepPriceFrame f price liquidity amount input zeroForOne).locals.get? name = f.locals.get? name :=
  (store_get_ne _ _ hn).trans (store_get_ne _ _ hr)

theorem swapStepPriceSource {f : Frame} {evm : EVM.State} {price liquidity amount : UInt256} {ea : Expr} {old : Value}
    (input zeroForOne : Bool) (hf : f.contract = contract) (hp : price.toNat < 2^160)
    (hs : f.locals.get? "sqrtPriceCurrentX96" = some (.int (Int.ofNat price.toNat)))
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (ha : evalExpr? config f evm ea = .ok (.int (Int.ofNat amount.toNat)))
    (hb : f.locals.get? "zeroForOne" = some (.bool zeroForOne))
    (hn : f.locals.get? "sqrtPriceNextX96" = some old) :
    ExecBlock config f evm (swapStepPriceStmts ea input)
      (if nextPriceFits price liquidity amount input zeroForOne then
        .ok (swapStepPriceFrame f price liquidity amount input zeroForOne) evm else .reverted) := by
  have hc := nextPriceCall input zeroForOne hf hp (evalLocalValue hs) (evalLocalValue hl) ha
    (evalLocalValue hb) (swapStepPriceRet input)
  by_cases hfit : nextPriceFits price liquidity amount input zeroForOne
  · rw [if_pos hfit] at hc ⊢
    exact ExecBlock.consNormal hc (ExecBlock.consNormal
      (ExecStmt.assign wordLocal_eval (assignLocalValue ((store_get_ne _ _
        (by cases input <;> decide : (swapStepPriceRet input == "sqrtPriceNextX96") = false)).trans hn))) ExecBlock.nil)
  · rw [if_neg hfit] at hc ⊢
    exact ExecBlock.consRevert hc

end Benchmarks.UniswapV4PoolManager
