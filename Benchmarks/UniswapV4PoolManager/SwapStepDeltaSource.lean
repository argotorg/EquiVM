import Benchmarks.UniswapV4PoolManager.SwapStepDeltaWords
import Benchmarks.UniswapV4PoolManager.Amount0Source
import Benchmarks.UniswapV4PoolManager.Amount1Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def amountDeltaName (use0 : Bool) : Ident :=
  if use0 then "SqrtPriceMath_getAmount0Delta_uint160_uint160_uint128_bool"
  else "SqrtPriceMath_getAmount1Delta_uint160_uint160_uint128_bool"

theorem amountDeltaCall {f : Frame} {evm : EVM.State} {a b liquidity : UInt256}
    {ea eb el : Expr} (use0 roundUp : Bool) (hf : f.contract = contract)
    (hac : a.toNat < 2^160) (hbc : b.toNat < 2^160)
    (ha : evalExpr? config f evm ea = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? config f evm eb = .ok (.int (Int.ofNat b.toNat)))
    (hl : evalExpr? config f evm el = .ok (.int (Int.ofNat liquidity.toNat))) (ret : Ident) :
    ExecStmt config f evm (.internalCall (amountDeltaName use0) [ea, eb, el, .boolLit roundUp] ret)
      (if amountDeltaFits a b liquidity use0 roundUp then
        .ok (wordLocal f ret (amountDeltaWord a b liquidity use0 roundUp)) evm else .reverted) := by
  cases use0 with
  | false => exact amount1Call hf ha hb hl (by simp only [evalExpr?, pure]) ret
  | true => exact amount0Call hf hac hbc ha hb hl (by simp only [evalExpr?, pure]) ret

def amountDeltaAssignStmts (ea eb : Expr) (ret : Ident) (use0 roundUp : Bool) : List Stmt :=
  [.internalCall (amountDeltaName use0) [ea, eb, .var "liquidity", .boolLit roundUp] "amount",
   .assign .localVar {base := ret} (.var "amount")]

def amountDeltaFrame (f : Frame) (ret : Ident) (w : UInt256) : Frame :=
  {f with locals := (f.locals.insert "amount" (.int (Int.ofNat w.toNat))).insert ret (.int (Int.ofNat w.toNat))}

theorem amountDeltaFrame_get (f : Frame) (ret : Ident) (w : UInt256) (name : Ident)
    (hr : (ret == name) = false) (ha : ("amount" == name) = false) :
    (amountDeltaFrame f ret w).locals.get? name = f.locals.get? name :=
  (store_get_ne _ _ hr).trans (store_get_ne _ _ ha)

theorem amountDeltaAssignSource {f : Frame} {evm : EVM.State} {a b liquidity : UInt256}
    {ea eb : Expr} {old : Value} (ret : Ident) (use0 roundUp : Bool)
    (hf : f.contract = contract) (hac : a.toNat < 2^160) (hbc : b.toNat < 2^160)
    (ha : evalExpr? config f evm ea = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? config f evm eb = .ok (.int (Int.ofNat b.toNat)))
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (hr : f.locals.get? ret = some old) (hne : ("amount" == ret) = false) :
    ExecBlock config f evm (amountDeltaAssignStmts ea eb ret use0 roundUp)
      (if amountDeltaFits a b liquidity use0 roundUp then
        .ok (amountDeltaFrame f ret (amountDeltaWord a b liquidity use0 roundUp)) evm else .reverted) := by
  have hc := amountDeltaCall use0 roundUp hf hac hbc ha hb (evalLocalValue hl) "amount"
  by_cases hfit : amountDeltaFits a b liquidity use0 roundUp
  · rw [if_pos hfit] at hc ⊢
    exact ExecBlock.consNormal hc (ExecBlock.consNormal
      (ExecStmt.assign wordLocal_eval (assignLocalValue ((store_get_ne _ _ hne).trans hr))) ExecBlock.nil)
  · rw [if_neg hfit] at hc ⊢
    exact ExecBlock.consRevert hc

def swapStepDeltaStmt (nextName ret : Ident) (input : Bool) : Stmt :=
  .ite (.var "zeroForOne")
    (amountDeltaAssignStmts (.var nextName) (.var "sqrtPriceCurrentX96") ret input input)
    (amountDeltaAssignStmts (.var "sqrtPriceCurrentX96") (.var nextName) ret (!input) input)

theorem swapStepDeltaSource {f : Frame} {evm : EVM.State} {price next liquidity : UInt256} {old : Value}
    (nextName ret : Ident) (input zeroForOne : Bool) (hf : f.contract = contract)
    (hp : price.toNat < 2^160) (hn : next.toNat < 2^160)
    (hs : f.locals.get? "sqrtPriceCurrentX96" = some (.int (Int.ofNat price.toNat)))
    (ht : f.locals.get? nextName = some (.int (Int.ofNat next.toNat)))
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (hb : f.locals.get? "zeroForOne" = some (.bool zeroForOne))
    (hr : f.locals.get? ret = some old) (hne : ("amount" == ret) = false) :
    ExecStmt config f evm (swapStepDeltaStmt nextName ret input)
      (if swapStepDeltaFits price next liquidity input zeroForOne then
        .ok (amountDeltaFrame f ret (swapStepDeltaWord price next liquidity input zeroForOne)) evm else .reverted) := by
  cases zeroForOne with
  | false =>
    exact ExecStmt.iteFalse (evalLocalValue hb)
      (amountDeltaAssignSource ret (!input) input hf hp hn (evalLocalValue hs) (evalLocalValue ht) hl hr hne)
  | true =>
    exact ExecStmt.iteTrue (evalLocalValue hb)
      (amountDeltaAssignSource ret input input hf hn hp (evalLocalValue ht) (evalLocalValue hs) hl hr hne)

end Benchmarks.UniswapV4PoolManager
