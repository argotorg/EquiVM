import Benchmarks.UniswapV4PoolManager.Amount0Words
import Benchmarks.UniswapV4PoolManager.WordBorrowSource
import Benchmarks.UniswapV4PoolManager.WordLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev amount0Function : FunctionDecl := contract.functions[93]!
theorem amount0_lookup : lookupCallable? contract "SqrtPriceMath_getAmount0Delta_uint160_uint160_uint128_bool" =
    some amount0Function.toCallable := rfl

def amount0SortFrame (f : Frame) (a b : UInt256) : Frame :=
  if b.toNat < a.toNat then
    wordLocal (wordLocal (wordLocal (wordLocal f "__t0" b) "__t1" a) "sqrtPriceAX96" b) "sqrtPriceBX96" a
  else f

theorem amount0SortFrame_get (f : Frame) (a b : UInt256) (name : Ident)
    (ht0 : ("__t0" == name) = false) (ht1 : ("__t1" == name) = false)
    (ha : ("sqrtPriceAX96" == name) = false) (hb : ("sqrtPriceBX96" == name) = false) :
    (amount0SortFrame f a b).locals.get? name = f.locals.get? name := by
  unfold amount0SortFrame
  split
  · simp only [wordLocal_get, ht0, ht1, ha, hb, Bool.false_eq_true, if_false]
  · rfl

theorem amount0SortFrame_contract (f : Frame) (a b : UInt256) :
    (amount0SortFrame f a b).contract = f.contract := by
  unfold amount0SortFrame
  split <;> rfl

theorem amount0SortFrame_prices {f : Frame} {a b : UInt256}
    (ha : f.locals.get? "sqrtPriceAX96" = some (.int (Int.ofNat a.toNat)))
    (hb : f.locals.get? "sqrtPriceBX96" = some (.int (Int.ofNat b.toNat))) :
    (amount0SortFrame f a b).locals.get? "sqrtPriceAX96" = some (.int (Int.ofNat (amount0Lo a b).toNat)) ∧
    (amount0SortFrame f a b).locals.get? "sqrtPriceBX96" = some (.int (Int.ofNat (amount0Hi a b).toNat)) := by
  unfold amount0SortFrame amount0Lo amount0Hi
  split
  · simp only [wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, and_self]
  · exact ⟨ha, hb⟩

theorem amount0Sort {f : Frame} {evm : EVM.State} {a b : UInt256}
    (ha : f.locals.get? "sqrtPriceAX96" = some (.int (Int.ofNat a.toNat)))
    (hb : f.locals.get? "sqrtPriceBX96" = some (.int (Int.ofNat b.toNat))) :
    ExecStmt config f evm amount0Function.body[0]! (.ok (amount0SortFrame f a b) evm) := by
  have hgt := evalWordGt (evalLocalValue (cfg := config) (f := f) (evm := evm) ha) (evalLocalValue hb)
  unfold amount0SortFrame
  split
  next ho =>
    let f1 := wordLocal f "__t0" b
    let f2 := wordLocal f1 "__t1" a
    let f3 := wordLocal f2 "sqrtPriceAX96" b
    have ha1 : f1.locals.get? "sqrtPriceAX96" = some (.int (Int.ofNat a.toNat)) := by
      simp only [f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, ha]
    have ha2 : f2.locals.get? "sqrtPriceAX96" = some (.int (Int.ofNat a.toNat)) := by
      simp only [f2, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, ha1]
    have hb3 : f3.locals.get? "sqrtPriceBX96" = some (.int (Int.ofNat b.toNat)) := by
      simp only [f3, f2, f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hb]
    exact ExecStmt.iteTrue (by simpa only [decide_eq_true ho] using hgt)
      (ExecBlock.consNormal (ExecStmt.letDecl (evalLocalValue hb))
      (ExecBlock.consNormal (ExecStmt.letDecl (evalLocalValue ha1))
      (ExecBlock.consNormal (ExecStmt.assign
        (evalLocalValue (f := f2) (by simp only [f2, f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte]))
        (assignLocalValue ha2))
      (execBlock_singleton (ExecStmt.assign
        (evalLocalValue (f := f3) (by simp only [f3, f2, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte]))
        (assignLocalValue hb3))))))
  next ho => exact ExecStmt.iteFalse (by simpa only [decide_eq_false ho] using hgt) ExecBlock.nil

end Benchmarks.UniswapV4PoolManager
