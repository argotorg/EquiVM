import Benchmarks.UniswapV3.Pool.SwapPrefixSource
import Benchmarks.UniswapV3.Pool.StructFieldSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapLimitForPrice (a : SwapArgs) (price : UInt256) : Prop :=
  if a.zeroForOne then
    a.priceLimit.toNat < price.toNat ∧
      4295128739 < a.priceLimit.toNat
  else
    price.toNat < a.priceLimit.toNat ∧
      a.priceLimit.toNat < 1461446703485210103287273052203988822378723970342

instance (a : SwapArgs) (price : UInt256) : Decidable (swapLimitForPrice a price) :=
  inferInstanceAs (Decidable (if a.zeroForOne then _ else _))

def swapLimitValid (a : SwapArgs) (evm : EVM.State) : Prop :=
  swapLimitForPrice a (slot0FieldWord 0 20 evm.accountMap evm.executionEnv)

instance (a : SwapArgs) (evm : EVM.State) : Decidable (swapLimitValid a evm) :=
  inferInstanceAs (Decidable (swapLimitForPrice a _))

def swapLimitExpr : Expr :=
  .ite (.var "zeroForOne")
    (.binary .and
      (.binary .lt (.var "sqrtPriceLimitX96") (.field (.var "slot0Start") "sqrtPriceX96"))
      (.binary .gt (.var "sqrtPriceLimitX96") (.intLit 4295128739)))
    (.binary .and
      (.binary .gt (.var "sqrtPriceLimitX96") (.field (.var "slot0Start") "sqrtPriceX96"))
      (.binary .lt (.var "sqrtPriceLimitX96")
        (.intLit 1461446703485210103287273052203988822378723970342)))

macro "swap_slot_get" : tactic =>
  `(tactic| (simp only [swapSlot0Frame, swapDelegateFrame, swapInitFrame, poolAmountsFrame,
    swapFrame, swapLocals, resumeAfterInternalCall, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl))

theorem evalSwapUnlocked (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) :
    evalExpr? config (swapSlot0Frame v a evm) evm (.field (.var "slot0Start") "unlocked") =
      .ok (.bool (!decide (slot0FieldWord 30 1 evm.accountMap evm.executionEnv = ⟨0⟩))) := by
  rw [← wordToElemBool]
  exact evalExpr_structField (evalExpr_var_get (by swap_slot_get)) rfl

theorem evalSwapLimit (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) :
    evalExpr? config (swapSlot0Frame v a evm) evm swapLimitExpr =
      .ok (.bool (decide (swapLimitValid a evm))) := by
  have hz : evalExpr? config (swapSlot0Frame v a evm) evm (.var "zeroForOne") =
      .ok (.bool a.zeroForOne) := evalExpr_var_get (by swap_slot_get)
  have hl : evalExpr? config (swapSlot0Frame v a evm) evm (.var "sqrtPriceLimitX96") =
      .ok (.int (Int.ofNat a.priceLimit.toNat)) := evalExpr_var_get (by swap_slot_get)
  have hs : evalExpr? config (swapSlot0Frame v a evm) evm (.var "slot0Start") =
      .ok (slot0StructValue evm.accountMap evm.executionEnv) :=
    evalExpr_var_get (by swap_slot_get)
  have hp := evalExpr_structField (name := "sqrtPriceX96") hs (by rfl)
  cases hzdir : a.zeroForOne <;>
    simp [swapLimitExpr, evalExpr?, hz, hl, hp, evalBinaryOp?, bind, EvalResult.bind,
      pure, swapLimitValid, swapLimitForPrice, hzdir]
  all_goals split <;> simp_all

theorem swapGuardsSource (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hself : evm.executionEnv.codeOwner = v.original)
    (hn : a.amountSpecified ≠ 0)
    (hu : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hl : swapLimitValid a evm) :
    ExecBlock config (swapFrame v a) evm (swapTransition.body.take 8)
      (.ok (swapSlot0Frame v a evm) evm) := by
  change ExecBlock config _ _ (swapTransition.body.take 6 ++
    [.require (.field (.var "slot0Start") "unlocked"), .require swapLimitExpr]) _
  apply execBlock_append_ok (swapSlot0Source v a evm hwv hself hn)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_)
    (ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil)
  · simpa only [hu, decide_false, Bool.not_false] using evalSwapUnlocked v a evm
  · simpa only [hl, decide_true] using evalSwapLimit v a evm

theorem swapAssignLock (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) :
    ExecStmt config (swapSlot0Frame v a evm) evm
      (.assign .storage ⟨"slot0", [.field "unlocked"]⟩ (.boolLit false))
      (.ok (swapSlot0Frame v a evm) (storeSlot0Unlocked evm false)) :=
  ExecStmt.assign (by simp only [evalExpr?, pure])
    (assignSlot0Unlocked evm _ (immStore v) false (by swap_slot_get))

theorem swapLockSource (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hself : evm.executionEnv.codeOwner = v.original)
    (hn : a.amountSpecified ≠ 0)
    (hu : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hl : swapLimitValid a evm) :
    ExecBlock config (swapFrame v a) evm (swapTransition.body.take 9)
      (.ok (swapSlot0Frame v a evm) (storeSlot0Unlocked evm false)) := by
  change ExecBlock config _ _ (swapTransition.body.take 8 ++ [swapTransition.body[8]!]) _
  exact execBlock_append_ok (swapGuardsSource v a evm hwv hself hn hu hl)
    (ExecBlock.consNormal (swapAssignLock v a evm) ExecBlock.nil)

end Benchmarks.UniswapV3.Pool
