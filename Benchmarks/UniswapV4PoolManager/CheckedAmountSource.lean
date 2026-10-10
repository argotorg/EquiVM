import Benchmarks.UniswapV4PoolManager.SafeCast256Source
import Benchmarks.UniswapV4PoolManager.WordSignedSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def checkedAmountReturnExpr (negate : Bool) : Expr :=
  if negate then .cast (.binary .sub (.intLit 0) (.var "result")) (.elem (.int (.sint ⟨256, by decide⟩)))
  else .var "result"
def checkedAmountReturnWord (w : UInt256) (negate : Bool) : UInt256 :=
  if negate then UInt256.sub ⟨0⟩ w else w
def checkedAmountReturnBlock (negate : Bool) : List Stmt :=
  [.internalCall "SafeCast_toInt256" [.var "amount"] "result", .return [checkedAmountReturnExpr negate]]

theorem checkedAmountReturn {f : Frame} {evm : EVM.State} {w : UInt256}
    (hf : f.contract = contract) (ha : f.locals.get? "amount" = some (.int (Int.ofNat w.toNat)))
    (negate : Bool) :
    ∃ f', ExecBlock config f evm (checkedAmountReturnBlock negate)
      (if w.toNat < 2^255 then
        .returned f' evm (some [.int (EVM.signed (checkedAmountReturnWord w negate))]) else .reverted) := by
  have hc := uintToInt256Call (f := f) (evm := evm) hf (evalLocalValue ha) "result"
  by_cases hfit : w.toNat < 2^255
  · rw [if_pos hfit] at hc
    simp only [if_pos hfit]
    let f1 := {f with locals := f.locals.insert "result" (.int (EVM.signed w))}
    have hr : f1.locals.get? "result" = some (.int (EVM.signed w)) := store_get_self _ _ _
    have he : evalExpr? config f1 evm (checkedAmountReturnExpr negate) =
        .ok (.int (EVM.signed (checkedAmountReturnWord w negate))) := by
      cases negate with
      | false => exact evalLocalValue hr
      | true =>
        exact evalSignedWordSub (x := ⟨0⟩)
          (by simp only [evalExpr?, pure]; rfl) (evalLocalValue hr)
    exact ⟨f1, ExecBlock.consNormal hc (ABlock.start.returns he)⟩
  · rw [if_neg hfit] at hc
    simp only [if_neg hfit]
    exact ⟨f, ExecBlock.consRevert hc⟩

end Benchmarks.UniswapV4PoolManager
