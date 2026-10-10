import Benchmarks.UniswapV4PoolManager.CheckedAmountSource
import Benchmarks.UniswapV4PoolManager.WordLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem checkedAmountPath {f : Frame} {evm : EVM.State} {stmt : Stmt} {w : UInt256}
    {fits : Prop} [Decidable fits] (hf : f.contract = contract)
    (hcall : ExecStmt config f evm stmt (if fits then .ok (wordLocal f "amount" w) evm else .reverted))
    (negate : Bool) :
    ∃ f', ExecBlock config f evm (stmt :: checkedAmountReturnBlock negate)
      (if fits ∧ w.toNat < 2^255 then
        .returned f' evm (some [.int (EVM.signed (checkedAmountReturnWord w negate))]) else .reverted) := by
  by_cases hfit : fits
  · rw [if_pos hfit] at hcall
    let f1 := wordLocal f "amount" w
    obtain ⟨f', htail⟩ := checkedAmountReturn (f := f1) (evm := evm) hf (store_get_self _ _ _) negate
    by_cases hc : w.toNat < 2^255
    · rw [if_pos hc] at htail
      simp only [if_pos (And.intro hfit hc)]
      exact ⟨f', ExecBlock.consNormal hcall htail⟩
    · rw [if_neg hc] at htail
      simp only [if_neg (show ¬(fits ∧ w.toNat < 2^255) from fun hh => hc hh.2)]
      exact ⟨f', ExecBlock.consNormal hcall htail⟩
  · rw [if_neg hfit] at hcall
    simp only [if_neg (show ¬(fits ∧ w.toNat < 2^255) from fun hh => hfit hh.1)]
    exact ⟨f, ExecBlock.consRevert hcall⟩

end Benchmarks.UniswapV4PoolManager
