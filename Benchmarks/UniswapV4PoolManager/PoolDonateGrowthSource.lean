import Benchmarks.UniswapV4PoolManager.PoolDonateModel
import Benchmarks.UniswapV4PoolManager.SimpleMulDivSource
import Benchmarks.UniswapV4PoolManager.WordBoolean
import Benchmarks.UniswapV4PoolManager.WordBorrowSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolDonateAmountName (second : Bool) : Ident := if second then "amount1" else "amount0"
def poolDonateGrowthCallName (second : Bool) : Ident := if second then "__c4" else "__c3"
def poolDonateGrowthStmt (second : Bool) : Stmt :=
  .ite (.binary .gt (.var (poolDonateAmountName second)) (.intLit 0))
    [.internalCall "UnsafeMath_simpleMulDiv"
       [.var (poolDonateAmountName second), .intLit (2^128), .var "liquidity"] (poolDonateGrowthCallName second),
     .assign .storage {base := "state", steps := [.field (poolFeeGrowthName second)]}
       (.cast (.binary .add (.storage {base := "state", steps := [.field (poolFeeGrowthName second)]})
         (.var (poolDonateGrowthCallName second))) (.elem (.int (.uint ⟨256, by decide⟩))))] []

def poolDonateGrowthFrame (f : Frame) (second : Bool) (amount liquidity : UInt256) : Frame :=
  if amount = ⟨0⟩ then f else wordLocal f (poolDonateGrowthCallName second) (poolDonateGrowth amount liquidity)

theorem poolDonateGrowthFrame_contract (f : Frame) (second : Bool) (amount liquidity : UInt256) :
    (poolDonateGrowthFrame f second amount liquidity).contract = f.contract := by
  unfold poolDonateGrowthFrame
  split <;> rfl

theorem poolDonateGrowthFrame_get (f : Frame) (second : Bool) (amount liquidity : UInt256) (name : Ident)
    (hn : (poolDonateGrowthCallName second == name) = false) :
    (poolDonateGrowthFrame f second amount liquidity).locals.get? name = f.locals.get? name := by
  unfold poolDonateGrowthFrame
  split
  · rfl
  · exact store_get_ne _ _ hn

theorem poolDonateGrowthSource {f : Frame} {evm : State} {id amount liquidity : UInt256}
    (second : Bool) (hf : f.contract = contract)
    (hs : f.locals.get? "state" = some (poolRefValue id))
    (ha : f.locals.get? (poolDonateAmountName second) = some (.int (Int.ofNat amount.toNat)))
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat))) :
    ExecStmt config f evm (poolDonateGrowthStmt second)
      (if amount ≠ ⟨0⟩ ∧ evm.executionEnv.perm = false then .staticViolation else
        .ok (poolDonateGrowthFrame f second amount liquidity) (poolDonateStep evm id second amount liquidity)) := by
  have hg : evalExpr? config f evm (.binary .gt (.var (poolDonateAmountName second)) (.intLit 0)) =
      .ok (.bool (decide (amount ≠ ⟨0⟩))) := by
    simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, wordPositive_iff] using
      evalWordGt (evalLocalValue ha)
      (show evalExpr? config f evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by
        simp only [evalExpr?, pure]; rfl)
  by_cases hz : amount = ⟨0⟩
  · rw [if_neg (fun hh => hh.1 hz)]
    simp only [poolDonateGrowthFrame, poolDonateStep, if_pos hz]
    exact ExecStmt.iteFalse (by simpa only [hz, ne_eq, not_true_eq_false, decide_false] using hg) ExecBlock.nil
  · let f1 := wordLocal f (poolDonateGrowthCallName second) (poolDonateGrowth amount liquidity)
    have hcall := simpleMulDivCall hf (evalLocalValue (cfg := config) (evm := evm) ha)
      (show evalExpr? config f evm (.intLit (2^128)) = .ok (.int (Int.ofNat (UInt256.ofNat (2^128)).toNat)) by
        simp only [evalExpr?, pure]; rfl)
      (evalLocalValue hl) (poolDonateGrowthCallName second)
    have hs1 : f1.locals.get? "state" = some (poolRefValue id) :=
      (store_get_ne _ _ (by cases second <;> decide : (poolDonateGrowthCallName second == "state") = false)).trans hs
    have he := evalWordAdd (poolFeeGrowth_read (evm := evm) hs1 second)
      (evalLocalValue (cfg := config) (evm := evm) (store_get_self _ _ _))
    have hw := poolFeeGrowth_write (evm := evm) hs1 (value := poolFeeGrowthWord evm id second + poolDonateGrowth amount liquidity) second
    by_cases hperm : evm.executionEnv.perm = false
    · rw [if_pos ⟨hz, hperm⟩]
      exact ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using hg)
        (ExecBlock.consNormal hcall (ExecBlock.consStatic (ExecStmt.assignStatic he hw hperm)))
    · rw [if_neg (fun hh => hperm hh.2)]
      simp only [poolDonateGrowthFrame, poolDonateStep, if_neg hz]
      exact ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using hg)
        (ExecBlock.consNormal hcall (execBlock_singleton (ExecStmt.assign he hw)))

end Benchmarks.UniswapV4PoolManager
