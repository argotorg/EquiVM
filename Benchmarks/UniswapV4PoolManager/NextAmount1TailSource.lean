import Benchmarks.UniswapV4PoolManager.SafeCast160Source
import Benchmarks.UniswapV4PoolManager.WordBoundedSubSource
import Benchmarks.UniswapV4PoolManager.WordBorrowSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def nextAmount1TailStmts (add : Bool) : List Stmt :=
  if add then
    [.internalCall "SafeCast_toUint160"
      [.inRange (.uint ⟨256, by decide⟩) (.binary .add (.var "sqrtPX96") (.var "quotient"))] "result",
     .return [.var "result"]]
  else
    [.require (.binary .gt (.var "sqrtPX96") (.var "quotient")),
     .return [.cast (.binary .sub (.var "sqrtPX96") (.var "quotient")) (.elem (.int (.uint ⟨160, by decide⟩)))]]

theorem nextAmount1TailSource {f : Frame} {evm : EVM.State} {price q : UInt256}
    (add : Bool) (hf : f.contract = contract) (hp : price.toNat < 2^160)
    (hs : f.locals.get? "sqrtPX96" = some (.int (Int.ofNat price.toNat)))
    (hq : f.locals.get? "quotient" = some (.int (Int.ofNat q.toNat))) :
    ∃ f', ExecBlock config f evm (nextAmount1TailStmts add)
      (if (if add then price.toNat+q.toNat < 2^160 else q.toNat < price.toNat) then
        .returned f' evm (some [.int (Int.ofNat (if add then price+q else UInt256.sub price q).toNat)])
       else .reverted) := by
  cases add with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    have hg := evalWordGt (evalLocalValue (cfg := config) (f := f) (evm := evm) hs) (evalLocalValue hq)
    by_cases hlt : q.toNat < price.toNat
    · simp only [if_pos hlt]
      exact ⟨f, ExecBlock.consNormal (ExecStmt.requireTrue (by simpa only [decide_eq_true hlt] using hg))
        (ABlock.start.returns (evalBoundedWordSub ⟨160, by decide⟩ (Nat.le_of_lt hlt) hp
          (evalLocalValue hs) (evalLocalValue hq)))⟩
    · simp only [if_neg hlt]
      exact ⟨f, ExecBlock.consRevert (ExecStmt.requireFalse (by simpa only [decide_eq_false hlt] using hg))⟩
  | true =>
    simp only [if_true]
    by_cases h256 : price.toNat+q.toNat < UInt256.size
    · have he := checkedAddSourceOk (evalLocalValue (cfg := config) (f := f) (evm := evm) hs)
        (evalLocalValue hq) h256
      have hc := uintToUint160Call hf he "result"
      have hr : (price+q).toNat = price.toNat+q.toNat := by rw [uadd_toNat, Nat.mod_eq_of_lt h256]
      by_cases h160 : price.toNat+q.toNat < 2^160
      · have hw : (price+q).toNat < 2^160 := by rw [hr]; exact h160
        rw [if_pos hw] at hc
        simp only [if_pos h160]
        exact ⟨wordLocal f "result" (price+q), ExecBlock.consNormal hc (ABlock.start.returns wordLocal_eval)⟩
      · have hw : ¬(price+q).toNat < 2^160 := by rw [hr]; exact h160
        rw [if_neg hw] at hc
        simp only [if_neg h160]
        exact ⟨f, ExecBlock.consRevert hc⟩
    · have h160 : ¬price.toNat+q.toNat < 2^160 := by
        change ¬price.toNat+q.toNat < 2^256 at h256
        omega
      simp only [if_neg h160]
      have he := checkedAddSourceOverflow (evalLocalValue (cfg := config) (f := f) (evm := evm) hs)
        (evalLocalValue hq) (Nat.le_of_not_gt h256)
      refine ⟨f, ExecBlock.consRevert (ExecStmt.internalCallArgsRevert ?_)⟩
      simp only [evalExprs?, he, bind, EvalResult.bind]

end Benchmarks.UniswapV4PoolManager
