import Benchmarks.Midnight.ClaimFeeState
import Benchmarks.Midnight.ToUint128Source

/-! Source semantics of each checked subtraction in a continuous-fee claim. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def claimFeeSubtractStmts (i : Fin 3) (name : Ident) : List Stmt :=
  [.internalCall "UtilsLib_toUint128" [.var "amount"] name,
    .assign .storage { base := "_marketState", steps := [.field (marketBalanceName i)] }
      (.inRange packedUInt128Int (.binary .sub
        (.storage { base := "_marketState", steps := [.field (marketBalanceName i)] })
        (.var name)))]

theorem claimFeeSubtractSource {frame : Frame} {evm : EVM.State} {id amount : UInt256}
    (i : Fin 3) (name : Ident) (hne : name ≠ "_marketState")
    (hc : frame.contract = contract)
    (ha : frame.locals.get? "amount" = some (.int amount.toNat))
    (hm : frame.locals.get? "_marketState" = some (.storageRef (marketStateRef id) marketStateType))
    (hamount : amount.toNat < 2^128) (hle : amount.toNat ≤ (marketBalanceWord evm id i).toNat)
    (hperm : evm.executionEnv.perm = true) {tail : List Stmt} {result : ExecResult}
    (htail : ExecBlock config (wordLocal frame name amount)
      (marketBalanceStore evm id i (UInt256.sub (marketBalanceWord evm id i) amount)) tail result) :
    ExecBlock config frame evm (claimFeeSubtractStmts i name ++ tail) result := by
  have he : evalExprs? config frame evm [.var "amount"] = .ok [.int amount.toNat] := by
    simp only [evalExprs?, evalWordLocal ha, EvalResult.bind, bind, pure]
  refine ExecBlock.consNormal (callToUint128 hc he hamount) ?_
  have hm' : (wordLocal frame name amount).locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType) := by
    rw [wordLocal_get_ne _ _ _ _ hne, hm]
  exact ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm)
    (evalCheckedSub128 (evalMarketBalance i hm') (evalWordLocal (wordLocal_get _ _ _))
      (marketBalanceWord_lt evm id i) hle)
    (assignMarketBalance i _ hm')) htail

theorem claimFeeSubtractUnderflow {frame : Frame} {evm : EVM.State} {id amount : UInt256}
    (i : Fin 3) (name : Ident) (hne : name ≠ "_marketState")
    (hc : frame.contract = contract)
    (ha : frame.locals.get? "amount" = some (.int amount.toNat))
    (hm : frame.locals.get? "_marketState" = some (.storageRef (marketStateRef id) marketStateType))
    (hamount : amount.toNat < 2^128) (hlt : (marketBalanceWord evm id i).toNat < amount.toNat)
    (tail : List Stmt) :
    ExecBlock config frame evm (claimFeeSubtractStmts i name ++ tail) .reverted := by
  have he : evalExprs? config frame evm [.var "amount"] = .ok [.int amount.toNat] := by
    simp only [evalExprs?, evalWordLocal ha, EvalResult.bind, bind, pure]
  refine ExecBlock.consNormal (callToUint128 hc he hamount) ?_
  have hm' : (wordLocal frame name amount).locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType) := by
    rw [wordLocal_get_ne _ _ _ _ hne, hm]
  exact ExecBlock.consRevert (ExecStmt.assignExprRevert
    (evalCheckedSubUnderflow ⟨128, by decide⟩
      (evalMarketBalance i hm') (evalWordLocal (wordLocal_get _ _ _)) hlt))

theorem claimFeeSubtractStatic {frame : Frame} {evm : EVM.State} {id amount : UInt256}
    (i : Fin 3) (name : Ident) (hne : name ≠ "_marketState")
    (hc : frame.contract = contract)
    (ha : frame.locals.get? "amount" = some (.int amount.toNat))
    (hm : frame.locals.get? "_marketState" = some (.storageRef (marketStateRef id) marketStateType))
    (hamount : amount.toNat < 2^128) (hle : amount.toNat ≤ (marketBalanceWord evm id i).toNat)
    (hperm : evm.executionEnv.perm = false) (tail : List Stmt) :
    ExecBlock config frame evm (claimFeeSubtractStmts i name ++ tail) .staticViolation := by
  have he : evalExprs? config frame evm [.var "amount"] = .ok [.int amount.toNat] := by
    simp only [evalExprs?, evalWordLocal ha, EvalResult.bind, bind, pure]
  refine ExecBlock.consNormal (callToUint128 hc he hamount) ?_
  have hm' : (wordLocal frame name amount).locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType) := by
    rw [wordLocal_get_ne _ _ _ _ hne, hm]
  exact ExecBlock.consStatic (ExecStmt.assignStatic
    (evalCheckedSub128 (evalMarketBalance i hm') (evalWordLocal (wordLocal_get _ _ _))
      (marketBalanceWord_lt evm id i) hle) (assignMarketBalance i _ hm') hperm)

end Benchmarks.Midnight
