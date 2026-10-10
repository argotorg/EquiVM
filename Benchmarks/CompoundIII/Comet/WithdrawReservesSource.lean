import Benchmarks.CompoundIII.Comet.WithdrawReservesTailSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem withdrawReservesTrace_source {v : CometWithExtendedAssetListImmutables}
    {evm : EVM.State} {recipient : AccountAddress} {amount : UInt256} {result : Option EVM.State}
    (ht : WithdrawReservesTrace v recipient amount evm result) :
    WithdrawReservesBlockResult (withdrawReservesEntry v evm recipient amount) evm
      ([.require withdrawReservesAuth, .internalCall "getReserves_body" [] "reserves"] ++
        withdrawReservesTail) result := by
  have hguard := withdrawReservesAuth_eval v evm
    (withdrawReservesEntry v evm recipient amount).locals
  cases ht with
  | unauthorized ha =>
    rw [decide_eq_false ha] at hguard
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  | reservesFailed ha ht =>
    rw [decide_eq_true ha] at hguard
    apply ExecBlock.consNormal (ExecStmt.requireTrue hguard)
    exact ExecBlock.consRevert
      (reservesTrace_call ht (withdrawReservesEntry v evm recipient amount) "reserves" rfl rfl)
  | @reservesOk evm' reserves result ha ht ht' =>
    rw [decide_eq_true ha] at hguard
    have hc := reservesTrace_call ht (withdrawReservesEntry v evm recipient amount)
      "reserves" rfl rfl
    have hb := withdrawReservesAfter_source ht' evm
    cases result with
    | none =>
      exact ExecBlock.consNormal (ExecStmt.requireTrue hguard) (ExecBlock.consNormal hc hb)
    | some evm'' =>
      simp only [WithdrawReservesBlockResult] at hb ⊢
      by_cases hp : evm''.executionEnv.perm = true
      · rw [if_pos hp] at hb ⊢
        obtain ⟨final, hb⟩ := hb
        exact ⟨final, ExecBlock.consNormal (ExecStmt.requireTrue hguard)
          (ExecBlock.consNormal hc hb)⟩
      · rw [if_neg hp] at hb ⊢
        exact ExecBlock.consNormal (ExecStmt.requireTrue hguard) (ExecBlock.consNormal hc hb)

def WithdrawReservesSourceResult (v : CometWithExtendedAssetListImmutables)
    (recipient : AccountAddress) (amount : UInt256) (evm : EVM.State)
    (result : Option EVM.State) : Prop :=
  match result with
  | none => ExecTransitionBody config contract evm (withdrawReservesArgs recipient amount)
      withdrawReservesTransition.body .reverted (immStore v)
  | some evm' => if evm'.executionEnv.perm = true then
      ∃ final, ExecTransitionBody config contract evm (withdrawReservesArgs recipient amount)
        withdrawReservesTransition.body (.returned final evm' none) (immStore v)
    else ExecTransitionBody config contract evm (withdrawReservesArgs recipient amount)
      withdrawReservesTransition.body .staticViolation (immStore v)

theorem withdrawReserves_source {v : CometWithExtendedAssetListImmutables}
    {evm : EVM.State} {recipient : AccountAddress} {amount : UInt256} {result : Option EVM.State}
    (ht : WithdrawReservesTrace v recipient amount evm result)
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < 2^255 + 4) :
    WithdrawReservesSourceResult v recipient amount evm result := by
  have hb := withdrawReservesTrace_source ht
  cases result with
  | none =>
    unfold WithdrawReservesSourceResult
    rw [withdrawReservesTransition_body]
    exact ExecFuncBody.execBlockRevert ((calldataPrologue_ok hv hhi).run hb)
  | some evm' =>
    simp only [WithdrawReservesSourceResult, WithdrawReservesBlockResult] at hb ⊢
    by_cases hp : evm'.executionEnv.perm = true
    · rw [if_pos hp] at hb ⊢
      obtain ⟨final, hb⟩ := hb
      refine ⟨final, ?_⟩
      rw [withdrawReservesTransition_body]
      exact ExecFuncBody.execBlockOK ((calldataPrologue_ok hv hhi).run hb)
    · rw [if_neg hp] at hb ⊢
      rw [withdrawReservesTransition_body]
      exact ExecFuncBody.execBlockStatic ((calldataPrologue_ok hv hhi).run hb)

end Benchmarks.CompoundIII.Comet
