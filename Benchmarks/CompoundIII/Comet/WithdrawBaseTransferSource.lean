import Benchmarks.CompoundIII.Comet.WithdrawBaseTailModel
import Benchmarks.CompoundIII.Comet.PrincipalTransferEventSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem withdrawBaseTransferEvent_source {v src recipient amount supplied}
    (frame : Frame) (evm : EVM.State) (hf : WithdrawBaseArgs frame v src recipient amount supplied)
    (hsupplied : supplied.toNat < 2^104) :
    ∃ final, ExecStmt config frame evm withdrawBaseTransferEvent (.ok final evm) := by
  exact ⟨_, principalTransferEvent_source frame evm false src supplied
    "src" "withdrawAmount" "__c8" (by decide) hf.contract hf.src hf.supplied hf.index hsupplied⟩

theorem withdrawBaseTransfer_source {v recipient amount evm result}
    (ht : WithdrawBaseTransfer v recipient amount evm result) (frame : Frame)
    (src : AccountAddress) (supplied : UInt256)
    (hf : WithdrawBaseArgs frame v src recipient amount supplied)
    (hsupplied : supplied.toNat < 2^104) :
    internalBlockResult config frame evm withdrawBaseTransferTail result := by
  have hcall {r} (hc : TransferOutTrace v.baseToken recipient amount evm r) :=
    transferOut_call hc frame (.immutable "baseToken") (.var "to") (.var "amount") "__c7"
      hf.contract (by simp only [evalExpr?, hf.immutables, immStore_get_baseToken, EvalResult.ofOption])
      (by simp only [evalExpr?, hf.recipient, EvalResult.ofOption])
      (by simp only [evalExpr?, hf.amount, EvalResult.ofOption]; rfl)
  cases ht with
  | failed ht => exact ExecBlock.consRevert (hcall ht)
  | @done evm' ht =>
    let ready := { frame with locals := frame.locals.insert "__c7" .unit }
    have hf' := hf.insert "__c7" .unit (by decide)
    obtain ⟨final, hevent⟩ := withdrawBaseTransferEvent_source ready evm' hf' hsupplied
    refine ⟨final, ExecBlock.consNormal (hcall ht)
      (ExecBlock.consNormal (ExecStmt.emit
        (vals := [.address src, .address recipient, .int amount.toNat]) ?_)
          (ExecBlock.consNormal hevent .nil))⟩
    simp only [evalExprs?, evalExpr?, hf'.src, hf'.recipient, hf'.amount,
      EvalResult.ofOption, pure, bind, EvalResult.bind]

end Benchmarks.CompoundIII.Comet
