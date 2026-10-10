import Benchmarks.UniswapV3.Pool.TickLogChoiceSource
import Benchmarks.UniswapV3.Pool.SourceContract

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem tickLogBoundsReadySource (imms : Store) (evm : EVM.State) (price : UInt256)
    (hp : price.toNat < 2 ^ 160) (hv : tickLogValid price) :
    ∃ frame, ExecBlock config (tickLogFrame imms price) evm (tickLogFunction.body.take 74)
        (.ok frame evm) ∧ frame.contract = contract ∧
      frame.locals.get? "tickLow" = some (.int (tickLogLow (tickLogResult price))) ∧
      frame.locals.get? "tickHi" = some (.int (tickLogHigh (tickLogResult price))) ∧
      frame.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)) ∧
      frame.locals.get? "__cond1" = some (.int 0) ∧
      frame.locals.get? "tick" = some (.int 0) := by
  obtain ⟨base, hseries, hl, hp', ht⟩ := tickLogSeriesSource imms evm price hp hv
  generalize hlog : tickLogResult price = log at hl ⊢
  have hc : base.contract = contract := execBlock_contract hseries
  have hbounds := tickLogBoundsSource (evm := evm) log hl
  have hvalues := tickLogBoundsFrame_values base log
  refine ⟨tickLogBoundsFrame base log, ?_, hc, hvalues.1, hvalues.2.1, ?_, hvalues.2.2, ?_⟩
  · change ExecBlock _ _ _ (tickLogFunction.body.take 70 ++
      (tickLogFunction.body.drop 70).take 4) _
    exact execBlock_append_ok hseries hbounds
  · rw [tickLogBoundsFrame_preserves base log "sqrtPriceX96"
      (by decide) (by decide) (by decide) (by decide)]
    exact hp'
  · rw [tickLogBoundsFrame_preserves base log "tick"
      (by decide) (by decide) (by decide) (by decide)]
    exact ht

theorem tickLogReturns (imms : Store) (evm : EVM.State) (price : UInt256)
    (hp : price.toNat < 2 ^ 160) (hv : tickLogValid price)
    (hs : tickLogSafe (tickLogResult price)) :
    ∃ out, ExecFuncBody config (tickLogFrame imms price) evm tickLogFunction.body
      (.returned out evm (some [.int (tickLogChoice (tickLogResult price) price)])) := by
  obtain ⟨frame, hprefix, hc, hl, hh, hp', hcond, ht⟩ :=
    tickLogBoundsReadySource imms evm price hp hv
  generalize hlog : tickLogResult price = log at hs hl hh ⊢
  obtain ⟨out, hfinish⟩ := tickLogChoiceSource log price hc hl hh hp' hcond ht hs
  refine ⟨out, ExecFuncBody.execBlockRet ?_⟩
  rw [← List.take_append_drop 74 tickLogFunction.body]
  exact execBlock_append_ok hprefix hfinish

theorem tickLogCalleeReverts (imms : Store) (evm : EVM.State) (price : UInt256)
    (hp : price.toNat < 2 ^ 160) (hv : tickLogValid price)
    (hs : ¬ tickLogSafe (tickLogResult price)) :
    ExecFuncBody config (tickLogFrame imms price) evm tickLogFunction.body .reverted := by
  obtain ⟨frame, hprefix, hc, hl, hh, _⟩ := tickLogBoundsReadySource imms evm price hp hv
  generalize hlog : tickLogResult price = log at hs hl hh
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 74 tickLogFunction.body]
  exact execBlock_append_ok hprefix (tickLogChoiceSourceReverts log hc hl hh hs)

end Benchmarks.UniswapV3.Pool
