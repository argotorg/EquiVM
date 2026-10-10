import Benchmarks.UniswapV3.Pool.TickUpdateRawModel
import Benchmarks.UniswapV3.Pool.TickUpdateStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def TickUpdateArgs.withRaw (a : TickUpdateArgs) (time maximum : UInt256) : TickUpdateArgs :=
  {a with time := time, maxLiquidity := maximum}

theorem TickUpdateArgs.TraceFits.withRaw {a : TickUpdateArgs} (h : a.TraceFits)
    (time maximum : UInt256) : (a.withRaw time maximum).TraceFits := h

-- LIBRARY CANDIDATE: storage packing ignores bits outside the field's width.
theorem packedFieldUpdate_mask (old value : UInt256) (offset width : Nat) :
    packedFieldUpdate old (UInt256.land value (UInt256.ofNat (2 ^ width - 1))) offset width =
      packedFieldUpdate old value offset width := by
  simp only [packedFieldUpdate, packedFieldValue, maskTwice]

theorem tickUpdateOutsideState_withRaw (a : TickUpdateArgs) (evm : EVM.State)
    (time maximum : UInt256)
    (ht : UInt256.land time (UInt256.ofNat (2 ^ 32 - 1)) = a.time) :
    tickUpdateOutsideState (a.withRaw time maximum) evm = tickUpdateOutsideState a evm := by
  have hstate (e : EVM.State) : tickHistoryState e a.tick .seconds time =
      tickHistoryState e a.tick .seconds a.time := by
    rw [← ht]
    simp only [tickHistoryState, tickHistoryUpdate, TickHistoryField.bits, packedFieldUpdate_mask]
  simpa only [tickUpdateOutsideState, TickUpdateArgs.withRaw] using hstate _

theorem tickUpdateInitializedState_withRaw (a : TickUpdateArgs) (evm : EVM.State)
    (time maximum : UInt256)
    (ht : UInt256.land time (UInt256.ofNat (2 ^ 32 - 1)) = a.time) :
    tickUpdateInitializedState (a.withRaw time maximum) evm = tickUpdateInitializedState a evm := by
  unfold tickUpdateInitializedState
  rw [tickUpdateOutsideState_withRaw a evm time maximum ht]
  rfl

theorem tickUpdateGrossState_withRaw (a : TickUpdateArgs) (evm : EVM.State)
    (time maximum : UInt256)
    (ht : UInt256.land time (UInt256.ofNat (2 ^ 32 - 1)) = a.time) :
    tickUpdateGrossState (a.withRaw time maximum) evm = tickUpdateGrossState a evm := by
  unfold tickUpdateGrossState
  rw [tickUpdateInitializedState_withRaw a evm time maximum ht]
  rfl

theorem tickUpdateNetResult_withRaw (a : TickUpdateArgs) (evm : EVM.State)
    (time maximum : UInt256) (subtract : Bool)
    (ht : UInt256.land time (UInt256.ofNat (2 ^ 32 - 1)) = a.time) :
    tickUpdateNetResult (a.withRaw time maximum) evm subtract =
      tickUpdateNetResult a evm subtract := by
  unfold tickUpdateNetResult tickUpdateNetBefore
  rw [tickUpdateGrossState_withRaw a evm time maximum ht]
  rfl

theorem tickUpdateFinalState_withRaw (a : TickUpdateArgs) (evm : EVM.State)
    (time maximum : UInt256)
    (ht : UInt256.land time (UInt256.ofNat (2 ^ 32 - 1)) = a.time) :
    tickUpdateFinalState (a.withRaw time maximum) evm = tickUpdateFinalState a evm := by
  unfold tickUpdateFinalState
  rw [tickUpdateNetResult_withRaw a evm time maximum _ ht,
    tickUpdateGrossState_withRaw a evm time maximum ht]
  rfl

end Benchmarks.UniswapV3.Pool
