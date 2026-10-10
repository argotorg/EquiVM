import Benchmarks.UniswapV3.Pool.TickCrossModel
import Benchmarks.UniswapV3.Pool.TickUpdateStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def tickCrossOutsideWord (a : TickCrossArgs) (old : UInt256) : UInt256 :=
  tickCrossHistoryWord a .seconds
    (tickCrossHistoryWord a .cumulative (tickCrossHistoryWord a .secondsPerLiquidity old))

theorem tickCrossState_eq (evm : EVM.State) (a : TickCrossArgs) :
    tickCrossState evm a =
      modifyStorageWord (tickCrossFeeState (tickCrossFeeState evm a false) a true)
        (tickFieldSlot a.tick 3) (tickCrossOutsideWord a) := by
  simp only [tickCrossState, tickCrossHistoryState, modifyStorageWord_comp]
  rfl

def tickCrossFeeMap (a : TickCrossArgs) (second : Bool) (σ : AccountMap) (ee : ExecutionEnv) :
    AccountMap :=
  sstoreAccountMap ee.codeOwner σ (tickFieldSlot a.tick (if second then 2 else 1))
    (tickCrossFeeWord a second σ ee)

def tickCrossFeesMap (a : TickCrossArgs) (σ : AccountMap) (ee : ExecutionEnv) : AccountMap :=
  tickCrossFeeMap a true (tickCrossFeeMap a false σ ee) ee

def tickCrossMap (a : TickCrossArgs) (σ : AccountMap) (ee : ExecutionEnv) : AccountMap :=
  let σ1 := tickCrossFeesMap a σ ee
  sstoreAccountMap ee.codeOwner σ1 (tickFieldSlot a.tick 3)
    (tickCrossOutsideWord a (solcSlotWordAt (tickFieldSlot a.tick 3) σ1 ee))

theorem SourceState.tickCrossFee {s0 : EVM.State} {ee : ExecutionEnv} {σ : AccountMap}
    {evm : EVM.State} (hs : SourceState s0 ee σ evm) (a : TickCrossArgs) (second : Bool) :
    SourceState s0 ee (tickCrossFeeMap a second σ ee) (tickCrossFeeState evm a second) := by
  unfold tickCrossFeeState tickCrossFeeMap
  rw [← hs.accounts, hs.env]
  exact SourceState.tickFeeOutside hs a.tick second _

theorem SourceState.tickCross {s0 : EVM.State} {ee : ExecutionEnv} {σ : AccountMap}
    {evm : EVM.State} (hs : SourceState s0 ee σ evm) (a : TickCrossArgs) :
    SourceState s0 ee (tickCrossMap a σ ee) (tickCrossState evm a) := by
  rw [tickCrossState_eq]
  exact (SourceState.tickCrossFee (SourceState.tickCrossFee hs a false) a true).readModifyWrite
    (tickFieldSlot a.tick 3) (tickCrossOutsideWord a)

end Benchmarks.UniswapV3.Pool
