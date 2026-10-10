import Benchmarks.UniswapV3.Pool.TickUpdateSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def tickUpdateOutsideWord (a : TickUpdateArgs) (old : UInt256) : UInt256 :=
  tickHistoryUpdate .seconds
    (tickHistoryUpdate .cumulative
      (tickHistoryUpdate .secondsPerLiquidity old a.secondsPerLiquidity)
      (EVM.wordOfInt a.cumulative)) a.time

theorem tickUpdateOutsideState_eq (a : TickUpdateArgs) (evm : EVM.State) :
    tickUpdateOutsideState a evm =
      modifyStorageWord (tickFeeOutsideState (tickFeeOutsideState evm a.tick false a.global0)
        a.tick true a.global1) (tickFieldSlot a.tick 3) (tickUpdateOutsideWord a) := by
  simp only [tickUpdateOutsideState, tickHistoryState, modifyStorageWord_comp]
  rfl

def tickUpdateOutsideMap (a : TickUpdateArgs) (σ : AccountMap) (ee : ExecutionEnv) : AccountMap :=
  let σ0 := sstoreAccountMap ee.codeOwner σ (tickFieldSlot a.tick 1) a.global0
  let σ1 := sstoreAccountMap ee.codeOwner σ0 (tickFieldSlot a.tick 2) a.global1
  sstoreAccountMap ee.codeOwner σ1 (tickFieldSlot a.tick 3)
    (tickUpdateOutsideWord a (solcSlotWordAt (tickFieldSlot a.tick 3) σ1 ee))

theorem SourceState.tickFeeOutside {s0 : EVM.State} {ee : ExecutionEnv} {σ : AccountMap}
    {evm : EVM.State} (hs : SourceState s0 ee σ evm) (tick : Int) (second : Bool) (word : UInt256) :
    SourceState s0 ee
      (sstoreAccountMap ee.codeOwner σ (tickFieldSlot tick (if second then 2 else 1)) word)
      (tickFeeOutsideState evm tick second word) := by
  simpa only [tickFeeOutsideState, hs.env] using
    hs.storageWrite (tickFieldSlot tick (if second then 2 else 1)) word

theorem SourceState.tickUpdateOutside {s0 : EVM.State} {ee : ExecutionEnv} {σ : AccountMap}
    {evm : EVM.State} (hs : SourceState s0 ee σ evm) (a : TickUpdateArgs) :
    SourceState s0 ee (tickUpdateOutsideMap a σ ee) (tickUpdateOutsideState a evm) := by
  rw [tickUpdateOutsideState_eq]
  have h0 := SourceState.tickFeeOutside hs a.tick false a.global0
  have h1 := SourceState.tickFeeOutside h0 a.tick true a.global1
  exact h1.readModifyWrite (tickFieldSlot a.tick 3) (tickUpdateOutsideWord a)

def tickLiquidityMap (σ : AccountMap) (ee : ExecutionEnv) (tick : Int) (net : Bool)
    (word : UInt256) : AccountMap :=
  sstoreAccountMap ee.codeOwner σ (tickClearBase tick)
    (protocolFeeUpdateWord net (solcSlotWordAt (tickClearBase tick) σ ee) word)

theorem SourceState.tickLiquidity {s0 : EVM.State} {ee : ExecutionEnv} {σ : AccountMap}
    {evm : EVM.State} (hs : SourceState s0 ee σ evm) (tick : Int) (net : Bool) (word : UInt256) :
    SourceState s0 ee (tickLiquidityMap σ ee tick net word) (tickLiquidityState evm tick net word) :=
  hs.readModifyWrite (tickClearBase tick) (fun old ↦ protocolFeeUpdateWord net old word)

end Benchmarks.UniswapV3.Pool
