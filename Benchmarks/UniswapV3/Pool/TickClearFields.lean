import Benchmarks.UniswapV3.Pool.PackedClear
import Benchmarks.UniswapV3.Pool.TickReferences
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def tickClearBase (tick : Int) : UInt256 := solcMappingSlot ⟨5⟩ (EVM.wordOfInt tick)

def tickClearGrossLoc (tick : Int) : StorageLoc :=
  {slot := tickClearBase tick, offset := 0, size := 16, hbound := by decide,
    type := .int (.uint ⟨128, by decide⟩)}

def tickClearNetLoc (tick : Int) : StorageLoc :=
  {slot := tickClearBase tick, offset := 16, size := 16, hbound := by decide,
    type := .int (.sint ⟨128, by decide⟩)}

def tickClearFee0Loc (tick : Int) : StorageLoc :=
  {slot := tickFieldSlot tick 1, offset := 0, size := 32, hbound := by decide,
    type := .int (.uint ⟨256, by decide⟩)}

def tickClearFee1Loc (tick : Int) : StorageLoc :=
  {slot := tickFieldSlot tick 2, offset := 0, size := 32, hbound := by decide,
    type := .int (.uint ⟨256, by decide⟩)}

def tickClearCumulativeLoc (tick : Int) : StorageLoc :=
  {slot := tickFieldSlot tick 3, offset := 0, size := 7, hbound := by decide,
    type := .int (.sint ⟨56, by decide⟩)}

def tickClearSecondsPerLiquidityLoc (tick : Int) : StorageLoc :=
  {slot := tickFieldSlot tick 3, offset := 7, size := 20, hbound := by decide,
    type := .int (.uint ⟨160, by decide⟩)}

def tickClearSecondsLoc (tick : Int) : StorageLoc :=
  {slot := tickFieldSlot tick 3, offset := 27, size := 4, hbound := by decide,
    type := .int (.uint ⟨32, by decide⟩)}

def tickClearInitializedLoc (tick : Int) : StorageLoc :=
  {slot := tickFieldSlot tick 3, offset := 31, size := 1, hbound := by decide,
    type := .bool}

theorem tickClearFields (tick : Int) (evm e0 e1 e2 e3 e4 e5 e6 e7 : EVM.State)
    (h0 : storageLocStore evm (tickClearGrossLoc tick) (.int 0) = some e0)
    (h1 : storageLocStore e0 (tickClearNetLoc tick) (.int 0) = some e1)
    (h2 : storageLocStore e1 (tickClearFee0Loc tick) (.int 0) = some e2)
    (h3 : storageLocStore e2 (tickClearFee1Loc tick) (.int 0) = some e3)
    (h4 : storageLocStore e3 (tickClearCumulativeLoc tick) (.int 0) = some e4)
    (h5 : storageLocStore e4 (tickClearSecondsPerLiquidityLoc tick) (.int 0) = some e5)
    (h6 : storageLocStore e5 (tickClearSecondsLoc tick) (.int 0) = some e6)
    (h7 : storageLocStore e6 (tickClearInitializedLoc tick) (.int 0) = some e7)
    : solidityClearStorage? storageBackend.locate? evm (tickReference tick) tickStorageType =
      .ok e7 := by
  have hl0 : storageBackend.locate? ⟨"ticks", [.mindex (.int tick), .field "liquidityGross"]⟩ =
      some (.leaf (tickClearGrossLoc tick)) := rfl
  have hl1 : storageBackend.locate? ⟨"ticks", [.mindex (.int tick), .field "liquidityNet"]⟩ =
      some (.leaf (tickClearNetLoc tick)) := rfl
  have hl2 : storageBackend.locate? ⟨"ticks", [.mindex (.int tick), .field "feeGrowthOutside0X128"]⟩ =
      some (.leaf (tickClearFee0Loc tick)) := rfl
  have hl3 : storageBackend.locate? ⟨"ticks", [.mindex (.int tick), .field "feeGrowthOutside1X128"]⟩ =
      some (.leaf (tickClearFee1Loc tick)) := rfl
  have hl4 : storageBackend.locate? ⟨"ticks", [.mindex (.int tick), .field "tickCumulativeOutside"]⟩ =
      some (.leaf (tickClearCumulativeLoc tick)) := rfl
  have hl5 : storageBackend.locate? ⟨"ticks", [.mindex (.int tick), .field "secondsPerLiquidityOutsideX128"]⟩ =
      some (.leaf (tickClearSecondsPerLiquidityLoc tick)) := rfl
  have hl6 : storageBackend.locate? ⟨"ticks", [.mindex (.int tick), .field "secondsOutside"]⟩ =
      some (.leaf (tickClearSecondsLoc tick)) := rfl
  have hl7 : storageBackend.locate? ⟨"ticks", [.mindex (.int tick), .field "initialized"]⟩ =
      some (.leaf (tickClearInitializedLoc tick)) := rfl
  simp only [tickStorageType, tickReference, solidityClearStorage?, solidityClearFields?,
    List.cons_append, List.nil_append,
    solidityLeafLoc?_of_leaf hl0, solidityLeafLoc?_of_leaf hl1,
    solidityLeafLoc?_of_leaf hl2, solidityLeafLoc?_of_leaf hl3,
    solidityLeafLoc?_of_leaf hl4, solidityLeafLoc?_of_leaf hl5,
    solidityLeafLoc?_of_leaf hl6, solidityLeafLoc?_of_leaf hl7,
    h0, h1, h2, h3, h4, h5, h6, h7, EvalResult.ofOption, bind, EvalResult.bind]

def tickClearState (evm : EVM.State) (tick : Int) : EVM.State :=
  let e0 := EVM.storageStore evm evm.executionEnv.codeOwner (tickClearBase tick) ⟨0⟩
  let e1 := EVM.storageStore e0 evm.executionEnv.codeOwner (tickFieldSlot tick 1) ⟨0⟩
  let e2 := EVM.storageStore e1 evm.executionEnv.codeOwner (tickFieldSlot tick 2) ⟨0⟩
  EVM.storageStore e2 evm.executionEnv.codeOwner (tickFieldSlot tick 3) ⟨0⟩

def tickClearMap (σ : AccountMap) (ee : ExecutionEnv) (tick : Int) : AccountMap :=
  let σ0 := sstoreAccountMap ee.codeOwner σ (tickClearBase tick) ⟨0⟩
  let σ1 := sstoreAccountMap ee.codeOwner σ0 (tickFieldSlot tick 1) ⟨0⟩
  let σ2 := sstoreAccountMap ee.codeOwner σ1 (tickFieldSlot tick 2) ⟨0⟩
  sstoreAccountMap ee.codeOwner σ2 (tickFieldSlot tick 3) ⟨0⟩

theorem tickClearState_executionEnv (evm : EVM.State) (tick : Int) :
    (tickClearState evm tick).executionEnv = evm.executionEnv := by
  simp only [tickClearState, storageStore_executionEnv]

theorem SourceState.tickClear {s0 : EVM.State} {ee : ExecutionEnv} {σ : AccountMap}
    {evm : EVM.State} (hs : SourceState s0 ee σ evm) (tick : Int) :
    SourceState s0 ee (tickClearMap σ ee tick) (tickClearState evm tick) := by
  have h0 := hs.storageWrite (tickClearBase tick) ⟨0⟩
  have h1 := h0.storageWrite (tickFieldSlot tick 1) ⟨0⟩
  have h2 := h1.storageWrite (tickFieldSlot tick 2) ⟨0⟩
  have h3 := h2.storageWrite (tickFieldSlot tick 3) ⟨0⟩
  simpa only [tickClearState, tickClearMap, hs.env] using h3

end Benchmarks.UniswapV3.Pool
