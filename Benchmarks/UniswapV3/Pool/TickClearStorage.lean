import Benchmarks.UniswapV3.Pool.TickClearFields

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem tickClearStorage (evm : EVM.State) (tick : Int) :
    solidityClearStorage? storageBackend.locate? evm (tickReference tick) tickStorageType =
      .ok (tickClearState evm tick) := by
  let e0 := clearPackedPrefix evm (tickClearBase tick) 128
  let e1 := EVM.storageStore evm evm.executionEnv.codeOwner (tickClearBase tick) ⟨0⟩
  let e2 := EVM.storageStore e1 evm.executionEnv.codeOwner (tickFieldSlot tick 1) ⟨0⟩
  let e3 := EVM.storageStore e2 evm.executionEnv.codeOwner (tickFieldSlot tick 2) ⟨0⟩
  let e4 := clearPackedPrefix e3 (tickFieldSlot tick 3) 56
  let e5 := clearPackedPrefix e3 (tickFieldSlot tick 3) 216
  let e6 := clearPackedPrefix e3 (tickFieldSlot tick 3) 248
  have h0 : storageLocStore evm (tickClearGrossLoc tick) (.int 0) = some e0 :=
    storageLocStore_clearLow evm (tickClearGrossLoc tick) rfl rfl
  have h1 : storageLocStore e0 (tickClearNetLoc tick) (.int 0) = some e1 := by
    have h := storageLocStore_clearMore evm (tickClearNetLoc tick) rfl
    change storageLocStore e0 (tickClearNetLoc tick) (.int 0) =
      some (clearPackedPrefix evm (tickClearBase tick) 256) at h
    simpa only [clearPackedPrefix_full] using h
  have h2 : storageLocStore e1 (tickClearFee0Loc tick) (.int 0) = some e2 := by
    have h := storageLocStore_clearLow e1 (tickClearFee0Loc tick) rfl rfl
    change storageLocStore e1 (tickClearFee0Loc tick) (.int 0) =
      some (clearPackedPrefix e1 (tickFieldSlot tick 1) 256) at h
    simpa only [clearPackedPrefix_full, e1, e2, storageStore_executionEnv] using h
  have h3 : storageLocStore e2 (tickClearFee1Loc tick) (.int 0) = some e3 := by
    have h := storageLocStore_clearLow e2 (tickClearFee1Loc tick) rfl rfl
    change storageLocStore e2 (tickClearFee1Loc tick) (.int 0) =
      some (clearPackedPrefix e2 (tickFieldSlot tick 2) 256) at h
    simpa only [clearPackedPrefix_full, e1, e2, e3, storageStore_executionEnv] using h
  have h4 : storageLocStore e3 (tickClearCumulativeLoc tick) (.int 0) = some e4 :=
    storageLocStore_clearLow e3 (tickClearCumulativeLoc tick) rfl rfl
  have h5 : storageLocStore e4 (tickClearSecondsPerLiquidityLoc tick) (.int 0) = some e5 :=
    storageLocStore_clearMore e3 (tickClearSecondsPerLiquidityLoc tick) rfl
  have h6 : storageLocStore e5 (tickClearSecondsLoc tick) (.int 0) = some e6 :=
    storageLocStore_clearMore e3 (tickClearSecondsLoc tick) rfl
  have h7 : storageLocStore e6 (tickClearInitializedLoc tick) (.int 0) =
      some (tickClearState evm tick) := by
    have h := storageLocStore_clearMore e3 (tickClearInitializedLoc tick) rfl
    change storageLocStore e6 (tickClearInitializedLoc tick) (.int 0) =
      some (clearPackedPrefix e3 (tickFieldSlot tick 3) 256) at h
    simpa only [clearPackedPrefix_full, tickClearState, e1, e2, e3,
      storageStore_executionEnv] using h
  exact tickClearFields tick evm e0 e1 e2 e3 e4 e5 e6 _ h0 h1 h2 h3 h4 h5 h6 h7

end Benchmarks.UniswapV3.Pool
