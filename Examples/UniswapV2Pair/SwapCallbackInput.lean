import Examples.UniswapV2Pair.SwapCallbackSource
import Examples.UniswapV2Pair.SwapDecodeRuntime
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

theorem swapDataBytes_eq_runtimeExtract {I : ExecutionEnv} (hoff : ¬ solcLegacyMaxU32 < swapDataOffset I) :
    swapDataBytes I = I.calldata.extract (swapRuntimePayloadPtr I).toNat
      ((swapRuntimePayloadPtr I).toNat + (swapDataSizeWord I).toNat) := by
  rw [(swapRuntimeWords_eq hoff).2]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [ByteArray.data_extract, Array.toList_extract,
    List.extract_eq_take_drop, byteArray_toList_eq, List.drop_drop]
  rw [show 4 + swapDataOffset I + 32 + (swapDataSizeWord I).toNat - (4 + swapDataOffset I + 32) = swapDataSize I by
    change 4 + swapDataOffset I + 32 + swapDataSize I - (4 + swapDataOffset I + 32) = swapDataSize I
    omega]
  simp only [Nat.add_assoc]

theorem swapAfterTransfersFrame_callbackGets (evm : EVM.State) (I : ExecutionEnv) :
    (swapAfterTransfersFrame { contract := contract, locals := swapTokenStore evm I }
      (swapAmount0OutWord I) (swapAmount1OutWord I)).locals.get? "to" = some (swapToValue I) ∧
    (swapAfterTransfersFrame { contract := contract, locals := swapTokenStore evm I }
      (swapAmount0OutWord I) (swapAmount1OutWord I)).locals.get? "amount0Out" = some (uniswapUint256Value (swapAmount0OutWord I)) ∧
    (swapAfterTransfersFrame { contract := contract, locals := swapTokenStore evm I }
      (swapAmount0OutWord I) (swapAmount1OutWord I)).locals.get? "amount1Out" = some (uniswapUint256Value (swapAmount1OutWord I)) ∧
    (swapAfterTransfersFrame { contract := contract, locals := swapTokenStore evm I }
      (swapAmount0OutWord I) (swapAmount1OutWord I)).locals.get? "data" = some (swapDataValue I) := by
  obtain ⟨_, _, hto, ha0, ha1⟩ := swapTokenStore_transferGets evm I
  refine ⟨?_, ?_, ?_, swapAfterTransfersFrame_data evm I⟩
  · rw [swapAfterTransfersFrame_get_ne _ _ _ _ (by decide) (by decide)]; exact hto
  · rw [swapAfterTransfersFrame_get_ne _ _ _ _ (by decide) (by decide)]; exact ha0
  · rw [swapAfterTransfersFrame_get_ne _ _ _ _ (by decide) (by decide)]; exact ha1

end UniswapV2Pair
