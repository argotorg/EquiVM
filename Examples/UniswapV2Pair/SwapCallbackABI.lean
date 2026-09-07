import Examples.UniswapV2Pair.ExternalCalls
import Examples.UniswapV2Pair.SwapTransfersSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev swapCallbackArgs (senderAddr : AccountAddress) (amount0Out amount1Out : UInt256) (data : ByteArray) : List Value :=
  [.address senderAddr, uniswapUint256Value amount0Out, uniswapUint256Value amount1Out, .bytes data]
noncomputable def swapCallbackCalldata (senderAddr : AccountAddress) (amount0Out amount1Out : UInt256) (data : ByteArray) : ByteArray :=
  uniswapV2CallSelector ++ (UInt256.ofNat senderAddr.val).toByteArray ++ amount0Out.toByteArray ++ amount1Out.toByteArray ++
    (⟨128⟩ : UInt256).toByteArray ++ (UInt256.ofNat data.size).toByteArray ++ (ABI.padRightToWord data.toList).toByteArray

theorem swapCallbackCalldata_encode (senderAddr : AccountAddress) (amount0Out amount1Out : UInt256) (data : ByteArray) :
    config.externalABI.encode? "uniswapV2Call" (swapCallbackArgs senderAddr amount0Out amount1Out data) =
      some (swapCallbackCalldata senderAddr amount0Out amount1Out data) := by
  have ha0 : EVM.word amount0Out.toNat = amount0Out := u256_ofNat_toNat amount0Out
  have ha1 : EVM.word amount1Out.toNat = amount1Out := u256_ofNat_toNat amount1Out
  have hs : EVM.word senderAddr.val = UInt256.ofNat senderAddr.val := by apply u256_inj; rfl
  have hlo0 : amount0Out.toNat < EVM.twoPow 256 := amount0Out.val.isLt
  have hlo1 : amount1Out.toNat < EVM.twoPow 256 := amount1Out.val.isLt
  change uniswapExternalABI.encode? "uniswapV2Call" _ = _
  unfold uniswapExternalABI ABI.encodeCallWithSelector? ABI.encodeABIValues? swapCallbackArgs swapCallbackCalldata
  simp [addr, uint256, uint256Int, uniswapUint256Value, ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
    ABI.isDynamicABIType, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.encodeABIValuesFrom?,
    ABI.natBytes, hlo0, hlo1, ha0, ha1, hs, word_toBytesBE_toByteArray_eq_toByteArray]
  simp only [ByteArray.append_assoc]
  rfl

end UniswapV2Pair
