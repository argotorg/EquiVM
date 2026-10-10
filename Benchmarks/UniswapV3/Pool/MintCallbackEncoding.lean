import Benchmarks.UniswapV3.Pool.CallbackEncoding

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def mintCallbackCalldata (amount0 amount1 : UInt256) (data : ByteArray) : ByteArray :=
  selectorBytes 0xd3 0x48 0x79 0x97 ++ wordPairBytesPayload amount0 amount1 data

theorem mintCallbackEncode (amount0 amount1 : UInt256) (data : ByteArray) :
    externalABI.encode? "uniswapV3MintCallback"
      [.int (Int.ofNat amount0.toNat), .int (Int.ofNat amount1.toNat), .bytes data] =
      some (mintCallbackCalldata amount0 amount1 data) :=
  encodeCall_of_encodeReturn (selectorBytes 0xd3 0x48 0x79 0x97)
    (wordPairBytesEncoding abiUInt256 abiUInt256 _ _ amount0 amount1 data rfl rfl rfl rfl
      (encodeABIValue_uint256 amount0) (encodeABIValue_uint256 amount1))

theorem mintCallbackDecode (out : ByteArray) :
    externalABI.decode? "uniswapV3MintCallback" out = some [] := rfl

theorem mintCallbackCalldata_size (a b : UInt256) (data : ByteArray) :
    (mintCallbackCalldata a b data).size = 132 + paddedSize data.size := by
  rw [mintCallbackCalldata, ByteArray.size_append, wordPairBytesPayload_size]
  change 4 + (128 + paddedSize data.size) = 132 + paddedSize data.size
  omega

end Benchmarks.UniswapV3.Pool
