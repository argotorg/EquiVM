import Benchmarks.UniswapV3.Pool.CallbackEncoding

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: encode a signed integer using its explicit ABI range bound.
theorem encodeABIValue_sint_of_bounds (width : ABI.BitWidth) (i : Int)
    (h : -(2 ^ (width.val - 1) : Int) ≤ i ∧ i < 2 ^ (width.val - 1)) :
    encodeABIValue? (.elem (.int (.sint width))) (.int i) =
      some (EVM.Word.toBytesBE (EVM.wordOfInt i)) := by
  simp only [encodeABIValue?, encodeABIWord?, if_neg (Nat.ne_of_gt width.property.1),
    EVM.twoPow, Int.ofNat_eq_natCast, Int.natCast_pow, Nat.cast_ofNat,
    if_pos h, bind, Option.bind]

def swapCallbackCalldata (amount0 amount1 : UInt256) (data : ByteArray) : ByteArray :=
  selectorBytes 0xfa 0x46 0x1e 0x33 ++ wordPairBytesPayload amount0 amount1 data

theorem swapCallbackEncode (amount0 amount1 : Int) (data : ByteArray)
    (h0 : -(2 ^ 255 : Int) ≤ amount0 ∧ amount0 < 2 ^ 255)
    (h1 : -(2 ^ 255 : Int) ≤ amount1 ∧ amount1 < 2 ^ 255) :
    externalABI.encode? "uniswapV3SwapCallback" [.int amount0, .int amount1, .bytes data] =
      some (swapCallbackCalldata (EVM.wordOfInt amount0) (EVM.wordOfInt amount1) data) :=
  encodeCall_of_encodeReturn (selectorBytes 0xfa 0x46 0x1e 0x33)
    (wordPairBytesEncoding (.elem (.int (.sint ⟨256, by decide⟩)))
      (.elem (.int (.sint ⟨256, by decide⟩))) _ _ _ _ data rfl rfl rfl rfl
      (encodeABIValue_sint_of_bounds ⟨256, by decide⟩ amount0 h0)
      (encodeABIValue_sint_of_bounds ⟨256, by decide⟩ amount1 h1))

theorem swapCallbackDecode (out : ByteArray) :
    externalABI.decode? "uniswapV3SwapCallback" out = some [] := rfl

theorem swapCallbackCalldata_size (a b : UInt256) (data : ByteArray) :
    (swapCallbackCalldata a b data).size = 132 + paddedSize data.size := by
  rw [swapCallbackCalldata, ByteArray.size_append, wordPairBytesPayload_size]
  change 4 + (128 + paddedSize data.size) = 132 + paddedSize data.size
  omega

end Benchmarks.UniswapV3.Pool
