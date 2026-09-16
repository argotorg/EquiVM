import Examples.UniswapV2Pair.SwapCallbackMemory
import Examples.UniswapV2Pair.SwapCallbackCallRuntime
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapSwapCallbackPrepared
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {ptr aw token1 token0 scratch1 scratch0 reserve1 reserve0
      dataLen dataPtr toWord amount1Out amount0Out : UInt256} {R : List UInt256} {k C : Nat}
    (rd1911 : RD uniswapV2PairBytecode I g s0 ⟨1911⟩
      (token1 :: token0 :: scratch1 :: scratch0 :: reserve1 :: reserve0 :: dataLen :: dataPtr ::
        toWord :: amount1Out :: amount0Out :: R) mem aw rdata acc k C)
    (hready : SafeTransferMemoryReady mem aw ptr)
    (hdata : dataPtr.toNat + dataLen.toNat ≤ I.calldata.size) (hlen : dataLen.toNat ≠ 0)
    (hfit : ptr.toNat + dataLen.toNat + 227 < UInt256.size) (hov : R.length + 29 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨2054⟩
      (UInt256.land solcAddrMask toWord :: UInt256.land solcAddrMask toWord :: ⟨0⟩ :: ptr ::
        swapCallbackCallLen ptr dataLen :: ptr :: ⟨0⟩ :: ((ptr + ⟨164⟩) + swapCallbackPaddedLen dataLen) ::
        ⟨282191964⟩ :: UInt256.land solcAddrMask toWord ::
        token1 :: token0 :: scratch1 :: scratch0 :: reserve1 :: reserve0 :: dataLen :: dataPtr ::
        toWord :: amount1Out :: amount0Out :: R)
      (swapCallbackMem I mem ptr amount0Out amount1Out dataPtr dataLen) (swapCallbackWords aw ptr dataLen) rdata acc k' C' := by
  have hcover : (⟨64⟩ : UInt256).toNat + 32 ≤ aw.toNat * 32 := hready.wordsLo
  have hload : memoryWordLoad mem aw ⟨64⟩ = ptr :=
    mloadWordValue_of_readWithPadding (by change 64 < _; have := hready.sizeLo; omega)
      (UInt256_mload_haw_of_cover _ _ hready.wordsHi hcover) hready.read64
  have hw64 : memoryWordActiveWords aw ⟨64⟩ = aw := UInt256_M_same_of_cover _ _ hready.wordsHi hcover
  obtain ⟨_, _, rd2001⟩ := uniswapSwapCallbackHeadStored rd1911 hload hw64 (by omega)
  have hclean : UInt256.land solcAddrMask (UInt256.ofNat I.source.val) = UInt256.ofNat I.source.val := by
    rw [u256_land_comm]
    exact solcAddrMask_clean (solcSourceWord_canonical I)
  rw [hclean] at rd2001
  obtain ⟨_, _, rd2041⟩ := uniswapSwapCallbackPayloadCopied rd2001 (by simp only [List.length_cons]; omega)
  obtain ⟨hload', hw64'⟩ := swapCallbackMem_mload64 ptr amount0Out amount1Out dataPtr dataLen hready hdata hlen hfit
  exact uniswapSwapCallbackCallPrepared rd2041 hload' hw64' (by simp only [List.length_cons]; omega)

end UniswapV2Pair
