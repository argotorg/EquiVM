import Examples.UniswapV2Pair.SafeTransferDynamicCallRuntime
import Examples.UniswapV2Pair.ReturnDataMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferDynamicEmptyReturnToRet_of_zeroSlot
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base out : ByteArray} {ptr aw value toWord token ret : UInt256} {R : List UInt256} {k C : Nat}
    (rd6595 : RD uniswapV2PairBytecode I g s0 ⟨6595⟩
      (⟨1⟩ :: (ptr + ⟨232⟩) :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ :: value :: toWord :: token :: ret :: R)
      (safeTransferDynamicCallMem2 base ptr toWord value) (safeTransferDynamicCallWords2 aw ptr) out acc k C)
    (hout : out.size = 0) (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hptrLo : 128 ≤ ptr.toNat) (haw : aw.toNat * 32 < UInt256.size) (hptr : ptr.toNat + 291 < UInt256.size)
    (hzero : (safeTransferDynamicCallMem2 base ptr toWord value).readWithPadding 96 32 = (⟨0⟩ : UInt256).toByteArray)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true) (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ret R
      (safeTransferDynamicCallMem2 base ptr toWord value) (safeTransferDynamicCallWords2 aw ptr) out acc k' C' := by
  obtain ⟨_, _, ⟨hb2, hc2⟩⟩ := safeTransferDynamicCallWords_bounds aw ptr haw hptr
  have hc96 : (⟨96⟩ : UInt256).toNat + 32 ≤ (safeTransferDynamicCallWords2 aw ptr).toNat * 32 := by
    change 96 + 32 ≤ _
    omega
  have hload : memoryWordLoad (safeTransferDynamicCallMem2 base ptr toWord value)
      (safeTransferDynamicCallWords2 aw ptr) ⟨96⟩ = ⟨0⟩ := by
    apply mloadWordValue_of_readWithPadding
    · change 96 < _
      rw [safeTransferDynamicCallMem2_size ptr toWord value (by omega) hgap (by omega)]
      omega
    · exact UInt256_mload_haw_of_cover _ _ hb2 hc96
    · exact hzero
  exact RD.uniswapSafeTransferEmptyReturnToRet rd6595 hout hload
    (UInt256_M_same_of_cover _ _ hb2 hc96) hret hov

end UniswapV2Pair
