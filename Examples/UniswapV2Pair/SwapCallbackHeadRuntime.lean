import Examples.UniswapV2Pair.SwapTransfersRuntime
import Examples.UniswapV2Pair.MemorySteps
import Examples.UniswapV2Pair.MintCommon
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev swapCallbackSelectorWord : UInt256 := UInt256.shiftLeft ⟨282191964⟩ ⟨224⟩
noncomputable def swapCallbackHeadMem0 (mem : ByteArray) (ptr _senderWord _amount0Out _amount1Out _dataLen : UInt256) : ByteArray :=
  (swapCallbackSelectorWord : UInt256).toByteArray.write 0 mem ptr.toNat 32
abbrev swapCallbackHeadWords0 (aw ptr : UInt256) : UInt256 :=
  memoryWordActiveWords aw ptr
noncomputable def swapCallbackHeadMem1 (mem : ByteArray) (ptr senderWord amount0Out amount1Out dataLen : UInt256) : ByteArray :=
  (senderWord : UInt256).toByteArray.write 0 (swapCallbackHeadMem0 mem ptr senderWord amount0Out amount1Out dataLen) (ptr + ⟨4⟩).toNat 32
abbrev swapCallbackHeadWords1 (aw ptr : UInt256) : UInt256 :=
  memoryWordActiveWords (swapCallbackHeadWords0 aw ptr) (ptr + ⟨4⟩)
noncomputable def swapCallbackHeadMem2 (mem : ByteArray) (ptr senderWord amount0Out amount1Out dataLen : UInt256) : ByteArray :=
  (amount0Out : UInt256).toByteArray.write 0 (swapCallbackHeadMem1 mem ptr senderWord amount0Out amount1Out dataLen) (ptr + ⟨36⟩).toNat 32
abbrev swapCallbackHeadWords2 (aw ptr : UInt256) : UInt256 :=
  memoryWordActiveWords (swapCallbackHeadWords1 aw ptr) (ptr + ⟨36⟩)
noncomputable def swapCallbackHeadMem3 (mem : ByteArray) (ptr senderWord amount0Out amount1Out dataLen : UInt256) : ByteArray :=
  (amount1Out : UInt256).toByteArray.write 0 (swapCallbackHeadMem2 mem ptr senderWord amount0Out amount1Out dataLen) (ptr + ⟨68⟩).toNat 32
abbrev swapCallbackHeadWords3 (aw ptr : UInt256) : UInt256 :=
  memoryWordActiveWords (swapCallbackHeadWords2 aw ptr) (ptr + ⟨68⟩)
noncomputable def swapCallbackHeadMem4 (mem : ByteArray) (ptr senderWord amount0Out amount1Out dataLen : UInt256) : ByteArray :=
  (⟨128⟩ : UInt256).toByteArray.write 0 (swapCallbackHeadMem3 mem ptr senderWord amount0Out amount1Out dataLen) (ptr + ⟨100⟩).toNat 32
abbrev swapCallbackHeadWords4 (aw ptr : UInt256) : UInt256 :=
  memoryWordActiveWords (swapCallbackHeadWords3 aw ptr) (ptr + ⟨100⟩)
noncomputable def swapCallbackHeadMem5 (mem : ByteArray) (ptr senderWord amount0Out amount1Out dataLen : UInt256) : ByteArray :=
  (dataLen : UInt256).toByteArray.write 0 (swapCallbackHeadMem4 mem ptr senderWord amount0Out amount1Out dataLen) (ptr + ⟨132⟩).toNat 32
abbrev swapCallbackHeadWords5 (aw ptr : UInt256) : UInt256 :=
  memoryWordActiveWords (swapCallbackHeadWords4 aw ptr) (ptr + ⟨132⟩)

set_option maxHeartbeats 1000000 in
theorem uniswapSwapCallbackHeadStored
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {ptr aw token1 token0 scratch1 scratch0 reserve1 reserve0
      dataLen dataPtr toWord amount1Out amount0Out : UInt256} {R : List UInt256} {k C : Nat}
    (rd1911 : RD uniswapV2PairBytecode I g s0 ⟨1911⟩
      (token1 :: token0 :: scratch1 :: scratch0 :: reserve1 :: reserve0 :: dataLen :: dataPtr ::
        toWord :: amount1Out :: amount0Out :: R) mem aw rdata acc k C)
    (hload : memoryWordLoad mem aw ⟨64⟩ = ptr) (hw64 : memoryWordActiveWords aw ⟨64⟩ = aw)
    (hov : R.length + 28 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨2001⟩
      ((ptr + ⟨132⟩) :: dataLen :: dataPtr :: (ptr + ⟨132⟩) :: (ptr + ⟨100⟩) :: (ptr + ⟨4⟩) ::
        dataLen :: dataPtr :: amount1Out :: amount0Out :: UInt256.ofNat I.source.val :: ⟨282191964⟩ ::
        UInt256.land solcAddrMask toWord :: token1 :: token0 :: scratch1 :: scratch0 ::
        reserve1 :: reserve0 :: dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R)
      (swapCallbackHeadMem5 mem ptr (UInt256.land solcAddrMask (UInt256.ofNat I.source.val))
        amount0Out amount1Out dataLen) (swapCallbackHeadWords5 aw ptr) rdata acc k' C' := by
  have rd1933 := evm_run rd1911 with [dup9, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    and, push4 ⟨282191964⟩, caller, dup14, dup14, dup13, dup13, push1 ⟨64⟩]
  have rd1934 := RD.mloadWord rd1933 (by native_decide) hload (by evm_ov)
  rw [hw64] at rd1934
  have rd1945 := evm_run rd1934 with [dup7, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  have rd1946 := RD.mstoreWord rd1945 (by native_decide) (by evm_ov)
  have rd1970 := evm_run rd1946 with [push1 ⟨4⟩, add, dup1, dup7,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, dup2]
  have hmask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by native_decide
  rw [hmask, u256_add_comm ⟨4⟩ ptr, u256_land_solcAddrMask_idem_left] at rd1970
  have rd1971 := RD.mstoreWord rd1970 (by native_decide) (by evm_ov)
  have rd1976 := evm_run rd1971 with [push1 ⟨32⟩, add, dup6, dup2]
  rw [u256_add_comm ⟨32⟩ (ptr + ⟨4⟩), u256_add_assoc ptr ⟨4⟩ ⟨32⟩, show (⟨4⟩ : UInt256) + ⟨32⟩ = ⟨36⟩ from by decide] at rd1976
  have rd1977 := RD.mstoreWord rd1976 (by native_decide) (by evm_ov)
  have rd1982 := evm_run rd1977 with [push1 ⟨32⟩, add, dup5, dup2]
  rw [u256_add_comm ⟨32⟩ (ptr + ⟨36⟩), u256_add_assoc ptr ⟨36⟩ ⟨32⟩, show (⟨36⟩ : UInt256) + ⟨32⟩ = ⟨68⟩ from by decide] at rd1982
  have rd1983 := RD.mstoreWord rd1982 (by native_decide) (by evm_ov)
  have rd1994 := evm_run rd1983 with [push1 ⟨32⟩, add, dup1, push1 ⟨32⟩, add, dup3, dup2, sub, dup3]
  rw [u256_add_comm ⟨32⟩ (ptr + ⟨68⟩), u256_add_assoc ptr ⟨68⟩ ⟨32⟩, show (⟨68⟩ : UInt256) + ⟨32⟩ = ⟨100⟩ from by decide,
    u256_add_comm ⟨32⟩ (ptr + ⟨100⟩), u256_add_assoc ptr ⟨100⟩ ⟨32⟩, show (⟨100⟩ : UInt256) + ⟨32⟩ = ⟨132⟩ from by decide] at rd1994
  have hsub : UInt256.sub (ptr + ⟨132⟩) (ptr + ⟨4⟩) = ⟨128⟩ := by
    rw [show (⟨132⟩ : UInt256) = ⟨4⟩ + ⟨128⟩ from by decide, ← u256_add_assoc]
    simpa only [u256_ofNat_toNat] using
      usub_uadd_lit_cancel_mod (base := (ptr + ⟨4⟩).toNat) (n := 128) (ptr + (⟨4⟩ : UInt256)).val.isLt (by decide)
  rw [hsub] at rd1994
  have rd1995 := RD.mstoreWord rd1994 (by native_decide) (by evm_ov)
  have rd2000 := evm_run rd1995 with [dup5, dup5, dup3, dup2, dup2]
  have rd2001 := RD.mstoreWord rd2000 (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2001⟩

end UniswapV2Pair
