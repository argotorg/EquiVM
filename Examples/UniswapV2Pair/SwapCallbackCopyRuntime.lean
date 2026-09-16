import Examples.UniswapV2Pair.SwapCallbackHeadRuntime
import Examples.UniswapV2Pair.CalldataCopyStep
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev swapCallbackPaddedLen (dataLen : UInt256) : UInt256 :=
  UInt256.land (dataLen + ⟨31⟩) (UInt256.lnot ⟨31⟩)
noncomputable def swapCallbackCopyMem (calldata mem : ByteArray) (ptr dataPtr dataLen : UInt256) : ByteArray :=
  calldata.write dataPtr.toNat mem (ptr + ⟨164⟩).toNat dataLen.toNat
noncomputable def swapCallbackPaddedMem (calldata mem : ByteArray) (ptr dataPtr dataLen : UInt256) : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0 (swapCallbackCopyMem calldata mem ptr dataPtr dataLen)
    ((ptr + ⟨164⟩) + dataLen).toNat 32
abbrev swapCallbackCopyWords (aw ptr dataLen : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat (ptr + ⟨164⟩).toNat dataLen.toNat)
abbrev swapCallbackPaddedWords (aw ptr dataLen : UInt256) : UInt256 :=
  memoryWordActiveWords (swapCallbackCopyWords aw ptr dataLen) ((ptr + ⟨164⟩) + dataLen)

set_option maxHeartbeats 1000000 in
theorem uniswapSwapCallbackPayloadCopied
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {ptr aw dataLen dataPtr amount1Out amount0Out senderWord selector target : UInt256}
    {R : List UInt256} {k C : Nat}
    (rd2001 : RD uniswapV2PairBytecode I g s0 ⟨2001⟩
      ((ptr + ⟨132⟩) :: dataLen :: dataPtr :: (ptr + ⟨132⟩) :: (ptr + ⟨100⟩) :: (ptr + ⟨4⟩) ::
        dataLen :: dataPtr :: amount1Out :: amount0Out :: senderWord :: selector :: target :: R)
      mem aw rdata acc k C)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨2041⟩
      (((ptr + ⟨164⟩) + swapCallbackPaddedLen dataLen) :: selector :: target :: R)
      (swapCallbackPaddedMem I.calldata mem ptr dataPtr dataLen)
      (swapCallbackPaddedWords aw ptr dataLen) rdata acc k' C' := by
  have rd2009 := evm_run rd2001 with [push1 ⟨32⟩, add, swap3, pop, dup1, dup3, dup5]
  rw [u256_add_comm ⟨32⟩ (ptr + ⟨132⟩), u256_add_assoc ptr ⟨132⟩ ⟨32⟩,
    show (⟨132⟩ : UInt256) + ⟨32⟩ = ⟨164⟩ from by decide] at rd2009
  have rd2010 := RD.calldatacopyAny rd2009 (by native_decide) (by evm_ov)
  have rd2015 := evm_run rd2010 with [push1 ⟨0⟩, dup2, dup5, add]
  have rd2016 := RD.mstoreWord rd2015 (by native_decide) (by evm_ov)
  have rd2041 := evm_run rd2016 with [push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and,
    swap1, pop, dup1, dup4, add, swap3, pop, pop, pop, swap7, pop, pop, pop, pop, pop, pop, pop]
  exact ⟨_, _, rd2041⟩

end UniswapV2Pair
