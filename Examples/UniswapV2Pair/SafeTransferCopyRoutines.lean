import Examples.UniswapV2Pair.MemorySteps
import Examples.UniswapV2Pair.SkimSafeTransferReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferCopyWord
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {src dst len aw word : UInt256} {R : List UInt256} {k C : Nat}
    (rd6512 : RD uniswapV2PairBytecode I g s0 ⟨6512⟩ (src :: dst :: len :: R) mem aw rdata acc k C)
    (hlen : UInt256.lt len ⟨32⟩ = ⟨0⟩) (hload : memoryWordLoad mem aw src = word)
    (haw : memoryWordActiveWords aw src = aw) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6512⟩
      ((⟨32⟩ + src) :: (⟨32⟩ + dst) :: (len + UInt256.lnot ⟨31⟩) :: R)
      (word.toByteArray.write 0 mem dst.toNat 32) (memoryWordActiveWords aw dst) rdata acc k' C' := by
  have rd6521 := evm_run rd6512 with [jumpdest, push1 ⟨32⟩, dup4, lt, push2 ⟨6543⟩, jumpiNT hlen]
  have rd6522 := evm_run rd6521 with [dup1]
  have rd6523 := RD.mloadWord rd6522 (by native_decide) hload (by evm_ov)
  rw [haw] at rd6523
  have rd6524 := evm_run rd6523 with [dup3]
  have rd6525 := RD.mstoreWord rd6524 (by native_decide) (by evm_ov)
  have rd6542 := evm_run rd6525 with [push1 ⟨31⟩, not, swap1, swap3, add, swap2,
    push1 ⟨32⟩, swap2, dup3, add, swap2, add, push2 ⟨6512⟩]
  have rd6512' := rd6542.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, rd6512'⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferCopyTail4
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {src dst aw sourceWord : UInt256} {R : List UInt256} {k C : Nat}
    (rd6512 : RD uniswapV2PairBytecode I g s0 ⟨6512⟩ (src :: dst :: ⟨4⟩ :: R) mem aw rdata acc k C)
    (hloadSrc : memoryWordLoad mem aw src = sourceWord)
    (hawSrc : memoryWordActiveWords aw src = aw)
    (hloadDst : memoryWordLoad mem aw dst = ⟨0⟩)
    (hawDst : memoryWordActiveWords (memoryWordActiveWords aw dst) dst = memoryWordActiveWords aw dst)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6575⟩ R
      ((UInt256.lor (UInt256.land sourceWord (UInt256.lnot skimSafeTransferTailMask))
        (UInt256.land ⟨0⟩ skimSafeTransferTailMask)).toByteArray.write 0 mem dst.toNat 32)
      (memoryWordActiveWords aw dst) rdata acc k' C' := by
  have rd6543 := evm_run rd6512 with [jumpdest, push1 ⟨32⟩, dup4, lt, push2 ⟨6543⟩,
    jumpiT (by native_decide) (by jump_dest)]
  have rd6558 := evm_run rd6543 with [jumpdest, push1 ⟨1⟩, dup4, push1 ⟨32⟩, sub,
    push2 ⟨256⟩, exp, sub, dup1, not, dup3]
  have rd6559 := RD.mloadWord rd6558 (by native_decide) hloadSrc (by evm_ov)
  rw [hawSrc] at rd6559
  have rd6562 := evm_run rd6559 with [and, dup2, dup5]
  have rd6563 := RD.mloadWord rd6562 (by native_decide) hloadDst (by evm_ov)
  have rd6568 := evm_run rd6563 with [and, dup1, dup3, or, dup6]
  have rd6569 := RD.mstoreWord rd6568 (by native_decide) (by evm_ov)
  rw [hawDst] at rd6569
  have rd6575 := evm_run rd6569 with [pop, pop, pop, pop, pop, pop]
  exact ⟨_, _, rd6575⟩

end UniswapV2Pair
