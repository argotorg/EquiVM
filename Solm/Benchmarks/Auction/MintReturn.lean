import Solm.Benchmarks.Auction.TransferReturn
import Solm.Benchmarks.Auction.UIntReturnDecoder

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem mintReturnPrefix {I g s0 ret R mem aw ptr out acc k C}
    (h : RD auctionBytecode I g s0 ⟨3071⟩ (⟨1⟩ :: ret :: R) mem aw out acc k C)
    (hm : MemoryCursor mem aw ptr) (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨5820⟩
      (ptr :: (ptr + UInt256.ofNat out.size) :: ⟨3108⟩ :: ret :: R)
      (returnReserveMem mem ptr out.size) aw out acc k' C' := by
  have rd3077 := evm_run h with [dup1, iszero, push2 ⟨3111⟩, jumpiNT (by decide)]
  have rd3082 := evm_run rd3077 with [pop, push1 ⟨64⟩, dup1,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hm.load64, expandedWords64_eq hm.active] at rd3082
  have rd3097 := evm_run rd3082 with [push1 ⟨31⟩,
    raw returndatasize (by native_decide) (by evm_ov), swap1, dup2, add,
    push1 ⟨31⟩, not, and, dup3, add, swap1, swap3,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  rw [expandedWords64_eq hm.active] at rd3097
  change RD _ _ _ _ ⟨3097⟩ (ptr :: UInt256.ofNat out.size :: ret :: R)
    (returnReserveMem mem ptr out.size) aw out acc _ _ at rd3097
  exact ⟨_, _, evm_run rd3097 with [push2 ⟨3108⟩, swap2, dup2, add, swap1,
    push2 ⟨5820⟩, jump (by jump_dest)]⟩

theorem mintReturnOk {I g s0 ret R mem aw ptr out acc k C word}
    (h : RD auctionBytecode I g s0 ⟨3071⟩ (⟨1⟩ :: ret :: R) mem aw out acc k C)
    (hm : MemoryCursor mem aw ptr) (hlen : 32 ≤ out.size) (hhi : out.size < 2 ^ 255)
    (hin : ptr.toNat + 32 ≤ mem.size) (hcover : ptr.toNat < aw.toNat * 32)
    (hread : mem.readWithPadding ptr.toNat 32 = word.toByteArray)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨3172⟩ (word :: ret :: R)
      (returnReserveMem mem ptr out.size) (expandedWords aw ptr ⟨32⟩) out acc k' C' := by
  obtain ⟨_, _, rd5820⟩ := mintReturnPrefix h hm hov
  have hcheck : UInt256.slt (UInt256.sub (ptr + UInt256.ofNat out.size) ptr) ⟨32⟩ = ⟨0⟩ := by
    rw [word_add_sub_left]
    exact slt_ofNat_lit_zero (by decide) hlen hhi
  obtain ⟨_, _, rd3108⟩ := uintReturnDecodeOk rd5820 hcheck
    (returnReserve_load hm out.size hin hcover hread) (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd3108 with [jumpdest, push1 ⟨1⟩, jumpdest, push2 ⟨3172⟩,
    jumpiT (by decide) (by jump_dest)]⟩

theorem mintReturnShort {I g s0 ret R mem aw ptr out acc k C}
    (h : RD auctionBytecode I g s0 ⟨3071⟩ (⟨1⟩ :: ret :: R) mem aw out acc k C)
    (hm : MemoryCursor mem aw ptr) (hlen : out.size < 32) (hov : R.length + 11 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, rd5820⟩ := mintReturnPrefix h hm hov
  apply uintReturnDecodeShort rd5820 _ (by evm_ov)
  rw [word_add_sub_left]
  exact slt_ofNat_lit_one_low (by decide) hlen

end Auction
