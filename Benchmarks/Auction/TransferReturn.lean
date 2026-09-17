import Benchmarks.Auction.ReturnReserve
import Benchmarks.Auction.BoolDecoder
import Benchmarks.Auction.DepositPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem transferReturnPrefix {I g s0 amount recipient ret R mem aw ptr out acc k C}
    (h : RD auctionBytecode I g s0 ⟨3537⟩ (amount :: recipient :: ret :: R)
      mem aw out acc k C)
    (hm : MemoryCursor mem aw ptr) (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨6062⟩
      (ptr :: (ptr + UInt256.ofNat out.size) :: ⟨3568⟩ :: amount :: recipient :: ret :: R)
      (returnReserveMem mem ptr out.size) aw out acc k' C' := by
  have rd3540 := evm_run h with [push1 ⟨64⟩,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hm.load64, expandedWords64_eq hm.active] at rd3540
  have rd3555 := evm_run rd3540 with [raw returndatasize (by native_decide) (by evm_ov),
    push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and, dup3, add, dup1, push1 ⟨64⟩,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  simp only [u256_land_comm (UInt256.ofNat out.size + ⟨31⟩) (UInt256.lnot ⟨31⟩),
    expandedWords64_eq hm.active] at rd3555
  change RD _ _ _ _ ⟨3555⟩ (returnReservePtr ptr out.size :: UInt256.ofNat out.size ::
    ptr :: amount :: recipient :: ret :: R) (returnReserveMem mem ptr out.size)
    aw out acc _ _ at rd3555
  exact ⟨_, _, evm_run rd3555 with [pop, dup2, add, swap1, push2 ⟨3568⟩, swap2,
    swap1, push2 ⟨6062⟩, jump (by jump_dest)]⟩

theorem returnReserve_load {mem aw ptr word} (hm : MemoryCursor mem aw ptr) (size : Nat)
    (hin : ptr.toNat + 32 ≤ mem.size) (hcover : ptr.toNat < aw.toNat * 32)
    (hread : mem.readWithPadding ptr.toNat 32 = word.toByteArray) :
    loadedWord (returnReserveMem mem ptr size) aw ptr = word := by
  apply loadedWord_of_read hm.active (by rw [returnReserveMem_size hm size]; exact hin) hcover
  rw [returnReserve_read_word hm size hin, hread]

theorem transferReturnOk {I g s0 amount recipient ret R mem aw ptr out acc k C} {word : UInt256}
    (h : RD auctionBytecode I g s0 ⟨3537⟩ (amount :: recipient :: ret :: R)
      mem aw out acc k C)
    (hm : MemoryCursor mem aw ptr) (hlen : 32 ≤ out.size) (hhi : out.size < 2 ^ 255)
    (hin : ptr.toNat + 32 ≤ mem.size) (hcover : ptr.toNat < aw.toNat * 32)
    (hread : mem.readWithPadding ptr.toNat 32 = word.toByteArray)
    (hc : word = ⟨0⟩ ∨ word = ⟨1⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R
      (returnReserveMem mem ptr out.size) (expandedWords aw ptr ⟨32⟩) out acc k' C' := by
  obtain ⟨_, _, rd6062⟩ := transferReturnPrefix h hm hov
  have hcheck : UInt256.slt (UInt256.sub (ptr + UInt256.ofNat out.size) ptr) ⟨32⟩ = ⟨0⟩ := by
    rw [word_add_sub_left]
    exact slt_ofNat_lit_zero (by decide) hlen hhi
  obtain ⟨_, _, rd3568⟩ := boolDecodeOk rd6062 hcheck
    (returnReserve_load hm out.size hin hcover hread) hc (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd3568 with [jumpdest, pop, jumpdest, pop, pop, jump hret]⟩

theorem transferReturnShort {I g s0 amount recipient ret R mem aw ptr out acc k C}
    (h : RD auctionBytecode I g s0 ⟨3537⟩ (amount :: recipient :: ret :: R)
      mem aw out acc k C)
    (hm : MemoryCursor mem aw ptr) (hlen : out.size < 32) (hov : R.length + 12 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, rd6062⟩ := transferReturnPrefix h hm hov
  apply boolDecodeShort rd6062 _ (by evm_ov)
  rw [word_add_sub_left]
  exact slt_ofNat_lit_one_low (by decide) hlen

theorem transferReturnNoncanonical {I g s0 amount recipient ret R mem aw ptr out acc k C}
    {word : UInt256}
    (h : RD auctionBytecode I g s0 ⟨3537⟩ (amount :: recipient :: ret :: R)
      mem aw out acc k C)
    (hm : MemoryCursor mem aw ptr) (hlen : 32 ≤ out.size) (hhi : out.size < 2 ^ 255)
    (hin : ptr.toNat + 32 ≤ mem.size) (hcover : ptr.toNat < aw.toNat * 32)
    (hread : mem.readWithPadding ptr.toNat 32 = word.toByteArray)
    (hc : ¬ (word = ⟨0⟩ ∨ word = ⟨1⟩)) (hov : R.length + 12 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, rd6062⟩ := transferReturnPrefix h hm hov
  have hcheck : UInt256.slt (UInt256.sub (ptr + UInt256.ofNat out.size) ptr) ⟨32⟩ = ⟨0⟩ := by
    rw [word_add_sub_left]
    exact slt_ofNat_lit_zero (by decide) hlen hhi
  exact boolDecodeNoncanonical rd6062 hcheck (returnReserve_load hm out.size hin hcover hread) hc
    (by evm_ov)

end Auction
