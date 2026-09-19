import Solm.Benchmarks.Auction.ReturnReserve
import Solm.Benchmarks.Auction.CheckedAdd

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def errorAllocPtr (ptr size : UInt256) : UInt256 :=
  ptr + UInt256.land (UInt256.lnot ⟨31⟩) (size + ⟨31⟩)

def ErrorAllocAllowed (ptr size : UInt256) : Prop :=
  (errorAllocPtr ptr size).toNat ≤ 2 ^ 64 - 1 ∧ ptr.toNat ≤ (errorAllocPtr ptr size).toNat

theorem errorAllocationPanic {I g s0 R mem aw out acc k C}
    (h : RD auctionBytecode I g s0 ⟨5899⟩ R mem aw out acc k C)
    (hov : R.length + 3 ≤ 1024) : RDrev auctionBytecode g s0 := by
  exact evm_run h with [push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0,
    raw mstoreSymbolic (by native_decide) (by evm_ov), push1 ⟨65⟩, push1 ⟨4⟩,
    raw mstoreSymbolic (by native_decide) (by evm_ov), push1 ⟨36⟩, push0,
    raw revertSymbolic (by native_decide) (by evm_ov)]

theorem errorAllocationPrefix {I g s0 ptr size ret R mem aw out acc k C}
    (h : RD auctionBytecode I g s0 ⟨5868⟩ (ptr :: size :: ret :: R) mem aw out acc k C)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨5898⟩
      (⟨5918⟩ :: UInt256.isZero
        (UInt256.lor (UInt256.lt (errorAllocPtr ptr size) ptr)
          (UInt256.gt (errorAllocPtr ptr size) ⟨2 ^ 64 - 1⟩)) ::
        errorAllocPtr ptr size :: ptr :: size :: ret :: R)
      mem aw out acc k' C' := by
  have rd5879 := evm_run h with [jumpdest, push1 ⟨31⟩, dup3, add, push1 ⟨31⟩, not,
    and, dup2, add]
  have rd5888 := rd5879.pushConst ⟨0xffffffffffffffff⟩ (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd5888 with [dup2, gt, dup3, dup3, lt, or, iszero, push2 ⟨5918⟩]⟩

theorem errorAllocationOk {I g s0 ptr size ret R mem aw out acc k C}
    (h : RD auctionBytecode I g s0 ⟨5868⟩ (ptr :: size :: ret :: R) mem aw out acc k C)
    (ha : ActiveWords aw) (hok : ErrorAllocAllowed ptr size)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R
      (writeWord mem 64 (errorAllocPtr ptr size)) aw out acc k' C' := by
  obtain ⟨_, _, rd5898⟩ := errorAllocationPrefix h hov
  have hmax : UInt256.gt (errorAllocPtr ptr size) ⟨2 ^ 64 - 1⟩ = ⟨0⟩ := ugt_zero hok.1
  have hwrap : UInt256.lt (errorAllocPtr ptr size) ptr = ⟨0⟩ := ult_zero hok.2
  have rd5922 := evm_run rd5898 with [jumpiT (by rw [hmax, hwrap]; decide) (by jump_dest),
    jumpdest, push1 ⟨64⟩, raw mstoreSymbolic (by native_decide) (by evm_ov)]
  rw [expandedWords64_eq ha] at rd5922
  exact ⟨_, _, evm_run rd5922 with [pop, pop, jump hret]⟩

theorem errorAllocationFail {I g s0 ptr size ret R mem aw out acc k C}
    (h : RD auctionBytecode I g s0 ⟨5868⟩ (ptr :: size :: ret :: R) mem aw out acc k C)
    (hfail : ¬ ErrorAllocAllowed ptr size) (hov : R.length + 8 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, rd5898⟩ := errorAllocationPrefix h hov
  have hcond : UInt256.isZero
      (UInt256.lor (UInt256.lt (errorAllocPtr ptr size) ptr)
        (UInt256.gt (errorAllocPtr ptr size) ⟨2 ^ 64 - 1⟩)) = ⟨0⟩ := by
    by_cases hmax : (errorAllocPtr ptr size).toNat ≤ 2 ^ 64 - 1
    · have hwrap : (errorAllocPtr ptr size).toNat < ptr.toNat := by
        have hnot : ¬ ptr.toNat ≤ (errorAllocPtr ptr size).toNat := fun hw ↦ hfail ⟨hmax, hw⟩
        omega
      rw [ugt_zero hmax, ult_one hwrap]
      decide
    · have hgt : UInt256.gt (errorAllocPtr ptr size) ⟨2 ^ 64 - 1⟩ = ⟨1⟩ :=
        ugt_one (by change 2 ^ 64 - 1 < _; omega)
      rw [hgt]
      by_cases hw : ptr.toNat ≤ (errorAllocPtr ptr size).toNat
      · rw [ult_zero hw]; decide
      · rw [ult_one (by omega : (errorAllocPtr ptr size).toNat < ptr.toNat)]; decide
  have rd5899 := evm_run rd5898 with [jumpiNT hcond]
  exact errorAllocationPanic rd5899 (by evm_ov)

end Auction
