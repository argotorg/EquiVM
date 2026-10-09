import Benchmarks.Auction.ErrorOffsetGuard
import Benchmarks.Auction.ErrorAllocation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def errorPayloadCondition (ptr : UInt256) (out : ByteArray) : UInt256 :=
  UInt256.isZero (UInt256.gt ((ptr + errorOffset out + errorLength out) + ⟨32⟩)
    (UInt256.lnot ⟨3⟩ + (ptr + UInt256.ofNat out.size)))

def errorAllocSize (out : ByteArray) : UInt256 := errorOffset out + errorLength out + ⟨32⟩

theorem errorLengthDenied {I g s0 ret R mem aw ptr out acc k C}
    (h : RD auctionBytecode I g s0 ⟨6001⟩
      (⟨6010⟩ :: UInt256.isZero (UInt256.gt (errorLength out) ⟨2 ^ 64 - 1⟩) ::
        errorLength out :: ⟨2 ^ 64 - 1⟩ :: (ptr + errorOffset out) :: errorOffset out ::
        UInt256.lnot ⟨3⟩ :: ptr :: ⟨0⟩ :: ret :: R) mem aw out acc k C)
    (hlen : 2 ^ 64 - 1 < (errorLength out).toNat)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret (⟨0⟩ :: R) mem aw out acc k' C' := by
  have hg : UInt256.gt (errorLength out) ⟨2 ^ 64 - 1⟩ = ⟨1⟩ := ugt_one hlen
  exact ⟨_, _, evm_run h with [jumpiNT (by rw [hg]; decide),
    pop, pop, pop, pop, pop, pop, swap1, jump hret]⟩

set_option maxRecDepth 2048 in
theorem errorLengthAllowed {I g s0 ret R mem aw ptr out acc k C}
    (h : RD auctionBytecode I g s0 ⟨6001⟩
      (⟨6010⟩ :: UInt256.isZero (UInt256.gt (errorLength out) ⟨2 ^ 64 - 1⟩) ::
        errorLength out :: ⟨2 ^ 64 - 1⟩ :: (ptr + errorOffset out) :: errorOffset out ::
        UInt256.lnot ⟨3⟩ :: ptr :: ⟨0⟩ :: ret :: R) mem aw out acc k C)
    (hlen : (errorLength out).toNat ≤ 2 ^ 64 - 1) (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨6027⟩
      (⟨6036⟩ :: errorPayloadCondition ptr out :: errorLength out :: ⟨2 ^ 64 - 1⟩ ::
        (ptr + errorOffset out) :: errorOffset out :: UInt256.lnot ⟨3⟩ :: ptr :: ⟨0⟩ :: ret :: R)
      mem aw out acc k' C' := by
  have hg : UInt256.gt (errorLength out) ⟨2 ^ 64 - 1⟩ = ⟨0⟩ := ugt_zero hlen
  have rd6016 := evm_run h with [jumpiT (by rw [hg]; decide) (by jump_dest),
    jumpdest, dup5, raw returndatasize (by native_decide) (by evm_ov), dup8, add, add]
  have rd6027 := evm_run rd6016 with [push1 ⟨32⟩, dup3, dup6, add, add, gt, iszero,
    push2 ⟨6036⟩]
  rw [u256_add_comm (ptr + UInt256.ofNat out.size) (UInt256.lnot ⟨3⟩)] at rd6027
  exact ⟨_, _, rd6027⟩

theorem errorPayloadCondition_eq {ptr : UInt256} {out : ByteArray}
    (hl : 68 ≤ out.size) (hb : ptr.toNat + out.size ≤ 2 ^ 200)
    (ho : (errorOffset out).toNat ≤ 2 ^ 64 - 1)
    (hn : (errorLength out).toNat ≤ 2 ^ 64 - 1) :
    errorPayloadCondition ptr out =
      if (errorOffset out).toNat + (errorLength out).toNat + 36 ≤ out.size then ⟨1⟩ else ⟨0⟩ := by
  have hout : (UInt256.ofNat out.size).toNat = out.size :=
    ulit_toNat' _ (by change out.size < 2 ^ 256; omega)
  have hsum : (ptr + UInt256.ofNat out.size).toNat = ptr.toNat + out.size := by
    change (UInt256.add _ _).toNat = _
    rw [addWord_toNat ptr _ (by rw [hout]; change _ < 2 ^ 256; omega), hout]
  have hword : ptr + UInt256.ofNat out.size = UInt256.ofNat (ptr.toNat + out.size) := by
    apply u256_inj
    rw [hsum, ulit_toNat' _ (by change ptr.toNat + out.size < 2 ^ 256; omega)]
  have hbuf : (UInt256.lnot ⟨3⟩ + (ptr + UInt256.ofNat out.size)).toNat =
      ptr.toNat + out.size - 4 := by
    rw [hword, lnot3_add_returnSize (by omega) (by change _ < 2 ^ 256; omega)]
    exact ulit_toNat' _ (by change _ < 2 ^ 256; omega)
  have h1 : (ptr + errorOffset out).toNat = ptr.toNat + (errorOffset out).toNat :=
    addWord_toNat _ _ (by change _ < 2 ^ 256; omega)
  have h2 : (ptr + errorOffset out + errorLength out).toNat =
      ptr.toNat + (errorOffset out).toNat + (errorLength out).toNat := by
    change (UInt256.add _ _).toNat = _
    rw [addWord_toNat _ _ (by rw [h1]; change _ < 2 ^ 256; omega), h1]
  have h3 : ((ptr + errorOffset out + errorLength out) + ⟨32⟩).toNat =
      ptr.toNat + (errorOffset out).toNat + (errorLength out).toNat + 32 := by
    change (UInt256.add _ _).toNat = _
    rw [addWord_toNat _ ⟨32⟩ (by rw [h2]; change _ + 32 < 2 ^ 256; omega), h2]
    rfl
  unfold errorPayloadCondition
  by_cases hg : (errorOffset out).toNat + (errorLength out).toNat + 36 ≤ out.size
  · rw [if_pos hg, ugt_zero (by rw [h3, hbuf]; omega)]
    rfl
  · rw [if_neg hg, ugt_one (by rw [h3, hbuf]; omega)]
    rfl

theorem errorPayloadDenied {I g s0 ret R mem aw ptr out acc k C}
    (h : RD auctionBytecode I g s0 ⟨6027⟩
      (⟨6036⟩ :: errorPayloadCondition ptr out :: errorLength out :: ⟨2 ^ 64 - 1⟩ ::
        (ptr + errorOffset out) :: errorOffset out :: UInt256.lnot ⟨3⟩ :: ptr :: ⟨0⟩ :: ret :: R)
      mem aw out acc k C)
    (hc : errorPayloadCondition ptr out = ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret (⟨0⟩ :: R) mem aw out acc k' C' := by
  exact ⟨_, _, evm_run h with [jumpiNT hc, pop, pop, pop, pop, pop, pop, swap1, jump hret]⟩

theorem errorPayloadAllowed {I g s0 ret R mem aw ptr out acc k C}
    (h : RD auctionBytecode I g s0 ⟨6027⟩
      (⟨6036⟩ :: errorPayloadCondition ptr out :: errorLength out :: ⟨2 ^ 64 - 1⟩ ::
        (ptr + errorOffset out) :: errorOffset out :: UInt256.lnot ⟨3⟩ :: ptr :: ⟨0⟩ :: ret :: R)
      mem aw out acc k C)
    (hc : errorPayloadCondition ptr out = ⟨1⟩) (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨5868⟩
      (ptr :: errorAllocSize out :: ⟨6051⟩ :: errorLength out :: ⟨2 ^ 64 - 1⟩ ::
        (ptr + errorOffset out) :: errorOffset out :: UInt256.lnot ⟨3⟩ :: ptr :: ⟨0⟩ :: ret :: R)
      mem aw out acc k' C' := by
  exact ⟨_, _, evm_run h with [jumpiT (by rw [hc]; decide) (by jump_dest),
    jumpdest, push2 ⟨6051⟩, push1 ⟨32⟩, dup3, dup7, add, add, dup8,
    push2 ⟨5868⟩, jump (by jump_dest)]⟩

theorem errorDecodeReturn {I g s0 ret R mem aw ptr out acc k C}
    (h : RD auctionBytecode I g s0 ⟨6051⟩
      (errorLength out :: ⟨2 ^ 64 - 1⟩ :: (ptr + errorOffset out) :: errorOffset out ::
        UInt256.lnot ⟨3⟩ :: ptr :: ⟨0⟩ :: ret :: R) mem aw out acc k C)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret ((ptr + errorOffset out) :: R)
      mem aw out acc k' C' := by
  exact ⟨_, _, evm_run h with [jumpdest, pop, swap1, swap6, swap5,
    pop, pop, pop, pop, pop, jump hret]⟩

end Auction
