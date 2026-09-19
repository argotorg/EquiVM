import Solm.Benchmarks.Auction.ErrorDecodePrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def ErrorOffsetValid (out : ByteArray) : Prop :=
  (errorOffset out).toNat ≤ 2 ^ 64 - 1 ∧ (errorOffset out).toNat + 36 ≤ out.size

def errorOffsetCondition (out : ByteArray) : UInt256 :=
  UInt256.isZero (UInt256.lor (UInt256.gt (errorOffset out) ⟨2 ^ 64 - 1⟩)
    (UInt256.gt (errorOffset out + ⟨36⟩) (UInt256.ofNat out.size)))

theorem errorOffsetCondition_ok {out : ByteArray} (ho : out.size < UInt256.size)
    (hv : ErrorOffsetValid out) : errorOffsetCondition out = ⟨1⟩ := by
  have hn := ulit_toNat' out.size ho
  have hadd : (errorOffset out + ⟨36⟩).toNat = (errorOffset out).toNat + 36 :=
    addWord_toNat _ ⟨36⟩ (by
      have hb := hv.1
      change (errorOffset out).toNat + 36 < 2 ^ 256
      omega)
  rw [errorOffsetCondition, ugt_zero hv.1, ugt_zero (by rw [hadd, hn]; exact hv.2)]
  decide

theorem errorOffsetCondition_fail {out : ByteArray} (ho : out.size < UInt256.size)
    (hv : ¬ ErrorOffsetValid out) : errorOffsetCondition out = ⟨0⟩ := by
  have hn := ulit_toNat' out.size ho
  unfold errorOffsetCondition
  by_cases hb : (errorOffset out).toNat ≤ 2 ^ 64 - 1
  · have hgt : out.size < (errorOffset out).toNat + 36 := by
      have hno : ¬ (errorOffset out).toNat + 36 ≤ out.size := fun hh ↦ hv ⟨hb, hh⟩
      omega
    have hadd : (errorOffset out + ⟨36⟩).toNat = (errorOffset out).toNat + 36 :=
      addWord_toNat _ ⟨36⟩ (by change (errorOffset out).toNat + 36 < 2 ^ 256; omega)
    rw [ugt_zero hb, ugt_one (by rw [hadd, hn]; exact hgt)]
    decide
  · have hgt : UInt256.gt (errorOffset out) ⟨2 ^ 64 - 1⟩ = ⟨1⟩ :=
      ugt_one (by change 2 ^ 64 - 1 < _; omega)
    rw [hgt]
    by_cases hc : out.size < (errorOffset out + ⟨36⟩).toNat
    · rw [ugt_one (by rw [hn]; exact hc)]; decide
    · rw [ugt_zero (by rw [hn]; omega)]; decide

theorem errorOffsetDenied {I g s0 ret R mem aw ptr out acc k C}
    (h : RD auctionBytecode I g s0 ⟨5978⟩
      (⟨5986⟩ :: errorOffsetCondition out :: ⟨2 ^ 64 - 1⟩ :: UInt256.ofNat out.size ::
        errorOffset out :: UInt256.lnot ⟨3⟩ :: ptr :: ⟨0⟩ :: ret :: R)
      mem aw out acc k C)
    (ho : out.size < UInt256.size) (hv : ¬ ErrorOffsetValid out)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret (⟨0⟩ :: R) mem aw out acc k' C' := by
  exact ⟨_, _, evm_run h with [jumpiNT (errorOffsetCondition_fail ho hv),
    pop, pop, pop, pop, pop, swap1, jump hret]⟩

theorem errorOffsetAllowed {I g s0 ret R mem aw ptr out acc k C}
    (h : RD auctionBytecode I g s0 ⟨5978⟩
      (⟨5986⟩ :: errorOffsetCondition out :: ⟨2 ^ 64 - 1⟩ :: UInt256.ofNat out.size ::
        errorOffset out :: UInt256.lnot ⟨3⟩ :: ptr :: ⟨0⟩ :: ret :: R)
      (errorPayloadMem mem out ptr) (errorPayloadWords aw ptr out) out acc k C)
    (hm : HeapMemory mem aw ptr) (hin : ptr.toNat ≤ mem.size) (hl : 68 ≤ out.size)
    (hb : ptr.toNat + out.size ≤ 2 ^ 200) (hv : ErrorOffsetValid out)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨6001⟩
      (⟨6010⟩ :: UInt256.isZero (UInt256.gt (errorLength out) ⟨2 ^ 64 - 1⟩) ::
        errorLength out :: ⟨2 ^ 64 - 1⟩ :: (ptr + errorOffset out) :: errorOffset out ::
        UInt256.lnot ⟨3⟩ :: ptr :: ⟨0⟩ :: ret :: R)
      (errorPayloadMem mem out ptr) (errorPayloadWords aw ptr out) out acc k' C' := by
  have ho : out.size < UInt256.size := by change out.size < 2 ^ 256; omega
  have rd5994 := evm_run h with [
    jumpiT (by rw [errorOffsetCondition_ok ho hv]; decide) (by jump_dest),
    jumpdest, dup3, dup6, add, swap2, pop, dup2,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [errorPayload_load hm hin hl hb (errorOffset out) hv.2,
    errorPayload_expand hm hin hl hb (errorOffset out) hv.2] at rd5994
  exact ⟨_, _, evm_run rd5994 with [dup2, dup2, gt, iszero, push2 ⟨6010⟩]⟩

end Auction
