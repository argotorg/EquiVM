import Benchmarks.Auction.ErrorDecodeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem errorDecodeRoutine {I g s0 ret R mem aw ptr out acc k C}
    (h : RD auctionBytecode I g s0 ⟨5925⟩ (ret :: R) mem aw out acc k C)
    (hm : HeapMemory mem aw ptr) (hin : ptr.toNat ≤ mem.size)
    (hb : ptr.toNat + out.size + 64 ≤ 2 ^ 200)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 18 ≤ 1024) :
    (ErrorDataValid out ∧ ErrorAllocAllowed ptr (errorAllocSize out) ∧
      (∃ k' C', RD auctionBytecode I g s0 ret ((ptr + errorOffset out) :: R)
        (writeWord (errorPayloadMem mem out ptr) 64 (errorAllocPtr ptr (errorAllocSize out)))
        (errorPayloadWords aw ptr out) out acc k' C') ∧
      HeapMemory
        (writeWord (errorPayloadMem mem out ptr) 64 (errorAllocPtr ptr (errorAllocSize out)))
        (errorPayloadWords aw ptr out) (errorAllocPtr ptr (errorAllocSize out)) ∧
      ptr + errorOffset out ≠ ⟨0⟩) ∨
    (¬ ErrorDataValid out ∧
      ∃ mem' aw' k' C', RD auctionBytecode I g s0 ret (⟨0⟩ :: R) mem' aw' out acc k' C') ∨
    (ErrorDataValid out ∧ ¬ ErrorAllocAllowed ptr (errorAllocSize out) ∧
      RDrev auctionBytecode g s0) := by
  by_cases hl : 68 ≤ out.size
  · have hb' : ptr.toNat + out.size ≤ 2 ^ 200 := by omega
    have ho : out.size < UInt256.size := by change out.size < 2 ^ 256; omega
    obtain ⟨_, _, rd5978⟩ := errorDecodeLongPrefix h hm hin hl hb' (by omega)
    by_cases hoff : ErrorOffsetValid out
    · obtain ⟨_, _, rd6001⟩ := errorOffsetAllowed rd5978 hm hin hl hb' hoff (by omega)
      by_cases hlen : (errorLength out).toNat ≤ 2 ^ 64 - 1
      · obtain ⟨_, _, rd6027⟩ := errorLengthAllowed rd6001 hlen (by omega)
        have hc := errorPayloadCondition_eq hl hb' hoff.1 hlen
        by_cases hpay : (errorOffset out).toNat + (errorLength out).toNat + 36 ≤ out.size
        · have hv : ErrorDataValid out := ⟨hl, hoff, hlen, hpay⟩
          rw [if_pos hpay] at hc
          obtain ⟨_, _, rd5868⟩ := errorPayloadAllowed rd6027 hc (by omega)
          by_cases ha : ErrorAllocAllowed ptr (errorAllocSize out)
          · have hh := errorPayloadHeap hm hin hl hb'
            obtain ⟨_, _, rd6051⟩ := errorAllocationOk rd5868 hh.active ha
              (by jump_dest) (by evm_ov)
            exact Or.inl ⟨hv, ha, errorDecodeReturn rd6051 hret (by evm_ov),
              errorDecodeHeap hm hin hv hb, errorDecodedPtr_ne_zero hm hv hb'⟩
          · exact Or.inr (Or.inr ⟨hv, ha, errorAllocationFail rd5868 ha (by evm_ov)⟩)
        · rw [if_neg hpay] at hc
          obtain ⟨_, _, rdret⟩ := errorPayloadDenied rd6027 hc hret (by omega)
          exact Or.inr (Or.inl ⟨fun hv ↦ hpay hv.2.2.2, _, _, _, _, rdret⟩)
      · obtain ⟨_, _, rdret⟩ := errorLengthDenied rd6001 (by omega) hret (by omega)
        exact Or.inr (Or.inl ⟨fun hv ↦ hlen hv.2.2.1, _, _, _, _, rdret⟩)
    · obtain ⟨_, _, rdret⟩ := errorOffsetDenied rd5978 ho hoff hret (by omega)
      exact Or.inr (Or.inl ⟨fun hv ↦ hoff hv.2.1, _, _, _, _, rdret⟩)
  · obtain ⟨_, _, rdret⟩ := errorDecodeShort h (by omega) hret (by omega)
    exact Or.inr (Or.inl ⟨fun hv ↦ hl hv.1, _, _, _, _, rdret⟩)

end Auction
