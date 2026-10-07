import Benchmarks.Auction.UnpauseSource
import Benchmarks.Auction.PausableErrors
import Benchmarks.Auction.AddressEventHeap

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem unpausePrefix {I g s0 R mem aw rdata σ k C}
    (h : RD auctionBytecode I g s0 ⟨2853⟩ R mem aw rdata σ k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨2863⟩ (⟨2926⟩ :: pausedWord σ I :: R)
      mem aw rdata σ k' C' := by
  have rd2856 := evm_run h with [jumpdest, push1 ⟨51⟩]
  obtain ⟨_, _, rd2857⟩ := rd2856.sload (by native_decide) (by evm_ov)
  have rd2863 := evm_run rd2857 with [push1 ⟨255⟩, and, push2 ⟨2926⟩]
  rw [u256_land_comm ⟨255⟩] at rd2863
  exact ⟨_, _, rd2863⟩

theorem unpauseRoutineOkSplit {I g s0 ret R mem aw rdata σ k C}
    (h : RD auctionBytecode I g s0 ⟨2853⟩ (ret :: R) mem aw rdata σ k C)
    (hp : pausedWord σ I ≠ ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 7 ≤ 1024) :
    (I.perm = true ∧
      ∃ k' C', RD auctionBytecode I g s0 ret R (addressEventMem mem (solcSourceWord I))
        (addressEventWords mem aw (solcSourceWord I)) rdata
        (sstoreAccountMap I.codeOwner σ ⟨51⟩ (unpauseWord (solcSlotWord σ I ⟨51⟩))) k' C') ∨
      (I.perm = false ∧ RDstatic auctionBytecode g s0) := by
  obtain ⟨_, _, rd2863⟩ := unpausePrefix h (by evm_ov)
  have rd2930 := evm_run rd2863 with [jumpiT hp (by jump_dest), jumpdest, push1 ⟨51⟩, dup1]
  obtain ⟨_, _, rd2931⟩ := rd2930.sload (by native_decide) (by evm_ov)
  have rd2936 := evm_run rd2931 with [push1 ⟨255⟩, not, and, swap1]
  have hstoreDec : decode auctionBytecode ⟨2936⟩ = some (.SSTORE, none) := by native_decide
  by_cases hperm : I.perm = true
  swap
  · exact Or.inr ⟨by simpa using hperm,
      rd2936.sstoreStatic (by simpa using hperm) hstoreDec (by evm_ov)⟩
  refine Or.inl ⟨hperm, ?_⟩
  obtain ⟨_, _, rd2937⟩ := rd2936.sstore hperm hstoreDec (by evm_ov)
  have rd2970 := rd2937.pushConst
    ⟨0x5db9ee0a495bf2e6ff9c91a7834c1ba4fdd244a5e8aa4e537bd38aeae4b073aa⟩
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd2971 := evm_run rd2970 with [caller]
  rw [u256_land_comm (UInt256.lnot ⟨255⟩)] at rd2971
  exact addressEventReturn rd2971 hperm hret hov

theorem unpauseRoutineOk {I g s0 ret R mem aw rdata σ k C}
    (h : RD auctionBytecode I g s0 ⟨2853⟩ (ret :: R) mem aw rdata σ k C)
    (hp : pausedWord σ I ≠ ⟨0⟩) (hperm : I.perm = true)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R (addressEventMem mem (solcSourceWord I))
      (addressEventWords mem aw (solcSourceWord I)) rdata
      (sstoreAccountMap I.codeOwner σ ⟨51⟩ (unpauseWord (solcSlotWord σ I ⟨51⟩))) k' C' :=
  permSplit_true hperm (unpauseRoutineOkSplit h hp hret hov)

theorem unpauseRoutineRevert {I g s0 R mem aw rdata σ k C}
    (h : RD auctionBytecode I g s0 ⟨2853⟩ R mem aw rdata σ k C)
    (hp : pausedWord σ I = ⟨0⟩) (hov : R.length + 6 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, rd2863⟩ := unpausePrefix h (by omega)
  exact pausableError 3 (evm_run rd2863 with [jumpiNT hp]) hov

end Auction
