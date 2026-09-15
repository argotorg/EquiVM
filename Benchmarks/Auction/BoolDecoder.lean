import Benchmarks.Auction.CalldataHead
import Benchmarks.Auction.DynamicMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem boolWordClean_iff (word : UInt256) :
    UInt256.isZero (UInt256.isZero word) = word ↔ word = ⟨0⟩ ∨ word = ⟨1⟩ := by
  by_cases hz : word = ⟨0⟩
  · subst word
    decide
  · rw [isZero_eq_zero_of_ne hz]
    change ⟨1⟩ = word ↔ word = ⟨0⟩ ∨ word = ⟨1⟩
    simp only [hz, false_or, eq_comm]

set_option synthInstance.maxSize 1024 in
theorem boolHeadWf : calldataHeadWf auctionBytecode ⟨6062⟩ ⟨6078⟩ ⟨32⟩ := by
  unfold calldataHeadWf
  native_decide

theorem boolDecodeOk {I g s0 off finish ret R mem aw rdata acc k C word}
    (h : RD auctionBytecode I g s0 ⟨6062⟩ (off :: finish :: ret :: R)
      mem aw rdata acc k C)
    (hcheck : UInt256.slt (UInt256.sub finish off) ⟨32⟩ = ⟨0⟩)
    (hload : loadedWord mem aw off = word) (hc : word = ⟨0⟩ ∨ word = ⟨1⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret (word :: R)
      mem (expandedWords aw off ⟨32⟩) rdata acc k' C' := by
  obtain ⟨_, _, rd6078⟩ := calldataHeadOk h boolHeadWf hcheck hov
  have rd6081 := evm_run rd6078 with [jumpdest, dup2,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hload] at rd6081
  have rd5350 := evm_run rd6081 with [dup1, iszero, iszero, dup2, eq, push2 ⟨5350⟩,
    jumpiT (by rw [(boolWordClean_iff word).mpr hc, u256_eq_refl]; decide) (by jump_dest)]
  exact oneResultReturn rd5350 hret (by evm_ov)

theorem boolDecodeNoncanonical {I g s0 off finish ret R mem aw rdata acc k C word}
    (h : RD auctionBytecode I g s0 ⟨6062⟩ (off :: finish :: ret :: R)
      mem aw rdata acc k C)
    (hcheck : UInt256.slt (UInt256.sub finish off) ⟨32⟩ = ⟨0⟩)
    (hload : loadedWord mem aw off = word) (hc : ¬ (word = ⟨0⟩ ∨ word = ⟨1⟩))
    (hov : R.length + 8 ≤ 1024) : RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, rd6078⟩ := calldataHeadOk h boolHeadWf hcheck hov
  have rd6081 := evm_run rd6078 with [jumpdest, dup2,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hload] at rd6081
  have hne : word ≠ UInt256.isZero (UInt256.isZero word) :=
    fun he => hc ((boolWordClean_iff word).mp he.symm)
  exact evm_run rd6081 with [dup1, iszero, iszero, dup2, eq, push2 ⟨5350⟩,
    jumpiNT (u256_eq_of_ne hne),
    raw auctionRevert0 (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem boolDecodeShort {I g s0 off finish ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨6062⟩ (off :: finish :: ret :: R)
      mem aw rdata acc k C)
    (hcheck : UInt256.slt (UInt256.sub finish off) ⟨32⟩ = ⟨1⟩)
    (hov : R.length + 8 ≤ 1024) : RDrev auctionBytecode g s0 :=
  calldataHeadFail h boolHeadWf hcheck hov

end Auction
