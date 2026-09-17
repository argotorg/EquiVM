import Benchmarks.Auction.ErrorSelectorMemory
import Benchmarks.Auction.RevertData

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem errorSelectorRoutine {I g s0 ret R mem aw ptr out acc k C}
    (h : RD auctionBytecode I g s0 ⟨5843⟩ (ret :: R) mem aw out acc k C)
    (hm : HeapMemory mem aw ptr) (ho : out.size < UInt256.size)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret (returnSelector out :: R)
      (errorSelectorMem mem out) (errorSelectorWords aw out) out acc k' C' := by
  have hn : (UInt256.ofNat out.size).toNat = out.size := ulit_toNat' _ ho
  have rd5853 := evm_run h with [jumpdest, push0, push1 ⟨3⟩,
    raw returndatasize (by native_decide) (by evm_ov), gt, iszero, push2 ⟨5865⟩]
  by_cases hl : 4 ≤ out.size
  · have hgt : UInt256.gt (UInt256.ofNat out.size) ⟨3⟩ = ⟨1⟩ :=
      ugt_one (by change 3 < _; omega)
    have rd5858 := evm_run rd5853 with [jumpiNT (by rw [hgt]; decide),
      push1 ⟨4⟩, push0, dup1]
    obtain ⟨_, _, rd5859⟩ := rd5858.returndatacopySymbolic (by native_decide) hl (by evm_ov)
    simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (⟨4⟩ : UInt256).toNat = 4 from rfl] at rd5859
    have rd5862 := evm_run rd5859 with [pop, push0,
      raw mloadSymbolic (by native_decide) (by evm_ov)]
    have rd5865 := evm_run rd5862 with [push1 ⟨224⟩, shr]
    rw [copiedSelector hm.size
      (activeWords_expand (off := ⟨0⟩) (size := ⟨4⟩) hm.active (by decide)) hl] at rd5865
    simpa only [returnSelector, errorSelectorMem, errorSelectorWords, if_pos hl] using
      (show ∃ k' C', RD auctionBytecode I g s0 ret
          (UInt256.shiftRight (calldataWord out 0) ⟨224⟩ :: R)
          (out.write 0 mem 0 4) (expandedWords (expandedWords aw ⟨0⟩ ⟨4⟩) ⟨0⟩ ⟨32⟩)
          out acc k' C' from
        ⟨_, _, evm_run rd5865 with [jumpdest, swap1, jump hret]⟩)
  · have hgt : UInt256.gt (UInt256.ofNat out.size) ⟨3⟩ = ⟨0⟩ :=
      ugt_zero (by change _ ≤ 3; omega)
    have rdret := evm_run rd5853 with [jumpiT (by rw [hgt]; decide) (by jump_dest),
      jumpdest, swap1, jump hret]
    exact ⟨_, _, by simpa only [returnSelector, errorSelectorMem, errorSelectorWords, if_neg hl]
      using rdret⟩

theorem createErrorSelectorPrefix {I g s0 ret R mem aw ptr out acc k C}
    (h : RD auctionBytecode I g s0 ⟨3116⟩ (ret :: R) mem aw out acc k C)
    (hm : HeapMemory mem aw ptr) (ho : out.size < UInt256.size)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨3123⟩ (returnSelector out :: ret :: R)
      (errorSelectorMem mem out) (errorSelectorWords aw out) out acc k' C' := by
  have rd5843 := evm_run h with [push2 ⟨3123⟩, push2 ⟨5843⟩, jump (by jump_dest)]
  exact errorSelectorRoutine rd5843 hm ho (by jump_dest) (by evm_ov)

set_option synthInstance.maxSize 1024 in
theorem createErrorSelectorWrong {I g s0 ret R mem aw ptr out acc k C}
    (h : RD auctionBytecode I g s0 ⟨3116⟩ (ret :: R) mem aw out acc k C)
    (hm : HeapMemory mem aw ptr) (ho : out.size < UInt256.size)
    (he : returnSelector out ≠ ⟨0x08c379a0⟩) (hov : R.length + 6 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, rd3123⟩ := createErrorSelectorPrefix h hm ho hov
  have rd3165 := evm_run rd3123 with [jumpdest, dup1, push4 ⟨0x08c379a0⟩, sub, push2 ⟨3162⟩,
    jumpiT (u256_sub_ne_zero_of_ne he.symm) (by jump_dest), jumpdest, pop, jumpdest]
  exact rd3165.revertData (by unfold revertDataWf; native_decide) (by evm_ov)

end Auction
