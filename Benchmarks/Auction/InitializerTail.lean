import Benchmarks.Auction.InitializerBegin

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option synthInstance.maxSize 4096
set_option maxRecDepth 100000

namespace Auction

abbrev InitializerTailSite := Fin 4

def initializerTailPc (i : InitializerTailSite) : UInt256 :=
  match i.val with
  | 0 => ⟨3878⟩
  | 1 => ⟨4975⟩
  | 2 => ⟨5087⟩
  | _ => ⟨5194⟩

def initializerTailWf (i : InitializerTailSite) : Prop :=
  let p0 := initializerTailPc i
  let p1 := p0 + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + UInt256.ofNat 3
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + UInt256.ofNat 3
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  decode auctionBytecode p0 = some (.DUP1, .none) ∧
  decode auctionBytecode p1 = some (.ISZERO, .none) ∧
  decode auctionBytecode p2 = some (.Push .PUSH2, some (⟨2850⟩, 2)) ∧
  decode auctionBytecode p3 = some (.JUMPI, .none) ∧
  decode auctionBytecode p4 = some (.Push .PUSH0, .none) ∧
  decode auctionBytecode p5 = some (.DUP1, .none) ∧
  decode auctionBytecode p6 = some (.SLOAD, .none) ∧
  decode auctionBytecode p7 = some (.Push .PUSH2, some (⟨65280⟩, 2)) ∧
  decode auctionBytecode p8 = some (.NOT, .none) ∧
  decode auctionBytecode p9 = some (.AND, .none) ∧
  decode auctionBytecode p10 = some (.SWAP1, .none) ∧
  decode auctionBytecode p11 = some (.SSTORE, .none) ∧
  decode auctionBytecode p12 = some (.POP, .none) ∧
  decode auctionBytecode p13 = some (.JUMP, .none)

theorem initializerTails : ∀ i : InitializerTailSite, initializerTailWf i := by
  unfold initializerTailWf
  native_decide

theorem initializerTail {I g s0 top ret R mem aw rdata cA σ k C} (i : InitializerTailSite)
    (h : RD auctionBytecode I g s0 (initializerTailPc i)
      (top :: ret :: R) mem aw rdata (cA, σ) k C)
    (hf : InitializerNestedFlag σ I top) (hperm : I.perm = true)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R mem aw rdata (cA, σ) k' C' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    initializerTails i
  by_cases ht : top = ⟨0⟩
  · have rd2850 := evm_run h with [
      raw dup1 h0 (by evm_ov), raw iszero h1 (by evm_ov), raw push2 ⟨2850⟩ h2 (by evm_ov),
      raw jumpiT h3 (by rw [ht]; decide) (by jump_dest) (by evm_ov) ]
    exact ⟨_, _, evm_run rd2850 with [jumpdest, pop, jump hret]⟩
  · have ha := hf.resolve_left ht
    have rdLoad := evm_run h with [
      raw dup1 h0 (by evm_ov), raw iszero h1 (by evm_ov), raw push2 ⟨2850⟩ h2 (by evm_ov),
      raw jumpiNT h3 (isZero_eq_zero_of_ne ht) (by evm_ov),
      raw push0 h4 (by evm_ov), raw dup1 h5 (by evm_ov) ]
    obtain ⟨_, _, rdOld⟩ := rdLoad.sload h6 (by evm_ov)
    have rdStore := evm_run rdOld with [
      raw push2 ⟨65280⟩ h7 (by evm_ov), raw not h8 (by evm_ov),
      raw and h9 (by evm_ov), raw swap1 h10 (by evm_ov) ]
    obtain ⟨_, _, rdPop⟩ := rdStore.sstore hperm h11 (by evm_ov)
    rw [sstoreAccountMap_absent_same ha] at rdPop
    exact ⟨_, _, evm_run rdPop with [raw pop h12 (by evm_ov), raw jump h13 hret (by evm_ov)]⟩

theorem initializerSharedTail {I g s0 top ret R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨3877⟩ (top :: ret :: R) mem aw rdata (cA, σ) k C)
    (hf : InitializerNestedFlag σ I top) (hperm : I.perm = true)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R mem aw rdata (cA, σ) k' C' := by
  exact initializerTail 0 (h.jumpdest (by native_decide) (by evm_ov)) hf hperm hret hov

theorem contextInitializer {I g s0 ret R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨4892⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hr : InitializerReady σ I) (hperm : I.perm = true)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R mem aw rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd4943⟩ := initializerGuardReady 4 h hr (by evm_ov)
  have rd4945 := evm_run rd4943 with [jumpdest, push0]
  obtain ⟨_, _, rd4946⟩ := rd4945.sload (by native_decide) (by evm_ov)
  have rd4955 := evm_run rd4946 with [push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, iszero]
  change RD _ _ _ _ _
    (UInt256.isZero (UInt256.land ⟨255⟩ (UInt256.div (storedWord σ I ⟨0⟩) ⟨256⟩)) :: ret :: R)
    _ _ _ _ _ _ at rd4955
  rw [u256_land_comm ⟨255⟩] at rd4955
  by_cases hi : initializingWord σ I = ⟨0⟩
  · have ha := hr.resolve_left (not_not_intro hi)
    have ht : UInt256.isZero (UInt256.isZero (initializingWord σ I)) = ⟨0⟩ := by
      rw [hi]; decide
    have rd4963 := evm_run rd4955 with [dup1, iszero, push2 ⟨3877⟩, jumpiNT ht, push0, dup1]
    obtain ⟨_, _, rd4964⟩ := rd4963.sload (by native_decide) (by evm_ov)
    have rd4974 := evm_run rd4964 with [push2 ⟨65535⟩, not, and, push2 ⟨257⟩, or, swap1]
    obtain ⟨_, _, rd4975⟩ := rd4974.sstore hperm (by native_decide) (by evm_ov)
    rw [sstoreAccountMap_absent_same ha] at rd4975
    exact initializerTail 1 rd4975 (Or.inr ha) hperm hret (by omega)
  · have ht : UInt256.isZero (UInt256.isZero (initializingWord σ I)) ≠ ⟨0⟩ := by
      rw [isZero_eq_zero_of_ne hi]; decide
    have rd3877 := evm_run rd4955 with [dup1, iszero, push2 ⟨3877⟩, jumpiT ht (by jump_dest)]
    exact initializerSharedTail rd3877 (initializerNestedFlag_of_ready hr) hperm hret (by omega)

end Auction
