import Solm.Benchmarks.Auction.InitializerFlags
import Solm.Benchmarks.Auction.DynamicMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option synthInstance.maxSize 4096
set_option maxRecDepth 100000

namespace Auction

abbrev InitializerSite := Fin 8

def initializerPc (i : InitializerSite) : UInt256 :=
  match i.val with
  | 0 => ⟨2130⟩
  | 1 => ⟨3778⟩
  | 2 => ⟨3896⟩
  | 3 => ⟨3987⟩
  | 4 => ⟨4892⟩
  | 5 => ⟨4993⟩
  | 6 => ⟨5105⟩
  | _ => ⟨5212⟩

def initializerGuardSuccess (i : InitializerSite) : UInt256 := initializerPc i + ⟨51⟩

def initializerGuardWf (i : InitializerSite) : Prop :=
  let p0 := initializerPc i
  let p1 := p0 + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + UInt256.ofNat 3
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + UInt256.ofNat 3
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + UInt256.ofNat 2
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + UInt256.ofNat 3
  decode auctionBytecode p0 = some (.JUMPDEST, .none) ∧
  decode auctionBytecode p1 = some (.Push .PUSH0, .none) ∧
  decode auctionBytecode p2 = some (.SLOAD, .none) ∧
  decode auctionBytecode p3 = some (.Push .PUSH2, some (⟨256⟩, 2)) ∧
  decode auctionBytecode p4 = some (.SWAP1, .none) ∧
  decode auctionBytecode p5 = some (.DIV, .none) ∧
  decode auctionBytecode p6 = some (.Push .PUSH1, some (⟨255⟩, 1)) ∧
  decode auctionBytecode p7 = some (.AND, .none) ∧
  decode auctionBytecode p8 = some (.DUP1, .none) ∧
  decode auctionBytecode p9 = some (.Push .PUSH2, some (p17, 2)) ∧
  decode auctionBytecode p10 = some (.JUMPI, .none) ∧
  decode auctionBytecode p11 = some (.POP, .none) ∧
  decode auctionBytecode p12 = some (.Push .PUSH0, .none) ∧
  decode auctionBytecode p13 = some (.SLOAD, .none) ∧
  decode auctionBytecode p14 = some (.Push .PUSH1, some (⟨255⟩, 1)) ∧
  decode auctionBytecode p15 = some (.AND, .none) ∧
  decode auctionBytecode p16 = some (.ISZERO, .none) ∧
  decode auctionBytecode p17 = some (.JUMPDEST, .none) ∧
  decode auctionBytecode p18 = some (.Push .PUSH2, some (initializerGuardSuccess i, 2)) ∧
  decode auctionBytecode p19 = some (.JUMPI, .none) ∧
  (D_J auctionBytecode 0).contains p17 = true ∧
  (D_J auctionBytecode 0).contains (initializerGuardSuccess i) = true

theorem initializerGuards : ∀ i : InitializerSite, initializerGuardWf i := by
  unfold initializerGuardWf
  native_decide

theorem initializerGuardOk {I g s0 R mem aw rdata cA σ k C} (i : InitializerSite)
    (h : RD auctionBytecode I g s0 (initializerPc i) R mem aw rdata (cA, σ) k C)
    (hg : initializingWord σ I ≠ ⟨0⟩ ∨ initializedWord σ I = ⟨0⟩)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 (initializerGuardSuccess i) R
      mem aw rdata (cA, σ) k' C' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, hd1, hd2⟩ := initializerGuards i
  have rdLoad := evm_run h with [
    raw jumpdest h0 (by evm_ov), raw push0 h1 (by evm_ov) ]
  obtain ⟨_, _, rdWord⟩ := rdLoad.sload h2 (by evm_ov)
  have rdTest := evm_run rdWord with [
    raw push2 ⟨256⟩ h3 (by evm_ov), raw swap1 h4 (by evm_ov), raw div h5 (by evm_ov),
    raw push1 ⟨255⟩ h6 (by evm_ov), raw and h7 (by evm_ov) ]
  change RD _ _ _ _ _
    (UInt256.land ⟨255⟩ (UInt256.div (storedWord σ I ⟨0⟩) ⟨256⟩) :: R)
    _ _ _ _ _ _ at rdTest
  rw [u256_land_comm ⟨255⟩] at rdTest
  by_cases hi : initializingWord σ I = ⟨0⟩
  · have hz := hg.resolve_left (not_not_intro hi)
    have rdSecondLoad := evm_run rdTest with [
      raw dup1 h8 (by evm_ov), raw push2 _ h9 (by evm_ov),
      raw jumpiNT h10 hi (by evm_ov), raw pop h11 (by evm_ov),
      raw push0 h12 (by evm_ov) ]
    obtain ⟨_, _, rdSecondWord⟩ := rdSecondLoad.sload h13 (by evm_ov)
    have rdMerge := evm_run rdSecondWord with [
      raw push1 ⟨255⟩ h14 (by evm_ov), raw and h15 (by evm_ov),
      raw iszero h16 (by evm_ov) ]
    change RD _ _ _ _ _ (UInt256.isZero (UInt256.land ⟨255⟩ (storedWord σ I ⟨0⟩)) :: R)
      _ _ _ _ _ _ at rdMerge
    rw [u256_land_comm ⟨255⟩] at rdMerge
    have ht : UInt256.isZero (initializedWord σ I) ≠ ⟨0⟩ := by rw [hz]; decide
    exact ⟨_, _, evm_run rdMerge with [
      raw jumpdest h17 (by evm_ov), raw push2 _ h18 (by evm_ov),
      raw jumpiT h19 ht hd2 (by evm_ov) ]⟩
  · have rdMerge := evm_run rdTest with [
      raw dup1 h8 (by evm_ov), raw push2 _ h9 (by evm_ov),
      raw jumpiT h10 hi hd1 (by evm_ov) ]
    exact ⟨_, _, evm_run rdMerge with [
      raw jumpdest h17 (by evm_ov), raw push2 _ h18 (by evm_ov),
      raw jumpiT h19 hi hd2 (by evm_ov) ]⟩

theorem initializerGuardReady {I g s0 R mem aw rdata cA σ k C} (i : InitializerSite)
    (h : RD auctionBytecode I g s0 (initializerPc i) R mem aw rdata (cA, σ) k C)
    (hr : InitializerReady σ I) (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 (initializerGuardSuccess i) R
      mem aw rdata (cA, σ) k' C' := by
  apply initializerGuardOk i h _ hov
  rcases hr with hi | ha
  · exact Or.inl hi
  · right
    rw [initializedWord, storedWord_absent ha]
    decide

end Auction
