import Solm.Benchmarks.Auction.InitializerGuard

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option synthInstance.maxSize 4096
set_option maxRecDepth 100000

namespace Auction

abbrev InitializerBodySite := Fin 7

def initializerBodyGuard (i : InitializerBodySite) : InitializerSite :=
  if h : i.val < 4 then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩

def initializerBodyPc (i : InitializerBodySite) : UInt256 :=
  initializerPc (initializerBodyGuard i) + ⟨83⟩

def initializerEntered (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  if initializingWord σ I = ⟨0⟩ then
    sstoreAccountMap I.codeOwner σ ⟨0⟩ (initializerBeginWord (storedWord σ I ⟨0⟩))
  else σ

def initializerBeginWf (i : InitializerBodySite) : Prop :=
  let p0 := initializerGuardSuccess (initializerBodyGuard i)
  let p1 := p0 + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + UInt256.ofNat 3
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + UInt256.ofNat 3
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + UInt256.ofNat 3
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + UInt256.ofNat 3
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  decode auctionBytecode p0 = some (.JUMPDEST, .none) ∧
  decode auctionBytecode p1 = some (.Push .PUSH0, .none) ∧
  decode auctionBytecode p2 = some (.SLOAD, .none) ∧
  decode auctionBytecode p3 = some (.Push .PUSH2, some (⟨256⟩, 2)) ∧
  decode auctionBytecode p4 = some (.SWAP1, .none) ∧
  decode auctionBytecode p5 = some (.DIV, .none) ∧
  decode auctionBytecode p6 = some (.Push .PUSH1, some (⟨255⟩, 1)) ∧
  decode auctionBytecode p7 = some (.AND, .none) ∧
  decode auctionBytecode p8 = some (.ISZERO, .none) ∧
  decode auctionBytecode p9 = some (.DUP1, .none) ∧
  decode auctionBytecode p10 = some (.ISZERO, .none) ∧
  decode auctionBytecode p11 = some (.Push .PUSH2, some (initializerBodyPc i, 2)) ∧
  decode auctionBytecode p12 = some (.JUMPI, .none) ∧
  decode auctionBytecode p13 = some (.Push .PUSH0, .none) ∧
  decode auctionBytecode p14 = some (.DUP1, .none) ∧
  decode auctionBytecode p15 = some (.SLOAD, .none) ∧
  decode auctionBytecode p16 = some (.Push .PUSH2, some (⟨65535⟩, 2)) ∧
  decode auctionBytecode p17 = some (.NOT, .none) ∧
  decode auctionBytecode p18 = some (.AND, .none) ∧
  decode auctionBytecode p19 = some (.Push .PUSH2, some (⟨257⟩, 2)) ∧
  decode auctionBytecode p20 = some (.OR, .none) ∧
  decode auctionBytecode p21 = some (.SWAP1, .none) ∧
  decode auctionBytecode p22 = some (.SSTORE, .none) ∧
  p23 = initializerBodyPc i ∧
  (D_J auctionBytecode 0).contains (initializerBodyPc i) = true

theorem initializerBegins : ∀ i : InitializerBodySite, initializerBeginWf i := by
  unfold initializerBeginWf
  native_decide

theorem initializerBegin {I g s0 R mem aw rdata cA σ k C} (i : InitializerBodySite)
    (h : RD auctionBytecode I g s0 (initializerGuardSuccess (initializerBodyGuard i))
      R mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true) (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 (initializerBodyPc i)
      (UInt256.isZero (initializingWord σ I) :: R) mem aw rdata
      (cA, initializerEntered σ I) k' C' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, h20, h21, h22, hp, hd⟩ := initializerBegins i
  have rdLoad := evm_run h with [
    raw jumpdest h0 (by evm_ov), raw push0 h1 (by evm_ov) ]
  obtain ⟨_, _, rdWord⟩ := rdLoad.sload h2 (by evm_ov)
  have rdTest := evm_run rdWord with [
    raw push2 ⟨256⟩ h3 (by evm_ov), raw swap1 h4 (by evm_ov), raw div h5 (by evm_ov),
    raw push1 ⟨255⟩ h6 (by evm_ov), raw and h7 (by evm_ov), raw iszero h8 (by evm_ov) ]
  change RD _ _ _ _ _
    (UInt256.isZero (UInt256.land ⟨255⟩ (UInt256.div (storedWord σ I ⟨0⟩) ⟨256⟩)) :: R)
    _ _ _ _ _ _ at rdTest
  rw [u256_land_comm ⟨255⟩] at rdTest
  by_cases hi : initializingWord σ I = ⟨0⟩
  · rw [initializerEntered, if_pos hi]
    have ht : UInt256.isZero (UInt256.isZero (initializingWord σ I)) = ⟨0⟩ := by
      rw [hi]; decide
    have rdStoreLoad := evm_run rdTest with [
      raw dup1 h9 (by evm_ov), raw iszero h10 (by evm_ov), raw push2 _ h11 (by evm_ov),
      raw jumpiNT h12 ht (by evm_ov), raw push0 h13 (by evm_ov),
      raw dup1 h14 (by evm_ov) ]
    obtain ⟨_, _, rdOld⟩ := rdStoreLoad.sload h15 (by evm_ov)
    have rdStore := evm_run rdOld with [
      raw push2 ⟨65535⟩ h16 (by evm_ov), raw not h17 (by evm_ov),
      raw and h18 (by evm_ov), raw push2 ⟨257⟩ h19 (by evm_ov),
      raw or h20 (by evm_ov), raw swap1 h21 (by evm_ov) ]
    obtain ⟨_, _, rdBody⟩ := rdStore.sstore hperm h22 (by evm_ov)
    rw [hp] at rdBody
    change RD _ _ _ _ _ _ _ _ _ (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩
      (UInt256.lor ⟨257⟩ (UInt256.land (UInt256.lnot ⟨65535⟩) (storedWord σ I ⟨0⟩))))
      _ _ at rdBody
    rw [u256_land_comm (UInt256.lnot ⟨65535⟩), u256_lor_comm ⟨257⟩] at rdBody
    exact ⟨_, _, rdBody⟩
  · rw [initializerEntered, if_neg hi]
    have ht : UInt256.isZero (UInt256.isZero (initializingWord σ I)) ≠ ⟨0⟩ := by
      rw [isZero_eq_zero_of_ne hi]; decide
    exact ⟨_, _, evm_run rdTest with [
      raw dup1 h9 (by evm_ov), raw iszero h10 (by evm_ov), raw push2 _ h11 (by evm_ov),
      raw jumpiT h12 ht hd (by evm_ov) ]⟩

theorem initializerEntered_ready_eq {σ : AccountMap} {I : ExecutionEnv}
    (hr : InitializerReady σ I) : initializerEntered σ I = σ := by
  rcases hr with hi | ha
  · exact if_neg hi
  · unfold initializerEntered
    split
    · exact sstoreAccountMap_absent_same ha
    · rfl

theorem initializerPrefixReady {I g s0 R mem aw rdata cA σ k C} (i : InitializerBodySite)
    (h : RD auctionBytecode I g s0 (initializerPc (initializerBodyGuard i))
      R mem aw rdata (cA, σ) k C)
    (hr : InitializerReady σ I) (hperm : I.perm = true) (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 (initializerBodyPc i)
      (UInt256.isZero (initializingWord σ I) :: R) mem aw rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rdGuard⟩ := initializerGuardReady (initializerBodyGuard i) h hr (by omega)
  obtain ⟨_, _, rdBody⟩ := initializerBegin i rdGuard hperm hov
  rw [initializerEntered_ready_eq hr] at rdBody
  exact ⟨_, _, rdBody⟩

end Auction
