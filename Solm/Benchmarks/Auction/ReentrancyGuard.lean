import Solm.Benchmarks.Auction.ReentrancySource
import Solm.Benchmarks.Auction.SettleGuards

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

abbrev ReentrancySite := Fin 3

def reentrancyPc (i : ReentrancySite) : UInt256 :=
  match i.val with
  | 0 => ⟨1165⟩
  | 1 => ⟨2424⟩
  | _ => ⟨2573⟩

def reentrancyAllowedPc (i : ReentrancySite) : UInt256 :=
  match i.val with
  | 0 => ⟨1199⟩
  | 1 => ⟨2458⟩
  | _ => ⟨2607⟩

abbrev reentrancyBranchPc (i : ReentrancySite) : UInt256 :=
  reentrancyPc i + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3

def reentrancyGuardWf (i : ReentrancySite) : Prop :=
  let p0 := reentrancyPc i
  let p1 := p0 + ⟨1⟩
  let p2 := p1 + UInt256.ofNat 2
  let p3 := p2 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + UInt256.ofNat 3
  decode auctionBytecode p0 = some (.JUMPDEST, .none) ∧
  decode auctionBytecode p1 = some (.Push .PUSH1, some (⟨2⟩, 1)) ∧
  decode auctionBytecode p2 = some (.Push .PUSH1, some (⟨101⟩, 1)) ∧
  decode auctionBytecode p3 = some (.SLOAD, .none) ∧
  decode auctionBytecode p4 = some (.SUB, .none) ∧
  decode auctionBytecode p5 = some (.Push .PUSH2, some (reentrancyAllowedPc i, 2)) ∧
  decode auctionBytecode p6 = some (.JUMPI, .none) ∧
  (D_J auctionBytecode 0).contains (reentrancyAllowedPc i) = true

set_option synthInstance.maxSize 2048 in
theorem reentrancyGuardWfs : ∀ i : ReentrancySite, reentrancyGuardWf i := by
  unfold reentrancyGuardWf
  native_decide

def reentrancyFailureWf (i : ReentrancySite) : Prop :=
  let p0 := reentrancyBranchPc i + ⟨1⟩
  let p1 := p0 + UInt256.ofNat 2
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + UInt256.ofNat 4
  let p4 := p3 + UInt256.ofNat 2
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + UInt256.ofNat 2
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + UInt256.ofNat 3
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + UInt256.ofNat 3
  decode auctionBytecode p0 = some (.Push .PUSH1, some (⟨64⟩, 1)) ∧
  decode auctionBytecode p1 = some (.MLOAD, .none) ∧
  decode auctionBytecode p2 = some (.Push .PUSH3, some (⟨4594637⟩, 3)) ∧
  decode auctionBytecode p3 = some (.Push .PUSH1, some (⟨229⟩, 1)) ∧
  decode auctionBytecode p4 = some (.SHL, .none) ∧
  decode auctionBytecode p5 = some (.DUP2, .none) ∧
  decode auctionBytecode p6 = some (.MSTORE, .none) ∧
  decode auctionBytecode p7 = some (.Push .PUSH1, some (⟨4⟩, 1)) ∧
  decode auctionBytecode p8 = some (.ADD, .none) ∧
  decode auctionBytecode p9 = some (.Push .PUSH2, some (⟨994⟩, 2)) ∧
  decode auctionBytecode p10 = some (.SWAP1, .none) ∧
  decode auctionBytecode p11 = some (.Push .PUSH2, some (⟨5575⟩, 2)) ∧
  decode auctionBytecode p12 = some (.JUMP, .none)

set_option synthInstance.maxSize 2048 in
theorem reentrancyFailureWfs : ∀ i : ReentrancySite, reentrancyFailureWf i := by
  unfold reentrancyFailureWf
  native_decide

theorem reentrancyPrefix {I g s0 R mem aw rdata cA σ k C} (i : ReentrancySite)
    (h : RD auctionBytecode I g s0 (reentrancyPc i) R mem aw rdata (cA, σ) k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 (reentrancyBranchPc i)
      (reentrancyAllowedPc i :: UInt256.sub (storedWord σ I ⟨101⟩) ⟨2⟩ :: R)
      mem aw rdata (cA, σ) k' C' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, _, _⟩ := reentrancyGuardWfs i
  have rdLoad := evm_run h with [raw jumpdest h0 (by evm_ov),
    raw push1 ⟨2⟩ h1 (by evm_ov), raw push1 ⟨101⟩ h2 (by evm_ov)]
  obtain ⟨_, _, rdWord⟩ := rdLoad.sload h3 (by evm_ov)
  exact ⟨_, _, evm_run rdWord with [raw sub h4 (by evm_ov),
    raw push2 (reentrancyAllowedPc i) h5 (by evm_ov)]⟩

theorem reentrancyAllowed {I g s0 R mem aw rdata cA σ k C} (i : ReentrancySite)
    (h : RD auctionBytecode I g s0 (reentrancyPc i) R mem aw rdata (cA, σ) k C)
    (hs : storedWord σ I ⟨101⟩ ≠ ⟨2⟩) (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 (reentrancyAllowedPc i) R
      mem aw rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd⟩ := reentrancyPrefix i h hov
  obtain ⟨_, _, _, _, _, _, hj, hd⟩ := reentrancyGuardWfs i
  exact ⟨_, _, evm_run rd with [raw jumpiT hj (u256_sub_ne_zero_of_ne hs) hd (by evm_ov)]⟩

theorem reentrancyErrorRevert {I g s0 ptr R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5575⟩ (ptr :: ⟨994⟩ :: R) mem aw rdata acc k C)
    (hov : R.length + 7 ≤ 1024) : RDrev auctionBytecode g s0 := by
  have rd5587 := evm_run h with [jumpdest, push1 ⟨32⟩, dup1, dup3,
    raw mstoreSymbolic (by native_decide) (by evm_ov), push1 ⟨31⟩, swap1, dup3, add,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have rd5620 := rd5587.pushConst
    ⟨0x5265656e7472616e637947756172643a207265656e7472616e742063616c6c00⟩
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd994 := evm_run rd5620 with [push1 ⟨64⟩, dup3, add,
    raw mstoreSymbolic (by native_decide) (by evm_ov), push1 ⟨96⟩, add, swap1,
    jump (by jump_dest)]
  exact auctionErrorRevert rd994 (by evm_ov)

theorem reentrancyDenied {I g s0 R mem aw rdata cA σ k C} (i : ReentrancySite)
    (h : RD auctionBytecode I g s0 (reentrancyPc i) R mem aw rdata (cA, σ) k C)
    (hs : storedWord σ I ⟨101⟩ = ⟨2⟩) (hov : R.length + 7 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, rd⟩ := reentrancyPrefix i h (by omega)
  obtain ⟨_, _, _, _, _, _, hj, _⟩ := reentrancyGuardWfs i
  have rdFail := evm_run rd with [raw jumpiNT hj (by rw [hs]; decide) (by evm_ov)]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := reentrancyFailureWfs i
  have rdSel := evm_run rdFail with [raw push1 ⟨64⟩ h0 (by evm_ov),
    raw mloadSymbolic h1 (by evm_ov)]
  have rdRaw := rdSel.pushConst ⟨4594637⟩ (width := 3) (op := .PUSH3)
    (by decide) h2 (by evm_ov)
  have rd5575 := evm_run rdRaw with [raw push1 ⟨229⟩ h3 (by evm_ov),
    raw shl h4 (by evm_ov), raw dup2 h5 (by evm_ov), raw mstoreSymbolic h6 (by evm_ov),
    raw push1 ⟨4⟩ h7 (by evm_ov), raw add h8 (by evm_ov), raw push2 ⟨994⟩ h9 (by evm_ov),
    raw swap1 h10 (by evm_ov), raw push2 ⟨5575⟩ h11 (by evm_ov),
    raw jump h12 (by jump_dest) (by evm_ov)]
  exact reentrancyErrorRevert rd5575 hov

end Auction
