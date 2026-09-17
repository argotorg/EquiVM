import Benchmarks.Auction.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

set_option synthInstance.maxSize 8192

def ownerErrorWord : UInt256 :=
  ⟨0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572⟩

theorem ownerErrorRevert {I g s0 R rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5522⟩ (⟨132⟩ :: ⟨994⟩ :: R)
      (solcErrorStringMem0 solcFreePtrMem) (UInt256.ofNat 5) rdata acc k C)
    (hov : R.length + 7 ≤ 1024) : RDrev auctionBytecode g s0 := by
  have rd5532 := evm_run h with [
    jumpdest, push1 ⟨32⟩, dup1, dup3,
    raw mstore 3 (solcErrorStringMem1 solcFreePtrMem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup2, dup2, add,
    raw mstore 3 (solcErrorStringMem2 ⟨32⟩ solcFreePtrMem) (UInt256.ofNat 7)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd5565 := rd5532.pushConst ownerErrorWord (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have rd994 := evm_run rd5565 with [
    push1 ⟨64⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem3 ⟨32⟩ ownerErrorWord solcFreePtrMem) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨96⟩, add, swap1, jump (by jump_dest) ]
  exact evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide) mem_cost
      (solcErrorStringMem3_mload64 ⟨32⟩ ownerErrorWord solcFreePtrMem_size
        solcFreePtrMem_read64) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by native_decide) mem_cost (by evm_ov) ]

abbrev OwnerSite := Fin 7

def ownerPc (i : OwnerSite) : UInt256 :=
  match i.val with
  | 0 => ⟨952⟩
  | 1 => ⟨1076⟩
  | 2 => ⟨1934⟩
  | 3 => ⟨2029⟩
  | 4 => ⟨2080⟩
  | 5 => ⟨2478⟩
  | _ => ⟨2698⟩

def ownerSuccessPc (i : OwnerSite) : UInt256 :=
  match i.val with
  | 0 => ⟨1003⟩
  | 1 => ⟨1118⟩
  | 2 => ⟨1976⟩
  | 3 => ⟨2071⟩
  | 4 => ⟨2122⟩
  | 5 => ⟨2520⟩
  | _ => ⟨2740⟩

def ownerWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (storedWord σ I ⟨151⟩)

abbrev ownerComparePc (i : OwnerSite) : UInt256 :=
  ownerPc i + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2
    + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩

abbrev ownerFailPc (i : OwnerSite) : UInt256 := ownerComparePc i + UInt256.ofNat 3 + ⟨1⟩

def ownerPrefixWf (i : OwnerSite) : Prop :=
  decode auctionBytecode (ownerPc i) = some (.JUMPDEST, .none) ∧
  decode auctionBytecode (ownerPc i + ⟨1⟩) = some (.Push .PUSH1, some (⟨151⟩, 1)) ∧
  decode auctionBytecode (ownerPc i + ⟨1⟩ + UInt256.ofNat 2) = some (.SLOAD, .none) ∧
  decode auctionBytecode (ownerPc i + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.Push .PUSH1, some
    (⟨1⟩, 1)) ∧
  decode auctionBytecode (ownerPc i + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2) = some
    (.Push .PUSH1, some (⟨1⟩, 1)) ∧
  decode auctionBytecode (ownerPc i + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 +
    UInt256.ofNat 2) = some (.Push .PUSH1, some (⟨160⟩, 1)) ∧
  decode auctionBytecode (ownerPc i + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 +
    UInt256.ofNat 2 + UInt256.ofNat 2) = some (.SHL, .none) ∧
  decode auctionBytecode (ownerPc i + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 +
    UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩) = some (.SUB, .none) ∧
  decode auctionBytecode (ownerPc i + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 +
    UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) = some (.AND, .none) ∧
  decode auctionBytecode (ownerPc i + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 +
    UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.CALLER, .none) ∧
  decode auctionBytecode (ownerPc i + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 +
    UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.EQ, .none) ∧
  decode auctionBytecode (ownerComparePc i) =
    some (.Push .PUSH2, some (ownerSuccessPc i, 2)) ∧
  decode auctionBytecode (ownerComparePc i + UInt256.ofNat 3) = some (.JUMPI, .none) ∧
  (D_J auctionBytecode 0).contains (ownerSuccessPc i) = true

theorem ownerPrefixes : ∀ i : OwnerSite, ownerPrefixWf i := by
  unfold ownerPrefixWf
  native_decide

def ownerFailWf (i : OwnerSite) : Prop :=
  decode auctionBytecode (ownerFailPc i) = some (.Push .PUSH1, some (⟨64⟩, 1)) ∧
  decode auctionBytecode (ownerFailPc i + UInt256.ofNat 2) = some (.MLOAD, .none) ∧
  decode auctionBytecode (ownerFailPc i + UInt256.ofNat 2 + ⟨1⟩) = some (.Push .PUSH3, some
    (⟨4594637⟩, 3)) ∧
  decode auctionBytecode (ownerFailPc i + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 4) = some (.Push
    .PUSH1, some (⟨229⟩, 1)) ∧
  decode auctionBytecode (ownerFailPc i + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 4 +
    UInt256.ofNat 2) = some (.SHL, .none) ∧
  decode auctionBytecode (ownerFailPc i + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 4 +
    UInt256.ofNat 2 + ⟨1⟩) = some (.DUP2, .none) ∧
  decode auctionBytecode (ownerFailPc i + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 4 +
    UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) = some (.MSTORE, .none) ∧
  decode auctionBytecode (ownerFailPc i + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 4 +
    UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH1, some (⟨4⟩, 1)) ∧
  decode auctionBytecode (ownerFailPc i + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 4 +
    UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) = some (.ADD, .none) ∧
  decode auctionBytecode (ownerFailPc i + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 4 +
    UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.Push .PUSH2, some
    (⟨994⟩, 2)) ∧
  decode auctionBytecode (ownerFailPc i + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 4 +
    UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 3) = some (.SWAP1,
    .none) ∧
  decode auctionBytecode (ownerFailPc i + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 4 +
    UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩) = some
    (.Push .PUSH2, some (⟨5522⟩, 2)) ∧
  decode auctionBytecode (ownerFailPc i + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 4 +
    UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ +
    UInt256.ofNat 3) = some (.JUMP, .none)

theorem ownerFailures : ∀ i : OwnerSite, ownerFailWf i := by
  unfold ownerFailWf
  native_decide

theorem ownerPrefix {I g s0 R rdata cA σ k C} (i : OwnerSite)
    (h : RD auctionBytecode I g s0 (ownerPc i) R solcFreePtrMem (UInt256.ofNat 3)
      rdata (cA, σ) k C)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 (ownerComparePc i)
      (UInt256.eq (solcSourceWord I) (ownerWord σ I) :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ := ownerPrefixes i
  have rdLoad := evm_run h with [
    raw jumpdest h0 (by evm_ov), raw push1 ⟨151⟩ h1 (by evm_ov) ]
  obtain ⟨_, _, rdWord⟩ := rdLoad.sload h2 (by evm_ov)
  exact ⟨_, _, evm_run rdWord with [
    raw push1 ⟨1⟩ h3 (by evm_ov), raw push1 ⟨1⟩ h4 (by evm_ov),
    raw push1 ⟨160⟩ h5 (by evm_ov), raw shl h6 (by evm_ov), raw sub h7 (by evm_ov),
    raw and h8 (by evm_ov), raw caller h9 (by evm_ov), raw eq h10 (by evm_ov) ]⟩

theorem ownerAllowed {I g s0 R rdata cA σ k C} (i : OwnerSite)
    (h : RD auctionBytecode I g s0 (ownerPc i) R solcFreePtrMem (UInt256.ofNat 3)
      rdata (cA, σ) k C)
    (ho : solcSourceWord I = ownerWord σ I) (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 (ownerSuccessPc i) R
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd⟩ := ownerPrefix i h (by omega)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hp, hj, hd⟩ := ownerPrefixes i
  exact ⟨_, _, evm_run rd with [
    raw push2 (ownerSuccessPc i) hp (by evm_ov),
    raw jumpiT hj (by rw [ho, uInt256_eq_self]; decide) hd (by evm_ov) ]⟩

theorem ownerDenied {I g s0 R rdata cA σ k C} (i : OwnerSite)
    (h : RD auctionBytecode I g s0 (ownerPc i) R solcFreePtrMem (UInt256.ofNat 3)
      rdata (cA, σ) k C)
    (ho : solcSourceWord I ≠ ownerWord σ I) (hov : R.length + 7 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, rd⟩ := ownerPrefix i h (by omega)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hp, hj, _⟩ := ownerPrefixes i
  have rdFail := evm_run rd with [
    raw push2 (ownerSuccessPc i) hp (by evm_ov),
    raw jumpiNT hj (u256_eq_of_ne ho) (by evm_ov) ]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := ownerFailures i
  have rdSelector := evm_run rdFail with [
    raw push1 ⟨64⟩ h0 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) h1 mem_cost
      solcFreePtrMem_mload64 (by decide) (by evm_ov) ]
  have rdRaw := rdSelector.pushConst ⟨4594637⟩ (width := 3) (op := .PUSH3)
    (by decide) h2 (by evm_ov)
  have rd5522 := evm_run rdRaw with [
    raw push1 ⟨229⟩ h3 (by evm_ov), raw shl h4 (by evm_ov), raw dup2 h5 (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 solcFreePtrMem) (UInt256.ofNat 5)
      h6 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨4⟩ h7 (by evm_ov), raw add h8 (by evm_ov),
    raw push2 ⟨994⟩ h9 (by evm_ov), raw swap1 h10 (by evm_ov),
    raw push2 ⟨5522⟩ h11 (by evm_ov), raw jump h12 (by jump_dest) (by evm_ov) ]
  exact ownerErrorRevert rd5522 hov

end Auction
