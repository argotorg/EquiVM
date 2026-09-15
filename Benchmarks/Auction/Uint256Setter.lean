import Benchmarks.Auction.Decoders
import Benchmarks.Auction.Events
import Benchmarks.Auction.OwnerGuard

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

set_option synthInstance.maxSize 4096

abbrev Uint256Setter := Fin 2

def setterOwner (i : Uint256Setter) : OwnerSite := if i.val = 0 then 2 else 5
def setterSlot (i : Uint256Setter) : UInt256 := if i.val = 0 then ⟨203⟩ else ⟨204⟩
def setterDecodePc (i : Uint256Setter) : UInt256 := if i.val = 0 then ⟨532⟩ else ⟨841⟩
def setterDecodeRet (i : Uint256Setter) : UInt256 := if i.val = 0 then ⟨545⟩ else ⟨854⟩
def setterTopic (i : Uint256Setter) : UInt256 :=
  if i.val = 0 then
    ⟨0x1b55d9f7002bda4490f467e326f22a4a847629c0f2d1ed421607d318d25b410d⟩
  else
    ⟨0x6ab2e127d7fdf53b8f304e59d3aab5bfe97979f52a85479691a6fab27a28a6b2⟩

def setterDecodeWf (i : Uint256Setter) : Prop :=
  let p0 := setterDecodePc i
  let p1 := p0 + UInt256.ofNat 3
  let p2 := p1 + UInt256.ofNat 3
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + UInt256.ofNat 2
  let p5 := p4 + UInt256.ofNat 3
  decode auctionBytecode p0 = some (.Push .PUSH2, some (⟨413⟩, 2)) ∧
  decode auctionBytecode p1 = some (.Push .PUSH2, some (setterDecodeRet i, 2)) ∧
  decode auctionBytecode p2 = some (.CALLDATASIZE, .none) ∧
  decode auctionBytecode p3 = some (.Push .PUSH1, some (⟨4⟩, 1)) ∧
  decode auctionBytecode p4 = some (.Push .PUSH2, some (⟨5357⟩, 2)) ∧
  decode auctionBytecode p5 = some (.JUMP, .none)

theorem setterDecodeWfAll : ∀ i : Uint256Setter, setterDecodeWf i := by
  unfold setterDecodeWf
  native_decide

def setterDecodeRetWf (i : Uint256Setter) : Prop :=
  let p0 := setterDecodeRet i
  let p1 := p0 + ⟨1⟩
  let p2 := p1 + UInt256.ofNat 3
  decode auctionBytecode p0 = some (.JUMPDEST, .none) ∧
  decode auctionBytecode p1 = some (.Push .PUSH2, some (ownerPc (setterOwner i), 2)) ∧
  decode auctionBytecode p2 = some (.JUMP, .none) ∧
  (D_J auctionBytecode 0).contains (setterDecodeRet i) = true ∧
  (D_J auctionBytecode 0).contains (ownerPc (setterOwner i)) = true

theorem setterDecodeRetWfAll : ∀ i : Uint256Setter, setterDecodeRetWf i := by
  unfold setterDecodeRetWf
  native_decide

def setterWriteWf (i : Uint256Setter) : Prop :=
  let p0 := ownerSuccessPc (setterOwner i)
  let p1 := p0 + ⟨1⟩
  let p2 := p1 + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + UInt256.ofNat 33
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + UInt256.ofNat 3
  decode auctionBytecode p0 = some (.JUMPDEST, .none) ∧
  decode auctionBytecode p1 = some (.Push .PUSH1, some (setterSlot i, 1)) ∧
  decode auctionBytecode p2 = some (.DUP2, .none) ∧
  decode auctionBytecode p3 = some (.SWAP1, .none) ∧
  decode auctionBytecode p4 = some (.SSTORE, .none) ∧
  decode auctionBytecode p5 = some (.Push .PUSH1, some (⟨64⟩, 1)) ∧
  decode auctionBytecode p6 = some (.MLOAD, .none) ∧
  decode auctionBytecode p7 = some (.DUP2, .none) ∧
  decode auctionBytecode p8 = some (.DUP2, .none) ∧
  decode auctionBytecode p9 = some (.MSTORE, .none) ∧
  decode auctionBytecode p10 = some (.Push .PUSH32, some (setterTopic i, 32)) ∧
  decode auctionBytecode p11 = some (.SWAP1, .none) ∧
  decode auctionBytecode p12 = some (.Push .PUSH1, some (⟨32⟩, 1)) ∧
  decode auctionBytecode p13 = some (.ADD, .none) ∧
  decode auctionBytecode p14 = some (.Push .PUSH2, some (⟨1065⟩, 2)) ∧
  decode auctionBytecode p15 = some (.JUMP, .none)

theorem setterWriteWfAll : ∀ i : Uint256Setter, setterWriteWf i := by
  unfold setterWriteWf
  native_decide

theorem setterToDecoder {I g s0 R mem aw rdata acc k C} (i : Uint256Setter)
    (h : RD auctionBytecode I g s0 (setterDecodePc i) R mem aw rdata acc k C)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨5357⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: setterDecodeRet i :: ⟨413⟩ :: R)
      mem aw rdata acc k' C' := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := setterDecodeWfAll i
  exact ⟨_, _, evm_run h with [
    raw push2 ⟨413⟩ h0 (by evm_ov), raw push2 (setterDecodeRet i) h1 (by evm_ov),
    raw calldatasize h2 (by evm_ov), raw push1 ⟨4⟩ h3 (by evm_ov),
    raw push2 ⟨5357⟩ h4 (by evm_ov), raw jump h5 (by jump_dest) (by evm_ov) ]⟩

theorem setterFromDecoder {I g s0 value R mem aw rdata acc k C} (i : Uint256Setter)
    (h : RD auctionBytecode I g s0 (setterDecodeRet i)
      (value :: R) mem aw rdata acc k C) (hov : R.length + 2 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 (ownerPc (setterOwner i))
      (value :: R) mem aw rdata acc k' C' := by
  obtain ⟨h0, h1, h2, _, hd⟩ := setterDecodeRetWfAll i
  exact ⟨_, _, evm_run h with [
    raw jumpdest h0 (by evm_ov), raw push2 (ownerPc (setterOwner i)) h1 (by evm_ov),
    raw jump h2 hd (by evm_ov) ]⟩

theorem setterStoreEvent {I g s0 value ret R rdata cA σ k C} (i : Uint256Setter)
    (h : RD auctionBytecode I g s0 (ownerSuccessPc (setterOwner i))
      (value :: ret :: R) solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R (solcReturnMem value) (UInt256.ofNat 5)
      rdata (cA, sstoreAccountMap I.codeOwner σ (setterSlot i) value) k' C' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    setterWriteWfAll i
  have rdStore := evm_run h with [
    raw jumpdest h0 (by evm_ov), raw push1 (setterSlot i) h1 (by evm_ov),
    raw dup2 h2 (by evm_ov), raw swap1 h3 (by evm_ov) ]
  obtain ⟨_, _, rdMemory⟩ := rdStore.sstore hperm h4 (by evm_ov)
  have rdTopic := evm_run rdMemory with [
    raw push1 ⟨64⟩ h5 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) h6 mem_cost solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    raw dup2 h7 (by evm_ov), raw dup2 h8 (by evm_ov),
    raw mstore 6 (solcReturnMem value) (UInt256.ofNat 5) h9 mem_cost
      (by rfl) (by decide) (by evm_ov) ]
  have rdEnd := rdTopic.pushConst (setterTopic i) (width := 32) (op := .PUSH32)
    (by decide) h10 (by evm_ov)
  have rd1065 := evm_run rdEnd with [
    raw swap1 h11 (by evm_ov), raw push1 ⟨32⟩ h12 (by evm_ov), raw add h13 (by evm_ov),
    raw push2 ⟨1065⟩ h14 (by evm_ov), raw jump h15 (by jump_dest) (by evm_ov) ]
  exact wordEventReturn rd1065 hperm hret hov

end Auction
