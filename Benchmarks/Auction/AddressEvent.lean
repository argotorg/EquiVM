import Benchmarks.Auction.DynamicMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def addressEventPtr (mem : ByteArray) (aw : UInt256) : UInt256 := loadedWord mem aw ⟨64⟩

noncomputable def addressEventMem (mem : ByteArray) (aw value : UInt256) : ByteArray :=
  (UInt256.land value solcAddrMask).toByteArray.write 0 mem (addressEventPtr mem aw).toNat 32

def addressEventStoredWords (mem : ByteArray) (aw : UInt256) : UInt256 :=
  expandedWords (expandedWords aw ⟨64⟩ ⟨32⟩) (addressEventPtr mem aw) ⟨32⟩

noncomputable def addressEventWords (mem : ByteArray) (aw value : UInt256) : UInt256 :=
  let aw' := addressEventStoredWords mem aw
  let ptr' := loadedWord (addressEventMem mem aw value) aw' ⟨64⟩
  expandedWords (expandedWords aw' ⟨64⟩ ⟨32⟩) ptr'
    (UInt256.sub (UInt256.add ⟨32⟩ (addressEventPtr mem aw)) ptr')

theorem addressEventReturn {I g s0 value topic ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨2971⟩ (value :: topic :: ret :: R)
      mem aw rdata acc k C)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R (addressEventMem mem aw value)
      (addressEventWords mem aw value) rdata acc k' C' := by
  have rd2987 := evm_run h with [
    jumpdest, push1 ⟨64⟩, raw mloadSymbolic (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap2, and, dup2 ]
  have rd2988 := rd2987.mstoreSymbolic (by native_decide) (by evm_ov)
  have rd2998 := evm_run rd2988 with [
    push1 ⟨32⟩, add, push1 ⟨64⟩, raw mloadSymbolic (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  obtain ⟨_, _, rd2999⟩ := rd2998.log1Symbolic (by native_decide) hperm (by evm_ov)
  exact ⟨_, _, evm_run rd2999 with [jump hret]⟩

end Auction
