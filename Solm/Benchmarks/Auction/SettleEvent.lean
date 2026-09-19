import Solm.Benchmarks.Auction.SettlePayment
import Solm.Benchmarks.Auction.Log2
import Solm.Benchmarks.Auction.PairEventMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

noncomputable def settleEventMem (mem : ByteArray) (ptr : UInt256) (s : Snapshot) : ByteArray :=
  pairEventMem mem ptr s.bidderWord s.amount

def settleEventWords (aw ptr : UInt256) : UInt256 :=
  pairEventWords aw ptr

theorem settleEventHeap {mem aw ptr s} (hm : MemoryCursor mem aw ptr)
    (hb : ptr.toNat + 64 ≤ 2 ^ 200) :
    HeapMemory (settleEventMem mem ptr s) (settleEventWords aw ptr) ptr :=
  pairEventHeap hm hb

theorem settleEventPrefix (mem : ByteArray) (ptr : UInt256) (s : Snapshot) :
    MemoryPrefix mem (settleEventMem mem ptr s) ptr.toNat :=
  pairEventPrefix mem ptr s.bidderWord s.amount

theorem settleEventGrowth {aw ptr} (ha : ActiveWords aw) (hb : ptr.toNat + 64 ≤ 2 ^ 200) :
    aw.toNat ≤ (settleEventWords aw ptr).toNat := pairEventGrowth ha hb

theorem settleEvent {I g s0 s snap ptr ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨4688⟩ (snap :: ret :: R) mem aw rdata acc k C)
    (hm : MemoryCursor mem aw ptr) (hb : ptr.toNat + 64 ≤ 2 ^ 200)
    (hsm : SnapshotMemory s mem aw snap) (hperm : I.perm = true)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R (settleEventMem mem ptr s)
      (settleEventWords aw ptr) rdata acc k' C' := by
  have hl0 : loadedWord mem aw snap = s.nounId := by
    have hl : loadedWord mem aw (snap + ⟨0⟩) = s.nounId := hsm.load ⟨0, by decide⟩
    rwa [u256_add_comm snap ⟨0⟩, u256_zero_add] at hl
  have ha0 : expandedWords aw snap ⟨32⟩ = aw := by
    have hl : expandedWords aw (snap + ⟨0⟩) ⟨32⟩ = aw := hsm.expand_eq ⟨0, by decide⟩
    rwa [u256_add_comm snap ⟨0⟩, u256_zero_add] at hl
  have hl4 : loadedWord mem aw (snap + ⟨128⟩) = s.bidderWord := hsm.load ⟨4, by decide⟩
  have ha4 : expandedWords aw (snap + ⟨128⟩) ⟨32⟩ = aw := hsm.expand_eq ⟨4, by decide⟩
  have hl1 : loadedWord mem aw (snap + ⟨32⟩) = s.amount := hsm.load ⟨1, by decide⟩
  have ha1 : expandedWords aw (snap + ⟨32⟩) ⟨32⟩ = aw := hsm.expand_eq ⟨1, by decide⟩
  have rd4691 := evm_run h with [jumpdest, dup1,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hl0, ha0] at rd4691
  have rd4696 := evm_run rd4691 with [push1 ⟨128⟩, dup3, add,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hl4, ha4] at rd4696
  have rd4702 := evm_run rd4696 with [push1 ⟨32⟩, dup1, dup5, add,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hl1, ha1] at rd4702
  have rd4706 := evm_run rd4702 with [push1 ⟨64⟩, dup1,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hm.load64, expandedWords64_eq hm.active] at rd4706
  have rd4719 := evm_run rd4706 with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap1, swap5, and, dup5, raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have hmask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  rw [hmask, Snapshot.bidderWord, maskTwice] at rd4719
  have rd4723 := evm_run rd4719 with [swap2, dup4, add,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have hp : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 :=
    addWord_toNat ptr ⟨32⟩ (by change ptr.toNat + 32 < 2 ^ 256; omega)
  rw [hp] at rd4723
  have rd4756 := rd4723.pushConst
    ⟨0xc9f72b276a388619c6d185d146697036241880c36654b1a3ffdad07c24038d99⟩
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd4761 := evm_run rd4756 with [swap2, add, push1 ⟨64⟩,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  have h1 := hm.writeAbove ptr s.bidderWord (le_refl _) (by omega)
  have h2 := h1.cursor.writeAbove (ptr + ⟨32⟩) s.amount (by omega) (by omega)
  rw [hp] at h2
  have hf := h2.load64
  simp only [Reasoning.Theory.writeWord, Snapshot.bidderWord] at hf
  rw [hf, expandedWords64_eq h2.active] at rd4761
  have rd4765 := evm_run rd4761 with [dup1, swap2, sub, swap1]
  have hsize : UInt256.sub (ptr + ⟨64⟩) ptr = ⟨64⟩ := by
    apply u256_inj
    have hadd : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 :=
      addWord_toNat ptr ⟨64⟩ (by change ptr.toNat + 64 < 2 ^ 256; omega)
    rw [usub_toNat (by omega), hadd]
    change ptr.toNat + 64 - ptr.toNat = 64
    omega
  rw [hsize] at rd4765
  obtain ⟨_, _, rd4766⟩ := rd4765.log2Symbolic (by native_decide) hperm (by evm_ov)
  exact ⟨_, _, evm_run rd4766 with [pop, jump hret]⟩

end Auction
