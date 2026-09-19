import Solm.Benchmarks.Auction.BytesMemory
import Solm.Benchmarks.Auction.ReturnDataCopy

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem rawEthAllocated {I g s0 z amount recipient ret R mem aw ptr out acc k C}
    (h : RD auctionBytecode I g s0 ⟨4842⟩
      (UInt256.ofNat out.size :: UInt256.ofNat out.size :: z :: ⟨0⟩ :: ⟨0⟩ ::
        amount :: recipient :: ret :: R) mem aw out acc k C)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + out.size + 63 ≤ 2 ^ 200)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret (z :: R)
      (bytesAllocMem mem out ptr) (bytesAllocWords aw ptr out.size) out acc k' C' := by
  have rd4845 := evm_run h with [push1 ⟨64⟩,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hm.load64, expandedWords64_eq hm.active] at rd4845
  have rd4860 := evm_run rd4845 with [swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩,
    raw returndatasize (by native_decide) (by evm_ov), add, and, dup3, add, push1 ⟨64⟩,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  simp only [u256_land_comm (UInt256.ofNat out.size + ⟨63⟩) (UInt256.lnot ⟨31⟩),
    expandedWords64_eq hm.active] at rd4860
  change RD _ _ _ _ ⟨4860⟩ (UInt256.ofNat out.size :: ptr :: z :: ⟨0⟩ :: ⟨0⟩ ::
    amount :: recipient :: ret :: R) (writeWord mem 64 (bytesAllocPtr ptr out.size))
    aw out acc _ _ at rd4860
  have rd4869 := evm_run rd4860 with [
    raw returndatasize (by native_decide) (by evm_ov), dup3,
    raw mstoreSymbolic (by native_decide) (by evm_ov),
    raw returndatasize (by native_decide) (by evm_ov), push0, push1 ⟨32⟩, dup5, add]
  have hn : (UInt256.ofNat out.size).toNat = out.size :=
    ulit_toNat' _ (by change out.size < 2 ^ 256; omega)
  have hadd : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 :=
    addWord_toNat ptr ⟨32⟩ (by change ptr.toNat + 32 < 2 ^ 256; omega)
  obtain ⟨_, _, rd4870⟩ := rd4869.returndatacopySymbolic (by native_decide)
    (by rw [hn]; change 0 + out.size ≤ out.size; omega) (by evm_ov)
  rw [hadd, hn] at rd4870
  change RD _ _ _ _ ⟨4870⟩ (UInt256.ofNat out.size :: ptr :: z :: ⟨0⟩ :: ⟨0⟩ ::
    amount :: recipient :: ret :: R) (bytesAllocMem mem out ptr)
    (bytesAllocWords aw ptr out.size) out acc _ _ at rd4870
  have rd4879 := evm_run rd4870 with [push2 ⟨4879⟩, jump (by jump_dest)]
  exact ⟨_, _, evm_run rd4879 with [jumpdest, pop, swap1, swap3, pop, pop, pop,
    jumpdest, swap3, swap2, pop, pop, jump hret]⟩

def rawReturnPtr (ptr : UInt256) (out : ByteArray) : UInt256 :=
  if out.size = 0 then ptr else bytesAllocPtr ptr out.size

noncomputable def rawReturnMem (mem out : ByteArray) (ptr : UInt256) : ByteArray :=
  if out.size = 0 then mem else bytesAllocMem mem out ptr

def rawReturnWords (aw ptr : UInt256) (out : ByteArray) : UInt256 :=
  if out.size = 0 then aw else bytesAllocWords aw ptr out.size

theorem rawEthAfter {I g s0 z amount recipient ret R mem aw ptr out acc k C}
    (h : RD auctionBytecode I g s0 ⟨4833⟩
      (z :: ⟨0⟩ :: ⟨0⟩ :: amount :: recipient :: ret :: R) mem aw out acc k C)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + out.size + 63 ≤ 2 ^ 200)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret (z :: R)
      (rawReturnMem mem out ptr) (rawReturnWords aw ptr out) out acc k' C' := by
  have rd4841 := evm_run h with [raw returndatasize (by native_decide) (by evm_ov),
    dup1, push0, dup2, eq, push2 ⟨4874⟩]
  by_cases hz : out.size = 0
  · have hw : UInt256.ofNat out.size = ⟨0⟩ := by rw [hz]; rfl
    rw [hw] at rd4841
    have rd4879 := evm_run rd4841 with [jumpiT (by decide) (by jump_dest),
      jumpdest, push1 ⟨96⟩, swap2, pop]
    have rdret := evm_run rd4879 with [jumpdest, pop, swap1, swap3, pop, pop, pop,
      jumpdest, swap3, swap2, pop, pop, jump hret]
    exact ⟨_, _, by simpa only [rawReturnMem, rawReturnWords, if_pos hz] using rdret⟩
  · have hn : (UInt256.ofNat out.size).toNat = out.size :=
      ulit_toNat' _ (by change out.size < 2 ^ 256; omega)
    have hw : UInt256.ofNat out.size ≠ ⟨0⟩ := by
      intro he
      have hv := congrArg UInt256.toNat he
      rw [hn] at hv
      exact hz hv
    have rd4842 := evm_run rd4841 with [jumpiNT (u256_eq_of_ne hw)]
    obtain ⟨_, _, rdret⟩ := rawEthAllocated rd4842 hm hb hret hov
    exact ⟨_, _, by simpa only [rawReturnMem, rawReturnWords, if_neg hz] using rdret⟩

theorem rawReturn_heap {mem aw ptr} (h : HeapMemory mem aw ptr) (out : ByteArray)
    (hb : ptr.toNat + out.size + 63 ≤ 2 ^ 200) :
    HeapMemory (rawReturnMem mem out ptr) (rawReturnWords aw ptr out) (rawReturnPtr ptr out) := by
  by_cases hz : out.size = 0
  · simpa only [rawReturnMem, rawReturnWords, rawReturnPtr, if_pos hz] using h
  · simpa only [rawReturnMem, rawReturnWords, rawReturnPtr, if_neg hz] using
      bytesAlloc_heap h out hz hb

theorem rawReturn_prefix {mem aw ptr} (h : HeapMemory mem aw ptr) (out : ByteArray) :
    MemoryPrefix mem (rawReturnMem mem out ptr) ptr.toNat := by
  by_cases hz : out.size = 0
  · simpa only [rawReturnMem, if_pos hz] using MemoryPrefix.refl mem ptr.toNat
  · simpa only [rawReturnMem, if_neg hz] using bytesAlloc_prefix h out hz

theorem rawReturnPtr_bounds {ptr : UInt256} {out : ByteArray}
    (hb : ptr.toNat + out.size + 63 ≤ 2 ^ 200) :
    ptr.toNat ≤ (rawReturnPtr ptr out).toNat ∧
      (rawReturnPtr ptr out).toNat ≤ ptr.toNat + out.size + 63 := by
  unfold rawReturnPtr
  split
  · constructor <;> omega
  · rw [bytesAllocPtr_toNat hb]
    constructor <;> omega

end Auction
