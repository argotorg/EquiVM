import Solm.Benchmarks.Auction.DepositPrefix
import Solm.Benchmarks.Auction.BurnPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def mintWord : UInt256 := ⟨0x1249c58b * 2 ^ 224⟩

theorem mintWord_prefix : mintWord.toByteArray.extract 0 4 = mintSelector := by
  native_decide

theorem mintPrefix {I g s0 ret R mem aw ptr rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨3000⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 32 ≤ 2 ^ 200)
    (hov : R.length + 13 ≤ 1024) :
    ∃ gasArg k' C', RD auctionBytecode I g s0 ⟨3066⟩
      (gasArg :: nounsWord σ I :: ⟨0⟩ :: ptr :: ⟨4⟩ :: ptr :: ⟨32⟩ ::
        (ptr + ⟨4⟩) :: ⟨0x1249c58b⟩ :: nounsWord σ I :: ret :: R)
      (selectorMem mem ptr mintWord) (expandedWords aw ptr ⟨32⟩)
      rdata (cA, σ) k' C' := by
  have rd3005 := evm_run h with [jumpdest, push1 ⟨201⟩, push0, swap1]
  obtain ⟨_, _, rd3006⟩ := rd3005.sload (by native_decide) (by evm_ov)
  have rd3036 := evm_run rd3006 with [swap1, push2 ⟨256⟩,
    raw exp (by native_decide) (by evm_ov), swap1, div,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, push4 ⟨0x1249c58b⟩]
  have he : UInt256.exp ⟨256⟩ ⟨0⟩ = ⟨1⟩ := by native_decide
  have hmask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  simp only [he, hmask, word_div_one, u256_land_comm solcAddrMask, maskTwice] at rd3036
  change RD _ _ _ _ ⟨3036⟩ (⟨0x1249c58b⟩ :: nounsWord σ I :: ret :: R)
    mem aw rdata (cA, σ) _ _ at rd3036
  have rd3039 := evm_run rd3036 with [push1 ⟨64⟩,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hm.load64, expandedWords64_eq hm.active] at rd3039
  have rd3051 := evm_run rd3039 with [dup2, push4 ⟨0xffffffff⟩, and, push1 ⟨224⟩,
    shl, dup2, raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have hsel : UInt256.shiftLeft (UInt256.land ⟨0xffffffff⟩ ⟨0x1249c58b⟩) ⟨224⟩ =
      mintWord := by native_decide
  simp only [hsel] at rd3051
  change RD _ _ _ _ ⟨3051⟩ (ptr :: ⟨0x1249c58b⟩ :: nounsWord σ I :: ret :: R)
    (selectorMem mem ptr mintWord) (expandedWords aw ptr ⟨32⟩) rdata (cA, σ) _ _ at rd3051
  have hh := selectorMem_heap hm mintWord hb
  have rd3059 := evm_run rd3051 with [push1 ⟨4⟩, add, push1 ⟨32⟩, push1 ⟨64⟩,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hh.load64, expandedWords64_eq hh.active] at rd3059
  have rd3065 := evm_run rd3059 with [dup1, dup4, sub, dup2, push0, dup8]
  simp only [u256_add_comm ⟨4⟩ ptr, word_add_sub_left] at rd3065
  obtain ⟨gasArg, rd3066⟩ := rd3065.gas (by native_decide) (by evm_ov)
  exact ⟨gasArg, _, _, rd3066⟩

end Auction
