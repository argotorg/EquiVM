import Solm.Benchmarks.Auction.DepositPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem transferPrefix {I g s0 amount recipient ret oldTarget R mem aw ptr rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨3449⟩
      (amount :: ⟨0xd0e30db0⟩ :: oldTarget :: amount :: recipient :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 68 ≤ 2 ^ 200)
    (hov : R.length + 18 ≤ 1024) :
    ∃ gasArg k' C', RD auctionBytecode I g s0 ⟨3517⟩
      (gasArg :: wethWord σ I :: ⟨0⟩ :: ptr :: ⟨68⟩ :: ptr :: ⟨32⟩ ::
        (ptr + ⟨68⟩) :: ⟨0xa9059cbb⟩ :: wethWord σ I :: amount :: recipient :: ret :: R)
      (callMem2 mem ptr transferWord (UInt256.land recipient solcAddrMask) amount)
      (callWords2 aw ptr) rdata (cA, σ) k' C' := by
  have rd3451 := evm_run h with [push1 ⟨202⟩]
  obtain ⟨_, _, rd3452⟩ := rd3451.sload (by native_decide) (by evm_ov)
  have rd3455 := evm_run rd3452 with [push1 ⟨64⟩,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hm.load64, expandedWords64_eq hm.active] at rd3455
  have rd3465 := evm_run rd3455 with [push4 ⟨0xa9059cbb⟩, push1 ⟨224⟩, shl, dup2,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have hsel : UInt256.shiftLeft ⟨0xa9059cbb⟩ ⟨224⟩ = transferWord := by native_decide
  simp only [hsel] at rd3465
  change RD _ _ _ _ ⟨3465⟩ (ptr :: storedWord σ I ⟨202⟩ :: amount :: ⟨0xd0e30db0⟩ ::
    oldTarget :: amount :: recipient :: ret :: R) (selectorMem mem ptr transferWord)
    (expandedWords aw ptr ⟨32⟩) rdata (cA, σ) _ _ at rd3465
  have rd3481 := evm_run rd3465 with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl,
    sub, dup8, dup2, and, push1 ⟨4⟩, dup4, add,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have hmask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have h4 : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 :=
    addWord_toNat ptr ⟨4⟩ (by change ptr.toNat + 4 < 2 ^ 256; omega)
  have h36 : (ptr + ⟨36⟩).toNat = ptr.toNat + 36 :=
    addWord_toNat ptr ⟨36⟩ (by change ptr.toNat + 36 < 2 ^ 256; omega)
  simp only [hmask, u256_land_comm solcAddrMask, h4] at rd3481
  have rd3488 := evm_run rd3481 with [push1 ⟨36⟩, dup3, add, dup8, swap1,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  simp only [h36] at rd3488
  change RD _ _ _ _ ⟨3488⟩ (solcAddrMask :: ptr :: storedWord σ I ⟨202⟩ :: amount ::
    ⟨0xd0e30db0⟩ :: oldTarget :: amount :: recipient :: ret :: R)
    (callMem2 mem ptr transferWord (UInt256.land recipient solcAddrMask) amount)
    (callWords2 aw ptr) rdata (cA, σ) _ _ at rd3488
  have rd3505 := evm_run rd3488 with [swap1, swap2, and, swap4, pop,
    push4 ⟨0xa9059cbb⟩, swap3, pop, push1 ⟨68⟩, add, swap1, pop]
  have rd3510 := evm_run rd3505 with [push1 ⟨32⟩, push1 ⟨64⟩,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  have hh := callMem2_heap hm transferWord (UInt256.land recipient solcAddrMask) amount hb
  rw [hh.load64, expandedWords64_eq hh.active] at rd3510
  have rd3516 := evm_run rd3510 with [dup1, dup4, sub, dup2, push0, dup8]
  simp only [u256_add_comm ⟨68⟩ ptr, word_add_sub_left] at rd3516
  obtain ⟨gasArg, rd3517⟩ := rd3516.gas (by native_decide) (by evm_ov)
  exact ⟨gasArg, _, _, rd3517⟩

end Auction
