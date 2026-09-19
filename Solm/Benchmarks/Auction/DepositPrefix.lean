import Solm.Benchmarks.Auction.CallMemory
import Solm.Benchmarks.Auction.CallBridge

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def wethWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (storedWord σ I ⟨202⟩) solcAddrMask

theorem word_add_sub_left (a b : UInt256) : UInt256.sub (a + b) a = b := by
  apply u256_inj
  change ((a.val + b.val) - a.val).val = b.val.val
  rw [add_sub_cancel_left]

theorem word_div_one (word : UInt256) : UInt256.div word ⟨1⟩ = word := by
  apply u256_inj
  rw [udiv_toNat]
  exact Nat.div_one word.toNat

theorem depositPrefix {I g s0 amount recipient ret R mem aw ptr rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨3352⟩ (amount :: recipient :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 32 ≤ 2 ^ 200)
    (hov : R.length + 17 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨3417⟩
      (wethWord σ I :: wethWord σ I :: amount :: ptr :: ⟨4⟩ :: ptr :: ⟨0⟩ ::
        (ptr + ⟨4⟩) :: amount :: ⟨0xd0e30db0⟩ :: wethWord σ I :: amount ::
        recipient :: ret :: R)
      (selectorMem mem ptr depositWord) (expandedWords aw ptr ⟨32⟩) rdata (cA, σ) k' C' := by
  have rd3356 := evm_run h with [push1 ⟨202⟩, push0, swap1]
  obtain ⟨_, _, rd3357⟩ := rd3356.sload (by native_decide) (by evm_ov)
  have rd3387 := evm_run rd3357 with [swap1, push2 ⟨256⟩,
    raw exp (by native_decide) (by evm_ov), swap1, div,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, push4 ⟨0xd0e30db0⟩]
  have he : UInt256.exp ⟨256⟩ ⟨0⟩ = ⟨1⟩ := by native_decide
  have hmask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  simp only [he, hmask, word_div_one, u256_land_comm solcAddrMask, maskTwice] at rd3387
  change RD _ _ _ _ ⟨3387⟩ (⟨0xd0e30db0⟩ :: wethWord σ I :: amount :: recipient :: ret :: R)
    mem aw rdata (cA, σ) _ _ at rd3387
  have rd3391 := evm_run rd3387 with [dup3, push1 ⟨64⟩,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hm.load64, expandedWords64_eq hm.active] at rd3391
  have rd3403 := evm_run rd3391 with [dup3, push4 ⟨0xffffffff⟩, and, push1 ⟨224⟩,
    shl, dup2, raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have hsel : UInt256.shiftLeft (UInt256.land ⟨0xffffffff⟩ ⟨0xd0e30db0⟩) ⟨224⟩ =
      depositWord := by native_decide
  simp only [hsel] at rd3403
  change RD _ _ _ _ ⟨3403⟩ (ptr :: amount :: ⟨0xd0e30db0⟩ :: wethWord σ I ::
    amount :: recipient :: ret :: R) (selectorMem mem ptr depositWord)
    (expandedWords aw ptr ⟨32⟩) rdata (cA, σ) _ _ at rd3403
  have hh := selectorMem_heap hm depositWord hb
  have rd3410 := evm_run rd3403 with [push1 ⟨4⟩, add, push0, push1 ⟨64⟩,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hh.load64, expandedWords64_eq hh.active] at rd3410
  have rd3417 := evm_run rd3410 with [dup1, dup4, sub, dup2, dup6, dup9, dup1]
  simp only [word_add_sub_left, u256_add_comm ⟨4⟩ ptr] at rd3417
  exact ⟨_, _, rd3417⟩

theorem depositCodeGuard {I g s0 amount recipient ret R mem aw ptr rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨3352⟩ (amount :: recipient :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 32 ≤ 2 ^ 200)
    (hov : R.length + 17 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨3424⟩
      (⟨3428⟩ :: UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (wethWord σ I))) ::
        UInt256.isZero (extCodeSizeWord σ (wethWord σ I)) :: wethWord σ I ::
        amount :: ptr :: ⟨4⟩ :: ptr :: ⟨0⟩ :: (ptr + ⟨4⟩) :: amount ::
        ⟨0xd0e30db0⟩ :: wethWord σ I :: amount :: recipient :: ret :: R)
      (selectorMem mem ptr depositWord) (expandedWords aw ptr ⟨32⟩) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd3417⟩ := depositPrefix h hm hb hov
  obtain ⟨_, _, rd3418⟩ := rd3417.extcodesize (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd3418 with [iszero, dup1, iszero, push2 ⟨3428⟩]⟩

theorem depositNoCode {I g s0 amount recipient ret R mem aw ptr rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨3352⟩ (amount :: recipient :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 32 ≤ 2 ^ 200)
    (hno : extCodeSizeWord σ (wethWord σ I) = ⟨0⟩) (hov : R.length + 18 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, rd3424⟩ := depositCodeGuard h hm hb (by omega)
  exact evm_run rd3424 with [jumpiNT (by rw [hno]; decide),
    raw auctionRevert0 (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem depositCallPrefix {I g s0 amount recipient ret R mem aw ptr rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨3352⟩ (amount :: recipient :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 32 ≤ 2 ^ 200)
    (hyes : extCodeSizeWord σ (wethWord σ I) ≠ ⟨0⟩) (hov : R.length + 18 ≤ 1024) :
    ∃ gasArg k' C', RD auctionBytecode I g s0 ⟨3431⟩
      (gasArg :: wethWord σ I :: amount :: ptr :: ⟨4⟩ :: ptr :: ⟨0⟩ ::
        (ptr + ⟨4⟩) :: amount :: ⟨0xd0e30db0⟩ :: wethWord σ I :: amount ::
        recipient :: ret :: R)
      (selectorMem mem ptr depositWord) (expandedWords aw ptr ⟨32⟩) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd3424⟩ := depositCodeGuard h hm hb (by omega)
  have rd3430 := evm_run rd3424 with [
    jumpiT (by rw [isZero_eq_zero_of_ne hyes]; decide) (by jump_dest), jumpdest, pop]
  obtain ⟨gasArg, rd3431⟩ := rd3430.gas (by native_decide) (by evm_ov)
  exact ⟨gasArg, _, _, rd3431⟩

end Auction
