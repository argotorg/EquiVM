import Benchmarks.Auction.NounCallMemory
import Benchmarks.Auction.DepositPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def nounsWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (storedWord σ I ⟨201⟩) solcAddrMask

theorem burnPrefix {I g s0 snap nounId ret R mem aw ptr rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨4435⟩ (snap :: ret :: R) mem aw rdata (cA, σ) k C)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 36 ≤ 2 ^ 200)
    (hn : loadedWord mem aw snap = nounId) (ha : expandedWords aw snap ⟨32⟩ = aw)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨4498⟩
      (nounsWord σ I :: nounsWord σ I :: ⟨0⟩ :: ptr :: ⟨36⟩ :: ptr :: ⟨0⟩ ::
        (ptr + ⟨36⟩) :: ⟨0x42966c68⟩ :: nounsWord σ I :: snap :: ret :: R)
      (callMem1 mem ptr burnWord nounId) (callWords1 aw ptr) rdata (cA, σ) k' C' := by
  have rd4437 := evm_run h with [push1 ⟨201⟩]
  obtain ⟨_, _, rd4438⟩ := rd4437.sload (by native_decide) (by evm_ov)
  have rd4440 := evm_run rd4438 with [dup2, raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hn, ha] at rd4440
  have rd4443 := evm_run rd4440 with [push1 ⟨64⟩,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hm.load64, expandedWords64_eq hm.active] at rd4443
  have rd4453 := evm_run rd4443 with [push4 ⟨0x0852cd8d⟩, push1 ⟨227⟩, shl, dup2,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have hsel : UInt256.shiftLeft ⟨0x0852cd8d⟩ ⟨227⟩ = burnWord := by native_decide
  rw [hsel] at rd4453
  change RD _ _ _ _ ⟨4453⟩ (ptr :: nounId :: storedWord σ I ⟨201⟩ :: snap :: ret :: R)
    (selectorMem mem ptr burnWord) (expandedWords aw ptr ⟨32⟩) rdata (cA, σ) _ _ at rd4453
  have rd4481 := evm_run rd4453 with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap1, swap3, and, swap2, push4 ⟨0x42966c68⟩, swap2, push2 ⟨4486⟩, swap2,
    push1 ⟨4⟩, add, swap1, dup2, raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have hmask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have h4 : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 :=
    addWord_toNat ptr ⟨4⟩ (by change ptr.toNat + 4 < 2 ^ 256; omega)
  simp only [hmask, u256_add_comm ⟨4⟩ ptr, h4] at rd4481
  change RD _ _ _ _ ⟨4481⟩ ((ptr + ⟨4⟩) :: ⟨4486⟩ :: ⟨0x42966c68⟩ ::
    nounsWord σ I :: snap :: ret :: R) (callMem1 mem ptr burnWord nounId)
    (callWords1 aw ptr) rdata (cA, σ) _ _ at rd4481
  have rd4491 := evm_run rd4481 with [push1 ⟨32⟩, add, swap1, jump (by jump_dest),
    jumpdest, push0, push1 ⟨64⟩, raw mloadSymbolic (by native_decide) (by evm_ov)]
  have hh := callMem1_heap hm burnWord nounId hb
  rw [hh.load64, expandedWords64_eq hh.active] at rd4491
  have hadd : (⟨32⟩ : UInt256) + (ptr + ⟨4⟩) = ptr + ⟨36⟩ := by
    rw [u256_add_comm ⟨32⟩, u256_add_assoc]
    rfl
  rw [hadd] at rd4491
  have rd4498 := evm_run rd4491 with [dup1, dup4, sub, dup2, push0, dup8, dup1]
  rw [word_add_sub_left] at rd4498
  exact ⟨_, _, rd4498⟩

theorem burnCodeGuard {I g s0 snap nounId ret R mem aw ptr rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨4435⟩ (snap :: ret :: R) mem aw rdata (cA, σ) k C)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 36 ≤ 2 ^ 200)
    (hn : loadedWord mem aw snap = nounId) (ha : expandedWords aw snap ⟨32⟩ = aw)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨4505⟩
      (⟨4509⟩ :: UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (nounsWord σ I))) ::
        UInt256.isZero (extCodeSizeWord σ (nounsWord σ I)) :: nounsWord σ I :: ⟨0⟩ ::
        ptr :: ⟨36⟩ :: ptr :: ⟨0⟩ :: (ptr + ⟨36⟩) :: ⟨0x42966c68⟩ ::
        nounsWord σ I :: snap :: ret :: R)
      (callMem1 mem ptr burnWord nounId) (callWords1 aw ptr) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd4498⟩ := burnPrefix h hm hb hn ha hov
  obtain ⟨_, _, rd4499⟩ := rd4498.extcodesize (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd4499 with [iszero, dup1, iszero, push2 ⟨4509⟩]⟩

theorem burnNoCode {I g s0 snap nounId ret R mem aw ptr rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨4435⟩ (snap :: ret :: R) mem aw rdata (cA, σ) k C)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 36 ≤ 2 ^ 200)
    (hn : loadedWord mem aw snap = nounId) (ha : expandedWords aw snap ⟨32⟩ = aw)
    (hno : extCodeSizeWord σ (nounsWord σ I) = ⟨0⟩) (hov : R.length + 16 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, rd4505⟩ := burnCodeGuard h hm hb hn ha (by omega)
  exact evm_run rd4505 with [jumpiNT (by rw [hno]; decide),
    raw auctionRevert0 (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem burnCallPrefix {I g s0 snap nounId ret R mem aw ptr rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨4435⟩ (snap :: ret :: R) mem aw rdata (cA, σ) k C)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 36 ≤ 2 ^ 200)
    (hn : loadedWord mem aw snap = nounId) (ha : expandedWords aw snap ⟨32⟩ = aw)
    (hyes : extCodeSizeWord σ (nounsWord σ I) ≠ ⟨0⟩) (hov : R.length + 16 ≤ 1024) :
    ∃ gasArg k' C', RD auctionBytecode I g s0 ⟨4512⟩
      (gasArg :: nounsWord σ I :: ⟨0⟩ :: ptr :: ⟨36⟩ :: ptr :: ⟨0⟩ ::
        (ptr + ⟨36⟩) :: ⟨0x42966c68⟩ :: nounsWord σ I :: snap :: ret :: R)
      (callMem1 mem ptr burnWord nounId) (callWords1 aw ptr) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd4505⟩ := burnCodeGuard h hm hb hn ha (by omega)
  have rd4511 := evm_run rd4505 with [
    jumpiT (by rw [isZero_eq_zero_of_ne hyes]; decide) (by jump_dest), jumpdest, pop]
  obtain ⟨gasArg, rd4512⟩ := rd4511.gas (by native_decide) (by evm_ov)
  exact ⟨gasArg, _, _, rd4512⟩

end Auction
