import Solm.Benchmarks.Auction.BurnPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def contractAddressWord (I : ExecutionEnv) : UInt256 := UInt256.ofNat I.codeOwner.val

theorem nounTransferPrefix {I g s0 snap nounId bidder ret R mem aw ptr rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨4536⟩ (snap :: ret :: R) mem aw rdata (cA, σ) k C)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 100 ≤ 2 ^ 200)
    (hn : loadedWord mem aw snap = nounId) (ha : expandedWords aw snap ⟨32⟩ = aw)
    (hbid : loadedWord mem aw (snap + ⟨128⟩) = bidder)
    (hab : expandedWords aw (snap + ⟨128⟩) ⟨32⟩ = aw)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨4613⟩
      (nounsWord σ I :: nounsWord σ I :: ⟨0⟩ :: ptr :: ⟨100⟩ :: ptr :: ⟨0⟩ ::
        (ptr + ⟨100⟩) :: ⟨0x23b872dd⟩ :: nounsWord σ I :: snap :: ret :: R)
      (callMem3 mem ptr transferFromWord (contractAddressWord I) (UInt256.land bidder solcAddrMask)
        nounId) (callWords3 aw ptr) rdata (cA, σ) k' C' := by
  have rd4539 := evm_run h with [jumpdest, push1 ⟨201⟩]
  obtain ⟨_, _, rd4540⟩ := rd4539.sload (by native_decide) (by evm_ov)
  have rd4545 := evm_run rd4540 with [push1 ⟨128⟩, dup3, add,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hbid, hab] at rd4545
  have rd4547 := evm_run rd4545 with [dup3, raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hn, ha] at rd4547
  have rd4550 := evm_run rd4547 with [push1 ⟨64⟩,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hm.load64, expandedWords64_eq hm.active] at rd4550
  have rd4560 := evm_run rd4550 with [push4 ⟨0x23b872dd⟩, push1 ⟨224⟩, shl, dup2,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have hsel : UInt256.shiftLeft ⟨0x23b872dd⟩ ⟨224⟩ = transferFromWord := by native_decide
  rw [hsel] at rd4560
  change RD _ _ _ _ ⟨4560⟩ (ptr :: nounId :: bidder :: storedWord σ I ⟨201⟩ :: snap :: ret :: R)
    (selectorMem mem ptr transferFromWord) (expandedWords aw ptr ⟨32⟩) rdata (cA, σ) _ _ at rd4560
  have h4 : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 :=
    addWord_toNat ptr ⟨4⟩ (by change ptr.toNat + 4 < 2 ^ 256; omega)
  have h36 : (ptr + ⟨36⟩).toNat = ptr.toNat + 36 :=
    addWord_toNat ptr ⟨36⟩ (by change ptr.toNat + 36 < 2 ^ 256; omega)
  have h68 : (ptr + ⟨68⟩).toNat = ptr.toNat + 68 :=
    addWord_toNat ptr ⟨68⟩ (by change ptr.toNat + 68 < 2 ^ 256; omega)
  have rd4566 := evm_run rd4560 with [address, push1 ⟨4⟩, dup3, add,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  rw [h4] at rd4566
  change RD _ _ _ _ ⟨4566⟩ (ptr :: nounId :: bidder :: storedWord σ I ⟨201⟩ :: snap :: ret :: R)
    (callMem1 mem ptr transferFromWord (contractAddressWord I)) (callWords1 aw ptr)
    rdata (cA, σ) _ _ at rd4566
  have rd4582 := evm_run rd4566 with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap3, dup4, and, push1 ⟨36⟩, dup3, add, raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have hmask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  simp only [hmask, u256_land_comm solcAddrMask, h36] at rd4582
  change RD _ _ _ _ ⟨4582⟩ (ptr :: nounId :: solcAddrMask :: storedWord σ I ⟨201⟩ ::
    snap :: ret :: R) (callMem2 mem ptr transferFromWord (contractAddressWord I)
      (UInt256.land bidder solcAddrMask)) (callWords2 aw ptr) rdata (cA, σ) _ _ at rd4582
  have rd4590 := evm_run rd4582 with [push1 ⟨68⟩, dup2, add, swap2, swap1, swap2,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  rw [h68] at rd4590
  change RD _ _ _ _ ⟨4590⟩ (ptr :: solcAddrMask :: storedWord σ I ⟨201⟩ :: snap :: ret :: R)
    (callMem3 mem ptr transferFromWord (contractAddressWord I) (UInt256.land bidder solcAddrMask)
      nounId) (callWords3 aw ptr) rdata (cA, σ) _ _ at rd4590
  have rd4606 := evm_run rd4590 with [swap2, and, swap1, push4 ⟨0x23b872dd⟩, swap1,
    push1 ⟨100⟩, add, push0, push1 ⟨64⟩, raw mloadSymbolic (by native_decide) (by evm_ov)]
  have hh := callMem3_heap hm transferFromWord (contractAddressWord I)
    (UInt256.land bidder solcAddrMask) nounId hb
  rw [hh.load64, expandedWords64_eq hh.active, u256_add_comm ⟨100⟩ ptr] at rd4606
  have rd4613 := evm_run rd4606 with [dup1, dup4, sub, dup2, push0, dup8, dup1]
  rw [word_add_sub_left] at rd4613
  exact ⟨_, _, rd4613⟩

theorem nounTransferCodeGuard {I g s0 snap nounId bidder ret R mem aw ptr rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨4536⟩ (snap :: ret :: R) mem aw rdata (cA, σ) k C)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 100 ≤ 2 ^ 200)
    (hn : loadedWord mem aw snap = nounId) (ha : expandedWords aw snap ⟨32⟩ = aw)
    (hbid : loadedWord mem aw (snap + ⟨128⟩) = bidder)
    (hab : expandedWords aw (snap + ⟨128⟩) ⟨32⟩ = aw)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨4620⟩
      (⟨4624⟩ :: UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (nounsWord σ I))) ::
        UInt256.isZero (extCodeSizeWord σ (nounsWord σ I)) :: nounsWord σ I :: ⟨0⟩ ::
        ptr :: ⟨100⟩ :: ptr :: ⟨0⟩ :: (ptr + ⟨100⟩) :: ⟨0x23b872dd⟩ ::
        nounsWord σ I :: snap :: ret :: R)
      (callMem3 mem ptr transferFromWord (contractAddressWord I) (UInt256.land bidder solcAddrMask)
        nounId) (callWords3 aw ptr) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd4613⟩ := nounTransferPrefix h hm hb hn ha hbid hab hov
  obtain ⟨_, _, rd4614⟩ := rd4613.extcodesize (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd4614 with [iszero, dup1, iszero, push2 ⟨4624⟩]⟩

theorem nounTransferNoCode {I g s0 snap nounId bidder ret R mem aw ptr rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨4536⟩ (snap :: ret :: R) mem aw rdata (cA, σ) k C)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 100 ≤ 2 ^ 200)
    (hn : loadedWord mem aw snap = nounId) (ha : expandedWords aw snap ⟨32⟩ = aw)
    (hbid : loadedWord mem aw (snap + ⟨128⟩) = bidder)
    (hab : expandedWords aw (snap + ⟨128⟩) ⟨32⟩ = aw)
    (hno : extCodeSizeWord σ (nounsWord σ I) = ⟨0⟩) (hov : R.length + 17 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, rd4620⟩ := nounTransferCodeGuard h hm hb hn ha hbid hab (by omega)
  exact evm_run rd4620 with [jumpiNT (by rw [hno]; decide),
    raw auctionRevert0 (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem nounTransferCallPrefix {I g s0 snap nounId bidder ret R mem aw ptr rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨4536⟩ (snap :: ret :: R) mem aw rdata (cA, σ) k C)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 100 ≤ 2 ^ 200)
    (hn : loadedWord mem aw snap = nounId) (ha : expandedWords aw snap ⟨32⟩ = aw)
    (hbid : loadedWord mem aw (snap + ⟨128⟩) = bidder)
    (hab : expandedWords aw (snap + ⟨128⟩) ⟨32⟩ = aw)
    (hyes : extCodeSizeWord σ (nounsWord σ I) ≠ ⟨0⟩) (hov : R.length + 17 ≤ 1024) :
    ∃ gasArg k' C', RD auctionBytecode I g s0 ⟨4627⟩
      (gasArg :: nounsWord σ I :: ⟨0⟩ :: ptr :: ⟨100⟩ :: ptr :: ⟨0⟩ ::
        (ptr + ⟨100⟩) :: ⟨0x23b872dd⟩ :: nounsWord σ I :: snap :: ret :: R)
      (callMem3 mem ptr transferFromWord (contractAddressWord I) (UInt256.land bidder solcAddrMask)
        nounId) (callWords3 aw ptr) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd4620⟩ := nounTransferCodeGuard h hm hb hn ha hbid hab (by omega)
  have rd4626 := evm_run rd4620 with [
    jumpiT (by rw [isZero_eq_zero_of_ne hyes]; decide) (by jump_dest), jumpdest, pop]
  obtain ⟨gasArg, rd4627⟩ := rd4626.gas (by native_decide) (by evm_ov)
  exact ⟨gasArg, _, _, rd4627⟩

end Auction
