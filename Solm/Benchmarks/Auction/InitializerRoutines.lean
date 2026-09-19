import Solm.Benchmarks.Auction.InitializerTail
import Solm.Benchmarks.Auction.OwnershipRoutine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

def initializerPauseMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨51⟩
    (UInt256.land (storedWord σ I ⟨51⟩) (UInt256.lnot ⟨255⟩))

def initializerStatusMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨101⟩ ⟨1⟩

def initializerOwnerMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨151⟩
    (setAddressOffset0Word (storedWord σ I ⟨151⟩) (solcSourceWord I))

theorem pausableInitializerLeaf {I g s0 ret R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨4993⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hr : InitializerReady σ I) (hperm : I.perm = true)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R mem aw rdata
      (cA, initializerPauseMap σ I) k' C' := by
  obtain ⟨_, _, rd5076⟩ := initializerPrefixReady 4 h hr hperm (by evm_ov)
  have rd5080 := evm_run rd5076 with [jumpdest, push1 ⟨51⟩, dup1]
  obtain ⟨_, _, rd5081⟩ := rd5080.sload (by native_decide) (by evm_ov)
  have rd5086 := evm_run rd5081 with [push1 ⟨255⟩, not, and, swap1]
  obtain ⟨_, _, rd5087⟩ := rd5086.sstore hperm (by native_decide) (by evm_ov)
  change RD _ _ _ _ _ _ _ _ _ (cA, sstoreAccountMap I.codeOwner σ ⟨51⟩
    (UInt256.land (UInt256.lnot ⟨255⟩) (storedWord σ I ⟨51⟩))) _ _ at rd5087
  rw [u256_land_comm (UInt256.lnot ⟨255⟩)] at rd5087
  exact initializerTail 2 rd5087
    (initializerNestedFlag_sstore (initializerNestedFlag_of_ready hr) _ _) hperm hret (by omega)

theorem reentrancyInitializerLeaf {I g s0 ret R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨5105⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hr : InitializerReady σ I) (hperm : I.perm = true)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R mem aw rdata
      (cA, initializerStatusMap σ I) k' C' := by
  obtain ⟨_, _, rd5188⟩ := initializerPrefixReady 5 h hr hperm (by evm_ov)
  have rd5193 := evm_run rd5188 with [jumpdest, push1 ⟨1⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd5194⟩ := rd5193.sstore hperm (by native_decide) (by evm_ov)
  exact initializerTail 3 rd5194
    (initializerNestedFlag_sstore (initializerNestedFlag_of_ready hr) _ _) hperm hret (by omega)

theorem ownableInitializerLeaf {I g s0 ret R rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨5212⟩ (ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hr : InitializerReady σ I) (hperm : I.perm = true)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R solcFreePtrMem (UInt256.ofNat 3) rdata
      (cA, initializerOwnerMap σ I) k' C' := by
  obtain ⟨_, _, rd5295⟩ := initializerPrefixReady 6 h hr hperm (by evm_ov)
  have rd3574 := evm_run rd5295 with [
    jumpdest, push2 ⟨3877⟩, caller, push2 ⟨3574⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd3877⟩ := transferOwnerRoutine rd3574 hperm (by jump_dest) (by evm_ov)
  exact initializerSharedTail rd3877
    (initializerNestedFlag_sstore (initializerNestedFlag_of_ready hr) _ _) hperm hret (by omega)

theorem pausableInitializer {I g s0 ret R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨3778⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hr : InitializerReady σ I) (hperm : I.perm = true)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R mem aw rdata
      (cA, initializerPauseMap σ I) k' C' := by
  obtain ⟨_, _, rd3861⟩ := initializerPrefixReady 1 h hr hperm (by evm_ov)
  have rd4892 := evm_run rd3861 with [
    jumpdest, push2 ⟨3869⟩, push2 ⟨4892⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd3869⟩ := contextInitializer rd4892 hr hperm (by jump_dest) (by evm_ov)
  have rd4993 := evm_run rd3869 with [
    jumpdest, push2 ⟨3877⟩, push2 ⟨4993⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd3877⟩ := pausableInitializerLeaf rd4993 hr hperm (by jump_dest) (by evm_ov)
  exact initializerSharedTail rd3877
    (initializerNestedFlag_sstore (initializerNestedFlag_of_ready hr) _ _) hperm hret (by omega)

theorem reentrancyInitializer {I g s0 ret R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨3896⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hr : InitializerReady σ I) (hperm : I.perm = true)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R mem aw rdata
      (cA, initializerStatusMap σ I) k' C' := by
  obtain ⟨_, _, rd3979⟩ := initializerPrefixReady 2 h hr hperm (by evm_ov)
  have rd5105 := evm_run rd3979 with [
    jumpdest, push2 ⟨3877⟩, push2 ⟨5105⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd3877⟩ := reentrancyInitializerLeaf rd5105 hr hperm (by jump_dest) (by evm_ov)
  exact initializerSharedTail rd3877
    (initializerNestedFlag_sstore (initializerNestedFlag_of_ready hr) _ _) hperm hret (by omega)

theorem ownableInitializer {I g s0 ret R rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨3987⟩ (ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hr : InitializerReady σ I) (hperm : I.perm = true)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R solcFreePtrMem (UInt256.ofNat 3) rdata
      (cA, initializerOwnerMap σ I) k' C' := by
  obtain ⟨_, _, rd4070⟩ := initializerPrefixReady 3 h hr hperm (by evm_ov)
  have rd4892 := evm_run rd4070 with [
    jumpdest, push2 ⟨4078⟩, push2 ⟨4892⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd4078⟩ := contextInitializer rd4892 hr hperm (by jump_dest) (by evm_ov)
  have rd5212 := evm_run rd4078 with [
    jumpdest, push2 ⟨3877⟩, push2 ⟨5212⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd3877⟩ := ownableInitializerLeaf rd5212 hr hperm (by jump_dest) (by evm_ov)
  exact initializerSharedTail rd3877
    (initializerNestedFlag_sstore (initializerNestedFlag_of_ready hr) _ _) hperm hret (by omega)

end Auction
