import Benchmarks.Auction.InitializerRoutines
import Benchmarks.Auction.InitializeStores
import Benchmarks.Auction.PauseRoutine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

def initializeBaseMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  initializerOwnerMap (initializerStatusMap (initializerPauseMap (initializerEntered σ I) I) I) I

def initializePausedMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (initializeBaseMap σ I) ⟨51⟩
    (pauseWord (storedWord (initializeBaseMap σ I) I ⟨51⟩))

def initializeFinalMap (args : InitializeArgs) (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  initializerExited (args.storeMap (initializePausedMap σ I) I) I
    (UInt256.isZero (initializingWord σ I))

theorem pausedWord_initializerPauseMap (σ : AccountMap) (I : ExecutionEnv) :
    pausedWord (initializerPauseMap σ I) I = ⟨0⟩ := by
  unfold initializerPauseMap pausedWord
  cases ha : σ.find? I.codeOwner with
  | none =>
    rw [sstoreAccountMap_absent_same ha, storedWord_absent ha]
    decide
  | some acc =>
    rw [storedWord_sstore_present σ I ha]
    apply u256_inj
    simp only [uland_toNat, Nat.and_assoc]
    have hm : (UInt256.lnot (⟨255⟩ : UInt256)).toNat &&& (⟨255⟩ : UInt256).toNat = 0 :=
      by decide
    rw [hm, Nat.and_zero]
    rfl

theorem initializeBaseMap_unpaused (σ : AccountMap) (I : ExecutionEnv) :
    pausedWord (initializeBaseMap σ I) I = ⟨0⟩ := by
  unfold initializeBaseMap initializerOwnerMap initializerStatusMap pausedWord
  rw [storedWord_sstore_ne _ _ ⟨51⟩ ⟨151⟩ _ (by decide),
    storedWord_sstore_ne _ _ ⟨51⟩ ⟨101⟩ _ (by decide)]
  exact pausedWord_initializerPauseMap _ _

theorem initializeNestedSetup {I g s0 R rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨2213⟩ R solcFreePtrMem (UInt256.ofNat 3)
      rdata (cA, initializerEntered σ I) k C)
    (hperm : I.perm = true) (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨2237⟩ R solcFreePtrMem (UInt256.ofNat 3)
      rdata (cA, initializeBaseMap σ I) k' C' := by
  have hr := initializerEntered_ready σ I
  have rd3778 := evm_run h with [
    jumpdest, push2 ⟨2221⟩, push2 ⟨3778⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd2221⟩ := pausableInitializer rd3778 hr hperm (by jump_dest) (by evm_ov)
  have hr1 := initializerReady_sstore hr ⟨51⟩
    (UInt256.land (storedWord (initializerEntered σ I) I ⟨51⟩) (UInt256.lnot ⟨255⟩)) (by decide)
  have rd3896 := evm_run rd2221 with [
    jumpdest, push2 ⟨2229⟩, push2 ⟨3896⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd2229⟩ := reentrancyInitializer rd3896 hr1 hperm (by jump_dest) (by evm_ov)
  have hr2 := initializerReady_sstore hr1 ⟨101⟩ ⟨1⟩ (by decide)
  have rd3987 := evm_run rd2229 with [
    jumpdest, push2 ⟨2237⟩, push2 ⟨3987⟩, jump (by jump_dest) ]
  exact ownableInitializer rd3987 hr2 hperm (by jump_dest) hov

theorem initializeRuntime {I g s0 ret R rdata cA σ k C} (args : InitializeArgs)
    (h : RD auctionBytecode I g s0 ⟨2130⟩ (args.words.reverse ++ ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hc : args.canonical) (hg : initializingWord σ I ≠ ⟨0⟩ ∨ initializedWord σ I = ⟨0⟩)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R
      (addressEventMem solcFreePtrMem (UInt256.ofNat 3) (solcSourceWord I))
      (addressEventWords solcFreePtrMem (UInt256.ofNat 3) (solcSourceWord I))
      rdata (cA, initializeFinalMap args σ I) k' C' := by
  change RD _ _ _ _ _
    (args.duration :: args.minBidIncrement :: args.reservePrice :: args.timeBuffer ::
      args.weth :: args.nouns :: ret :: R) _ _ _ _ _ _ at h
  obtain ⟨_, _, rd2181⟩ := initializerGuardOk 0 h hg (by evm_ov)
  obtain ⟨_, _, rd2213⟩ := initializerBegin 0 rd2181 hperm (by evm_ov)
  obtain ⟨_, _, rd2237⟩ := initializeNestedSetup rd2213 hperm (by evm_ov)
  have rd3655 := evm_run rd2237 with [
    jumpdest, push2 ⟨2245⟩, push2 ⟨3655⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd2245⟩ := pauseRoutineOk rd3655 (initializeBaseMap_unpaused σ I)
    hperm (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd2326⟩ := initializeStoreArgs args rd2245 hc hperm (by omega)
  exact initializeExit args rd2326 hperm hret (by omega)

end Auction
