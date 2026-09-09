import Benchmarks.Auction.InitializeAbsentRoutines
import Benchmarks.Auction.InitializeStores

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

theorem auctionInitializeOwnableUnchained_absent {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : Nat} {ret : UInt256} {R : List UInt256}
    (hR : R.length ≤ 970) (hmissing : σ.find? I.codeOwner = none)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5212⟩
      (ret :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h5295⟩ := auctionInitializerAbsentEnter5212 (by evm_ov) hmissing hperm h
  have h3574 := evm_run h5295 with [
    jumpdest, push2 ⟨3877⟩, caller, push2 ⟨3574⟩, jump (by jump_dest)]
  obtain ⟨_, _, h3877⟩ := auctionSetOwnerRoutine (σ := σ)
    (newOwner := auctionSourceWord I) (ret := ⟨3877⟩) (R := ⟨1⟩ :: ret :: R)
    (by evm_ov) hperm (by jump_dest) (by simpa only [auctionSourceWord] using h3574)
  have hm : auctionSetOwnerPostMap σ I (auctionSourceWord I) = σ :=
    sstoreAccountMap_absent_same hmissing
  rw [hm] at h3877
  exact auctionInitializerAbsentExit3877 (by omega) hmissing hperm hret h3877

theorem auctionInitializeOwnable_absent {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : Nat} {ret : UInt256} {R : List UInt256}
    (hR : R.length ≤ 965) (hmissing : σ.find? I.codeOwner = none)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3987⟩
      (ret :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h4070⟩ := auctionInitializerAbsentEnter3987 (by evm_ov) hmissing hperm h
  have h4892 := evm_run h4070 with [jumpdest, push2 ⟨4078⟩, push2 ⟨4892⟩, jump (by jump_dest)]
  obtain ⟨_, _, h4078⟩ := auctionInitializeNoop_absent
    (by evm_ov) hmissing hperm (by jump_dest) h4892
  have h5212 := evm_run h4078 with [jumpdest, push2 ⟨3877⟩, push2 ⟨5212⟩, jump (by jump_dest)]
  obtain ⟨_, _, h3877⟩ := auctionInitializeOwnableUnchained_absent
    (by evm_ov) hmissing hperm (by jump_dest) h5212
  exact auctionInitializerAbsentExit3877 (by omega) hmissing hperm hret h3877

theorem auctionInitializeArgsPostMap_absent {σ : AccountMap} {I : ExecutionEnv}
    (hmissing : σ.find? I.codeOwner = none) : auctionInitializeArgsPostMap σ I = σ := by
  simp only [auctionInitializeArgsPostMap, auctionInitializeSetAddressMap,
    auctionInitializeSetUint256Map, auctionInitializeSetMinBidMap,
    sstoreAccountMap_absent_same hmissing]

theorem auctionInitializeTopPostMap_absent {σ : AccountMap} {I : ExecutionEnv}
    (hmissing : σ.find? I.codeOwner = none) : auctionInitializeTopPostMap σ I = σ := by
  simp only [auctionInitializeTopPostMap, auctionInitializeSetInitializingFalseMap,
    auctionInitializeCorePostMap, auctionInitializeSetTopFlagsMap, auctionUnpausePostMap,
    auctionInitializeSetStatusMap, auctionSetOwnerPostMap, auctionPausePostMap,
    sstoreAccountMap_absent_same hmissing, auctionInitializeArgsPostMap_absent hmissing]

set_option maxHeartbeats 1000000 in
theorem auctionInitializeCore_absent {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : Nat} {ret : UInt256} {R : List UInt256}
    (hR : R.length ≤ 950)
    (hcanon : (auctionInitializeMinBidIncrementPercentageWord I).toNat < EVM.twoPow 8)
    (hmissing : σ.find? I.codeOwner = none)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨2213⟩
      (⟨1⟩ :: auctionInitializeDurationWord I :: auctionInitializeMinBidIncrementPercentageWord I ::
        auctionInitializeReservePriceWord I :: auctionInitializeTimeBufferWord I ::
        auctionInitializeWethWord I :: auctionInitializeNounsWord I :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
  have h3778 := evm_run h with [jumpdest, push2 ⟨2221⟩, push2 ⟨3778⟩, jump (by jump_dest)]
  obtain ⟨_, _, h2221⟩ := auctionInitializePausable_absent
    (by evm_ov) hmissing hperm (by jump_dest) h3778
  have h3896 := evm_run h2221 with [jumpdest, push2 ⟨2229⟩, push2 ⟨3896⟩, jump (by jump_dest)]
  obtain ⟨_, _, h2229⟩ := auctionInitializeReentrancyGuard_absent
    (by evm_ov) hmissing hperm (by jump_dest) h3896
  have h3987 := evm_run h2229 with [jumpdest, push2 ⟨2237⟩, push2 ⟨3987⟩, jump (by jump_dest)]
  obtain ⟨_, _, h2237⟩ := auctionInitializeOwnable_absent
    (by evm_ov) hmissing hperm (by jump_dest) h3987
  have h3655 := evm_run h2237 with [jumpdest, push2 ⟨2245⟩, push2 ⟨3655⟩, jump (by jump_dest)]
  have hpaused : auctionPausedWord σ I = ⟨0⟩ := by
    unfold auctionPausedWord
    rw [auctionSlotWord_of_absent hmissing]
    rfl
  obtain ⟨_, _, h2245⟩ := auctionPauseRoutine_success
    (by evm_ov) hperm hpaused (by jump_dest) h3655
  have hpause : auctionPausePostMap σ I = σ := sstoreAccountMap_absent_same hmissing
  rw [hpause] at h2245
  obtain ⟨_, _, hret'⟩ := auctionInitializeArgsStores_top (by omega) hcanon hperm hret h2245
  have hfinal : auctionInitializeSetInitializingFalseMap (auctionInitializeArgsPostMap σ I) I = σ := by
    rw [auctionInitializeArgsPostMap_absent hmissing]
    exact sstoreAccountMap_absent_same hmissing
  rw [hfinal] at hret'
  exact ⟨_, _, hret'⟩

end Auction
