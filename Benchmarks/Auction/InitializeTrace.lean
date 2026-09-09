import Benchmarks.Auction.InitializeAbsent

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000

namespace Auction

set_option maxHeartbeats 1000000 in
theorem auctionInitializeCore_nested {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hR : R.length ≤ 950)
    (hcanon : (auctionInitializeMinBidIncrementPercentageWord I).toNat < EVM.twoPow 8)
    (hperm : I.perm = true)
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨2213⟩
      (⟨0⟩ :: auctionInitializeDurationWord I ::
        auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
        auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
        auctionInitializeNounsWord I :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty
      (cA, auctionInitializeCorePostMap σ I) k C := by
  have rd3778 := evm_run h with [jumpdest, push2 ⟨2221⟩, push2 ⟨3778⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd2221⟩ := auctionInitializePausable_nested (σ := σ) (g := g)
    (ret := ⟨2221⟩)
    (R := ⟨0⟩ :: auctionInitializeDurationWord I ::
      auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
      auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
      auctionInitializeNounsWord I :: ret :: R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hperm hnz (by jump_dest) rd3778
  let s1 := auctionUnpausePostMap σ I
  have hnz1 : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ s1 I) ⟨256⟩) ⟨255⟩ ≠
      ⟨0⟩ := by
    dsimp [s1, auctionUnpausePostMap]
    exact auctionInitializingGuard_ne_sstore_ne (slot := ⟨51⟩)
      (val := auctionPausedSetFalseWord (auctionSlotWord ⟨51⟩ σ I)) (by native_decide) hnz
  have rd3896 := evm_run rd2221 with [jumpdest, push2 ⟨2229⟩, push2 ⟨3896⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd2229⟩ := auctionInitializeReentrancyGuard_nested (σ := s1) (g := g)
    (ret := ⟨2229⟩)
    (R := ⟨0⟩ :: auctionInitializeDurationWord I ::
      auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
      auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
      auctionInitializeNounsWord I :: ret :: R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hperm hnz1 (by jump_dest) rd3896
  let s2 := auctionInitializeSetStatusMap s1 I
  have hnz2 : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ s2 I) ⟨256⟩) ⟨255⟩ ≠
      ⟨0⟩ := by
    dsimp [s2, auctionInitializeSetStatusMap]
    exact auctionInitializingGuard_ne_sstore_ne (slot := ⟨101⟩) (val := ⟨1⟩)
      (by native_decide) hnz1
  have rd3987 := evm_run rd2229 with [jumpdest, push2 ⟨2237⟩, push2 ⟨3987⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd2237⟩ := auctionInitializeOwnable_nested (σ := s2) (g := g)
    (ret := ⟨2237⟩)
    (R := ⟨0⟩ :: auctionInitializeDurationWord I ::
      auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
      auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
      auctionInitializeNounsWord I :: ret :: R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hperm hnz2 (by jump_dest) rd3987
  let s3 := auctionSetOwnerPostMap s2 I (auctionSourceWord I)
  have hpaused0 : auctionPausedWord s3 I = ⟨0⟩ := by
    dsimp [s3, s2, s1]
    exact (auctionInitializePrePausePausedZero (σ := σ) (I := I))
  have rd3655 := evm_run rd2237 with [jumpdest, push2 ⟨2245⟩, push2 ⟨3655⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd2245⟩ := auctionPauseRoutine_success (σ := s3) (g := g)
    (ret := ⟨2245⟩)
    (R := ⟨0⟩ :: auctionInitializeDurationWord I ::
      auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
      auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
      auctionInitializeNounsWord I :: ret :: R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hperm hpaused0 (by jump_dest) rd3655
  let s4 := auctionPausePostMap s3 I
  obtain ⟨_, _, rdret⟩ := auctionInitializeArgsStores_nested (σ := s4) (g := g)
    (ret := ret) (R := R) (by omega) hcanon hperm hret rd2245
  exact ⟨_, _, by simpa [auctionInitializeCorePostMap, s1, s2, s3, s4] using rdret⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializeCore_top {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hR : R.length ≤ 950)
    (hcanon : (auctionInitializeMinBidIncrementPercentageWord I).toNat < EVM.twoPow 8)
    (hperm : I.perm = true)
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨2213⟩
      (⟨1⟩ :: auctionInitializeDurationWord I ::
        auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
        auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
        auctionInitializeNounsWord I :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty
      (cA, auctionInitializeSetInitializingFalseMap (auctionInitializeCorePostMap σ I) I) k C := by
  have rd3778 := evm_run h with [jumpdest, push2 ⟨2221⟩, push2 ⟨3778⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd2221⟩ := auctionInitializePausable_nested (σ := σ) (g := g)
    (ret := ⟨2221⟩)
    (R := ⟨1⟩ :: auctionInitializeDurationWord I ::
      auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
      auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
      auctionInitializeNounsWord I :: ret :: R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hperm hnz (by jump_dest) rd3778
  let s1 := auctionUnpausePostMap σ I
  have hnz1 : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ s1 I) ⟨256⟩) ⟨255⟩ ≠
      ⟨0⟩ := by
    dsimp [s1, auctionUnpausePostMap]
    exact auctionInitializingGuard_ne_sstore_ne (slot := ⟨51⟩)
      (val := auctionPausedSetFalseWord (auctionSlotWord ⟨51⟩ σ I)) (by native_decide) hnz
  have rd3896 := evm_run rd2221 with [
    jumpdest, push2 ⟨2229⟩, push2 ⟨3896⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd2229⟩ := auctionInitializeReentrancyGuard_nested (σ := s1) (g := g)
    (ret := ⟨2229⟩)
    (R := ⟨1⟩ :: auctionInitializeDurationWord I ::
      auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
      auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
      auctionInitializeNounsWord I :: ret :: R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hperm hnz1 (by jump_dest) rd3896
  let s2 := auctionInitializeSetStatusMap s1 I
  have hnz2 : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ s2 I) ⟨256⟩) ⟨255⟩ ≠
      ⟨0⟩ := by
    dsimp [s2, auctionInitializeSetStatusMap]
    exact auctionInitializingGuard_ne_sstore_ne (slot := ⟨101⟩) (val := ⟨1⟩)
      (by native_decide) hnz1
  have rd3987 := evm_run rd2229 with [
    jumpdest, push2 ⟨2237⟩, push2 ⟨3987⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd2237⟩ := auctionInitializeOwnable_nested (σ := s2) (g := g)
    (ret := ⟨2237⟩)
    (R := ⟨1⟩ :: auctionInitializeDurationWord I ::
      auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
      auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
      auctionInitializeNounsWord I :: ret :: R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hperm hnz2 (by jump_dest) rd3987
  let s3 := auctionSetOwnerPostMap s2 I (auctionSourceWord I)
  have hpaused0 : auctionPausedWord s3 I = ⟨0⟩ := by
    dsimp [s3, s2, s1]
    exact (auctionInitializePrePausePausedZero (σ := σ) (I := I))
  have rd3655 := evm_run rd2237 with [
    jumpdest, push2 ⟨2245⟩, push2 ⟨3655⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd2245⟩ := auctionPauseRoutine_success (σ := s3) (g := g)
    (ret := ⟨2245⟩)
    (R := ⟨1⟩ :: auctionInitializeDurationWord I ::
      auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
      auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
      auctionInitializeNounsWord I :: ret :: R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hperm hpaused0 (by jump_dest) rd3655
  let s4 := auctionPausePostMap s3 I
  obtain ⟨_, _, rdret⟩ := auctionInitializeArgsStores_top (σ := s4) (g := g)
    (ret := ret) (R := R) (by omega) hcanon hperm hret rd2245
  exact ⟨_, _, by
    simpa [auctionInitializeCorePostMap, s1, s2, s3, s4] using rdret⟩

set_option maxHeartbeats 1000000 in
theorem auctionX_initialize_success_nested {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz196 : 196 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonNouns : (auctionInitializeNounsWord I).toNat < EVM.addressModulus)
    (hcanonWeth : (auctionInitializeWethWord I).toNat < EVM.addressModulus)
    (hcanonMinBid : (auctionInitializeMinBidIncrementPercentageWord I).toNat < EVM.twoPow 8)
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨705⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, auctionInitializeCorePostMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd2130⟩ := auctionInitializeX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := auctionSelWord I)
    hwv hsz196 hsize hszhi hcanonNouns hcanonWeth hcanonMinBid hreach
  obtain ⟨_, _, rd2213⟩ := auctionInitializeX_toCore_nested (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := auctionSelWord I)
    hnz ⟨_, _, rd2130⟩
  obtain ⟨_, _, rd413⟩ := auctionInitializeCore_nested (cA := cA) (gh := gh)
    (bl := bl) (σInit := σ) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (ret := ⟨413⟩) (R := [auctionSelWord I]) (by evm_ov) hcanonMinBid hperm hnz (by jump_dest) rd2213
  have rd414 := evm_run rd413 with [jumpdest]
  exact rd414.stop (by native_decide) (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem auctionX_initialize_success_top {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz196 : 196 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonNouns : (auctionInitializeNounsWord I).toNat < EVM.addressModulus)
    (hcanonWeth : (auctionInitializeWethWord I).toNat < EVM.addressModulus)
    (hcanonMinBid : (auctionInitializeMinBidIncrementPercentageWord I).toNat < EVM.twoPow 8)
    (hinitZero : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ =
      ⟨0⟩)
    (hinitializedZero : UInt256.land (auctionSlotWord ⟨0⟩ σ I) ⟨255⟩ = ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨705⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, auctionInitializeTopPostMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd2130⟩ := auctionInitializeX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := auctionSelWord I)
    hwv hsz196 hsize hszhi hcanonNouns hcanonWeth hcanonMinBid hreach
  obtain ⟨_, _, rd2213⟩ := auctionInitializeX_toCore_top (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := auctionSelWord I)
    hperm hinitZero hinitializedZero ⟨_, _, rd2130⟩
  cases haccount : σ.find? I.codeOwner with
  | none =>
      rw [sstoreAccountMap_absent_same haccount] at rd2213
      obtain ⟨_, _, rd413⟩ := auctionInitializeCore_absent (cA := cA) (gh := gh)
        (bl := bl) (σInit := σ) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
        (ret := ⟨413⟩) (R := [auctionSelWord I]) (by evm_ov) hcanonMinBid haccount hperm
        (by jump_dest) rd2213
      have rd414 := evm_run rd413 with [jumpdest]
      rw [auctionInitializeTopPostMap_absent haccount]
      exact rd414.stop (by native_decide) (by evm_ov)
  | some acc =>
      have hnzTop := auctionInitializeSetTopFlagsMap_initializing_ne
        (σ := σ) (I := I) ⟨acc, haccount⟩
      obtain ⟨_, _, rd413⟩ := auctionInitializeCore_top (cA := cA) (gh := gh)
        (bl := bl) (σInit := σ) (σ := auctionInitializeSetTopFlagsMap σ I) (σ₀ := σ₀)
        (A := A) (g := g) (ret := ⟨413⟩) (R := [auctionSelWord I]) (by evm_ov) hcanonMinBid hperm hnzTop
        (by jump_dest) (by simpa only [auctionInitializeSetTopFlagsMap] using rd2213)
      have rd414 := evm_run rd413 with [jumpdest]
      exact by
        simpa only [auctionInitializeTopPostMap] using rd414.stop (by native_decide) (by evm_ov)


end Auction
