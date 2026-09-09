import Benchmarks.Auction.InitializeRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000

namespace Auction

set_option maxHeartbeats 1000000 in
theorem auctionInitializeArgsStores_common {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret flag : UInt256} {R : List UInt256}
    (hR : R.length ≤ 970)
    (hcanon : (auctionInitializeMinBidIncrementPercentageWord I).toNat < EVM.twoPow 8)
    (hperm : I.perm = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨2245⟩
      (flag :: auctionInitializeDurationWord I ::
        auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
        auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
        auctionInitializeNounsWord I :: ret :: R)
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨2326⟩
      (flag :: auctionInitializeDurationWord I ::
        auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
        auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
        auctionInitializeNounsWord I :: ret :: R)
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty
      (cA, auctionInitializeArgsPostMap σ I) k C := by
  have rd2249₀ := evm_run h with [jumpdest, push1 ⟨201⟩, dup1]
  obtain ⟨_, _, rd2250₀⟩ := rd2249₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2250⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2250⟩
      (auctionSlotWord ⟨201⟩ σ I :: ⟨201⟩ ::
        flag :: auctionInitializeDurationWord I ::
          auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
          auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
          auctionInitializeNounsWord I :: ret :: R)
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2250₀⟩
  have hsolcMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hpost201 :
      UInt256.lor (UInt256.land (UInt256.lnot solcAddrMask) (auctionSlotWord ⟨201⟩ σ I))
          (UInt256.land (auctionInitializeNounsWord I) solcAddrMask) =
        setAddressOffset0Word (auctionSlotWord ⟨201⟩ σ I) (auctionInitializeNounsWord I) := by
    unfold setAddressOffset0Word
    rw [u256_land_comm (UInt256.lnot solcAddrMask)]
  have rd2276₀ := evm_run rd2250 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup1, dup11, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, swap3, dup4, and,
    lor, swap1, swap3]
  have rd2276 := rd2276₀
  rw [hsolcMask] at rd2276
  rw [hpost201] at rd2276
  obtain ⟨_, _, rd2277₀⟩ := rd2276.sstore hperm (by native_decide) (by evm_ov)
  let s5 := auctionInitializeSetAddressMap σ I ⟨201⟩ (auctionInitializeNounsWord I)
  obtain ⟨_, _, rd2277⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2277⟩
      (UInt256.lnot solcAddrMask :: solcAddrMask :: flag :: auctionInitializeDurationWord I ::
        auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
        auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
        auctionInitializeNounsWord I :: ret :: R)
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty (cA, s5) k C := by
    exact ⟨_, _, by simpa [s5, auctionInitializeSetAddressMap] using rd2277₀⟩
  have rd2280₀ := evm_run rd2277 with [push1 ⟨202⟩, dup1]
  obtain ⟨_, _, rd2281₀⟩ := rd2280₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2281⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2281⟩
      (auctionSlotWord ⟨202⟩ s5 I :: ⟨202⟩ ::
        UInt256.lnot solcAddrMask :: solcAddrMask :: flag :: auctionInitializeDurationWord I ::
          auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
          auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
          auctionInitializeNounsWord I :: ret :: R)
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty (cA, s5) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2281₀⟩
  have hpost202 :
      UInt256.lor (UInt256.land (UInt256.lnot solcAddrMask) (auctionSlotWord ⟨202⟩ s5 I))
          (UInt256.land (auctionInitializeWethWord I) solcAddrMask) =
        setAddressOffset0Word (auctionSlotWord ⟨202⟩ s5 I) (auctionInitializeWethWord I) := by
    unfold setAddressOffset0Word
    rw [u256_land_comm (UInt256.lnot solcAddrMask)]
  have rd2293₀ := evm_run rd2281 with [
    swap3, dup10, and, swap3, swap1, swap2, and, swap2, swap1, swap2, lor, swap1]
  have rd2293 := rd2293₀
  rw [hpost202] at rd2293
  obtain ⟨_, _, rd2294₀⟩ := rd2293.sstore hperm (by native_decide) (by evm_ov)
  let s6 := auctionInitializeSetAddressMap s5 I ⟨202⟩ (auctionInitializeWethWord I)
  obtain ⟨_, _, rd2294⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2294⟩
      (flag :: auctionInitializeDurationWord I ::
        auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
        auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
        auctionInitializeNounsWord I :: ret :: R)
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty (cA, s6) k C := by
    exact ⟨_, _, by simpa [s6, auctionInitializeSetAddressMap] using rd2294₀⟩
  have rd2298₀ := evm_run rd2294 with [push1 ⟨203⟩, dup6, swap1]
  obtain ⟨_, _, rd2299₀⟩ := rd2298₀.sstore hperm (by native_decide) (by evm_ov)
  let s7 := auctionInitializeSetUint256Map s6 I ⟨203⟩ (auctionInitializeTimeBufferWord I)
  obtain ⟨_, _, rd2299⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2299⟩
      (flag :: auctionInitializeDurationWord I ::
        auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
        auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
        auctionInitializeNounsWord I :: ret :: R)
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty (cA, s7) k C := by
    exact ⟨_, _, by simpa [s7, auctionInitializeSetUint256Map] using rd2299₀⟩
  have rd2303₀ := evm_run rd2299 with [push1 ⟨204⟩, dup5, swap1]
  obtain ⟨_, _, rd2304₀⟩ := rd2303₀.sstore hperm (by native_decide) (by evm_ov)
  let s8 := auctionInitializeSetUint256Map s7 I ⟨204⟩ (auctionInitializeReservePriceWord I)
  obtain ⟨_, _, rd2304⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2304⟩
      (flag :: auctionInitializeDurationWord I ::
        auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
        auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
        auctionInitializeNounsWord I :: ret :: R)
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty (cA, s8) k C := by
    exact ⟨_, _, by simpa [s8, auctionInitializeSetUint256Map] using rd2304₀⟩
  have rd2307₀ := evm_run rd2304 with [push1 ⟨205⟩, dup1]
  obtain ⟨_, _, rd2308₀⟩ := rd2307₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2308⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2308⟩
      (auctionSlotWord ⟨205⟩ s8 I :: ⟨205⟩ ::
        flag :: auctionInitializeDurationWord I ::
          auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
          auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
          auctionInitializeNounsWord I :: ret :: R)
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty (cA, s8) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2308₀⟩
  have rd2320₀ := evm_run rd2308 with [
    push1 ⟨255⟩, dup6, and, push1 ⟨255⟩, not, swap1, swap2, and, lor, swap1]
  have hmin : UInt256.lor
      (UInt256.land (auctionSlotWord ⟨205⟩ s8 I) (UInt256.lnot ⟨255⟩))
      (UInt256.land (auctionInitializeMinBidIncrementPercentageWord I) ⟨255⟩) =
        auctionSetUint8Offset0Word (auctionSlotWord ⟨205⟩ s8 I)
          (auctionInitializeMinBidIncrementPercentageWord I) := by
    unfold auctionSetUint8Offset0Word
    rw [auctionLand255_eq_self_of_uint8 _ hcanon]
  have rd2320 := rd2320₀
  rw [hmin] at rd2320
  obtain ⟨_, _, rd2321₀⟩ := rd2320.sstore hperm (by native_decide) (by evm_ov)
  let s9 := auctionInitializeSetMinBidMap s8 I
  obtain ⟨_, _, rd2321⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2321⟩
      (flag :: auctionInitializeDurationWord I ::
        auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
        auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
        auctionInitializeNounsWord I :: ret :: R)
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty (cA, s9) k C := by
    exact ⟨_, _, by simpa [s9, auctionInitializeSetMinBidMap] using rd2321₀⟩
  have rd2325₀ := evm_run rd2321 with [push1 ⟨206⟩, dup3, swap1]
  obtain ⟨_, _, rd2326₀⟩ := rd2325₀.sstore hperm (by native_decide) (by evm_ov)
  let s10 := auctionInitializeSetUint256Map s9 I ⟨206⟩ (auctionInitializeDurationWord I)
  obtain ⟨_, _, rd2326⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2326⟩
      (flag :: auctionInitializeDurationWord I ::
        auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
        auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
        auctionInitializeNounsWord I :: ret :: R)
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty (cA, s10) k C := by
    exact ⟨_, _, by simpa [s10, auctionInitializeSetUint256Map] using rd2326₀⟩
  exact ⟨_, _, by
    simpa only [auctionInitializeArgsPostMap, s5, s6, s7, s8, s9, s10] using rd2326⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializeArgsStores_nested {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hR : R.length ≤ 970)
    (hcanon : (auctionInitializeMinBidIncrementPercentageWord I).toNat < EVM.twoPow 8)
    (hperm : I.perm = true)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨2245⟩
      (⟨0⟩ :: auctionInitializeDurationWord I ::
        auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
        auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
        auctionInitializeNounsWord I :: ret :: R)
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty
      (cA, auctionInitializeArgsPostMap σ I) k C := by
  obtain ⟨_, _, rd2326⟩ := auctionInitializeArgsStores_common hR hcanon hperm h
  have rd2342 := evm_run rd2326 with [
    dup1, iszero, push2 ⟨2342⟩, jumpiT (by native_decide) (by jump_dest), jumpdest]
  have rd2350 := evm_run rd2342 with [pop, pop, pop, pop, pop, pop, pop, jump hret]
  exact ⟨_, _, rd2350⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializeArgsStores_top {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hR : R.length ≤ 970)
    (hcanon : (auctionInitializeMinBidIncrementPercentageWord I).toNat < EVM.twoPow 8)
    (hperm : I.perm = true)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨2245⟩
      (⟨1⟩ :: auctionInitializeDurationWord I ::
        auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
        auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
        auctionInitializeNounsWord I :: ret :: R)
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty
      (cA, auctionInitializeSetInitializingFalseMap (auctionInitializeArgsPostMap σ I) I) k C := by
  obtain ⟨_, _, rd2326⟩ := auctionInitializeArgsStores_common hR hcanon hperm h
  have rd2332 := evm_run rd2326 with [
    dup1, iszero, push2 ⟨2342⟩, jumpiNT (by native_decide), push0, dup1]
  obtain ⟨_, _, rd2335₀⟩ := rd2332.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2335⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2335⟩
      (auctionSlotWord ⟨0⟩ (auctionInitializeArgsPostMap σ I) I :: ⟨0⟩ ::
        ⟨1⟩ :: auctionInitializeDurationWord I ::
          auctionInitializeMinBidIncrementPercentageWord I :: auctionInitializeReservePriceWord I ::
          auctionInitializeTimeBufferWord I :: auctionInitializeWethWord I ::
          auctionInitializeNounsWord I :: ret :: R)
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty (cA, (auctionInitializeArgsPostMap σ I)) k C := by
    exact ⟨_, _, by simpa only [auctionSlotWord] using rd2335₀⟩
  have hclear :
      UInt256.land (UInt256.lnot ⟨65280⟩)
          (auctionSlotWord ⟨0⟩ (auctionInitializeArgsPostMap σ I) I) =
        auctionSetBoolOffset1FalseWord
          (auctionSlotWord ⟨0⟩ (auctionInitializeArgsPostMap σ I) I) := by
    rw [u256_land_comm]
    exact auctionClearBoolOffset1Word_eq _
  have rd2341 := evm_run rd2335 with [push2 ⟨65280⟩, not, and, swap1]
  rw [hclear] at rd2341
  obtain ⟨_, _, rd2342⟩ := rd2341.sstore hperm (by native_decide) (by evm_ov)
  have rd2350 := evm_run rd2342 with [jumpdest, pop, pop, pop, pop, pop, pop, pop, jump hret]
  exact ⟨_, _, rd2350⟩

end Auction
