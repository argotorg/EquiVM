import Benchmarks.Auction.InitializeBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

def auctionInitializeSetStatusMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨101⟩ ⟨1⟩

def auctionInitializeSetTopFlagsMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨0⟩
    (setBoolOffset0Word (auctionSetBoolOffset1TrueWord (auctionSlotWord ⟨0⟩ σ I)) ⟨1⟩)

def auctionInitializeSetAddressMap
    (σ : AccountMap) (I : ExecutionEnv) (slot val : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner σ slot (setAddressOffset0Word (auctionSlotWord slot σ I) val)

def auctionInitializeSetUint256Map
    (σ : AccountMap) (I : ExecutionEnv) (slot val : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner σ slot val

def auctionInitializeSetMinBidMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨205⟩
    (auctionSetUint8Offset0Word (auctionSlotWord ⟨205⟩ σ I)
      (auctionInitializeMinBidIncrementPercentageWord I))

def auctionInitializeSetInitializingFalseMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨0⟩ (auctionSetBoolOffset1FalseWord (auctionSlotWord ⟨0⟩ σ I))

def auctionInitializeArgsPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  let s5 := auctionInitializeSetAddressMap σ I ⟨201⟩ (auctionInitializeNounsWord I)
  let s6 := auctionInitializeSetAddressMap s5 I ⟨202⟩ (auctionInitializeWethWord I)
  let s7 := auctionInitializeSetUint256Map s6 I ⟨203⟩ (auctionInitializeTimeBufferWord I)
  let s8 := auctionInitializeSetUint256Map s7 I ⟨204⟩ (auctionInitializeReservePriceWord I)
  let s9 := auctionInitializeSetMinBidMap s8 I
  auctionInitializeSetUint256Map s9 I ⟨206⟩ (auctionInitializeDurationWord I)

def auctionInitializeCorePostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  let s1 := auctionUnpausePostMap σ I
  let s2 := auctionInitializeSetStatusMap s1 I
  let s3 := auctionSetOwnerPostMap s2 I (auctionSourceWord I)
  let s4 := auctionPausePostMap s3 I
  auctionInitializeArgsPostMap s4 I

def auctionInitializeTopPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  auctionInitializeSetInitializingFalseMap
    (auctionInitializeCorePostMap (auctionInitializeSetTopFlagsMap σ I) I) I

set_option maxHeartbeats 1000000 in
theorem auctionInitializePrePausePausedZero {cA gh bl σ σ₀ A I} {g : Sat256} :
    let s1 := auctionUnpausePostMap σ I
    let s2 := auctionInitializeSetStatusMap s1 I
    let s3 := auctionSetOwnerPostMap s2 I (auctionSourceWord I)
    auctionPausedWord s3 I = ⟨0⟩ := by
  dsimp only
  unfold auctionSetOwnerPostMap auctionInitializeSetStatusMap auctionPausedWord auctionSlotWord
  rw [sstoreAccountMap_storage_findD_ne (readSlot := ⟨51⟩) (writeSlot := ⟨151⟩)
    (hne := by decide)]
  rw [sstoreAccountMap_storage_findD_ne (readSlot := ⟨51⟩) (writeSlot := ⟨101⟩)
    (hne := by decide)]
  have h := auctionUnpausePostState_paused_zero (initState cA gh bl σ σ₀ g A I)
  simpa [auctionUnpausePostMap, auctionUnpausePostState, initState, auctionSlotWord,
    auctionPausedWord, Solm.EVM.storageLoad, State.lookupAccount, storageStore_accountMap]
    using h

set_option maxHeartbeats 1000000 in
theorem auctionInitializingGuard_ne_sstore_ne {σ I} {slot val : UInt256}
    (hne : (⟨0⟩ : UInt256) ≠ slot)
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩) :
    UInt256.land
        (UInt256.div (auctionSlotWord ⟨0⟩ (sstoreAccountMap I.codeOwner σ slot val) I) ⟨256⟩)
        ⟨255⟩ ≠ ⟨0⟩ := by
  unfold auctionSlotWord at *
  rw [sstoreAccountMap_storage_findD_ne (a := I.codeOwner) (readSlot := ⟨0⟩)
    (writeSlot := slot) (val := val) (hne := hne)]
  exact hnz

set_option maxHeartbeats 1000000 in
theorem auctionInitializeSetTopFlagsMap_initializing_ne {σ I} :
    UInt256.land
        (UInt256.div (auctionSlotWord ⟨0⟩ (auctionInitializeSetTopFlagsMap σ I) I) ⟨256⟩)
        ⟨255⟩ ≠ ⟨0⟩ := by
  unfold auctionInitializeSetTopFlagsMap auctionSlotWord sstoreAccountMap
  cases hacc : Batteries.RBMap.find? σ I.codeOwner with
  | none =>
      simp [hacc]
  | some acc =>
      simp [hacc]

set_option maxHeartbeats 1000000 in
theorem auctionInitializeCorePostMap_accountMap {cA gh bl σ σ₀ A I} {g : Sat256} :
    accountMapEquiv (auctionInitializeCorePostMap σ I)
      (auctionInitializeCorePostState (initState cA gh bl σ σ₀ g A I) I).accountMap := by
  apply accountMapEquiv.of_eq
  simp [auctionInitializeCorePostMap, auctionInitializeArgsPostMap,
    auctionInitializeSetStatusMap, auctionInitializeSetAddressMap,
    auctionInitializeSetUint256Map, auctionInitializeSetMinBidMap,
    auctionInitializeCorePostState, auctionInitializeSetStatusState,
    auctionInitializeSetAddressState, auctionInitializeSetUint256State,
    auctionInitializeSetMinBidState, auctionUnpausePostMap, auctionUnpausePostState,
    auctionPausePostMap, auctionPausePostState, auctionSetOwnerPostMap, initState,
    storageStore_accountMap, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount]

set_option maxHeartbeats 1000000 in
theorem auctionInitializeTopPostMap_accountMap {cA gh bl σ σ₀ A I} {g : Sat256} :
    accountMapEquiv (auctionInitializeTopPostMap σ I)
      (auctionInitializeTopPostState (initState cA gh bl σ σ₀ g A I) I).accountMap := by
  apply accountMapEquiv.of_eq
  simp [auctionInitializeTopPostMap, auctionInitializeSetTopFlagsMap,
    auctionInitializeCorePostMap, auctionInitializeArgsPostMap,
    auctionInitializeSetStatusMap, auctionInitializeSetAddressMap,
    auctionInitializeSetUint256Map, auctionInitializeSetMinBidMap,
    auctionInitializeSetInitializingFalseMap, auctionInitializeTopPostState,
    auctionInitializeSetInitializingFalseState, auctionInitializeSetInitializedTrueState,
    auctionInitializeSetInitializingTrueState, auctionInitializeCorePostState,
    auctionInitializeSetStatusState, auctionInitializeSetAddressState,
    auctionInitializeSetUint256State, auctionInitializeSetMinBidState,
    auctionUnpausePostMap, auctionUnpausePostState, auctionPausePostMap, auctionPausePostState,
    auctionSetOwnerPostMap, initState, storageStore_accountMap, auctionSlotWord,
    Solm.EVM.storageLoad, State.lookupAccount]

def auctionInitializableAlreadyStringWord1 : UInt256 :=
  ⟨0x496e697469616c697a61626c653a20636f6e747261637420697320616c726561⟩

def auctionInitializableAlreadyRawStringWord2 : UInt256 :=
  ⟨0x191e481a5b9a5d1a585b1a5e9959⟩

def auctionInitializableAlreadyStringWord2 : UInt256 :=
  UInt256.shiftLeft auctionInitializableAlreadyRawStringWord2 ⟨146⟩

noncomputable def auctionInitializableAlreadyStringMem4 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray auctionInitializableAlreadyStringWord2).write 0
    (solcErrorStringMem3 ⟨46⟩ auctionInitializableAlreadyStringWord1 mem) 228 32

theorem auctionInitializableAlreadyStringMem4_read64 :
    (auctionInitializableAlreadyStringMem4 solcFreePtrMem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold auctionInitializableAlreadyStringMem4
  rw [toByteArray_write_read_below_of_gap auctionInitializableAlreadyStringWord2
    (solcErrorStringMem3 ⟨46⟩ auctionInitializableAlreadyStringWord1 solcFreePtrMem) 228 64]
  · exact solcErrorStringMem3_read64 ⟨46⟩ auctionInitializableAlreadyStringWord1
      solcFreePtrMem_size solcFreePtrMem_read64
  · rw [solcErrorStringMem3_size ⟨46⟩ auctionInitializableAlreadyStringWord1
      solcFreePtrMem_size]
    omega
  · omega
  · rw [solcErrorStringMem3_size ⟨46⟩ auctionInitializableAlreadyStringWord1
      solcFreePtrMem_size]
    native_decide

theorem auctionInitializableAlreadyStringMem4_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ (auctionInitializableAlreadyStringMem4 solcFreePtrMem).size
        ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 9) * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((auctionInitializableAlreadyStringMem4 solcFreePtrMem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = (⟨128⟩ : UInt256) := by
  apply mloadFreePtrValue
  · unfold auctionInitializableAlreadyStringMem4
    have hge := toByteArray_write_size_ge_off_add32 auctionInitializableAlreadyStringWord2
      (solcErrorStringMem3 ⟨46⟩ auctionInitializableAlreadyStringWord1 solcFreePtrMem) 228 (by
        rw [solcErrorStringMem3_size ⟨46⟩ auctionInitializableAlreadyStringWord1
          solcFreePtrMem_size]
        native_decide)
    omega
  · decide
  · exact auctionInitializableAlreadyStringMem4_read64

set_option maxHeartbeats 1000000 in
theorem auctionInitializeX_toCore_nested {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩)
    (hdecoded : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2130⟩
      [auctionInitializeDurationWord I, auctionInitializeMinBidIncrementPercentageWord I,
        auctionInitializeReservePriceWord I, auctionInitializeTimeBufferWord I,
        auctionInitializeWethWord I, auctionInitializeNounsWord I, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2213⟩
      [⟨0⟩, auctionInitializeDurationWord I, auctionInitializeMinBidIncrementPercentageWord I,
        auctionInitializeReservePriceWord I, auctionInitializeTimeBufferWord I,
        auctionInitializeWethWord I, auctionInitializeNounsWord I, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2130⟩ := hdecoded
  have rd2132₀ := evm_run rd2130 with [jumpdest, push0]
  obtain ⟨_, _, rd2133₀⟩ := rd2132₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2133⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2133⟩
      [auctionSlotWord ⟨0⟩ σ I, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I, auctionInitializeNounsWord I,
        ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2133₀⟩
  have rd2142₀ := evm_run rd2133 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1]
  have hinitComm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) =
        UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)
  have hnz' : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ≠ ⟨0⟩ := by
    simpa [hinitComm] using hnz
  have rd2153 := evm_run rd2142₀ with [
    push2 ⟨2153⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd2181 := evm_run rd2153 with [
    push2 ⟨2181⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd2183₀ := evm_run rd2181 with [push0]
  obtain ⟨_, _, rd2184₀⟩ := rd2183₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2184⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2184⟩
      [auctionSlotWord ⟨0⟩ σ I, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I, auctionInitializeNounsWord I,
        ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2184₀⟩
  have rd2195₀ := evm_run rd2184 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, iszero, dup1, iszero]
  have hiz : UInt256.isZero
      (UInt256.land ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne hnz'
  have rd2195 := rd2195₀
  rw [hiz] at rd2195
  exact ⟨_, _, evm_run rd2195 with [
    push2 ⟨2213⟩, jumpiT (by decide) (by jump_dest), jumpdest]⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializeX_toCore_top {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hinitZero : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ =
      ⟨0⟩)
    (hinitializedZero : UInt256.land (auctionSlotWord ⟨0⟩ σ I) ⟨255⟩ = ⟨0⟩)
    (hdecoded : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2130⟩
      [auctionInitializeDurationWord I, auctionInitializeMinBidIncrementPercentageWord I,
        auctionInitializeReservePriceWord I, auctionInitializeTimeBufferWord I,
        auctionInitializeWethWord I, auctionInitializeNounsWord I, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2213⟩
      [⟨1⟩, auctionInitializeDurationWord I, auctionInitializeMinBidIncrementPercentageWord I,
        auctionInitializeReservePriceWord I, auctionInitializeTimeBufferWord I,
        auctionInitializeWethWord I, auctionInitializeNounsWord I, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩
        (setBoolOffset0Word (auctionSetBoolOffset1TrueWord (auctionSlotWord ⟨0⟩ σ I)) ⟨1⟩))
      k C := by
  obtain ⟨_, _, rd2130⟩ := hdecoded
  have rd2132₀ := evm_run rd2130 with [jumpdest, push0]
  obtain ⟨_, _, rd2133₀⟩ := rd2132₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2133⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2133⟩
      [auctionSlotWord ⟨0⟩ σ I, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I, auctionInitializeNounsWord I,
        ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2133₀⟩
  have rd2142₀ := evm_run rd2133 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1]
  have hinitComm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) =
        UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)
  have hinitZero' : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) = ⟨0⟩ := by
    simpa [hinitComm] using hinitZero
  have rd2142 := rd2142₀
  rw [hinitZero'] at rd2142
  have rd2147 := evm_run rd2142 with [
    push2 ⟨2153⟩, jumpiNT (by decide), pop, push0]
  obtain ⟨_, _, rd2149₀⟩ := rd2147.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2149⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2149⟩
      [auctionSlotWord ⟨0⟩ σ I, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I, auctionInitializeNounsWord I,
        ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2149₀⟩
  have rd2153₀ := evm_run rd2149 with [push1 ⟨255⟩, and, iszero]
  have hinitdComm : UInt256.land ⟨255⟩ (auctionSlotWord ⟨0⟩ σ I) =
      UInt256.land (auctionSlotWord ⟨0⟩ σ I) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (auctionSlotWord ⟨0⟩ σ I)
  have hinitializedZero' : UInt256.land ⟨255⟩ (auctionSlotWord ⟨0⟩ σ I) = ⟨0⟩ := by
    simpa [hinitdComm] using hinitializedZero
  have hiszeroInitd :
      UInt256.isZero (UInt256.land ⟨255⟩ (auctionSlotWord ⟨0⟩ σ I)) = ⟨1⟩ := by
    rw [hinitializedZero']
    decide
  have rd2153 := rd2153₀
  rw [hiszeroInitd] at rd2153
  have rd2181 := evm_run rd2153 with [
    jumpdest, push2 ⟨2181⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  have rd2183₀ := evm_run rd2181 with [push0]
  obtain ⟨_, _, rd2184₀⟩ := rd2183₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2184⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2184⟩
      [auctionSlotWord ⟨0⟩ σ I, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I, auctionInitializeNounsWord I,
        ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2184₀⟩
  have rd2195₀ := evm_run rd2184 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, iszero, dup1, iszero]
  have hisTop : UInt256.isZero
      (UInt256.land ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)) =
        ⟨1⟩ := by
    rw [hinitZero']
    decide
  have rd2195 := rd2195₀
  rw [hisTop] at rd2195
  have rd2200 := evm_run rd2195 with [
    push2 ⟨2213⟩, jumpiNT (by decide), push0, dup1]
  obtain ⟨_, _, rd2202₀⟩ := rd2200.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2202⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2202⟩
      [auctionSlotWord ⟨0⟩ σ I, ⟨0⟩, ⟨1⟩, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
        auctionInitializeNounsWord I, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2202₀⟩
  have rd2212₀ := evm_run rd2202 with [
    push2 ⟨65535⟩, not, and, push2 ⟨257⟩]
  have rd2212₁ := RD.lor rd2212₀ (by decide) (by evm_ov)
  have hlor : UInt256.lor ⟨257⟩
      (UInt256.land (UInt256.lnot ⟨65535⟩) (auctionSlotWord ⟨0⟩ σ I)) =
        setBoolOffset0Word (auctionSetBoolOffset1TrueWord (auctionSlotWord ⟨0⟩ σ I)) ⟨1⟩ := by
    rw [u256_land_comm]
    rw [u256_lor_comm]
    exact (auctionSetBoolOffset1TrueThenOffset0True_eq_mask
      (auctionSlotWord ⟨0⟩ σ I)).symm
  have rd2212 := rd2212₁
  rw [hlor] at rd2212
  have rd2213₀ := evm_run rd2212 with [swap1]
  obtain ⟨_, _, rd2213₁⟩ := rd2213₀.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, by simpa [sstoreAccountMap] using rd2213₁⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializeX_revert_initialized {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hinitZero : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ =
      ⟨0⟩)
    (hinitializedNz : UInt256.land (auctionSlotWord ⟨0⟩ σ I) ⟨255⟩ ≠ ⟨0⟩)
    (hdecoded : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2130⟩
      [auctionInitializeDurationWord I, auctionInitializeMinBidIncrementPercentageWord I,
        auctionInitializeReservePriceWord I, auctionInitializeTimeBufferWord I,
        auctionInitializeWethWord I, auctionInitializeNounsWord I, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2130⟩ := hdecoded
  have rd2132₀ := evm_run rd2130 with [jumpdest, push0]
  obtain ⟨_, _, rd2133₀⟩ := rd2132₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2133⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2133⟩
      [auctionSlotWord ⟨0⟩ σ I, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I, auctionInitializeNounsWord I,
        ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2133₀⟩
  have rd2142₀ := evm_run rd2133 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1]
  have hinitComm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) =
        UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)
  have hinitZero' : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) = ⟨0⟩ := by
    simpa [hinitComm] using hinitZero
  have rd2142 := rd2142₀
  rw [hinitZero'] at rd2142
  have rd2147 := evm_run rd2142 with [
    push2 ⟨2153⟩, jumpiNT (by decide), pop, push0]
  obtain ⟨_, _, rd2149₀⟩ := rd2147.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2149⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2149⟩
      [auctionSlotWord ⟨0⟩ σ I, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I, auctionInitializeNounsWord I,
        ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2149₀⟩
  have rd2153₀ := evm_run rd2149 with [push1 ⟨255⟩, and, iszero]
  have hinitdComm : UInt256.land ⟨255⟩ (auctionSlotWord ⟨0⟩ σ I) =
      UInt256.land (auctionSlotWord ⟨0⟩ σ I) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (auctionSlotWord ⟨0⟩ σ I)
  have hinitializedNz' : UInt256.land ⟨255⟩ (auctionSlotWord ⟨0⟩ σ I) ≠ ⟨0⟩ := by
    simpa [hinitdComm] using hinitializedNz
  have hiszeroInitd :
      UInt256.isZero (UInt256.land ⟨255⟩ (auctionSlotWord ⟨0⟩ σ I)) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hinitializedNz'
  have rd2153 := rd2153₀
  rw [hiszeroInitd] at rd2153
  have rd2158 := evm_run rd2153 with [jumpdest, push2 ⟨2181⟩, jumpiNT (by decide)]
  have rd2161 := evm_run rd2158 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd2165 := rd2161.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd2173₀ := evm_run rd2165 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (solcErrorStringMem0 solcFreePtrMem) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨4⟩, add]
  have rd2173 := rd2173₀
  rw [show (⟨4⟩ : UInt256) + ⟨128⟩ = ⟨132⟩ by decide] at rd2173
  have rd5742 := evm_run rd2173 with [
    push2 ⟨994⟩, swap1, push2 ⟨5742⟩, jump (by jump_dest)]
  have rd5754 := evm_run rd5742 with [
    jumpdest, push1 ⟨32⟩, dup1, dup3,
    raw mstore 3 (solcErrorStringMem1 solcFreePtrMem) (UInt256.ofNat 6)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨46⟩, swap1, dup3, add,
    raw mstore 3 (solcErrorStringMem2 ⟨46⟩ solcFreePtrMem) (UInt256.ofNat 7)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd5787 := rd5754.pushConst auctionInitializableAlreadyStringWord1
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd5792 := evm_run rd5787 with [
    push1 ⟨64⟩, dup3, add,
    raw mstore 3
      (solcErrorStringMem3 ⟨46⟩ auctionInitializableAlreadyStringWord1 solcFreePtrMem)
      (UInt256.ofNat 8) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd5807 := rd5792.pushConst auctionInitializableAlreadyRawStringWord2
    (width := 14) (op := .PUSH14) (by decide) (by decide) (by evm_ov)
  have rd5809₀ := evm_run rd5807 with [push1 ⟨146⟩, shl]
  have rd5809 := rd5809₀
  rw [show UInt256.shiftLeft auctionInitializableAlreadyRawStringWord2 ⟨146⟩ =
      auctionInitializableAlreadyStringWord2 by rfl] at rd5809
  have rd5819₀ := evm_run rd5809 with [
    push1 ⟨96⟩, dup3, add,
    raw mstore 3 (auctionInitializableAlreadyStringMem4 solcFreePtrMem)
      (UInt256.ofNat 9) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup1, add, swap1]
  have rd5819 := rd5819₀
  rw [show (⟨132⟩ : UInt256) + ⟨132⟩ = ⟨264⟩ by decide] at rd5819
  have rd994 := evm_run rd5819 with [jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide)
      mem_cost auctionInitializableAlreadyStringMem4_mload64 (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨264⟩ : UInt256) ⟨128⟩ = ⟨136⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem auctionInitializePausableUnchained_nested {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hperm : I.perm = true)
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4993⟩
      (ret :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, auctionUnpausePostMap σ I) k C := by
  have rd4994 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, rd4995₀⟩ := rd4994.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd4995⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨4995⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd4995₀⟩
  have rd5004₀ := evm_run rd4995 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1]
  have hcomm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) =
        UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)
  have hnz' : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ≠ ⟨0⟩ := by
    simpa [hcomm] using hnz
  have rd5016 := evm_run rd5004₀ with [
    push2 ⟨5016⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd5044 := evm_run rd5016 with [
    push2 ⟨5044⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd5045 := evm_run rd5044 with [push0]
  obtain ⟨_, _, rd5046₀⟩ := rd5045.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd5046⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨5046⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd5046₀⟩
  have rd5058₀ := evm_run rd5046 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, iszero, dup1, iszero]
  have hiz : UInt256.isZero
      (UInt256.land ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne hnz'
  have rd5058 := rd5058₀
  rw [hiz] at rd5058
  have rd5076 := evm_run rd5058 with [
    push2 ⟨5076⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  have rd5080₀ := evm_run rd5076 with [push1 ⟨51⟩, dup1]
  obtain ⟨_, _, rd5081₀⟩ := rd5080₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd5081⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨5081⟩
      (auctionSlotWord ⟨51⟩ σ I :: ⟨51⟩ :: ⟨0⟩ :: ret :: R) solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd5081₀⟩
  have rd5086₀ := evm_run rd5081 with [push1 ⟨255⟩, not, and, swap1]
  have hclear : UInt256.land (UInt256.lnot ⟨255⟩) (auctionSlotWord ⟨51⟩ σ I) =
      auctionPausedSetFalseWord (auctionSlotWord ⟨51⟩ σ I) := by
    rw [u256_land_comm]
    rfl
  have rd5086 := rd5086₀
  rw [hclear] at rd5086
  obtain ⟨_, _, rd5087₀⟩ := rd5086.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd5087⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨5087⟩ (⟨0⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, auctionUnpausePostMap σ I) k C := by
    exact ⟨_, _, by simpa [auctionUnpausePostMap] using rd5087₀⟩
  have rd2850 := evm_run rd5087 with [
    dup1, iszero, push2 ⟨2850⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2850 with [pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializeNoop_nested {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4892⟩
      (ret :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have rd4894 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, rd4895₀⟩ := rd4894.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd4895⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨4895⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd4895₀⟩
  have rd4904₀ := evm_run rd4895 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1]
  have hcomm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) =
        UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)
  have hnz' : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ≠ ⟨0⟩ := by
    simpa [hcomm] using hnz
  have rd4915 := evm_run rd4904₀ with [
    push2 ⟨4915⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd4943 := evm_run rd4915 with [
    push2 ⟨4943⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd4945 := evm_run rd4943 with [push0]
  obtain ⟨_, _, rd4946₀⟩ := rd4945.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd4946⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨4946⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd4946₀⟩
  have rd4957₀ := evm_run rd4946 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, iszero, dup1, iszero]
  have hiz : UInt256.isZero
      (UInt256.land ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne hnz'
  have rd4957 := rd4957₀
  rw [hiz] at rd4957
  have rd3877 := evm_run rd4957 with [
    push2 ⟨3877⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  have rd2850 := evm_run rd3877 with [
    dup1, iszero, push2 ⟨2850⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2850 with [pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializePausable_nested {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hperm : I.perm = true)
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3778⟩
      (ret :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, auctionUnpausePostMap σ I) k C := by
  have rd3779 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, rd3780₀⟩ := rd3779.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd3780⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3780⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3780₀⟩
  have rd3789₀ := evm_run rd3780 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1]
  have hcomm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) =
        UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)
  have hnz' : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ≠ ⟨0⟩ := by
    simpa [hcomm] using hnz
  have rd3801 := evm_run rd3789₀ with [
    push2 ⟨3801⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd3829 := evm_run rd3801 with [
    push2 ⟨3829⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd3831 := evm_run rd3829 with [push0]
  obtain ⟨_, _, rd3832₀⟩ := rd3831.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd3832⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3832⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3832₀⟩
  have rd3843₀ := evm_run rd3832 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, iszero, dup1, iszero]
  have hiz : UInt256.isZero
      (UInt256.land ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne hnz'
  have rd3843 := rd3843₀
  rw [hiz] at rd3843
  have rd3861 := evm_run rd3843 with [
    push2 ⟨3861⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  have rd4892 := evm_run rd3861 with [push2 ⟨3869⟩, push2 ⟨4892⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd3869⟩ := auctionInitializeNoop_nested (σ := σ) (g := g)
    (ret := ⟨3869⟩) (R := ⟨0⟩ :: ret :: R) hnz (by jump_dest) rd4892
  have rd4993 := evm_run rd3869 with [
    jumpdest, push2 ⟨3877⟩, push2 ⟨4993⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd3877⟩ := auctionInitializePausableUnchained_nested (σ := σ) (g := g)
    (ret := ⟨3877⟩) (R := ⟨0⟩ :: ret :: R) hperm hnz (by jump_dest) rd4993
  have rd2850 := evm_run rd3877 with [
    jumpdest, dup1, iszero, push2 ⟨2850⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2850 with [pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializeReentrancyGuardUnchained_nested {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hperm : I.perm = true)
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5105⟩
      (ret :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨101⟩ ⟨1⟩) k C := by
  have rd5106 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, rd5107₀⟩ := rd5106.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd5107⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨5107⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd5107₀⟩
  have rd5116₀ := evm_run rd5107 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1]
  have hcomm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) =
        UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)
  have hnz' : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ≠ ⟨0⟩ := by
    simpa [hcomm] using hnz
  have rd5128 := evm_run rd5116₀ with [
    push2 ⟨5128⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd5156 := evm_run rd5128 with [
    push2 ⟨5156⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd5157 := evm_run rd5156 with [push0]
  obtain ⟨_, _, rd5158₀⟩ := rd5157.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd5158⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨5158⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd5158₀⟩
  have rd5169₀ := evm_run rd5158 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, iszero, dup1, iszero]
  have hiz : UInt256.isZero
      (UInt256.land ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne hnz'
  have rd5169 := rd5169₀
  rw [hiz] at rd5169
  have rd5188 := evm_run rd5169 with [
    push2 ⟨5188⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  have rd5192 := evm_run rd5188 with [push1 ⟨1⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd5193₀⟩ := rd5192.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd5193⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨5193⟩ (⟨0⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨101⟩ ⟨1⟩) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap] using rd5193₀⟩
  have rd2850 := evm_run rd5193 with [
    dup1, iszero, push2 ⟨2850⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2850 with [pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializeReentrancyGuard_nested {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hperm : I.perm = true)
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3896⟩
      (ret :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨101⟩ ⟨1⟩) k C := by
  have rd3897 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, rd3898₀⟩ := rd3897.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd3898⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3898⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3898₀⟩
  have rd3907₀ := evm_run rd3898 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1]
  have hcomm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) =
        UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)
  have hnz' : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ≠ ⟨0⟩ := by
    simpa [hcomm] using hnz
  have rd3919 := evm_run rd3907₀ with [
    push2 ⟨3919⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd3947 := evm_run rd3919 with [
    push2 ⟨3947⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd3949 := evm_run rd3947 with [push0]
  obtain ⟨_, _, rd3950₀⟩ := rd3949.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd3950⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3950⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3950₀⟩
  have rd3961₀ := evm_run rd3950 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, iszero, dup1, iszero]
  have hiz : UInt256.isZero
      (UInt256.land ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne hnz'
  have rd3961 := rd3961₀
  rw [hiz] at rd3961
  have rd3979 := evm_run rd3961 with [
    push2 ⟨3979⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  have rd5105 := evm_run rd3979 with [push2 ⟨3877⟩, push2 ⟨5105⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd3877⟩ := auctionInitializeReentrancyGuardUnchained_nested (σ := σ)
    (g := g) (ret := ⟨3877⟩) (R := ⟨0⟩ :: ret :: R) hperm hnz (by jump_dest) rd5105
  have rd2850 := evm_run rd3877 with [
    jumpdest, dup1, iszero, push2 ⟨2850⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2850 with [pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem auctionSetOwnerRoutine {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {newOwner ret : UInt256} {R : List UInt256}
    (hperm : I.perm = true)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3574⟩
      (newOwner :: ret :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSetOwnerPostMap σ I newOwner) k C := by
  have rd3578₀ := evm_run h with [jumpdest, push1 ⟨151⟩, dup1]
  obtain ⟨_, _, rd3579₀⟩ := rd3578₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd3579⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3579⟩
      (auctionSlotWord ⟨151⟩ σ I :: ⟨151⟩ :: newOwner :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3579₀⟩
  have hsolcMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hpostComm :
      UInt256.lor (UInt256.land solcAddrMask newOwner)
          (UInt256.land (auctionSlotWord ⟨151⟩ σ I) (UInt256.lnot solcAddrMask)) =
        auctionSetOwnerWord (auctionSlotWord ⟨151⟩ σ I) newOwner := by
    rw [u256_land_comm solcAddrMask newOwner]
    unfold auctionSetOwnerWord setAddressOffset0Word
    rw [u256_lor_comm]
  have rd3605₀ := evm_run rd3579 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, dup2, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, dup4, and, dup2, lor,
    swap1, swap4]
  have rd3605 := rd3605₀
  rw [hsolcMask] at rd3605
  rw [hpostComm] at rd3605
  obtain ⟨_, _, rd3606₀⟩ := rd3605.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd3606⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3606⟩
      [solcAddrMask, auctionSlotWord ⟨151⟩ σ I, UInt256.land solcAddrMask newOwner,
        newOwner, ret].append R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSetOwnerPostMap σ I newOwner) k C := by
    exact ⟨_, _, by simpa [auctionSetOwnerPostMap] using rd3606₀⟩
  have rd3615 := evm_run rd3606 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap2, and, swap2, swap1, dup3, swap1]
  have rd3648 := rd3615.pushConst auctionOwnershipTransferredTopic
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd3652 := evm_run rd3648 with [swap1, push0, swap1]
  have rd3653 := RD.log3 0 (UInt256.ofNat 3) rd3652 (by decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by decide) (by evm_ov)
  exact ⟨_, _, evm_run rd3653 with [pop, pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializeOwnableUnchained_nested {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hperm : I.perm = true)
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5212⟩
      (ret :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSetOwnerPostMap σ I (auctionSourceWord I)) k C := by
  have rd5213 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, rd5214₀⟩ := rd5213.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd5214⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨5214⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd5214₀⟩
  have rd5223₀ := evm_run rd5214 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1]
  have hcomm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) =
        UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)
  have hnz' : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ≠ ⟨0⟩ := by
    simpa [hcomm] using hnz
  have rd5235 := evm_run rd5223₀ with [
    push2 ⟨5235⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd5263 := evm_run rd5235 with [
    push2 ⟨5263⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd5264 := evm_run rd5263 with [push0]
  obtain ⟨_, _, rd5265₀⟩ := rd5264.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd5265⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨5265⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd5265₀⟩
  have rd5277₀ := evm_run rd5265 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, iszero, dup1, iszero]
  have hiz : UInt256.isZero
      (UInt256.land ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne hnz'
  have rd5277 := rd5277₀
  rw [hiz] at rd5277
  have rd5295 := evm_run rd5277 with [
    push2 ⟨5295⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  have rd3574 := evm_run rd5295 with [
    push2 ⟨3877⟩, caller, push2 ⟨3574⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd3877⟩ := auctionSetOwnerRoutine (σ := σ) (g := g)
    (newOwner := auctionSourceWord I) (ret := ⟨3877⟩) (R := ⟨0⟩ :: ret :: R)
    hperm (by jump_dest) (by simpa [auctionSourceWord] using rd3574)
  have rd2850 := evm_run rd3877 with [
    jumpdest, dup1, iszero, push2 ⟨2850⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2850 with [pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializeOwnable_nested {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hperm : I.perm = true)
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3987⟩
      (ret :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSetOwnerPostMap σ I (auctionSourceWord I)) k C := by
  have rd3988 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, rd3989₀⟩ := rd3988.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd3989⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3989⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3989₀⟩
  have rd3998₀ := evm_run rd3989 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1]
  have hcomm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) =
        UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)
  have hnz' : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ≠ ⟨0⟩ := by
    simpa [hcomm] using hnz
  have rd4010 := evm_run rd3998₀ with [
    push2 ⟨4010⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd4038 := evm_run rd4010 with [
    push2 ⟨4038⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd4039 := evm_run rd4038 with [push0]
  obtain ⟨_, _, rd4040₀⟩ := rd4039.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd4040⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨4040⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd4040₀⟩
  have rd4052₀ := evm_run rd4040 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, iszero, dup1, iszero]
  have hiz : UInt256.isZero
      (UInt256.land ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne hnz'
  have rd4052 := rd4052₀
  rw [hiz] at rd4052
  have rd4070 := evm_run rd4052 with [
    push2 ⟨4070⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  have rd4892 := evm_run rd4070 with [push2 ⟨4078⟩, push2 ⟨4892⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd4078⟩ := auctionInitializeNoop_nested (σ := σ) (g := g)
    (ret := ⟨4078⟩) (R := ⟨0⟩ :: ret :: R) hnz (by jump_dest) rd4892
  have rd5212 := evm_run rd4078 with [
    jumpdest, push2 ⟨3877⟩, push2 ⟨5212⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd3877⟩ := auctionInitializeOwnableUnchained_nested (σ := σ) (g := g)
    (ret := ⟨3877⟩) (R := ⟨0⟩ :: ret :: R) hperm hnz (by jump_dest) rd5212
  have rd2850 := evm_run rd3877 with [
    jumpdest, dup1, iszero, push2 ⟨2850⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2850 with [pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem auctionPauseRoutine_success {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hperm : I.perm = true)
    (hzero : auctionPausedWord σ I = ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3655⟩
      (ret :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, auctionPausePostMap σ I) k C := by
  have rd3663₀ := evm_run h with [jumpdest, push1 ⟨51⟩]
  obtain ⟨_, _, rd3659₀⟩ := rd3663₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd3659⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3659⟩
      (auctionSlotWord ⟨51⟩ σ I :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3659₀⟩
  have rd3663 := evm_run rd3659 with [push1 ⟨255⟩, and, iszero]
  have hmask : UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I) = auctionPausedWord σ I := by
    rw [auctionPausedWord, u256_land_comm]
  have hcond : UInt256.isZero (UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I)) ≠ ⟨0⟩ := by
    rw [hmask, hzero]
    decide
  have rd3725 := evm_run rd3663 with [
    push2 ⟨3725⟩, jumpiT hcond (by jump_dest), jumpdest]
  have rd3734₀ := evm_run rd3725 with [push1 ⟨51⟩, dup1]
  obtain ⟨_, _, rd3730₀⟩ := rd3734₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd3730⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3730⟩
      (auctionSlotWord ⟨51⟩ σ I :: ⟨51⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3730₀⟩
  have rd3737₀ := evm_run rd3730 with [push1 ⟨255⟩, not, and, push1 ⟨1⟩]
  have rd3737₁ := rd3737₀
  have hland : UInt256.land (UInt256.lnot ⟨255⟩) (auctionSlotWord ⟨51⟩ σ I) =
      UInt256.land (auctionSlotWord ⟨51⟩ σ I) (UInt256.lnot ⟨255⟩) := by
    exact u256_land_comm (UInt256.lnot ⟨255⟩) (auctionSlotWord ⟨51⟩ σ I)
  rw [hland] at rd3737₁
  have rd3737₂ := RD.lor rd3737₁ (by decide) (by evm_ov)
  have hlor :
      UInt256.lor ⟨1⟩
          (UInt256.land (auctionSlotWord ⟨51⟩ σ I) (UInt256.lnot ⟨255⟩)) =
        auctionPausedSetTrueWord (auctionSlotWord ⟨51⟩ σ I) := by
    unfold auctionPausedSetTrueWord
    exact u256_lor_comm ⟨1⟩
      (UInt256.land (auctionSlotWord ⟨51⟩ σ I) (UInt256.lnot ⟨255⟩))
  rw [hlor] at rd3737₂
  have rd3738 := evm_run rd3737₂ with [swap1]
  obtain ⟨_, _, rd3739₀⟩ := rd3738.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd3739⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3739⟩ (ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionPausePostMap σ I) k C := by
    exact ⟨_, _, by simpa [auctionPausePostMap] using rd3739₀⟩
  have rd3772 := rd3739.pushConst
    (⟨0x62e78cea01bee320cd4e420270b5ea74000d11b0c9f74754ebdbfc544b05a258⟩ : UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd2971 := evm_run rd3772 with [push2 ⟨2971⟩, caller, swap1, jump (by jump_dest)]
  have rd2988₀ := evm_run rd2971 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap2, and, dup2]
  have rd2988 := rd2988₀
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  rw [haddrMask] at rd2988
  have hcaller : UInt256.land (UInt256.ofNat I.source.val) solcAddrMask = auctionSourceWord I := by
    rw [u256_land_comm]
    simpa [auctionSourceWord] using solcAddrMask_clean_left (auctionSourceWord_canonical I)
  rw [hcaller] at rd2988
  have rd2991 := evm_run rd2988 with [
    raw mstore 6 (auctionEventMem I) (UInt256.ofNat 5) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd2998₀ := evm_run rd2991 with [
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (auctionEventMem_mload64 I) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have hlen32 : ((⟨32⟩ : UInt256) + ⟨128⟩).sub ⟨128⟩ = ⟨32⟩ := by
    decide
  have rd2998 := rd2998₀
  rw [hlen32] at rd2998
  have rd2999 := RD.log1 0 (UInt256.ofNat 5) rd2998 (by decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by decide) (by evm_ov)
  exact ⟨_, _, evm_run rd2999 with [jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializeArgsStores_nested {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hperm : I.perm = true)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨2245⟩
      ([⟨0⟩, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
        auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionInitializeArgsPostMap σ I) k C := by
  have rd2249₀ := evm_run h with [jumpdest, push1 ⟨201⟩, dup1]
  obtain ⟨_, _, rd2250₀⟩ := rd2249₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2250⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2250⟩
      (auctionSlotWord ⟨201⟩ σ I :: ⟨201⟩ ::
        [⟨0⟩, auctionInitializeDurationWord I,
          auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
          auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
          auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2250₀⟩
  have hsolcMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hpost201 :
      UInt256.lor (UInt256.land solcAddrMask (auctionInitializeNounsWord I))
          (UInt256.land (auctionSlotWord ⟨201⟩ σ I) (UInt256.lnot solcAddrMask)) =
        setAddressOffset0Word (auctionSlotWord ⟨201⟩ σ I) (auctionInitializeNounsWord I) := by
    rw [u256_land_comm solcAddrMask (auctionInitializeNounsWord I)]
    unfold setAddressOffset0Word
    rw [u256_lor_comm]
  have rd2276₀ := evm_run rd2250 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup1, dup11, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, swap3, dup4, and,
    lor, swap1, swap3]
  have rd2276 := rd2276₀
  rw [hsolcMask] at rd2276
  rw [hpost201] at rd2276
  obtain ⟨_, _, rd2277₀⟩ := rd2276.sstore hperm (by decide) (by evm_ov)
  let s5 := auctionInitializeSetAddressMap σ I ⟨201⟩ (auctionInitializeNounsWord I)
  obtain ⟨_, _, rd2277⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2277⟩
      ([⟨0⟩, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
        auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, s5) k C := by
    exact ⟨_, _, by simpa [s5, auctionInitializeSetAddressMap] using rd2277₀⟩
  have rd2280₀ := evm_run rd2277 with [push1 ⟨202⟩, dup1]
  obtain ⟨_, _, rd2281₀⟩ := rd2280₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2281⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2281⟩
      (auctionSlotWord ⟨202⟩ s5 I :: ⟨202⟩ ::
        [⟨0⟩, auctionInitializeDurationWord I,
          auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
          auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
          auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, s5) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2281₀⟩
  have hpost202 :
      UInt256.lor (UInt256.land solcAddrMask (auctionInitializeWethWord I))
          (UInt256.land (auctionSlotWord ⟨202⟩ s5 I) (UInt256.lnot solcAddrMask)) =
        setAddressOffset0Word (auctionSlotWord ⟨202⟩ s5 I) (auctionInitializeWethWord I) := by
    rw [u256_land_comm solcAddrMask (auctionInitializeWethWord I)]
    unfold setAddressOffset0Word
    rw [u256_lor_comm]
  have rd2293₀ := evm_run rd2281 with [
    swap3, dup10, and, swap3, swap1, swap2, and, swap2, swap1, swap2, lor, swap1]
  have rd2293 := rd2293₀
  rw [hpost202] at rd2293
  obtain ⟨_, _, rd2294₀⟩ := rd2293.sstore hperm (by decide) (by evm_ov)
  let s6 := auctionInitializeSetAddressMap s5 I ⟨202⟩ (auctionInitializeWethWord I)
  obtain ⟨_, _, rd2294⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2294⟩
      ([⟨0⟩, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
        auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, s6) k C := by
    exact ⟨_, _, by simpa [s6, auctionInitializeSetAddressMap] using rd2294₀⟩
  have rd2298₀ := evm_run rd2294 with [push1 ⟨203⟩, dup6, swap1]
  obtain ⟨_, _, rd2299₀⟩ := rd2298₀.sstore hperm (by decide) (by evm_ov)
  let s7 := auctionInitializeSetUint256Map s6 I ⟨203⟩ (auctionInitializeTimeBufferWord I)
  obtain ⟨_, _, rd2299⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2299⟩
      ([⟨0⟩, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
        auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, s7) k C := by
    exact ⟨_, _, by simpa [s7, auctionInitializeSetUint256Map] using rd2299₀⟩
  have rd2303₀ := evm_run rd2299 with [push1 ⟨204⟩, dup5, swap1]
  obtain ⟨_, _, rd2304₀⟩ := rd2303₀.sstore hperm (by decide) (by evm_ov)
  let s8 := auctionInitializeSetUint256Map s7 I ⟨204⟩ (auctionInitializeReservePriceWord I)
  obtain ⟨_, _, rd2304⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2304⟩
      ([⟨0⟩, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
        auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, s8) k C := by
    exact ⟨_, _, by simpa [s8, auctionInitializeSetUint256Map] using rd2304₀⟩
  have rd2307₀ := evm_run rd2304 with [push1 ⟨205⟩, dup1]
  obtain ⟨_, _, rd2308₀⟩ := rd2307₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2308⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2308⟩
      (auctionSlotWord ⟨205⟩ s8 I :: ⟨205⟩ ::
        [⟨0⟩, auctionInitializeDurationWord I,
          auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
          auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
          auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, s8) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2308₀⟩
  have rd2320₀ := evm_run rd2308 with [
    push1 ⟨255⟩, dup6, and, push1 ⟨255⟩, not, swap1, swap2, and, lor, swap1]
  have hmin : UInt256.lor
      (UInt256.land (UInt256.lnot ⟨255⟩) (auctionSlotWord ⟨205⟩ s8 I))
      (UInt256.land ⟨255⟩ (auctionInitializeMinBidIncrementPercentageWord I)) =
        auctionSetUint8Offset0Word (auctionSlotWord ⟨205⟩ s8 I)
          (auctionInitializeMinBidIncrementPercentageWord I) := by
    unfold auctionSetUint8Offset0Word
    rw [u256_land_comm ⟨255⟩ (auctionInitializeMinBidIncrementPercentageWord I)]
  have rd2320 := rd2320₀
  rw [hmin] at rd2320
  obtain ⟨_, _, rd2321₀⟩ := rd2320.sstore hperm (by decide) (by evm_ov)
  let s9 := auctionInitializeSetMinBidMap s8 I
  obtain ⟨_, _, rd2321⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2321⟩
      ([⟨0⟩, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
        auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, s9) k C := by
    exact ⟨_, _, by simpa [s9, auctionInitializeSetMinBidMap] using rd2321₀⟩
  have rd2325₀ := evm_run rd2321 with [push1 ⟨206⟩, dup3, swap1]
  obtain ⟨_, _, rd2326₀⟩ := rd2325₀.sstore hperm (by decide) (by evm_ov)
  let s10 := auctionInitializeSetUint256Map s9 I ⟨206⟩ (auctionInitializeDurationWord I)
  obtain ⟨_, _, rd2326⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2326⟩
      ([⟨0⟩, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
        auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, s10) k C := by
    exact ⟨_, _, by simpa [s10, auctionInitializeSetUint256Map] using rd2326₀⟩
  have rd2342 := evm_run rd2326 with [
    dup1, iszero, push2 ⟨2342⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  have rd2350 := evm_run rd2342 with [pop, pop, pop, pop, pop, pop, pop, jump hret]
  exact ⟨_, _, by simpa [auctionInitializeArgsPostMap, s5, s6, s7, s8, s9, s10] using rd2350⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializeArgsStores_top {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hperm : I.perm = true)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨2245⟩
      ([⟨1⟩, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
        auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionInitializeSetInitializingFalseMap (auctionInitializeArgsPostMap σ I) I) k C := by
  have rd2249₀ := evm_run h with [jumpdest, push1 ⟨201⟩, dup1]
  obtain ⟨_, _, rd2250₀⟩ := rd2249₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2250⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2250⟩
      (auctionSlotWord ⟨201⟩ σ I :: ⟨201⟩ ::
        [⟨1⟩, auctionInitializeDurationWord I,
          auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
          auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
          auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2250₀⟩
  have hsolcMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hpost201 :
      UInt256.lor (UInt256.land solcAddrMask (auctionInitializeNounsWord I))
          (UInt256.land (auctionSlotWord ⟨201⟩ σ I) (UInt256.lnot solcAddrMask)) =
        setAddressOffset0Word (auctionSlotWord ⟨201⟩ σ I) (auctionInitializeNounsWord I) := by
    rw [u256_land_comm solcAddrMask (auctionInitializeNounsWord I)]
    unfold setAddressOffset0Word
    rw [u256_lor_comm]
  have rd2276₀ := evm_run rd2250 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup1, dup11, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, swap3, dup4, and,
    lor, swap1, swap3]
  have rd2276 := rd2276₀
  rw [hsolcMask] at rd2276
  rw [hpost201] at rd2276
  obtain ⟨_, _, rd2277₀⟩ := rd2276.sstore hperm (by decide) (by evm_ov)
  let s5 := auctionInitializeSetAddressMap σ I ⟨201⟩ (auctionInitializeNounsWord I)
  obtain ⟨_, _, rd2277⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2277⟩
      ([⟨1⟩, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
        auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, s5) k C := by
    exact ⟨_, _, by simpa [s5, auctionInitializeSetAddressMap] using rd2277₀⟩
  have rd2280₀ := evm_run rd2277 with [push1 ⟨202⟩, dup1]
  obtain ⟨_, _, rd2281₀⟩ := rd2280₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2281⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2281⟩
      (auctionSlotWord ⟨202⟩ s5 I :: ⟨202⟩ ::
        [⟨1⟩, auctionInitializeDurationWord I,
          auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
          auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
          auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, s5) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2281₀⟩
  have hpost202 :
      UInt256.lor (UInt256.land solcAddrMask (auctionInitializeWethWord I))
          (UInt256.land (auctionSlotWord ⟨202⟩ s5 I) (UInt256.lnot solcAddrMask)) =
        setAddressOffset0Word (auctionSlotWord ⟨202⟩ s5 I) (auctionInitializeWethWord I) := by
    rw [u256_land_comm solcAddrMask (auctionInitializeWethWord I)]
    unfold setAddressOffset0Word
    rw [u256_lor_comm]
  have rd2293₀ := evm_run rd2281 with [
    swap3, dup10, and, swap3, swap1, swap2, and, swap2, swap1, swap2, lor, swap1]
  have rd2293 := rd2293₀
  rw [hpost202] at rd2293
  obtain ⟨_, _, rd2294₀⟩ := rd2293.sstore hperm (by decide) (by evm_ov)
  let s6 := auctionInitializeSetAddressMap s5 I ⟨202⟩ (auctionInitializeWethWord I)
  obtain ⟨_, _, rd2294⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2294⟩
      ([⟨1⟩, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
        auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, s6) k C := by
    exact ⟨_, _, by simpa [s6, auctionInitializeSetAddressMap] using rd2294₀⟩
  have rd2298₀ := evm_run rd2294 with [push1 ⟨203⟩, dup6, swap1]
  obtain ⟨_, _, rd2299₀⟩ := rd2298₀.sstore hperm (by decide) (by evm_ov)
  let s7 := auctionInitializeSetUint256Map s6 I ⟨203⟩ (auctionInitializeTimeBufferWord I)
  obtain ⟨_, _, rd2299⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2299⟩
      ([⟨1⟩, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
        auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, s7) k C := by
    exact ⟨_, _, by simpa [s7, auctionInitializeSetUint256Map] using rd2299₀⟩
  have rd2303₀ := evm_run rd2299 with [push1 ⟨204⟩, dup5, swap1]
  obtain ⟨_, _, rd2304₀⟩ := rd2303₀.sstore hperm (by decide) (by evm_ov)
  let s8 := auctionInitializeSetUint256Map s7 I ⟨204⟩ (auctionInitializeReservePriceWord I)
  obtain ⟨_, _, rd2304⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2304⟩
      ([⟨1⟩, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
        auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, s8) k C := by
    exact ⟨_, _, by simpa [s8, auctionInitializeSetUint256Map] using rd2304₀⟩
  have rd2307₀ := evm_run rd2304 with [push1 ⟨205⟩, dup1]
  obtain ⟨_, _, rd2308₀⟩ := rd2307₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2308⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2308⟩
      (auctionSlotWord ⟨205⟩ s8 I :: ⟨205⟩ ::
        [⟨1⟩, auctionInitializeDurationWord I,
          auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
          auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
          auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, s8) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2308₀⟩
  have rd2320₀ := evm_run rd2308 with [
    push1 ⟨255⟩, dup6, and, push1 ⟨255⟩, not, swap1, swap2, and, lor, swap1]
  have hmin : UInt256.lor
      (UInt256.land (UInt256.lnot ⟨255⟩) (auctionSlotWord ⟨205⟩ s8 I))
      (UInt256.land ⟨255⟩ (auctionInitializeMinBidIncrementPercentageWord I)) =
        auctionSetUint8Offset0Word (auctionSlotWord ⟨205⟩ s8 I)
          (auctionInitializeMinBidIncrementPercentageWord I) := by
    unfold auctionSetUint8Offset0Word
    rw [u256_land_comm ⟨255⟩ (auctionInitializeMinBidIncrementPercentageWord I)]
  have rd2320 := rd2320₀
  rw [hmin] at rd2320
  obtain ⟨_, _, rd2321₀⟩ := rd2320.sstore hperm (by decide) (by evm_ov)
  let s9 := auctionInitializeSetMinBidMap s8 I
  obtain ⟨_, _, rd2321⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2321⟩
      ([⟨1⟩, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
        auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, s9) k C := by
    exact ⟨_, _, by simpa [s9, auctionInitializeSetMinBidMap] using rd2321₀⟩
  have rd2325₀ := evm_run rd2321 with [push1 ⟨206⟩, dup3, swap1]
  obtain ⟨_, _, rd2326₀⟩ := rd2325₀.sstore hperm (by decide) (by evm_ov)
  let s10 := auctionInitializeSetUint256Map s9 I ⟨206⟩ (auctionInitializeDurationWord I)
  obtain ⟨_, _, rd2326⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2326⟩
      ([⟨1⟩, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
        auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, s10) k C := by
    exact ⟨_, _, by simpa [s10, auctionInitializeSetUint256Map] using rd2326₀⟩
  have rd2332 := evm_run rd2326 with [
    dup1, iszero, push2 ⟨2342⟩, jumpiNT (by decide), push0, dup1]
  obtain ⟨_, _, rd2335₀⟩ := rd2332.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2335⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2335⟩
      (auctionSlotWord ⟨0⟩ s10 I :: ⟨0⟩ ::
        [⟨1⟩, auctionInitializeDurationWord I,
          auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
          auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
          auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, s10) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2335₀⟩
  have hclear : UInt256.land (UInt256.lnot ⟨65280⟩) (auctionSlotWord ⟨0⟩ s10 I) =
      auctionSetBoolOffset1FalseWord (auctionSlotWord ⟨0⟩ s10 I) := by
    rw [u256_land_comm]
    exact auctionClearBoolOffset1Word_eq (auctionSlotWord ⟨0⟩ s10 I)
  have rd2341₀ := evm_run rd2335 with [push2 ⟨65280⟩, not, and, swap1]
  have rd2341 := rd2341₀
  rw [hclear] at rd2341
  obtain ⟨_, _, rd2342₀⟩ := rd2341.sstore hperm (by decide) (by evm_ov)
  let s11 := auctionInitializeSetInitializingFalseMap s10 I
  obtain ⟨_, _, rd2342⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2342⟩
      ([⟨1⟩, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
        auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, s11) k C := by
    exact ⟨_, _, by simpa [s11, auctionInitializeSetInitializingFalseMap] using rd2342₀⟩
  have rd2350 := evm_run rd2342 with [jumpdest, pop, pop, pop, pop, pop, pop, pop, jump hret]
  exact ⟨_, _, by
    simpa [auctionInitializeArgsPostMap, s5, s6, s7, s8, s9, s10, s11] using rd2350⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializeCore_nested {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hperm : I.perm = true)
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨2213⟩
      ([⟨0⟩, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
        auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionInitializeCorePostMap σ I) k C := by
  have rd3778 := evm_run h with [jumpdest, push2 ⟨2221⟩, push2 ⟨3778⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd2221⟩ := auctionInitializePausable_nested (σ := σ) (g := g)
    (ret := ⟨2221⟩)
    (R := [⟨0⟩, auctionInitializeDurationWord I,
      auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
      auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
      auctionInitializeNounsWord I].append (ret :: R))
    hperm hnz (by jump_dest) rd3778
  let s1 := auctionUnpausePostMap σ I
  have hnz1 : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ s1 I) ⟨256⟩) ⟨255⟩ ≠
      ⟨0⟩ := by
    dsimp [s1, auctionUnpausePostMap]
    exact auctionInitializingGuard_ne_sstore_ne (slot := ⟨51⟩)
      (val := auctionPausedSetFalseWord (auctionSlotWord ⟨51⟩ σ I)) (by decide) hnz
  have rd3896 := evm_run rd2221 with [jumpdest, push2 ⟨2229⟩, push2 ⟨3896⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd2229⟩ := auctionInitializeReentrancyGuard_nested (σ := s1) (g := g)
    (ret := ⟨2229⟩)
    (R := [⟨0⟩, auctionInitializeDurationWord I,
      auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
      auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
      auctionInitializeNounsWord I].append (ret :: R))
    hperm hnz1 (by jump_dest) rd3896
  let s2 := auctionInitializeSetStatusMap s1 I
  have hnz2 : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ s2 I) ⟨256⟩) ⟨255⟩ ≠
      ⟨0⟩ := by
    dsimp [s2, auctionInitializeSetStatusMap]
    exact auctionInitializingGuard_ne_sstore_ne (slot := ⟨101⟩) (val := ⟨1⟩)
      (by decide) hnz1
  have rd3987 := evm_run rd2229 with [jumpdest, push2 ⟨2237⟩, push2 ⟨3987⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd2237⟩ := auctionInitializeOwnable_nested (σ := s2) (g := g)
    (ret := ⟨2237⟩)
    (R := [⟨0⟩, auctionInitializeDurationWord I,
      auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
      auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
      auctionInitializeNounsWord I].append (ret :: R))
    hperm hnz2 (by jump_dest) rd3987
  let s3 := auctionSetOwnerPostMap s2 I (auctionSourceWord I)
  have hpaused0 : auctionPausedWord s3 I = ⟨0⟩ := by
    dsimp [s3, s2, s1]
    exact (auctionInitializePrePausePausedZero (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))
  have rd3655 := evm_run rd2237 with [jumpdest, push2 ⟨2245⟩, push2 ⟨3655⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd2245⟩ := auctionPauseRoutine_success (σ := s3) (g := g)
    (ret := ⟨2245⟩)
    (R := [⟨0⟩, auctionInitializeDurationWord I,
      auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
      auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
      auctionInitializeNounsWord I].append (ret :: R))
    hperm hpaused0 (by jump_dest) rd3655
  let s4 := auctionPausePostMap s3 I
  obtain ⟨_, _, rdret⟩ := auctionInitializeArgsStores_nested (σ := s4) (g := g)
    (ret := ret) (R := R) hperm hret rd2245
  exact ⟨_, _, by simpa [auctionInitializeCorePostMap, s1, s2, s3, s4] using rdret⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializeCore_top {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hperm : I.perm = true)
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨2213⟩
      ([⟨1⟩, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
        auctionInitializeNounsWord I].append (ret :: R))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionInitializeSetInitializingFalseMap (auctionInitializeCorePostMap σ I) I) k C := by
  have rd3778 := evm_run h with [jumpdest, push2 ⟨2221⟩, push2 ⟨3778⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd2221⟩ := auctionInitializePausable_nested (σ := σ) (g := g)
    (ret := ⟨2221⟩)
    (R := [⟨1⟩, auctionInitializeDurationWord I,
      auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
      auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
      auctionInitializeNounsWord I].append (ret :: R))
    hperm hnz (by jump_dest) rd3778
  let s1 := auctionUnpausePostMap σ I
  have hnz1 : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ s1 I) ⟨256⟩) ⟨255⟩ ≠
      ⟨0⟩ := by
    dsimp [s1, auctionUnpausePostMap]
    exact auctionInitializingGuard_ne_sstore_ne (slot := ⟨51⟩)
      (val := auctionPausedSetFalseWord (auctionSlotWord ⟨51⟩ σ I)) (by decide) hnz
  have rd3896 := evm_run rd2221 with [
    jumpdest, push2 ⟨2229⟩, push2 ⟨3896⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd2229⟩ := auctionInitializeReentrancyGuard_nested (σ := s1) (g := g)
    (ret := ⟨2229⟩)
    (R := [⟨1⟩, auctionInitializeDurationWord I,
      auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
      auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
      auctionInitializeNounsWord I].append (ret :: R))
    hperm hnz1 (by jump_dest) rd3896
  let s2 := auctionInitializeSetStatusMap s1 I
  have hnz2 : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ s2 I) ⟨256⟩) ⟨255⟩ ≠
      ⟨0⟩ := by
    dsimp [s2, auctionInitializeSetStatusMap]
    exact auctionInitializingGuard_ne_sstore_ne (slot := ⟨101⟩) (val := ⟨1⟩)
      (by decide) hnz1
  have rd3987 := evm_run rd2229 with [
    jumpdest, push2 ⟨2237⟩, push2 ⟨3987⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd2237⟩ := auctionInitializeOwnable_nested (σ := s2) (g := g)
    (ret := ⟨2237⟩)
    (R := [⟨1⟩, auctionInitializeDurationWord I,
      auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
      auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
      auctionInitializeNounsWord I].append (ret :: R))
    hperm hnz2 (by jump_dest) rd3987
  let s3 := auctionSetOwnerPostMap s2 I (auctionSourceWord I)
  have hpaused0 : auctionPausedWord s3 I = ⟨0⟩ := by
    dsimp [s3, s2, s1]
    exact (auctionInitializePrePausePausedZero (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))
  have rd3655 := evm_run rd2237 with [
    jumpdest, push2 ⟨2245⟩, push2 ⟨3655⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd2245⟩ := auctionPauseRoutine_success (σ := s3) (g := g)
    (ret := ⟨2245⟩)
    (R := [⟨1⟩, auctionInitializeDurationWord I,
      auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
      auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
      auctionInitializeNounsWord I].append (ret :: R))
    hperm hpaused0 (by jump_dest) rd3655
  let s4 := auctionPausePostMap s3 I
  obtain ⟨_, _, rdret⟩ := auctionInitializeArgsStores_top (σ := s4) (g := g)
    (ret := ret) (R := R) hperm hret rd2245
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
    (ret := ⟨413⟩) (R := [auctionSelWord I]) hperm hnz (by jump_dest) rd2213
  have rd414 := evm_run rd413 with [jumpdest]
  exact rd414.stop (by decide) (by evm_ov)

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
  have hnzTop := auctionInitializeSetTopFlagsMap_initializing_ne (σ := σ) (I := I)
  obtain ⟨_, _, rd413⟩ := auctionInitializeCore_top (cA := cA) (gh := gh)
    (bl := bl) (σInit := σ) (σ := auctionInitializeSetTopFlagsMap σ I) (σ₀ := σ₀)
    (A := A) (g := g) (ret := ⟨413⟩) (R := [auctionSelWord I]) hperm hnzTop
    (by jump_dest) (by simpa [auctionInitializeSetTopFlagsMap] using rd2213)
  have rd414 := evm_run rd413 with [jumpdest]
  exact by
    simpa [auctionInitializeTopPostMap] using rd414.stop (by decide) (by evm_ov)

end Auction
