import Benchmarks.Midnight.TakeConsumptionMemory
import Benchmarks.Midnight.RuntimeBlocks_045

/-! The asset-cap path reads consumed and selects the buyer or seller asset amount. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeConsumedAssetPC (buy : UInt256) : UInt256 :=
  if buy = ⟨0⟩ then ⟨14594⟩ else ⟨11785⟩

theorem midnightTakeConsumedAssetsRead {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw marketPtr arrayPtr callbackPtr root : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {offer : OfferData}
    (hstack : R.length + 5 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩) (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨11710⟩ R mem aw rdata σ k C) :
    ∃ aw' k' C',
      MemoryFunding credit (consumedHashMemory mem offer.group (UInt256.ofNat offer.maker.val))
        aw' C' ∧
      RD midnightBytecode I g s0 (takeConsumedAssetPC offer.buy)
        (takeConsumedWord σ I offer :: UInt256.ofNat 11794 :: R)
        (consumedHashMemory mem offer.group (UInt256.ofNat offer.maker.val)) aw' rdata σ k' C' := by
  have hmem : 416 ≤ mem.size := by
    have hh := ho.words.size
    change 832 + 32 * 15 ≤ mem.size at hh
    omega
  have hmaker : memLoad (UInt256.ofNat 64 + (⟨832⟩ : UInt256)) mem =
      UInt256.ofNat offer.maker.val := by
    rw [u256_add_comm]
    exact ho.words.load_offset ⟨2, by change 2 < 15; decide⟩ rfl
  let first := twoWordHashMem (UInt256.ofNat offer.maker.val) (UInt256.ofNat 2) mem
  have hroot1 : memLoad (UInt256.ofNat 384) first = ⟨832⟩ := by
    dsimp only [first]
    rw [memLoad_twoWordHashMem _ _ (UInt256.ofNat 384) (by decide) hmem, hroot]
  have ho1 := ho.preserve (twoWordHashMem_prefix mem (UInt256.ofNat offer.maker.val)
    (UInt256.ofNat 2) root.toNat)
  have hgroup : memLoad ((⟨832⟩ : UInt256) + UInt256.ofNat 192) first = offer.group :=
    ho1.words.load_offset ⟨6, by change 6 < 15; decide⟩ rfl
  have hh1 : keccakWord ⟨0⟩ (UInt256.ofNat 64) first =
      solcMappingSlot (UInt256.ofNat 2) (UInt256.ofNat offer.maker.val) :=
    twoWordHashMem_mapSlot_of_ge64 _ _ (by omega)
  have hh2 : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (consumedHashMemory mem offer.group (UInt256.ofNat offer.maker.val)) =
      consumedSlot offer.group (UInt256.ofNat offer.maker.val) :=
    twoWordHashMem_mapSlot_of_ge64 _ _
      (by rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; omega)
  dsimp only [first] at hroot1 hgroup hh1
  dsimp only [consumedHashMemory] at hh2
  have hroot2 : memLoad (UInt256.ofNat 384)
      (consumedHashMemory mem offer.group (UInt256.ofNat offer.maker.val)) = ⟨832⟩ := by
    rw [consumedHashMemory_load _ _ (UInt256.ofNat 384) (by decide) hmem, hroot]
  have ho2 := ho.preserve (consumedHashMemory_prefix mem offer.group
    (UInt256.ofNat offer.maker.val) root.toNat)
  have hbuy : memLoad ((⟨832⟩ : UInt256) + UInt256.ofNat 32)
      (consumedHashMemory mem offer.group (UInt256.ofNat offer.maker.val)) = offer.buy :=
    ho2.words.load_offset ⟨1, by change 1 < 15; decide⟩ rfl
  dsimp only [consumedHashMemory] at hroot2 hbuy
  -- Retain the SLOAD cost hidden by the generated block summary.
  let r0 := rd
  have r1 := r0.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.sub (by native_decide) (by evm_ov)
  have r13 := r12.and (by native_decide) (by evm_ov)
  have r14 := r13.push0 (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.dup2 (by native_decide) (by evm_ov)
  have r17 := RD.genMstore r16 (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r20 := RD.genMstore r19 (by native_decide) (by evm_ov)
  have r21 := RD.genKeccak256 r20 (by native_decide) (by evm_ov)
  have ha21 := memoryFundingAt (credit := credit) r21 (by memory_fund ha)
  simp only [hroot, hmaker, addressMask_computed, u256_land_comm solcAddrMask,
    solcAddrMask_clean (addressWord_canonical offer.maker),
    show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold] at r21 ha21
  rw [hh1] at r21
  have r22 := r21.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r24 := RD.genMload r23 (by native_decide) (by evm_ov)
  have r25 := r24.add (by native_decide) (by evm_ov)
  have r26 := RD.genMload r25 (by native_decide) (by evm_ov)
  have r27 := r26.push0 (by native_decide) (by evm_ov)
  have r28 := RD.genMstore r27 (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r30 := RD.genMstore r29 (by native_decide) (by evm_ov)
  have r31 := r30.push2 (UInt256.ofNat 11794) (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r35 := r34.shl (by native_decide) (by evm_ov)
  have r36 := r35.sub (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r38 := r37.push0 (by native_decide) (by evm_ov)
  have r39 := RD.genKeccak256 r38 (by native_decide) (by evm_ov)
  have ha39 := memoryFundingAt (credit := credit) r39 (by memory_fund ha21)
  simp only [hroot1, hgroup,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold] at r39 ha39
  rw [hh2] at r39
  obtain ⟨_, _, hC40, r40⟩ := RD.sloadMono r39 (by native_decide) (by evm_ov)
  have ha40 := ha39.mono hC40
  have r41 := r40.and (by native_decide) (by evm_ov)
  have r42 := r41.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r43 := r42.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r44 := RD.genMload r43 (by native_decide) (by evm_ov)
  have r45 := r44.add (by native_decide) (by evm_ov)
  have r46 := RD.genMload r45 (by native_decide) (by evm_ov)
  have r47 := r46.iszero (by native_decide) (by evm_ov)
  have r48 := r47.iszero (by native_decide) (by evm_ov)
  have r49 := r48.push0 (by native_decide) (by evm_ov)
  have r50 := r49.eq (by native_decide) (by evm_ov)
  have r51 := r50.push2 (UInt256.ofNat 14594) (by native_decide) (by evm_ov)
  simp only [hroot2, hbuy, uint128Mask_computed] at r51
  by_cases hz : offer.buy = ⟨0⟩
  · have r52 := r51.jumpiT (by native_decide) (by rw [hz]; decide)
      (by jump_dest) (by evm_ov)
    have rf := RD.normalizePC (pc' := UInt256.ofNat 14594) r52 (by native_decide)
    simp only [takeConsumedAssetPC, if_pos hz]
    exact ⟨_, _, _, by unfold consumedHashMemory; memory_fund ha40, rf⟩
  · have r52 := r51.jumpiNT (by native_decide) (by
      rw [isZero_eq_zero_of_ne hz]; decide) (by evm_ov)
    have rf := RD.normalizePC (pc' := UInt256.ofNat 11785) r52 (by native_decide)
    simp only [takeConsumedAssetPC, if_neg hz]
    exact ⟨_, _, _, by unfold consumedHashMemory; memory_fund ha40, rf⟩

end Benchmarks.Midnight
