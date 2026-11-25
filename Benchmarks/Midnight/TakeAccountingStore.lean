import Benchmarks.Midnight.TakeSettlementRead
import Benchmarks.Midnight.TakeConsumptionMemory
import Benchmarks.Midnight.RuntimeBlocks_048

variable {fork : Ethereum.Fork}

/-! The ordered fee and consumed-counter writes preserve the offer heap. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeAccountingStore {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw fee feeSlot value marketPtr arrayPtr callbackPtr root : UInt256}
    {offer : OfferData} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hperm : I.perm = true)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (hvalue : memLoad (UInt256.ofNat 480) mem = value)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨12638⟩ (fee :: feeSlot :: R) mem aw rdata σ k C) :
    ∃ aw' k' C',
      MemoryFunding credit (consumedHashMemory mem offer.group (UInt256.ofNat offer.maker.val))
        aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨12719⟩ (offer.buy :: R)
        (consumedHashMemory mem offer.group (UInt256.ofNat offer.maker.val)) aw' rdata
        (storeLow128Accounts (sstoreAccountMap I.codeOwner σ feeSlot fee) I
          (consumedSlot offer.group (UInt256.ofNat offer.maker.val)) value) k' C' := by
  have hmem : 512 ≤ mem.size := by
    have h := ho.words.size
    change 832 + 32 * 15 ≤ mem.size at h
    omega
  have hmaker : memLoad ((⟨832⟩ : UInt256) + UInt256.ofNat 64) mem =
      UInt256.ofNat offer.maker.val :=
    ho.words.load_offset ⟨2, by change 2 < 15; decide⟩ rfl
  let first := twoWordHashMem (UInt256.ofNat offer.maker.val) (UInt256.ofNat 2) mem
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
  have hv : memLoad (UInt256.ofNat 480)
      (consumedHashMemory mem offer.group (UInt256.ofNat offer.maker.val)) = value :=
    (consumedHashMemory_load offer.group (UInt256.ofNat offer.maker.val)
      (UInt256.ofNat 480) (by decide) hmem).trans hvalue
  have ho2 := ho.preserve
    (consumedHashMemory_prefix mem offer.group (UInt256.ofNat offer.maker.val) root.toNat)
  have hbuy : memLoad (UInt256.ofNat 32 + (⟨832⟩ : UInt256))
      (consumedHashMemory mem offer.group (UInt256.ofNat offer.maker.val)) = offer.buy := by
    rw [u256_add_comm]
    exact ho2.words.load_offset ⟨1, by change 1 < 15; decide⟩ rfl
  dsimp only [first] at hgroup hh1
  dsimp only [consumedHashMemory] at hh2 hv hbuy
  let r0 := rd
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc3, r3⟩ := sstoreMono r2 hperm (by native_decide) (by evm_ov)
  have ha3 := memoryFundingAt (credit := credit) r3 (ha.mono (by omega))
  have r4 := r3.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r14 := r13.shl (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.and (by native_decide) (by evm_ov)
  have r17 := r16.push0 (by native_decide) (by evm_ov)
  have r18 := r17.swap1 (by native_decide) (by evm_ov)
  have r19 := r18.dup2 (by native_decide) (by evm_ov)
  have r20 := RD.genMstore r19 (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r23 := r22.swap1 (by native_decide) (by evm_ov)
  have r24 := r23.dup2 (by native_decide) (by evm_ov)
  have r25 := RD.genMstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.dup3 (by native_decide) (by evm_ov)
  have r27 := r26.dup3 (by native_decide) (by evm_ov)
  have r28 := RD.genKeccak256 r27 (by native_decide) (by evm_ov)
  have ha28 := memoryFundingAt (credit := credit) r28 (by memory_fund ha3)
  simp only [hoffer, hmaker, addressMask_computed, u256_land_comm solcAddrMask,
    solcAddrMask_clean (addressWord_canonical offer.maker),
    show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold] at r28 ha28
  rw [hh1] at r28
  have r29 := r28.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r30 := r29.dup6 (by native_decide) (by evm_ov)
  have r31 := r30.add (by native_decide) (by evm_ov)
  have r32 := RD.genMload r31 (by native_decide) (by evm_ov)
  have r33 := r32.dup4 (by native_decide) (by evm_ov)
  have r34 := RD.genMstore r33 (by native_decide) (by evm_ov)
  have r35 := r34.dup2 (by native_decide) (by evm_ov)
  have r36 := RD.genMstore r35 (by native_decide) (by evm_ov)
  have r37 := r36.swap2 (by native_decide) (by evm_ov)
  have r38 := r37.swap1 (by native_decide) (by evm_ov)
  have r39 := RD.genKeccak256 r38 (by native_decide) (by evm_ov)
  have ha39 := memoryFundingAt (credit := credit) r39 (by memory_fund ha28)
  simp only [hgroup,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold] at r39 ha39
  rw [hh2] at r39
  have r40 := r39.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r41 := RD.genMload r40 (by native_decide) (by evm_ov)
  have ha41 := memoryFundingAt (credit := credit) r41 (by memory_fund ha39)
  rw [hv] at r41
  have r42 := r41.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc43, r43⟩ := RD.sloadMono r42 (by native_decide) (by evm_ov)
  have ha43 := ha41.mono ((Nat.le_add_right _ 3).trans hc43)
  have r44 := r43.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r45 := r44.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r46 := r45.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r47 := r46.shl (by native_decide) (by evm_ov)
  have r48 := r47.sub (by native_decide) (by evm_ov)
  have r49 := r48.not (by native_decide) (by evm_ov)
  have r50 := r49.and (by native_decide) (by evm_ov)
  have r51 := r50.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r52 := r51.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r53 := r52.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r54 := r53.shl (by native_decide) (by evm_ov)
  have r55 := r54.sub (by native_decide) (by evm_ov)
  have r56 := r55.swap2 (by native_decide) (by evm_ov)
  have r57 := r56.swap1 (by native_decide) (by evm_ov)
  have r58 := r57.swap2 (by native_decide) (by evm_ov)
  have r59 := r58.and (by native_decide) (by evm_ov)
  have r60 := r59.or (by native_decide) (by evm_ov)
  have r61 := r60.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc62, r62⟩ := sstoreMono r61 hperm (by native_decide) (by evm_ov)
  have ha62 := memoryFundingAt (credit := credit) r62 (ha43.mono (by omega))
  simp only [uint128Mask_computed, u256_land_comm uint128Mask,
    u256_land_comm (UInt256.lnot uint128Mask),
    u256_lor_comm (UInt256.land value uint128Mask)] at r62
  have r63 := r62.add (by native_decide) (by evm_ov)
  have r64 := RD.genMload r63 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12719)) r64 (by native_decide)
  have haf := memoryFundingAt (credit := credit) rFinal (by memory_fund ha62)
  rw [hbuy] at rFinal
  exact ⟨_, _, _, haf, rFinal⟩

end Benchmarks.Midnight
