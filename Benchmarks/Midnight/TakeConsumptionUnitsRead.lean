import Benchmarks.Midnight.TakeConsumptionMemory
import Benchmarks.Midnight.RuntimeBlocks_054

variable {fork : Ethereum.Fork}

/-! The unit-cap path reads the low 128 bits of the consumed mapping with funding retained. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeConsumedUnitsRead {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw marketPtr arrayPtr callbackPtr root : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {offer : OfferData}
    (hstack : R.length + 5 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨14604⟩ R mem aw rdata σ k C) :
    ∃ aw' k' C',
      MemoryFunding credit (consumedHashMemory mem offer.group (UInt256.ofNat offer.maker.val))
        aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨19536⟩
        (takeConsumedWord σ I offer :: calldataWord I.calldata 68 :: UInt256.ofNat 14672 :: R)
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
  -- Retain the SLOAD cost hidden by the generated block summary.
  let r0 := rd
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r12 := r11.shl (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.and (by native_decide) (by evm_ov)
  have r15 := r14.push0 (by native_decide) (by evm_ov)
  have r16 := r15.swap1 (by native_decide) (by evm_ov)
  have r17 := r16.dup2 (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r21 := RD.genMstore r20 (by native_decide) (by evm_ov)
  have r22 := RD.genKeccak256 r21 (by native_decide) (by evm_ov)
  have ha22 := memoryFundingAt (credit := credit) r22 (by memory_fund ha)
  simp only [hroot, hmaker, addressMask_computed, u256_land_comm solcAddrMask,
    solcAddrMask_clean (addressWord_canonical offer.maker),
    show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold] at r22 ha22
  rw [hh1] at r22
  have r23 := r22.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r25 := RD.genMload r24 (by native_decide) (by evm_ov)
  have r26 := r25.add (by native_decide) (by evm_ov)
  have r27 := RD.genMload r26 (by native_decide) (by evm_ov)
  have r28 := r27.push0 (by native_decide) (by evm_ov)
  have r29 := RD.genMstore r28 (by native_decide) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r31 := RD.genMstore r30 (by native_decide) (by evm_ov)
  have r32 := r31.push2 (UInt256.ofNat 14672) (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r36 := r35.shl (by native_decide) (by evm_ov)
  have r37 := r36.sub (by native_decide) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r39 := r38.push0 (by native_decide) (by evm_ov)
  have r40 := RD.genKeccak256 r39 (by native_decide) (by evm_ov)
  have ha40 := memoryFundingAt (credit := credit) r40 (by memory_fund ha22)
  simp only [hroot1, hgroup,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold] at r40 ha40
  rw [hh2] at r40
  obtain ⟨_, _, hC41, r41⟩ := RD.sloadMono r40 (by native_decide) (by evm_ov)
  have ha41 := ha40.mono hC41
  have r42 := r41.and (by native_decide) (by evm_ov)
  have r43 := r42.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r44 := r43.calldataload (by native_decide) (by evm_ov)
  have r45 := r44.swap1 (by native_decide) (by evm_ov)
  have r46 := r45.push2 (UInt256.ofNat 19536) (by native_decide) (by evm_ov)
  have r47 := r46.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19536)) r47 (by native_decide)
  have haf := memoryFundingAt (credit := credit) rFinal (by memory_fund ha41)
  simp only [uint128Mask_computed] at rFinal
  exact ⟨_, _, _, haf, rFinal⟩

end Benchmarks.Midnight
