import Benchmarks.Midnight.TakePositionsMemory

variable {fork : Ethereum.Fork}

/-! Read the seller's credit after the possible buyer update. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeSellerCreditRead {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw id seller : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hm : 544 ≤ mem.size)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (hs : memLoad (UInt256.ofNat 448) mem = seller)
    (hcanon : seller.toNat < EVM.addressModulus) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨11966⟩ R mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (positionReadMemory mem id seller) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨12021⟩ (takeHasCreditWord σ I id seller :: R)
        (positionReadMemory mem id seller) aw' rdata σ k' C' := by
  have hh1 : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem id ⟨0⟩ mem) =
      solcMappingSlot ⟨0⟩ id := twoWordHashMem_mapSlot_of_ge64 _ _ (by omega)
  have hh2 : keccakWord ⟨0⟩ (UInt256.ofNat 64) (positionReadMemory mem id seller) =
      positionSlot id seller := twoWordHashMem_mapSlot_of_ge64 _ _
        (by rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; omega)
  dsimp only [positionReadMemory] at hh2
  -- Retain the gas spent by the storage read hidden inside the generated summary.
  let r0 := rd
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 12021) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 512) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push0 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r15 := r14.shl (by native_decide) (by evm_ov)
  have r16 := r15.sub (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r18 := r17.push0 (by native_decide) (by evm_ov)
  have r19 := RD.genKeccak256 r18 (by native_decide) (by evm_ov)
  have ha19 := memoryFundingAt (credit := credit) r19 (by memory_fund ha)
  simp only [hid, hs, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold] at r19 ha19
  rw [hh1] at r19
  have r20 := r19.swap2 (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.push0 (by native_decide) (by evm_ov)
  have r23 := RD.genMstore r22 (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r25 := RD.genMstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r29 := r28.shl (by native_decide) (by evm_ov)
  have r30 := r29.sub (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r32 := r31.push0 (by native_decide) (by evm_ov)
  have r33 := RD.genKeccak256 r32 (by native_decide) (by evm_ov)
  have ha33 := memoryFundingAt (credit := credit) r33 (by memory_fund ha19)
  simp only [addressMask_computed, solcAddrMask_clean hcanon,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold] at r33 ha33
  rw [hh2] at r33
  obtain ⟨_, _, hC34, r34⟩ := RD.sloadMono r33 (by native_decide) (by evm_ov)
  have ha34 := ha33.mono hC34
  have r35 := r34.and (by native_decide) (by evm_ov)
  have r36 := r35.iszero (by native_decide) (by evm_ov)
  have r37 := r36.iszero (by native_decide) (by evm_ov)
  have r38 := r37.swap1 (by native_decide) (by evm_ov)
  have r39 := r38.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12021)) r39 (by native_decide)
  have haf := memoryFundingAt (credit := credit) rFinal (by memory_fund ha34)
  simp only [uint128Mask_computed] at rFinal
  exact ⟨_, _, _, haf, rFinal⟩

end Benchmarks.Midnight
