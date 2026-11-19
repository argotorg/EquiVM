import Benchmarks.Midnight.TakePositionsMemory

/-! Compute the two position slots and read the buyer's credit, retaining memory funding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakePositionsRead {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw id buyer seller saved : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024) (hm : 608 ≤ mem.size)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (hb : memLoad (UInt256.ofNat 576) mem = buyer)
    (hs : memLoad (UInt256.ofNat 448) mem = seller)
    (hbc : buyer.toNat < EVM.addressModulus) (hsc : seller.toNat < EVM.addressModulus)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨11880⟩ (saved :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (takePositionsMemory mem id buyer seller) aw' C' ∧
      RD midnightBytecode I g s0 ⟨11960⟩
        ([UInt256.ofNat 14521, UInt256.isZero (takeHasCreditWord σ I id buyer),
          takeHasCreditWord σ I id buyer, positionSlot id seller, saved, positionSlot id buyer] ++ R)
        (takePositionsMemory mem id buyer seller) aw' rdata σ k' C' := by
  have hbuyer1 : memLoad (UInt256.ofNat 576) (twoWordHashMem id ⟨0⟩ mem) = buyer := by
    rw [memLoad_twoWordHashMem _ _ (UInt256.ofNat 576) (by decide) hm, hb]
  have hh1 : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem id ⟨0⟩ mem) =
      solcMappingSlot ⟨0⟩ id := twoWordHashMem_mapSlot_of_ge64 _ _ (by omega)
  have hh2 : keccakWord ⟨0⟩ (UInt256.ofNat 64) (positionReadMemory mem id buyer) =
      positionSlot id buyer := twoWordHashMem_mapSlot_of_ge64 _ _
        (by rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; omega)
  have hs2 : 64 ≤ (positionReadMemory mem id buyer).size := by
    rw [positionReadMemory_size _ _ _ (by omega)]; omega
  have hs32 : (positionReadMemory mem id buyer).readWithPadding 32 32 =
      (solcMappingSlot ⟨0⟩ id).toByteArray := twoWordHashMem_read32_any ..
  have hh3 : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (wordAt0Mem seller (positionReadMemory mem id buyer)) = positionSlot id seller :=
    writeWord_zero_mappingHash seller (solcMappingSlot ⟨0⟩ id) hs2 hs32
  have hseller1 : memLoad (UInt256.ofNat 448) (positionReadMemory mem id buyer) = seller := by
    rw [positionReadMemory, memLoad_twoWordHashMem _ _ (UInt256.ofNat 448) (by decide) (by
      rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; change 480 ≤ mem.size; omega),
      memLoad_twoWordHashMem _ _ (UInt256.ofNat 448) (by decide)
        (by change 480 ≤ mem.size; omega), hs]
  dsimp only [positionReadMemory] at hh2 hh3 hseller1
  -- The generated block hides SLOAD's gas; retain it through the monotone primitive.
  let r0 := rd
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 512) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := r12.dup1 (by native_decide) (by evm_ov)
  have r14 := r13.dup4 (by native_decide) (by evm_ov)
  have r15 := RD.genKeccak256 r14 (by native_decide) (by evm_ov)
  have ha15 := memoryFundingAt (credit := credit) r15 (by memory_fund ha)
  simp only [hid, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold] at r15 ha15
  rw [hh1] at r15
  have r16 := r15.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  have r17 := RD.genMload r16 (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r21 := r20.shl (by native_decide) (by evm_ov)
  have r22 := r21.sub (by native_decide) (by evm_ov)
  have r23 := r22.swap1 (by native_decide) (by evm_ov)
  have r24 := r23.dup2 (by native_decide) (by evm_ov)
  have r25 := r24.and (by native_decide) (by evm_ov)
  have r26 := r25.dup1 (by native_decide) (by evm_ov)
  have r27 := r26.dup7 (by native_decide) (by evm_ov)
  have r28 := RD.genMstore r27 (by native_decide) (by evm_ov)
  have r29 := r28.swap2 (by native_decide) (by evm_ov)
  have r30 := r29.swap1 (by native_decide) (by evm_ov)
  have r31 := r30.swap4 (by native_decide) (by evm_ov)
  have r32 := RD.genMstore r31 (by native_decide) (by evm_ov)
  have r33 := r32.dup2 (by native_decide) (by evm_ov)
  have r34 := r33.dup5 (by native_decide) (by evm_ov)
  have r35 := RD.genKeccak256 r34 (by native_decide) (by evm_ov)
  have ha35 := memoryFundingAt (credit := credit) r35 (by memory_fund ha15)
  simp only [hbuyer1, addressMask_computed, u256_land_comm solcAddrMask,
    solcAddrMask_clean hbc, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold] at r35 ha35
  rw [hh2] at r35
  have r36 := r35.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r37 := RD.genMload r36 (by native_decide) (by evm_ov)
  have r38 := r37.swap1 (by native_decide) (by evm_ov)
  have r39 := r38.swap4 (by native_decide) (by evm_ov)
  have r40 := r39.and (by native_decide) (by evm_ov)
  have r41 := r40.dup5 (by native_decide) (by evm_ov)
  have r42 := RD.genMstore r41 (by native_decide) (by evm_ov)
  have r43 := r42.swap1 (by native_decide) (by evm_ov)
  have r44 := r43.dup4 (by native_decide) (by evm_ov)
  have r45 := RD.genKeccak256 r44 (by native_decide) (by evm_ov)
  have ha45 := memoryFundingAt (credit := credit) r45 (by memory_fund ha35)
  simp only [hseller1, u256_land_comm solcAddrMask, solcAddrMask_clean hsc,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, wordAt0_fold] at r45 ha45
  rw [hh3] at r45
  have r46 := r45.swap3 (by native_decide) (by evm_ov)
  have r47 := RD.genMstore r46 (by native_decide) (by evm_ov)
  have r48 := r47.dup1 (by native_decide) (by evm_ov)
  have ha48 := memoryFundingAt (credit := credit) r48 (by memory_fund ha45)
  obtain ⟨_, _, hC49, r49⟩ := RD.sloadMono r48 (by native_decide) (by evm_ov)
  have ha49 := ha48.mono hC49
  have r50 := r49.swap1 (by native_decide) (by evm_ov)
  have r51 := r50.swap3 (by native_decide) (by evm_ov)
  have r52 := r51.swap2 (by native_decide) (by evm_ov)
  have r53 := r52.swap1 (by native_decide) (by evm_ov)
  have r54 := r53.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r55 := r54.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r56 := r55.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r57 := r56.shl (by native_decide) (by evm_ov)
  have r58 := r57.sub (by native_decide) (by evm_ov)
  have r59 := r58.and (by native_decide) (by evm_ov)
  have r60 := r59.iszero (by native_decide) (by evm_ov)
  have r61 := r60.iszero (by native_decide) (by evm_ov)
  have r62 := r61.dup1 (by native_decide) (by evm_ov)
  have r63 := r62.iszero (by native_decide) (by evm_ov)
  have r64 := r63.push2 (UInt256.ofNat 14521) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11960)) r64 (by native_decide)
  have haf := memoryFundingAt (credit := credit) rFinal (by memory_fund ha49)
  simp only [uint128Mask_computed, u256_land_comm uint128Mask] at rFinal
  exact ⟨_, _, _, haf, rFinal⟩

end Benchmarks.Midnight
