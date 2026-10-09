import Benchmarks.Morpho.MorphoBlue.SetFeeMemory
import Benchmarks.Morpho.MorphoBlue.SetFeeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

section Guards
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}

theorem morphoSetFeeReachOwner (p : MarketParamsWords)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 9639)
      [UInt256.ofNat 128, UInt256.ofNat 0] (createMarketDecodedMem p) aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      [UInt256.eq (solcSourceWord ee) (solcAddressSlotWord ⟨0⟩ σ ee), UInt256.ofNat 288,
        UInt256.ofNat 9714, calldataWord ee.calldata 164, UInt256.ofNat 32, setFeeTopic,
        UInt256.ofNat 128, UInt256.ofNat 0] (setFeeOwnerMem p) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_9639_packed
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoNotOwnerMessage (v := v)
    (by simp [morphoBlocks.morpho_block_9639_stack])
    (by rw [morphoPatchedValidJumps v]; jump_dest)
    (by rw [(createMarketDecodedHeap p).freePtr]; decide) rd1
  have rd3 := morphoBlocks.morpho_block_585 (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  change RD _ _ _ _ _
    [UInt256.eq (solcSourceWord ee) (solcAddressSlotWord ⟨0⟩ σ ee),
      memLoad (UInt256.ofNat 64) (createMarketDecodedMem p), UInt256.ofNat 9714,
      calldataWord ee.calldata 164, UInt256.ofNat 32, setFeeTopic, UInt256.ofNat 128, UInt256.ofNat 0]
    (setFeeOwnerMem p) aw2 rdata σ _ _ at rd3
  rw [(createMarketDecodedHeap p).freePtr] at rd3
  exact ⟨aw2, _, _, rd3⟩

theorem morphoSetFeeReachCreated (p : MarketParamsWords) (fee : UInt256)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 9714)
      [fee, UInt256.ofNat 32, setFeeTopic, UInt256.ofNat 128, UInt256.ofNat 0]
      (setFeeOwnerMem p) aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      ([UInt256.isZero (UInt256.isZero (marketFieldWord σ ee p.id 4)), UInt256.ofNat 352,
        UInt256.ofNat 9774] ++ setFeeAccrueStack p.id fee) (setFeeCreatedMem p) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_9714_packed
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [morphoBlocks.morpho_block_9714_stack, morphoBlocks.morpho_block_9714_memory,
    setFeeOwnerMem_hash] at rd1
  let mem := twoWordHashMem p.id (UInt256.ofNat 3) (setFeeOwnerMem p)
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem = solcMappingSlot ⟨3⟩ p.id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  change RD _ _ _ _ _
    ([UInt256.ofNat 585, UInt256.isZero (UInt256.isZero (UInt256.land
      (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem + UInt256.ofNat 2) σ ee)
      uint128Mask)), UInt256.ofNat 9774] ++ setFeeAccrueStack p.id fee) mem _ _ _ _ _ at rd1
  rw [hh] at rd1
  have hm := createMarketHeap_morpho ((setFeeOwnerHeap p).1.hash (by decide) p.id (UInt256.ofNat 3))
    (by decide) 512 (by decide) (lt_usize _ (by decide))
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoMarketCreatedMessage (v := v)
    (by simp [setFeeAccrueStack, setFeeAccrueTail]) hm (by decide)
    (by rw [morphoPatchedValidJumps v]; jump_dest) rd1
  have rd3 := morphoBlocks.morpho_block_585 (immWords := wordsOf (immStore v))
    (by simp [setFeeAccrueStack, setFeeAccrueTail])
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact ⟨aw2, _, _, rd3⟩

theorem morphoSetFeeReachChanged (p : MarketParamsWords) (fee : UInt256)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 9774)
      (setFeeAccrueStack p.id fee) (setFeeCreatedMem p) aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      ([UInt256.isZero (UInt256.eq fee (marketFieldWord σ ee p.id 5)), UInt256.ofNat 416,
        UInt256.ofNat 9806] ++ setFeeAccrueStack p.id fee) (setFeeChangedMem p) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_9774_packed
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  let mem := twoWordHashMem p.id (UInt256.ofNat 3) (setFeeCreatedMem p)
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem = solcMappingSlot ⟨3⟩ p.id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  have hm := (setFeeCreatedHeap p).1.hash (by decide) p.id (UInt256.ofNat 3)
  change RD _ _ _ _ _
    ([UInt256.ofNat 585, UInt256.isZero (UInt256.eq fee (UInt256.shiftRight
      (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem + UInt256.ofNat 2) σ ee)
      (UInt256.ofNat 128))), UInt256.ofNat 9806] ++ setFeeAccrueStack p.id fee) mem _ _ _ _ _ at rd1
  rw [hh] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoAlreadySetMessage (v := v)
    (by simp [setFeeAccrueStack, setFeeAccrueTail])
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [hm.freePtr]; decide) rd1
  change RD _ _ _ _ _
    ([memLoad (UInt256.ofNat 64) mem, UInt256.isZero (UInt256.eq fee (marketFieldWord σ ee p.id 5)),
      UInt256.ofNat 9806] ++ setFeeAccrueStack p.id fee) (setFeeChangedMem p) _ _ _ _ _ at rd2
  rw [hm.freePtr] at rd2
  have rd3 := morphoBlocks.morpho_block_585 (immWords := wordsOf (immStore v))
    (by simp [setFeeAccrueStack, setFeeAccrueTail])
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact ⟨aw2, _, _, rd3⟩

theorem morphoSetFeeReachLimit (p : MarketParamsWords) (fee : UInt256)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 9806)
      (setFeeAccrueStack p.id fee) (setFeeChangedMem p) aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      ([UInt256.isZero (UInt256.gt fee (UInt256.ofNat maxMarketFee)), UInt256.ofNat 480,
        UInt256.ofNat 9879] ++ setFeeAccrueStack p.id fee) (setFeeLimitMem p) aw' rdata σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_9806 (immWords := wordsOf (immStore v))
    (by simp [setFeeAccrueStack, setFeeAccrueTail])
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [morphoBlocks.morpho_block_9806_stack, (setFeeChangedHeap p).1.freePtr] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoAlloc64 (v := v)
    (by simp [setFeeAccrueStack, setFeeAccrueTail])
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by decide) rd1
  obtain ⟨aw3, k3, C3, rd3⟩ := morphoBlocks.morpho_block_9821_packed (immWords := wordsOf (immStore v))
    (by simp [setFeeAccrueStack, setFeeAccrueTail])
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  refine ⟨aw3, k3, C3, ?_⟩
  have hm : setFeeLimitMem p = morphoBlocks.morpho_block_9821_memory
      (mem := (UInt256.ofNat 480 + UInt256.ofNat 64).toByteArray.write 0 (setFeeChangedMem p) 64 32)
      (x0 := UInt256.ofNat 480) (x8 := UInt256.ofNat 32) := by
    rw [setFeeLimitMem, morphoErrorMem, (setFeeChangedHeap p).1.freePtr]
    rfl
  rw [hm]
  exact rd3


theorem morphoSetFeeEnter (p : MarketParamsWords)
    (hg : SetFeeGuards σ ee p (calldataWord ee.calldata 164))
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 9639)
      [UInt256.ofNat 128, UInt256.ofNat 0] (createMarketDecodedMem p) aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13166)
      (setFeeAccrueStack p.id (calldataWord ee.calldata 164)) (setFeeLimitMem p) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoSetFeeReachOwner (v := v) p h
  obtain ⟨k2, C2, rd2⟩ := morphoRequireTrue (v := v) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [hg.1, uInt256_eq_self]; decide) rd1
  obtain ⟨aw3, k3, C3, rd3⟩ := morphoSetFeeReachCreated (v := v) p _ rd2
  obtain ⟨k4, C4, rd4⟩ := morphoRequireTrue (v := v)
    (by simp [setFeeAccrueStack, setFeeAccrueTail])
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [isZero_eq_zero_of_ne hg.2.1]; decide) rd3
  obtain ⟨aw5, k5, C5, rd5⟩ := morphoSetFeeReachChanged (v := v) p _ rd4
  obtain ⟨k6, C6, rd6⟩ := morphoRequireTrue (v := v)
    (by simp [setFeeAccrueStack, setFeeAccrueTail])
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [u256_eq_of_ne hg.2.2.1]; decide) rd5
  obtain ⟨aw7, k7, C7, rd7⟩ := morphoSetFeeReachLimit (v := v) p _ rd6
  have hle : UInt256.gt (calldataWord ee.calldata 164) (UInt256.ofNat maxMarketFee) = ⟨0⟩ :=
    ugt_zero hg.2.2.2
  obtain ⟨k8, C8, rd8⟩ := morphoRequireTrue (v := v)
    (by simp [setFeeAccrueStack, setFeeAccrueTail])
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [hle]; decide) rd7
  exact ⟨aw7, _, _, morphoBlocks.morpho_block_9879 (immWords := wordsOf (immStore v))
    (by simp [setFeeAccrueStack, setFeeAccrueTail])
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd8⟩

theorem morphoSetFeeGuardReverts (p : MarketParamsWords)
    (hbad : ¬ SetFeeGuards σ ee p (calldataWord ee.calldata 164))
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 9639)
      [UInt256.ofNat 128, UInt256.ofNat 0] (createMarketDecodedMem p) aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoSetFeeReachOwner (v := v) p h
  by_cases ho : solcSourceWord ee = solcAddressSlotWord ⟨0⟩ σ ee
  · obtain ⟨k2, C2, rd2⟩ := morphoRequireTrue (v := v) (by simp)
      (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [ho, uInt256_eq_self]; decide) rd1
    obtain ⟨aw3, k3, C3, rd3⟩ := morphoSetFeeReachCreated (v := v) p _ rd2
    by_cases hc : marketFieldWord σ ee p.id 4 ≠ ⟨0⟩
    · obtain ⟨k4, C4, rd4⟩ := morphoRequireTrue (v := v)
        (by simp [setFeeAccrueStack, setFeeAccrueTail])
        (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [isZero_eq_zero_of_ne hc]; decide) rd3
      obtain ⟨aw5, k5, C5, rd5⟩ := morphoSetFeeReachChanged (v := v) p _ rd4
      by_cases hn : calldataWord ee.calldata 164 ≠ marketFieldWord σ ee p.id 5
      · obtain ⟨k6, C6, rd6⟩ := morphoRequireTrue (v := v)
          (by simp [setFeeAccrueStack, setFeeAccrueTail])
          (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [u256_eq_of_ne hn]; decide) rd5
        obtain ⟨aw7, k7, C7, rd7⟩ := morphoSetFeeReachLimit (v := v) p _ rd6
        have hgt : UInt256.gt (calldataWord ee.calldata 164) (UInt256.ofNat maxMarketFee) = ⟨1⟩ := by
          apply ugt_one
          change maxMarketFee < (calldataWord ee.calldata 164).toNat
          have hfail : ¬ (calldataWord ee.calldata 164).toNat ≤ maxMarketFee := fun hf => hbad ⟨ho, hc, hn, hf⟩
          omega
        exact morphoRequireFalseShort (v := v) (by simp [setFeeAccrueStack, setFeeAccrueTail])
          (by rw [hgt]; rfl) (by rw [(setFeeLimitHeap p).2]; decide) (by rw [(setFeeLimitHeap p).2]; decide) rd7
      · exact morphoRequireFalseShort (v := v) (by simp [setFeeAccrueStack, setFeeAccrueTail])
          (by rw [not_not.mp hn, uInt256_eq_self]; rfl)
          (by rw [(setFeeChangedHeap p).2]; decide) (by rw [(setFeeChangedHeap p).2]; decide) rd5
    · exact morphoRequireFalseShort (v := v) (by simp [setFeeAccrueStack, setFeeAccrueTail])
        (by rw [not_not.mp hc]; rfl)
        (by rw [(setFeeCreatedHeap p).2]; decide) (by rw [(setFeeCreatedHeap p).2]; decide) rd3
  · exact morphoRequireFalseShort (v := v) (by simp) (u256_eq_of_ne ho)
      (by rw [(setFeeOwnerHeap p).2]; decide) (by rw [(setFeeOwnerHeap p).2]; decide) rd1

end Guards
end Benchmarks.Morpho.MorphoBlue
