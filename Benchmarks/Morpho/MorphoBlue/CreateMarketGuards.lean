import Benchmarks.Morpho.MorphoBlue.CreateMarketMemory
import Benchmarks.Morpho.MorphoBlue.CreateMarketSource
import Benchmarks.Morpho.MorphoBlue.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def createMarketIrmMem (p : MarketParamsWords) : ByteArray :=
  morphoErrorMem (UInt256.ofNat 15)
    (UInt256.ofNat 33164251714707471531685028710914369538198252872362372732198613325951038128128)
    (twoWordHashMem p.irm (UInt256.ofNat 4) (createMarketDecodedMem p))

def createMarketLltvMem (p : MarketParamsWords) : ByteArray :=
  morphoErrorMem (UInt256.ofNat 16)
    (UInt256.ofNat 34510638937915370315515363731873320992723177039537578968211748559238524305408)
    (twoWordHashMem p.lltv (UInt256.ofNat 5) (createMarketIrmMem p))

def createMarketUnusedMem (p : MarketParamsWords) : ByteArray :=
  morphoErrorMem (UInt256.ofNat 22)
    (UInt256.ofNat 49474274355341680246294123618020960933857875614369968334246212219823082962944)
    (twoWordHashMem p.id (UInt256.ofNat 3) (createMarketLltvMem p))

theorem createMarketIrmHeap (p : MarketParamsWords) :
    CreateMarketHeap p 352 (createMarketIrmMem p) ∧
      morphoErrorLength (createMarketIrmMem p) (UInt256.ofNat 288) = UInt256.ofNat 15 := by
  exact ((createMarketDecodedHeap p).hash (by decide) p.irm (UInt256.ofNat 4)).message
    (by decide) (by decide) _ _

theorem createMarketLltvHeap (p : MarketParamsWords) :
    CreateMarketHeap p 416 (createMarketLltvMem p) ∧
      morphoErrorLength (createMarketLltvMem p) (UInt256.ofNat 352) = UInt256.ofNat 16 := by
  exact ((createMarketIrmHeap p).1.hash (by decide) p.lltv (UInt256.ofNat 5)).message
    (by decide) (by decide) _ _

theorem createMarketUnusedHeap (p : MarketParamsWords) :
    CreateMarketHeap p 480 (createMarketUnusedMem p) ∧
      morphoErrorLength (createMarketUnusedMem p) (UInt256.ofNat 416) = UInt256.ofNat 22 := by
  exact ((createMarketLltvHeap p).1.hash (by decide) p.id (UInt256.ofNat 3)).message
    (by decide) (by decide) _ _

theorem morphoCreateMarketReachDecode {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 16)) (hcv : I.weiValue = ⟨0⟩)
    (hlen : 164 ≤ I.calldata.size) (hbound : I.calldata.size < 2 ^ 255 + 4) :
    ∃ aw k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 11655)
      [UInt256.ofNat 4657, UInt256.ofNat 128, UInt256.ofNat 0]
      (marketParamsAllocatedMem solcFreePtrMem) aw ByteArray.empty σ k C := by
  obtain ⟨k, C, rd⟩ := morphoReachCreateMarketBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode (by omega) hsize hsel
  change RD _ _ _ _ _ _ solcFreePtrMem _ _ _ _ _ at rd
  have rd0 := morphoBlocks.morpho_block_4600_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) hcv rd
  have hcond := solcCalldataStaticLenCheckOk (words := 5) hlen hbound hsize
  have rd1 := morphoBlocks.morpho_block_4607_fallthrough
    (immWords := wordsOf (immStore v)) (by simp [morphoBlocks.morpho_block_4600_fallthrough_stack])
    (by simpa only [wordAddNegFour] using hcond) rd0
  have rd2 := morphoBlocks.morpho_block_4649 (immWords := wordsOf (immStore v))
    (by simp [morphoBlocks.morpho_block_4600_fallthrough_stack])
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  have hfp : memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 := solcFreePtrMem_mload64
  obtain ⟨aw, k', C', rd3⟩ := morphoDecodeMarketParamsPrefix (v := v)
    (by simp [morphoBlocks.morpho_block_4600_fallthrough_stack])
    hsize hlen hbound (by rw [hfp]; decide) rd2
  refine ⟨aw, k', C', ?_⟩
  simpa only [hfp, morphoBlocks.morpho_block_4600_fallthrough_stack] using rd3

theorem morphoCreateMarketReachIrm {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    (p : MarketParamsWords) (hc : p.Canonical)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 4657)
      [UInt256.ofNat 128, UInt256.ofNat 0] (createMarketDecodedMem p) aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      [createMarketIrmByte σ ee p, UInt256.ofNat 288, UInt256.ofNat 4771,
       UInt256.ofNat 224, solcAddrMask, p.id, UInt256.ofNat 128, UInt256.ofNat 32, UInt256.ofNat 0]
      (createMarketIrmMem p) aw' rdata σ k' C' := by
  have hp := createMarketDecodedHeap p
  have hi : memLoad (UInt256.ofNat 128 + UInt256.ofNat 96) (createMarketDecodedMem p) = p.irm := by
    simpa only [MarketParamsWords.word] using hp.params ⟨3, by decide⟩
  have hid : keccakWord (UInt256.ofNat 128) (UInt256.ofNat 160) (createMarketDecodedMem p) = p.id :=
    marketParamsMem_hash p _ _ (by decide) (by native_decide) (by native_decide)
  let hm := twoWordHashMem p.irm (UInt256.ofNat 4) (createMarketDecodedMem p)
  have hfp : memLoad (UInt256.ofNat 64) hm = UInt256.ofNat 288 :=
    (hp.hash (by decide) p.irm (UInt256.ofNat 4)).freePtr
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) hm = solcMappingSlot ⟨4⟩ p.irm :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_4657_packed
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [morphoBlocks.morpho_block_4657_stack, morphoBlocks.morpho_block_4657_memory,
    hi, show UInt256.ofNat 1461501637330902918203684832716283019655932542975 = solcAddrMask from rfl,
    solcAddrMask_clean hc.2.2.2, hid] at rd1
  change RD _ _ _ _ _
    [memLoad (UInt256.ofNat 64) hm, UInt256.ofNat 4725,
     UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) hm) σ ee) ⟨255⟩,
     memLoad (UInt256.ofNat 64) hm, UInt256.ofNat 4771,
     UInt256.ofNat 224, solcAddrMask, p.id, UInt256.ofNat 128, UInt256.ofNat 32, UInt256.ofNat 0]
    hm _ _ _ _ _ at rd1
  rw [hfp, hh] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoAlloc64 (v := v) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by decide) rd1
  obtain ⟨aw3, k3, C3, rd3⟩ := morphoBlocks.morpho_block_4725_packed
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  refine ⟨aw3, k3, C3, ?_⟩
  have hmEq : createMarketIrmMem p = morphoBlocks.morpho_block_4725_memory
      (mem := (UInt256.ofNat 288 + UInt256.ofNat 64).toByteArray.write 0 hm 64 32)
      (x1 := UInt256.ofNat 288) (x7 := UInt256.ofNat 32) := by
    change morphoErrorMem _ _ hm = _
    rw [morphoErrorMem, hfp]
    rfl
  rw [hmEq]
  exact rd3

theorem morphoCreateMarketReachLltv {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    (p : MarketParamsWords)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 4771)
      [UInt256.ofNat 224, solcAddrMask, p.id, UInt256.ofNat 128, UInt256.ofNat 32, UInt256.ofNat 0]
      (createMarketIrmMem p) aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      [createMarketLltvByte σ ee p, UInt256.ofNat 352, UInt256.ofNat 4853,
       UInt256.ofNat 256, UInt256.ofNat 224, solcAddrMask, p.id,
       UInt256.ofNat 128, UInt256.ofNat 32, UInt256.ofNat 0]
      (createMarketLltvMem p) aw' rdata σ k' C' := by
  have hp := (createMarketIrmHeap p).1
  have hl : memLoad (UInt256.ofNat 128 + UInt256.ofNat 128) (createMarketIrmMem p) = p.lltv := by
    simpa only [MarketParamsWords.word] using hp.params ⟨4, by decide⟩
  let hm := twoWordHashMem p.lltv (UInt256.ofNat 5) (createMarketIrmMem p)
  have hfp : memLoad (UInt256.ofNat 64) hm = UInt256.ofNat 352 :=
    (hp.hash (by decide) p.lltv (UInt256.ofNat 5)).freePtr
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) hm = solcMappingSlot ⟨5⟩ p.lltv :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_4771_packed
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [morphoBlocks.morpho_block_4771_stack, morphoBlocks.morpho_block_4771_memory, hl] at rd1
  change RD _ _ _ _ _
    [memLoad (UInt256.ofNat 64) hm, UInt256.ofNat 4807,
     UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) hm) σ ee) ⟨255⟩,
     memLoad (UInt256.ofNat 64) hm, UInt256.ofNat 4853, UInt256.ofNat 256,
     UInt256.ofNat 224, solcAddrMask, p.id, UInt256.ofNat 128, UInt256.ofNat 32, UInt256.ofNat 0]
    hm _ _ _ _ _ at rd1
  rw [hfp, hh] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoAlloc64 (v := v) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by decide) rd1
  obtain ⟨aw3, k3, C3, rd3⟩ := morphoBlocks.morpho_block_4807_packed
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  refine ⟨aw3, k3, C3, ?_⟩
  have hmEq : createMarketLltvMem p = morphoBlocks.morpho_block_4807_memory
      (mem := (UInt256.ofNat 352 + UInt256.ofNat 64).toByteArray.write 0 hm 64 32)
      (x1 := UInt256.ofNat 352) (x8 := UInt256.ofNat 32) := by
    change morphoErrorMem _ _ hm = _
    rw [morphoErrorMem, hfp]
    rfl
  rw [hmEq]
  exact rd3

theorem morphoCreateMarketReachUnused {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    (p : MarketParamsWords)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 4853)
      [UInt256.ofNat 256, UInt256.ofNat 224, solcAddrMask, p.id,
       UInt256.ofNat 128, UInt256.ofNat 32, UInt256.ofNat 0]
      (createMarketLltvMem p) aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      [UInt256.isZero (marketFieldWord σ ee p.id 4), UInt256.ofNat 416, UInt256.ofNat 4950,
       uint128Mask, UInt256.ofNat 256, UInt256.ofNat 224, solcAddrMask, p.id,
       UInt256.ofNat 128, UInt256.ofNat 32, UInt256.ofNat 0]
      (createMarketUnusedMem p) aw' rdata σ k' C' := by
  have hp := (createMarketLltvHeap p).1
  let hm := twoWordHashMem p.id (UInt256.ofNat 3) (createMarketLltvMem p)
  have hfp : memLoad (UInt256.ofNat 64) hm = UInt256.ofNat 416 :=
    (hp.hash (by decide) p.id (UInt256.ofNat 3)).freePtr
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) hm = solcMappingSlot ⟨3⟩ p.id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_4853_packed
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  change RD _ _ _ _ _
    [memLoad (UInt256.ofNat 64) hm, UInt256.ofNat 4904,
     UInt256.isZero (UInt256.land (solcSlotWordAt
       (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) hm + UInt256.ofNat 2) σ ee) uint128Mask),
     memLoad (UInt256.ofNat 64) hm, UInt256.ofNat 4950, uint128Mask,
     UInt256.ofNat 256, UInt256.ofNat 224, solcAddrMask, p.id,
     UInt256.ofNat 128, UInt256.ofNat 32, UInt256.ofNat 0] hm _ _ _ _ _ at rd1
  rw [hfp, hh] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoAlloc64 (v := v) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by decide) rd1
  obtain ⟨aw3, k3, C3, rd3⟩ := morphoBlocks.morpho_block_4904_packed
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  refine ⟨aw3, k3, C3, ?_⟩
  have hmEq : createMarketUnusedMem p = morphoBlocks.morpho_block_4904_memory
      (mem := (UInt256.ofNat 416 + UInt256.ofNat 64).toByteArray.write 0 hm 64 32)
      (x1 := UInt256.ofNat 416) (x9 := UInt256.ofNat 32) := by
    change morphoErrorMem _ _ hm = _
    rw [morphoErrorMem, hfp]
    rfl
  rw [hmEq]
  exact rd3

theorem morphoCreateMarketReachStore {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    (p : MarketParamsWords) (hc : p.Canonical)
    (hirm : createMarketIrmByte σ ee p ≠ ⟨0⟩)
    (hlltv : createMarketLltvByte σ ee p ≠ ⟨0⟩)
    (hnew : marketFieldWord σ ee p.id 4 = ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 4657)
      [UInt256.ofNat 128, UInt256.ofNat 0] (createMarketDecodedMem p) aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 4950)
      [uint128Mask, UInt256.ofNat 256, UInt256.ofNat 224, solcAddrMask, p.id,
       UInt256.ofNat 128, UInt256.ofNat 32, UInt256.ofNat 0]
      (createMarketUnusedMem p) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoCreateMarketReachIrm (v := v) p hc h
  obtain ⟨k2, C2, rd2⟩ := morphoRequireTrue (v := v) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (isZero_eq_zero_of_ne hirm) rd1
  obtain ⟨aw3, k3, C3, rd3⟩ := morphoCreateMarketReachLltv (v := v) p rd2
  obtain ⟨k4, C4, rd4⟩ := morphoRequireTrue (v := v) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (isZero_eq_zero_of_ne hlltv) rd3
  obtain ⟨aw5, k5, C5, rd5⟩ := morphoCreateMarketReachUnused (v := v) p rd4
  obtain ⟨k6, C6, rd6⟩ := morphoRequireTrue (v := v) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [hnew]; decide) rd5
  exact ⟨aw5, k6, C6, rd6⟩

theorem morphoCreateMarketGuardReverts {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    (p : MarketParamsWords) (hc : p.Canonical)
    (hbad : createMarketIrmByte σ ee p = ⟨0⟩ ∨ createMarketLltvByte σ ee p = ⟨0⟩ ∨
      marketFieldWord σ ee p.id 4 ≠ ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 4657)
      [UInt256.ofNat 128, UInt256.ofNat 0] (createMarketDecodedMem p) aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoCreateMarketReachIrm (v := v) p hc h
  by_cases hi : createMarketIrmByte σ ee p = ⟨0⟩
  · exact morphoRequireFalseShort (v := v) (by simp) hi
      (by rw [(createMarketIrmHeap p).2]; decide) (by rw [(createMarketIrmHeap p).2]; decide) rd1
  · obtain ⟨k2, C2, rd2⟩ := morphoRequireTrue (v := v) (by simp)
      (by rw [morphoPatchedValidJumps v]; jump_dest) (isZero_eq_zero_of_ne hi) rd1
    obtain ⟨aw3, k3, C3, rd3⟩ := morphoCreateMarketReachLltv (v := v) p rd2
    by_cases hl : createMarketLltvByte σ ee p = ⟨0⟩
    · exact morphoRequireFalseShort (v := v) (by simp) hl
        (by rw [(createMarketLltvHeap p).2]; decide) (by rw [(createMarketLltvHeap p).2]; decide) rd3
    · obtain ⟨k4, C4, rd4⟩ := morphoRequireTrue (v := v) (by simp)
        (by rw [morphoPatchedValidJumps v]; jump_dest) (isZero_eq_zero_of_ne hl) rd3
      obtain ⟨aw5, k5, C5, rd5⟩ := morphoCreateMarketReachUnused (v := v) p rd4
      exact morphoRequireFalseShort (v := v) (by simp)
        (isZero_eq_zero_of_ne ((hbad.resolve_left hi).resolve_left hl))
        (by rw [(createMarketUnusedHeap p).2]; decide)
        (by rw [(createMarketUnusedHeap p).2]; decide) rd5

end Benchmarks.Morpho.MorphoBlue
