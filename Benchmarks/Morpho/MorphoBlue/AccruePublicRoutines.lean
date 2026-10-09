import Benchmarks.Morpho.MorphoBlue.AccrueHeap
import Benchmarks.Morpho.MorphoBlue.CreateMarketMemory
import Benchmarks.Morpho.MorphoBlue.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def marketCreatedErrorMem (mem : ByteArray) : ByteArray :=
  morphoErrorMem (UInt256.ofNat 18)
    (UInt256.ofNat 49474274355341680327970171712989548750577954063360504421786356785527335682048) mem

theorem morphoMarketCreatedMessage {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {dest fp : UInt256} {R : List UInt256} {spare : Nat}
    (hstack : R.length + 9 ≤ 1024) (hm : MorphoHeap mem fp spare) (hb : 64 ≤ spare)
    (hvalid : (D_J (deployedRuntime v) 0).contains dest = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12310) (dest :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 dest (fp :: R)
      (marketCreatedErrorMem mem) aw' rdata σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_12310 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoAlloc64 (v := v) (by simp only [List.length_cons]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (hm.alloc64Guard hb) rd1
  obtain ⟨aw3, k3, C3, rd3⟩ := morphoBlocks.morpho_block_12323_packed
    (immWords := wordsOf (immStore v)) (by omega) hvalid rd2
  change RD _ _ _ _ _ (memLoad (UInt256.ofNat 64) mem :: R)
    (marketCreatedErrorMem mem) aw3 rdata σ k3 C3 at rd3
  exact ⟨aw3, k3, C3, by simpa only [hm.free] using rd3⟩

def accruePublicMem (p : MarketParamsWords) : ByteArray :=
  marketCreatedErrorMem (twoWordHashMem p.id (UInt256.ofNat 3) (createMarketDecodedMem p))

theorem accruePublicMemory (p : MarketParamsWords) :
    CreateMarketHeap p 352 (accruePublicMem p) ∧
      morphoErrorLength (accruePublicMem p) (UInt256.ofNat 288) = UInt256.ofNat 18 :=
  ((createMarketDecodedHeap p).hash (by decide) p.id (UInt256.ofNat 3)).message (by decide) (by decide) _ _

theorem createMarketHeap_morpho {p free mem} (h : CreateMarketHeap p free mem)
    (hlo : 288 ≤ free) (spare : Nat) (hfit : free + spare ≤ 2 ^ 64 - 1) (hgap : spare < USize.size) :
    MorphoHeap mem (UInt256.ofNat free) spare := by
  have hf : free < UInt256.size := by change _ < 2 ^ 256; omega
  refine ⟨by rw [h.size]; omega, h.freePtr, ?_, ?_, ?_⟩
  · rw [UInt256.toNat_ofNat_of_lt hf]; omega
  · rw [UInt256.toNat_ofNat_of_lt hf, h.size]; omega
  · rw [UInt256.toNat_ofNat_of_lt hf]; exact hfit

theorem morphoAccruePublicReachDecode {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 1)) (hcv : I.weiValue = ⟨0⟩)
    (hlen : 164 ≤ I.calldata.size) (hbound : I.calldata.size < 2 ^ 255 + 4) :
    ∃ aw k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 11655)
      [UInt256.ofNat 11100, UInt256.ofNat 128, UInt256.ofNat 1211, UInt256.ofNat 0]
      (marketParamsAllocatedMem solcFreePtrMem) aw ByteArray.empty σ k C := by
  obtain ⟨k, C, rd⟩ := morphoReachAccrueInterestBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode (by omega) hsize hsel
  change RD _ _ _ _ _ _ solcFreePtrMem _ _ _ _ _ at rd
  have rd0 := morphoBlocks.morpho_block_11040_fallthrough (immWords := wordsOf (immStore v)) (by simp [morphoBlocks.morpho_block_11040_fallthrough_stack]) hcv rd
  have hcond := solcCalldataStaticLenCheckOk (words := 5) hlen hbound hsize
  have rd1 := morphoBlocks.morpho_block_11047_fallthrough (immWords := wordsOf (immStore v)) (by simp [morphoBlocks.morpho_block_11040_fallthrough_stack])
    (by simpa only [wordAddNegFour] using hcond) rd0
  have rd2 := morphoBlocks.morpho_block_11089 (immWords := wordsOf (immStore v)) (by simp [morphoBlocks.morpho_block_11040_fallthrough_stack])
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  have hfp : memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 := solcFreePtrMem_mload64
  obtain ⟨aw, k', C', rd3⟩ := morphoDecodeMarketParamsPrefix (v := v) (by simp [morphoBlocks.morpho_block_11040_fallthrough_stack])
    hsize hlen hbound (by rw [hfp]; decide) rd2
  refine ⟨aw, k', C', ?_⟩
  simpa only [hfp] using rd3

theorem morphoAccruePublicReachGuard {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    (p : MarketParamsWords)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11100)
      [UInt256.ofNat 128, UInt256.ofNat 1211, UInt256.ofNat 0] (createMarketDecodedMem p) aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      [UInt256.isZero (UInt256.isZero (marketFieldWord σ ee p.id 4)), UInt256.ofNat 288,
       UInt256.ofNat 9879, UInt256.ofNat 128, p.id, UInt256.ofNat 1211, UInt256.ofNat 0]
      (accruePublicMem p) aw' rdata σ k' C' := by
  have hid : keccakWord (UInt256.ofNat 128) (UInt256.ofNat 160) (createMarketDecodedMem p) = p.id :=
    marketParamsMem_hash p _ _ (by decide) (by native_decide) (by native_decide)
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_11100_packed (immWords := wordsOf (immStore v))
    (by simp) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [morphoBlocks.morpho_block_11100_stack, morphoBlocks.morpho_block_11100_memory, hid] at rd1
  let mem := twoWordHashMem p.id (UInt256.ofNat 3) (createMarketDecodedMem p)
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem = solcMappingSlot ⟨3⟩ p.id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  change RD _ _ _ _ _
    [UInt256.ofNat 585, UInt256.isZero (UInt256.isZero
      (UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem + UInt256.ofNat 2) σ ee) uint128Mask)),
      UInt256.ofNat 9879, UInt256.ofNat 128, p.id, UInt256.ofNat 1211, UInt256.ofNat 0] mem _ _ _ _ _ at rd1
  rw [hh] at rd1
  have hm := createMarketHeap_morpho ((createMarketDecodedHeap p).hash (by decide) p.id (UInt256.ofNat 3))
    (by decide) 512 (by decide) (lt_usize _ (by decide))
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoMarketCreatedMessage (v := v) (by simp) hm (by decide)
    (by rw [morphoPatchedValidJumps v]; jump_dest) rd1
  have rd3 := morphoBlocks.morpho_block_585 (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact ⟨aw2, _, _, rd3⟩

theorem morphoAccruePublicEnter {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    (p : MarketParamsWords) (hcreated : marketFieldWord σ ee p.id 4 ≠ ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11100)
      [UInt256.ofNat 128, UInt256.ofNat 1211, UInt256.ofNat 0] (createMarketDecodedMem p) aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13166)
      [UInt256.ofNat 128, p.id, UInt256.ofNat 1211, UInt256.ofNat 0]
      (accruePublicMem p) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccruePublicReachGuard (v := v) p h
  obtain ⟨k2, C2, rd2⟩ := morphoRequireTrue (v := v) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [isZero_eq_zero_of_ne hcreated]; decide) rd1
  have rd3 := morphoBlocks.morpho_block_9879 (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact ⟨aw1, _, _, rd3⟩

theorem morphoAccruePublicGuardReverts {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    (p : MarketParamsWords) (hcreated : marketFieldWord σ ee p.id 4 = ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11100)
      [UInt256.ofNat 128, UInt256.ofNat 1211, UInt256.ofNat 0] (createMarketDecodedMem p) aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccruePublicReachGuard (v := v) p h
  exact morphoRequireFalseShort (v := v) (by simp) (by rw [hcreated]; rfl)
    (by rw [(accruePublicMemory p).2]; decide) (by rw [(accruePublicMemory p).2]; decide) rd1

end Benchmarks.Morpho.MorphoBlue
