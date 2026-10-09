import Benchmarks.Morpho.MorphoBlue.CreateMarketStore
import Benchmarks.Morpho.MorphoBlue.CreateMarketCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoCreateMarketNoIrmReturns {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    (p : MarketParamsWords) (hc : p.Canonical) (hperm : ee.perm = true) (hi0 : p.irm = ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5234)
      (createMarketLogStack p) (createMarketEventMem p) aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ ByteArray.empty := by
  have hi := (createMarketEventMemory p).2.2 ⟨3, by decide⟩
  change memLoad (UInt256.ofNat 224) (createMarketEventMem p) = p.irm at hi
  have rd1 := morphoBlocks.morpho_block_5234_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) hperm
    (by rw [hi, solcAddrMask_clean hc.2.2.2, hi0]; rfl) h
  have ret := morphoBlocks.morpho_block_5244 (immWords := wordsOf (immStore v)) (by simp) rd1
  simpa only [show (UInt256.ofNat 0).toNat = 0 from rfl, byteArray_readWithPadding_zero] using ret

theorem morphoCreateMarketReachCall {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    (p : MarketParamsWords) (hc : p.Canonical) (hperm : ee.perm = true) (hi0 : p.irm ≠ ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5234)
      (createMarketLogStack p) (createMarketEventMem p) aw rdata σ k C) :
    ∃ mem aw' gasArg k' C',
      mem.readWithPadding 480 356 = borrowRateCalldata p σ ee p.id ∧
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5322)
        [gasArg, p.irm, UInt256.ofNat 0, UInt256.ofNat 480, UInt256.ofNat 356,
         UInt256.ofNat 480, UInt256.ofNat 32, UInt256.ofNat 480, UInt256.ofNat 32, UInt256.ofNat 0]
        mem aw' rdata σ k' C' := by
  obtain ⟨hsize, hfree, hparams⟩ := createMarketEventMemory p
  have hi := hparams ⟨3, by decide⟩
  change memLoad (UInt256.ofNat 224) (createMarketEventMem p) = p.irm at hi
  have rd1 := morphoBlocks.morpho_block_5234_taken
    (immWords := wordsOf (immStore v)) (by simp) hperm
    (by rw [hi, solcAddrMask_clean hc.2.2.2]; exact hi0)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [morphoBlocks.morpho_block_5234_taken_stack, hi, solcAddrMask_clean hc.2.2.2] at rd1
  let hm := twoWordHashMem p.id (UInt256.ofNat 3) (createMarketEventMem p)
  have hms : hm.size = 640 := by rw [twoWordHashMem_size_of_ge_64' _ _ (by rw [hsize]; decide), hsize]
  have hmf : memLoad (UInt256.ofNat 64) hm = UInt256.ofNat 480 := by
    rw [twoWordHashMem_memLoad_above64 _ _ _ (by decide) (by rw [hsize]; decide), hfree]
  have hmh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) hm = solcMappingSlot ⟨3⟩ p.id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  have hmr : p.InMemory (UInt256.ofNat 128) hm :=
    hparams.twoWordHashMem _ _ (by decide) (by rw [hsize]; decide) (by decide)
  let callMem := writeWord hm (UInt256.ofNat 480).toNat borrowRateSelectorWord
  have hcs : callMem.size = 640 := by
    rw [writeWord_size _ _ _ (by rw [hms]; exact lt_usize _ (by decide)), hms]; rfl
  have hcr : p.InMemory (UInt256.ofNat 128) callMem := hmr.writeWord _ _ (by decide)
    (by rw [hms]; decide) (by rw [hms]; exact lt_usize _ (by decide)) (by left; decide)
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_5247_packed
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  change RD _ _ _ _ _
    [memLoad (UInt256.ofNat 64) hm + UInt256.ofNat 4, UInt256.ofNat 128,
     keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) hm, UInt256.ofNat 5318,
     memLoad (UInt256.ofNat 64) hm, UInt256.ofNat 0, memLoad (UInt256.ofNat 64) hm, p.irm,
     memLoad (UInt256.ofNat 64) hm, UInt256.ofNat 32, memLoad (UInt256.ofNat 64) hm,
     UInt256.ofNat 32, UInt256.ofNat 0]
    (borrowRateSelectorWord.toByteArray.write 0 hm (memLoad (UInt256.ofNat 64) hm).toNat 32)
    _ _ _ _ _ at rd2
  rw [hmf, hmh] at rd2
  obtain ⟨aw3, k3, C3, rd3⟩ := morphoBorrowRateArguments (v := v) p hc hcr
    (by decide) (by decide) (by rw [hcs]; decide) (by decide)
    (by rw [hcs]; exact lt_usize _ (by decide)) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest) rd2
  obtain ⟨aw4, k4, C4, rd4⟩ := morphoBlocks.morpho_block_5318_packed
    (immWords := wordsOf (immStore v)) (by simp) rd3
  refine ⟨_, aw4, _, k4, C4, ?_, rd4⟩
  exact borrowRateCalldata_read p σ ee p.id hm 480
    (by rw [hms]; exact lt_usize _ (by decide))

end Benchmarks.Morpho.MorphoBlue
