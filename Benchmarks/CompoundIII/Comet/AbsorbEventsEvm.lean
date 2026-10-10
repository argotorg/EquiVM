import Benchmarks.CompoundIII.Comet.AbsorbEventsMemory
import Benchmarks.CompoundIII.Comet.PackedPresentValueEvm
import Benchmarks.CompoundIII.Comet.SignedDebtWords
import Benchmarks.CompoundIII.Comet.Signed104Encoding

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAbsorbEvents {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw paid value principal account absorber ret free : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 13 ≤ 1024)
    (hp : principal.toNat < 2^103) (hperm : ee.perm = true)
    (hf : memLoad ⟨64⟩ mem = free) (hl : 96 ≤ free.toNat) (hm : free.toNat ≤ mem.size)
    (hb : free.toNat + 64 < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨17410⟩
      (value :: account :: paid :: principal :: absorber :: ret :: R) mem aw rdata σ k C) :
    ∃ mem' aw' k' C', RD (deployedRuntime v) ee g s0 ret R mem' aw' rdata σ k' C' ∧
      memLoad ⟨64⟩ mem' = free ∧ mem.size ≤ mem'.size := by
  let mem1 := pairEventMem mem free paid value
  have he1 : cometWithExtendedAssetList_block_17410_taken_memory
      (mem := mem) (x0 := value) (x2 := paid) = mem1 := absorbDebtEventMemory hf (by omega)
  have hf1 := absorbDebtEventMemory_free (paid := paid) (value := value) hf hl hm
  have hcond : UInt256.slt (UInt256.ofNat 0)
      (UInt256.signextend (UInt256.ofNat 12) principal) =
      UInt256.fromBool (decide (0 < principal.toNat)) := by
    rw [signedWord_slt, signedWord_signextend104, signed104_low hp]
    change UInt256.fromBool (decide (0 < (principal.toNat : Int))) = _
    simp only [Int.natCast_pos]
  by_cases hpos : 0 < principal.toNat
  · have r1 := cometWithExtendedAssetList_block_17410_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega) hperm
      (by rw [hcond, decide_eq_true hpos]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    rw [he1] at r1
    obtain ⟨k2, C2, r2⟩ := cometWithExtendedAssetList_block_17493
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 9 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    let mem2 := cometWithExtendedAssetList_block_17493_memory
      (immWords := wordsOf (immStore v)) (mem := mem1)
    have hf2 := absorbTransferCopyMemory_free v mem1 (by
      have hsz := hf1.2
      change 96 ≤ (pairEventMem mem free paid value).size; omega)
    have hf2' : memLoad ⟨64⟩ mem2 = free := hf2.1.trans hf1.1
    have hm2 : mem.size ≤ mem2.size := by rw [hf2.2]; exact hf1.2
    have r3 := cometWithExtendedAssetList_block_2959 (immWords := wordsOf (immStore v))
      (by change R.length + 8 + 5 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    have r4 := cometWithExtendedAssetList_block_17530 (immWords := wordsOf (immStore v))
      (by change R.length + 6 + 4 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
    obtain ⟨k5, C5, r5⟩ := cometUnsigned104 (v := v)
      (by change R.length + 7 + 5 ≤ 1024; omega) hp
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4
    have r6 := cometWithExtendedAssetList_block_17536 (immWords := wordsOf (immStore v))
      (by change R.length + 6 + 3 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
    obtain ⟨k7, C7, r7⟩ := cometPresentValue (v := v)
      (by change R.length + 5 + 8 ≤ 1024; omega)
      (by rw [u256_land_comm]; exact u256LandMaskToNatLtOfToNat _ _ (bits := 64) (by decide))
      (lt_trans hp (by decide))
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r6
    have r8 := cometWithExtendedAssetList_block_12721 (immWords := wordsOf (immStore v))
      (by change R.length + 4 + 5 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r7
    have r9 := cometWithExtendedAssetList_block_12737 (immWords := wordsOf (immStore v))
      (by omega) hperm hret r8
    refine ⟨_, _, _, _, r9, ?_, ?_⟩
    · change memLoad ⟨64⟩ (writeWord mem2 (memLoad ⟨64⟩ mem2).toNat _) = free
      rw [hf2', memLoad_writeWord_preserved _ _ _ _
        (by change 64 + 32 ≤ mem2.size; omega) (Or.inl (by change 64 + 32 ≤ free.toNat; omega))]
      exact hf2'
    · change mem.size ≤ (writeWord mem2 (memLoad ⟨64⟩ mem2).toNat _).size
      rw [writeWord_sparse_size]; omega
  · have r1 := cometWithExtendedAssetList_block_17410_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega) hperm
      (by rw [hcond, decide_eq_false hpos]; rfl) h
    have he0 : cometWithExtendedAssetList_block_17410_fallthrough_memory
        (mem := mem) (x0 := value) (x2 := paid) = mem1 := he1
    rw [he0] at r1
    have r2 := cometWithExtendedAssetList_block_17490 (immWords := wordsOf (immStore v))
      (by omega) hret r1
    exact ⟨_, _, _, _, r2, hf1⟩

end Benchmarks.CompoundIII.Comet
