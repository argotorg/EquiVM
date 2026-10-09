import Benchmarks.CompoundIII.Comet.CreateAssetListCall
import Benchmarks.CompoundIII.Comet.ConstructorFactoryResponse

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometCreateAssetListResponse {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {σ : AccountMap} {mem out : ByteArray} {z : Bool}
    {aw ptr base : UInt256} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (hmem : ptr.toNat + 32 ≤ mem.size)
    (hptr : 96 ≤ ptr.toNat) (hfit : ptr.toNat + 32 < 2^64) (hhi : out.size < 2^138)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1394⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: ptr :: base :: R)
      (callOutputMem mem out ptr ⟨32⟩) aw out σ k C) :
    if z = true ∧ ConstructorFactoryReturnValid out then
      ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1410⟩
        (base :: calldataWord out 0 :: base :: R)
        (constructorFactoryReturnMemory mem out ptr) aw' out σ k' C'
    else RDrev (cometWithExtendedAssetListCreationBytecode ++ tail) g s0 := by
  have hsize : out.size < UInt256.size := by change _ < 2^256; omega
  have hout : (UInt256.ofNat out.size).toNat = out.size := UInt256.toNat_ofNat_of_lt hsize
  have hsub (n : Nat) : UInt256.sub (ptr + UInt256.ofNat n) ptr = UInt256.ofNat n :=
    word_add_sub_left _ _
  cases z with
  | false =>
    rw [if_neg (by simp)]
    have r1 := cometWithExtendedAssetListCreation_block_1394_taken
      (by change R.length + 1 + 4 ≤ 1024; omega) (by decide) (by native_decide) h
    exact cometWithExtendedAssetListCreation_block_2063 (by
      change R.length + 3 + 4 ≤ 1024; omega)
      (by rw [hout]; change 0 + out.size ≤ out.size; omega) r1
  | true =>
    have r1 := cometWithExtendedAssetListCreation_block_1394_fallthrough
      (by change R.length + 1 + 4 ≤ 1024; omega) (by decide) h
    have r2 := cometWithExtendedAssetListCreation_block_1402_taken
      (by change R.length + 1 + 4 ≤ 1024; omega) (by decide) (by native_decide) r1
    by_cases hlo : 32 ≤ out.size
    · have r3 := cometWithExtendedAssetListCreation_block_1994_fallthrough
        (by change R.length + 2 + 5 ≤ 1024; omega)
        (by apply ugt_zero; rw [hout]; exact hlo) r2
      have r4 := cometWithExtendedAssetListCreation_block_2007
        (by change R.length + 3 + 7 ≤ 1024; omega) (by native_decide) r3
      obtain ⟨_, _, _, r5⟩ := cometCreationAllocateSmall
        (by change R.length + 6 + 6 ≤ 1024; omega) (by decide) hfit (by native_decide) r4
      have r6 := cometWithExtendedAssetListCreation_block_2022_fallthrough
        (by change R.length + 3 + 4 ≤ 1024; omega) (by
          rw [hsub 32]
          exact slt_ofNat_lit_zero (by decide) (by decide) (by decide)) r5
      have r7 := cometWithExtendedAssetListCreation_block_2032
        (by change R.length + 1 + 3 ≤ 1024; omega) (by native_decide) r6
      have hread := constructorFactoryReturnMemory_word hmem hptr hsize hlo
      change RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨2747⟩
        (ptr :: ⟨2043⟩ :: base :: R)
        (constructorFactoryReturnMemory mem out ptr) _ out σ _ _ at r7
      by_cases hcanon : (calldataWord out 0).toNat < 2^160
      · rw [if_pos ⟨rfl, hlo, hcanon⟩]
        obtain ⟨_, _, _, r8⟩ := cometCreationReadAddress
          (by change R.length + 1 + 5 ≤ 1024; omega) hread hcanon (by native_decide) r7
        have r9 := cometWithExtendedAssetListCreation_block_2043
          (by omega) (by native_decide) r8
        exact ⟨_, _, _, r9⟩
      · rw [if_neg (fun hh ↦ hcanon hh.2.2)]
        have r8 := cometWithExtendedAssetListCreation_block_2747_taken
          (by change R.length + 2 + 4 ≤ 1024; omega) (by
            rw [hread]
            apply u256_sub_ne_zero_of_ne
            intro he
            apply hcanon
            rw [he]
            exact u256LandMaskToNatLtOfToNat _ _ (by native_decide)) (by native_decide) r7
        exact cometWithExtendedAssetListCreation_block_2684
          (by change R.length + 3 + 2 ≤ 1024; omega) r8
    · rw [if_neg (fun hh ↦ hlo hh.2.1)]
      have r3 := cometWithExtendedAssetListCreation_block_1994_taken
        (by change R.length + 2 + 5 ≤ 1024; omega) (by
          rw [ugt_one (by rw [hout]; change out.size < 32; omega)]; decide)
        (by native_decide) r2
      have r4 := cometWithExtendedAssetListCreation_block_2054
        (by change R.length + 3 + 3 ≤ 1024; omega) (by native_decide) r3
      have r5 := cometWithExtendedAssetListCreation_block_2007
        (by change R.length + 3 + 7 ≤ 1024; omega) (by native_decide) r4
      obtain ⟨_, _, _, r6⟩ := cometCreationAllocateSmall
        (by change R.length + 6 + 6 ≤ 1024; omega) (by rw [hout]; omega) hfit
        (by native_decide) r5
      have r7 := cometWithExtendedAssetListCreation_block_2022_taken
        (by change R.length + 3 + 4 ≤ 1024; omega) (by
          rw [hsub out.size, slt_ofNat_lit_one_low (by decide) (by omega)]; decide)
        (by native_decide) r6
      exact cometWithExtendedAssetListCreation_block_2050
        (by change R.length + 1 + 2 ≤ 1024; omega) r7

end Benchmarks.CompoundIII.Comet
