import Benchmarks.CompoundIII.Comet.ConstructorFactoryCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def constructorFactoryReturnMemory (mem out : ByteArray) (ptr : UInt256) : ByteArray :=
  writeWord (callOutputMem mem out ptr ⟨32⟩) 64 (ptr + UInt256.ofNat 32)

theorem constructorFactoryReturnMemory_word {mem out : ByteArray} {ptr : UInt256}
    (hmem : ptr.toNat + 32 ≤ mem.size) (hptr : 96 ≤ ptr.toNat)
    (hhi : out.size < UInt256.size) (hlo : 32 ≤ out.size) :
    memLoad ptr (constructorFactoryReturnMemory mem out ptr) = calldataWord out 0 := by
  unfold constructorFactoryReturnMemory
  rw [memLoad_writeWord_preserved _ _ _ _ (by
    rw [callOutput32_size _ _ _ hhi hmem]
    exact hmem) (Or.inr hptr)]
  apply loadedWord_of_read
  · rw [callOutput32_size _ _ _ hhi hmem]; exact hmem
  · exact callOutput32_read_word _ _ _ hhi hlo (by omega)

theorem cometConstructorFactoryResponse {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {σ : AccountMap} {mem out : ByteArray} {z : Bool}
    {aw ptr base : UInt256} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (hmem : ptr.toNat + 32 ≤ mem.size)
    (hptr : 96 ≤ ptr.toNat) (hfit : ptr.toNat + 32 < 2^64) (hhi : out.size < 2^138)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1292⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: base :: ptr :: R)
      (callOutputMem mem out ptr ⟨32⟩) aw out σ k C) :
    if z = true ∧ ConstructorFactoryReturnValid out then
      ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1308⟩
        (UInt256.ofNat 640 :: base :: calldataWord out 0 :: R)
        (constructorFactoryReturnMemory mem out ptr) aw' out σ k' C'
    else RDrev (cometWithExtendedAssetListCreationBytecode ++ tail) g s0 := by
  have hsize : out.size < UInt256.size := by change _ < 2^256; omega
  have hout : (UInt256.ofNat out.size).toNat = out.size := UInt256.toNat_ofNat_of_lt hsize
  have hsub (n : Nat) : UInt256.sub (ptr + UInt256.ofNat n) ptr = UInt256.ofNat n :=
    word_add_sub_left _ _
  cases z with
  | false =>
    rw [if_neg (by simp)]
    have r1 := cometWithExtendedAssetListCreation_block_1292_taken
      (by omega) (by decide) (by native_decide) h
    exact cometWithExtendedAssetListCreation_block_2063 (by
      change R.length + 3 + 4 ≤ 1024; omega)
      (by rw [hout]; change 0 + out.size ≤ out.size; omega) r1
  | true =>
    have r1 := cometWithExtendedAssetListCreation_block_1292_fallthrough (by omega) (by decide) h
    have r2 := cometWithExtendedAssetListCreation_block_1300_taken
      (by omega) (by decide) (by native_decide) r1
    by_cases hlo : 32 ≤ out.size
    · have r3 := cometWithExtendedAssetListCreation_block_2211_fallthrough
        (by omega) (by apply ugt_zero; rw [hout]; exact hlo) r2
      have r4 := cometWithExtendedAssetListCreation_block_2226
        (by change R.length + 3 + 7 ≤ 1024; omega) (by native_decide) r3
      obtain ⟨_, _, _, r5⟩ := cometCreationAllocateSmall
        (by change R.length + 6 + 6 ≤ 1024; omega) (by decide) hfit (by native_decide) r4
      have r6 := cometWithExtendedAssetListCreation_block_2241_fallthrough (by
        change R.length + 3 + 4 ≤ 1024; omega) (by
        rw [hsub 32]
        exact slt_ofNat_lit_zero (by decide) (by decide) (by decide)) r5
      have r7 := cometWithExtendedAssetListCreation_block_2251
        (by change R.length + 1 + 4 ≤ 1024; omega) (by native_decide) r6
      have hread := constructorFactoryReturnMemory_word hmem hptr hsize hlo
      change RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨2747⟩
        (ptr :: ⟨2265⟩ :: ⟨640⟩ :: base :: R)
        (constructorFactoryReturnMemory mem out ptr) _ out σ _ _ at r7
      by_cases hcanon : (calldataWord out 0).toNat < 2^160
      · rw [if_pos ⟨rfl, hlo, hcanon⟩]
        obtain ⟨_, _, _, r8⟩ := cometCreationReadAddress
          (by change R.length + 2 + 5 ≤ 1024; omega) hread hcanon (by native_decide) r7
        have r9 := cometWithExtendedAssetListCreation_block_2265
          (by omega) (by native_decide) r8
        exact ⟨_, _, _, r9⟩
      · rw [if_neg (fun hh ↦ hcanon hh.2.2)]
        have r8 := cometWithExtendedAssetListCreation_block_2747_taken
          (by change R.length + 3 + 4 ≤ 1024; omega) (by
            rw [hread]
            apply u256_sub_ne_zero_of_ne
            intro he
            apply hcanon
            rw [he]
            exact u256LandMaskToNatLtOfToNat _ _ (by native_decide)) (by native_decide) r7
        exact cometWithExtendedAssetListCreation_block_2684 (by
          change R.length + 4 + 2 ≤ 1024; omega) r8
    · rw [if_neg (fun hh ↦ hlo hh.2.1)]
      have r3 := cometWithExtendedAssetListCreation_block_2211_taken (by omega) (by
        rw [ugt_one (by rw [hout]; change out.size < 32; omega)]; decide) (by native_decide) r2
      have r4 := cometWithExtendedAssetListCreation_block_2276
        (by change R.length + 3 + 3 ≤ 1024; omega) (by native_decide) r3
      have r5 := cometWithExtendedAssetListCreation_block_2226
        (by change R.length + 3 + 7 ≤ 1024; omega) (by native_decide) r4
      obtain ⟨_, _, _, r6⟩ := cometCreationAllocateSmall
        (by change R.length + 6 + 6 ≤ 1024; omega) (by rw [hout]; omega) hfit (by native_decide) r5
      have r7 := cometWithExtendedAssetListCreation_block_2241_taken (by
        change R.length + 3 + 4 ≤ 1024; omega) (by
        rw [hsub out.size, slt_ofNat_lit_one_low (by decide) (by omega)]; decide)
        (by native_decide) r6
      exact cometWithExtendedAssetListCreation_block_2273 (by
        change R.length + 2 + 2 ≤ 1024; omega) r7

end Benchmarks.CompoundIII.Comet
