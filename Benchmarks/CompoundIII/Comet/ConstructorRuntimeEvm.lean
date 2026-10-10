import Benchmarks.CompoundIII.Comet.ConstructorRuntimeStart

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometConstructorRuntimeReturn {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw ptr assetList discard : UInt256}
    {σ : AccountMap} {k C : Nat} {w : Nat → UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hm : 928 ≤ mem.size) (hlo : 928 ≤ ptr.toNat)
    (hin : ptr.toNat ≤ mem.size) (hfit : ptr.toNat + 18599 < UInt256.size)
    (hptr : memLoad (UInt256.ofNat 64) mem = ptr)
    (hr : ∀ off, 96 ≤ off → off + 32 ≤ 928 →
      memLoad (UInt256.ofNat off) (writeWord mem 896 assetList) = w off)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1410⟩
      (discard :: assetList :: R) mem aw rdata σ k C) :
    RDret (cometWithExtendedAssetListCreationBytecode ++ tail) g s0 σ
      (immutableLayout.runtime cometWithExtendedAssetListBytecode (constructorRuntimeWords w)) := by
  let copied := constructorRuntimeCopy (writeWord mem 896 assetList) tail ptr
  have hcopy := constructorRuntimeCopy_prefix (tail := tail) (ptr := ptr)
    (mem := writeWord mem 896 assetList) (by rw [writeWord_sparse_size]; omega)
  have hcm : 928 ≤ copied.size := by
    have hh := hcopy.size
    rw [writeWord_sparse_size] at hh
    exact le_trans (by omega) hh
  have hpm (n : Nat) : 928 ≤ (constructorRuntimePatchedMemory copied ptr w n).size :=
    le_trans hcm (constructorRuntimePatchedMemory_prefix _ _ _ _).size
  have hread (n off : Nat) (h1 : 96 ≤ off) (h2 : off + 32 ≤ 928) :
      memLoad (UInt256.ofNat off) (constructorRuntimePatchedMemory copied ptr w n) = w off := by
    have hn : (UInt256.ofNat off).toNat = off := UInt256.toNat_ofNat_of_lt (by omega)
    rw [constructorRuntimePatchedMemory_low (by rw [hn]; exact h1)
      (by rw [hn]; omega) (by rw [hn]; omega)]
    rw [memoryPrefix_load hcopy (by rw [hn]; exact h1) (by rw [hn]; omega)
      (by rw [hn, writeWord_sparse_size]; omega)]
    exact hr off h1 h2
  obtain ⟨aw1, k1, C1, r1⟩ := cometWithExtendedAssetListCreation_block_1410_packed hstack h
  have he1 := constructorRuntimeStart_eq (tail := tail) hm hlo hin hfit hptr hr R
  rw [he1.1, he1.2] at r1
  change RD _ _ _ _ _
    ((UInt256.ofNat 6266 + ptr) :: w 192 :: ptr :: w 192 :: ptr :: R)
    (constructorRuntimePatchedMemory copied ptr w 9) _ _ _ _ _ at r1
  obtain ⟨aw2, k2, C2, r2⟩ := cometWithExtendedAssetListCreation_block_1505_packed hstack r1
  have he2 := constructorRuntimePart1505_eq (hpm 9) hlo hfit (hread 9) R
  rw [he2.1, he2.2, constructorRuntimePart_compose] at r2
  obtain ⟨aw3, k3, C3, r3⟩ := cometWithExtendedAssetListCreation_block_1598_packed hstack r2
  have he3 := constructorRuntimePart1598_eq (hpm 22) hlo hfit (hread 22) R
  rw [he3.1, he3.2, constructorRuntimePart_compose] at r3
  obtain ⟨aw4, k4, C4, r4⟩ := cometWithExtendedAssetListCreation_block_1696_packed hstack r3
  have he4 := constructorRuntimePart1696_eq (hpm 34) hlo hfit (hread 34) R
  rw [he4.1, he4.2, constructorRuntimePart_compose] at r4
  obtain ⟨aw5, k5, C5, r5⟩ := cometWithExtendedAssetListCreation_block_1792_packed hstack r4
  have he5 := constructorRuntimePart1792_eq (hpm 45) hlo hfit (hread 45) R
  rw [he5.1, he5.2, constructorRuntimePart_compose] at r5
  obtain ⟨aw6, k6, C6, r6⟩ := cometWithExtendedAssetListCreation_block_1890_packed hstack r5
  have he6 := constructorRuntimePart1890_eq (hpm 57) hlo hfit (hread 57) R
  rw [he6.1, he6.2, constructorRuntimePart_compose] at r6
  have r7 := cometWithExtendedAssetListCreation_block_1988 (by omega) r6
  have hlast : writeWord (constructorRuntimePatchedMemory copied ptr w 69)
      (ptr.toNat + 7222) (w 896) = constructorRuntimePatchedMemory copied ptr w 70 :=
    constructorRuntimePart_compose copied ptr w 69 1
  have hadd : (UInt256.ofNat 7222 + ptr).toNat = ptr.toNat + 7222 := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat _ _ (by omega)
  change RDret _ _ _ _ ((writeWord (constructorRuntimePatchedMemory copied ptr w 69)
    (UInt256.ofNat 7222 + ptr).toNat (w 896)).readWithPadding ptr.toNat 18599) at r7
  rw [hadd, hlast, constructorRuntimePatchedMemory_return (by
    rw [writeWord_sparse_size]; omega)] at r7
  exact r7

end Benchmarks.CompoundIII.Comet
