import Benchmarks.CompoundIII.Comet.ConstructorRuntimeParts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem constructorRuntimeStart_eq {mem tail : ByteArray} {ptr assetList : UInt256}
    {w : Nat → UInt256} (hm : 928 ≤ mem.size) (hlo : 928 ≤ ptr.toNat)
    (hin : ptr.toNat ≤ mem.size) (hfit : ptr.toNat + 18599 < UInt256.size)
    (hptr : memLoad (UInt256.ofNat 64) mem = ptr)
    (hr : ∀ off, 96 ≤ off → off + 32 ≤ 928 →
      memLoad (UInt256.ofNat off) (writeWord mem 896 assetList) = w off)
    (R : List UInt256) :
    cometWithExtendedAssetListCreation_block_1410_stack (tail := tail) (mem := mem)
      (x1 := assetList) (R := R) =
        (UInt256.ofNat 6266 + ptr) :: w 192 :: ptr :: w 192 :: ptr :: R ∧
    cometWithExtendedAssetListCreation_block_1410_memory (tail := tail) (mem := mem)
      (x1 := assetList) =
        constructorRuntimePart (constructorRuntimeCopy (writeWord mem 896 assetList) tail ptr)
          ptr w 0 9 := by
  have hfree : memLoad (UInt256.ofNat 64) (writeWord mem 896 assetList) = ptr := by
    rw [memLoad_writeWord_preserved _ _ _ _ (by change 96 ≤ mem.size; omega)
      (Or.inl (by decide)), hptr]
  have hc := constructorRuntimeCopy_prefix (tail := tail) (ptr := ptr)
    (mem := writeWord mem 896 assetList) (by rw [writeWord_sparse_size]; omega)
  have hcm : 928 ≤ (constructorRuntimeCopy (writeWord mem 896 assetList) tail ptr).size := by
    have hh := hc.size
    rw [writeWord_sparse_size] at hh
    omega
  have hread (off : Nat) (h1 : 96 ≤ off) (h2 : off + 32 ≤ 928) :
      memLoad (UInt256.ofNat off)
        (constructorRuntimeCopy (writeWord mem 896 assetList) tail ptr) = w off := by
    have hn : (UInt256.ofNat off).toNat = off :=
      UInt256.toNat_ofNat_of_lt (by omega)
    rw [memoryPrefix_load hc (by rw [hn]; exact h1) (by rw [hn]; omega)
      (by rw [hn, writeWord_sparse_size]; omega)]
    exact hr off h1 h2
  have hwrite (m : ByteArray) (off : Nat) (word : UInt256) :
      word.toByteArray.write 0 m off 32 = writeWord m off word := rfl
  have hcopy : (cometWithExtendedAssetListCreationBytecode ++ tail).write 2826
      (writeWord mem 896 assetList) ptr.toNat 18599 =
      constructorRuntimeCopy (writeWord mem 896 assetList) tail ptr := rfl
  have hadd (off : Nat) (hb : off ≤ 18599) :
      (UInt256.ofNat off + ptr).toNat = ptr.toNat + off := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat _ _ (by omega)
  unfold cometWithExtendedAssetListCreation_block_1410_stack
    cometWithExtendedAssetListCreation_block_1410_memory
  simp (disch := (first | omega | (simp (disch := decide) only
    [writeWord_sparse_size, UInt256.toNat_ofNat_of_lt]; omega))) only
    [UInt256.toNat_ofNat_of_lt, hwrite, hfree, hcopy, hadd, memLoad_writeWord_preserved, hread]
  exact ⟨trivial, rfl⟩

end Benchmarks.CompoundIII.Comet
