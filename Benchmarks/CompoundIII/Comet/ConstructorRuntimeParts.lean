import Benchmarks.CompoundIII.Comet.ConstructorRuntimeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def constructorRuntimePart (mem : ByteArray) (ptr : UInt256) (w : Nat → UInt256)
    (start count : Nat) : ByteArray :=
  writeCascade mem (((constructorRuntimeSites.drop start).take count).map fun (off, slot) ↦
    (ptr.toNat + off, w slot))

theorem constructorRuntimePart_compose (mem : ByteArray) (ptr : UInt256) (w : Nat → UInt256)
    (start count : Nat) :
    constructorRuntimePart (constructorRuntimePatchedMemory mem ptr w start) ptr w start count =
      constructorRuntimePatchedMemory mem ptr w (start + count) := by
  unfold constructorRuntimePart constructorRuntimePatchedMemory
  rw [← writeCascade_append, ← List.map_append, List.take_add]

theorem constructorRuntimePart1505_eq {mem : ByteArray} {ptr : UInt256} {w : Nat → UInt256}
    (hm : 928 ≤ mem.size) (hlo : 928 ≤ ptr.toNat) (hfit : ptr.toNat + 18599 < UInt256.size)
    (hr : ∀ off, 96 ≤ off → off + 32 ≤ 928 → memLoad (UInt256.ofNat off) mem = w off)
    (R : List UInt256) :
    cometWithExtendedAssetListCreation_block_1505_stack (mem := mem)
      (x0 := UInt256.ofNat 6266 + ptr) (x1 := w 192) (x2 := ptr) (x3 := w 192) (x4 := ptr)
      (R := R) = UInt256.ofNat 18431 :: ptr :: w 256 :: ptr :: R ∧
    cometWithExtendedAssetListCreation_block_1505_memory (mem := mem)
      (x0 := UInt256.ofNat 6266 + ptr) (x1 := w 192) (x2 := ptr) (x3 := w 192) (x4 := ptr) =
        constructorRuntimePart mem ptr w 9 13 := by
  have hwrite (m : ByteArray) (off : Nat) (word : UInt256) :
      word.toByteArray.write 0 m off 32 = writeWord m off word := rfl
  have hadd (off : Nat) (hb : off ≤ 18599) :
      (UInt256.ofNat off + ptr).toNat = ptr.toNat + off := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat _ _ (by omega)
  unfold cometWithExtendedAssetListCreation_block_1505_stack
    cometWithExtendedAssetListCreation_block_1505_memory
  simp (disch := (first | omega | (simp (disch := decide) only
    [writeWord_sparse_size, UInt256.toNat_ofNat_of_lt]; omega))) only
    [hwrite, hadd, memLoad_writeWord_preserved, hr]
  exact ⟨trivial, rfl⟩

theorem constructorRuntimePart1598_eq {mem : ByteArray} {ptr : UInt256} {w : Nat → UInt256}
    (hm : 928 ≤ mem.size) (hlo : 928 ≤ ptr.toNat) (hfit : ptr.toNat + 18599 < UInt256.size)
    (hr : ∀ off, 96 ≤ off → off + 32 ≤ 928 → memLoad (UInt256.ofNat off) mem = w off)
    (R : List UInt256) :
    cometWithExtendedAssetListCreation_block_1598_stack (mem := mem)
      (x0 := UInt256.ofNat 18431) (x1 := ptr) (x2 := w 256) (x3 := ptr) (R := R) =
      w 448 :: ptr :: R ∧
    cometWithExtendedAssetListCreation_block_1598_memory (mem := mem)
      (x0 := UInt256.ofNat 18431) (x1 := ptr) (x2 := w 256) (x3 := ptr) =
        constructorRuntimePart mem ptr w 22 12 := by
  have hwrite (m : ByteArray) (off : Nat) (word : UInt256) :
      word.toByteArray.write 0 m off 32 = writeWord m off word := rfl
  have hadd (off : Nat) (hb : off ≤ 18599) :
      (UInt256.ofNat off + ptr).toNat = ptr.toNat + off := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat _ _ (by omega)
  unfold cometWithExtendedAssetListCreation_block_1598_stack
    cometWithExtendedAssetListCreation_block_1598_memory
  simp (disch := (first | omega | (simp (disch := decide) only
    [writeWord_sparse_size, UInt256.toNat_ofNat_of_lt]; omega))) only
    [hwrite, hadd, memLoad_writeWord_preserved, hr]
  exact ⟨trivial, rfl⟩

theorem constructorRuntimePart1696_eq {mem : ByteArray} {ptr : UInt256} {w : Nat → UInt256}
    (hm : 928 ≤ mem.size) (hlo : 928 ≤ ptr.toNat) (hfit : ptr.toNat + 18599 < UInt256.size)
    (hr : ∀ off, 96 ≤ off → off + 32 ≤ 928 → memLoad (UInt256.ofNat off) mem = w off)
    (R : List UInt256) :
    cometWithExtendedAssetListCreation_block_1696_stack (mem := mem)
      (x0 := w 448) (x1 := ptr) (R := R) =
      (UInt256.ofNat 11157 + ptr) :: w 576 :: ptr :: w 576 :: ptr :: R ∧
    cometWithExtendedAssetListCreation_block_1696_memory (mem := mem)
      (x0 := w 448) (x1 := ptr) =
        constructorRuntimePart mem ptr w 34 11 := by
  have hwrite (m : ByteArray) (off : Nat) (word : UInt256) :
      word.toByteArray.write 0 m off 32 = writeWord m off word := rfl
  have hadd (off : Nat) (hb : off ≤ 18599) :
      (UInt256.ofNat off + ptr).toNat = ptr.toNat + off := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat _ _ (by omega)
  unfold cometWithExtendedAssetListCreation_block_1696_stack
    cometWithExtendedAssetListCreation_block_1696_memory
  simp (disch := (first | omega | (simp (disch := decide) only
    [writeWord_sparse_size, UInt256.toNat_ofNat_of_lt]; omega))) only
    [hwrite, hadd, memLoad_writeWord_preserved, hr]
  exact ⟨trivial, rfl⟩

theorem constructorRuntimePart1792_eq {mem : ByteArray} {ptr : UInt256} {w : Nat → UInt256}
    (hm : 928 ≤ mem.size) (hlo : 928 ≤ ptr.toNat) (hfit : ptr.toNat + 18599 < UInt256.size)
    (hr : ∀ off, 96 ≤ off → off + 32 ≤ 928 → memLoad (UInt256.ofNat off) mem = w off)
    (R : List UInt256) :
    cometWithExtendedAssetListCreation_block_1792_stack (mem := mem)
      (x0 := UInt256.ofNat 11157 + ptr) (x1 := w 576) (x2 := ptr) (x3 := w 576) (x4 := ptr) (R
      := R) =
      UInt256.ofNat 15134 :: ptr :: w 736 :: ptr :: w 736 :: ptr :: R ∧
    cometWithExtendedAssetListCreation_block_1792_memory (mem := mem)
      (x0 := UInt256.ofNat 11157 + ptr) (x1 := w 576) (x2 := ptr) (x3 := w 576) (x4 := ptr) =
        constructorRuntimePart mem ptr w 45 12 := by
  have hwrite (m : ByteArray) (off : Nat) (word : UInt256) :
      word.toByteArray.write 0 m off 32 = writeWord m off word := rfl
  have hadd (off : Nat) (hb : off ≤ 18599) :
      (UInt256.ofNat off + ptr).toNat = ptr.toNat + off := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat _ _ (by omega)
  unfold cometWithExtendedAssetListCreation_block_1792_stack
    cometWithExtendedAssetListCreation_block_1792_memory
  simp (disch := (first | omega | (simp (disch := decide) only
    [writeWord_sparse_size, UInt256.toNat_ofNat_of_lt]; omega))) only
    [hwrite, hadd, memLoad_writeWord_preserved, hr]
  exact ⟨trivial, rfl⟩

theorem constructorRuntimePart1890_eq {mem : ByteArray} {ptr : UInt256} {w : Nat → UInt256}
    (hm : 928 ≤ mem.size) (hlo : 928 ≤ ptr.toNat) (hfit : ptr.toNat + 18599 < UInt256.size)
    (hr : ∀ off, 96 ≤ off → off + 32 ≤ 928 → memLoad (UInt256.ofNat off) mem = w off)
    (R : List UInt256) :
    cometWithExtendedAssetListCreation_block_1890_stack (mem := mem)
      (x0 := UInt256.ofNat 15134) (x1 := ptr) (x2 := w 736) (x3 := ptr) (x4 := w 736) (x5 :=
      ptr) (R := R) =
      (UInt256.ofNat 7222 + ptr) :: w 896 :: ptr :: R ∧
    cometWithExtendedAssetListCreation_block_1890_memory (mem := mem)
      (x0 := UInt256.ofNat 15134) (x1 := ptr) (x2 := w 736) (x3 := ptr) (x4 := w 736) (x5 :=
      ptr) =
        constructorRuntimePart mem ptr w 57 12 := by
  have hwrite (m : ByteArray) (off : Nat) (word : UInt256) :
      word.toByteArray.write 0 m off 32 = writeWord m off word := rfl
  have hadd (off : Nat) (hb : off ≤ 18599) :
      (UInt256.ofNat off + ptr).toNat = ptr.toNat + off := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat _ _ (by omega)
  unfold cometWithExtendedAssetListCreation_block_1890_stack
    cometWithExtendedAssetListCreation_block_1890_memory
  simp (disch := (first | omega | (simp (disch := decide) only
    [writeWord_sparse_size, UInt256.toNat_ofNat_of_lt]; omega))) only
    [hwrite, hadd, memLoad_writeWord_preserved, hr]
  exact ⟨trivial, rfl⟩

end Benchmarks.CompoundIII.Comet
