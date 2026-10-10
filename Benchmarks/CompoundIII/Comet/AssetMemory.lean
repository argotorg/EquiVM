import Benchmarks.CompoundIII.Comet.AssetResultMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

/-- The returned asset structure and enough free space for its public ABI encoding. -/
structure AssetMemory (mem : ByteArray) (ptr free : UInt256) (out : ByteArray) : Prop where
  lower : 96 ≤ ptr.toNat
  present : ptr.toNat + 256 ≤ mem.size
  separate : ptr.toNat + 256 ≤ free.toNat
  bounded : free.toNat + 256 < UInt256.size
  freeWord : memLoad ⟨64⟩ mem = free
  words : ∀ j < 8, memLoad (ptr + UInt256.ofNat (32 * j)) mem = calldataWord out (32 * j)

def assetInternalMemory (mem : ByteArray) (ptr i : UInt256) (out : ByteArray) : ByteArray :=
  assetResultMemory (assetZeroMemory mem ptr) (ptr + ⟨256⟩) i out

theorem assetInternalMemory_free {mem out : ByteArray} {ptr i : UInt256}
    (hlo : 96 ≤ ptr.toNat) (hb : ptr.toNat + 768 < UInt256.size) :
    memLoad ⟨64⟩ (assetInternalMemory mem ptr i out) = ((ptr + ⟨256⟩) + ⟨256⟩) + ⟨256⟩ := by
  have ha : (ptr + (⟨256⟩ : UInt256)).toNat = ptr.toNat + 256 :=
    uadd_word_ofNat_toNat ptr 256 (by omega)
  exact assetResultMemory_free (by rw [ha]; omega) (by rw [ha]; omega)

theorem assetInternalMemory_spec {mem out : ByteArray} {ptr i : UInt256}
    (hlo : 96 ≤ ptr.toNat) (hb : ptr.toNat + 1024 < UInt256.size)
    (hout : 256 ≤ out.size) (hhi : out.size < UInt256.size) :
    AssetMemory (assetInternalMemory mem ptr i out) ((ptr + ⟨256⟩) + ⟨256⟩)
      (((ptr + ⟨256⟩) + ⟨256⟩) + ⟨256⟩) out := by
  have h1 : (ptr + (⟨256⟩ : UInt256)).toNat = ptr.toNat + 256 :=
    uadd_word_ofNat_toNat ptr 256 (by omega)
  have h2 : ((ptr + (⟨256⟩ : UInt256)) + ⟨256⟩).toNat = ptr.toNat + 512 := by
    have ha : ((ptr + (⟨256⟩ : UInt256)) + ⟨256⟩).toNat =
        (ptr + (⟨256⟩ : UInt256)).toNat + 256 :=
      uadd_word_ofNat_toNat _ 256 (by rw [h1]; omega)
    omega
  have h3 : (((ptr + (⟨256⟩ : UInt256)) + ⟨256⟩) + ⟨256⟩).toNat = ptr.toNat + 768 := by
    have ha : (((ptr + (⟨256⟩ : UInt256)) + ⟨256⟩) + ⟨256⟩).toNat =
        ((ptr + (⟨256⟩ : UInt256)) + ⟨256⟩).toNat + 256 :=
      uadd_word_ofNat_toNat _ 256 (by rw [h2]; omega)
    omega
  refine ⟨by rw [h2]; omega, ?_, by rw [h2, h3], by rw [h3]; omega,
    assetInternalMemory_free hlo (by omega), ?_⟩
  · rw [assetInternalMemory, assetResultMemory_size (by rw [h1]; omega)
      (by rw [h1]; omega) hout hhi, h1]
    omega
  · intro j hj
    unfold assetInternalMemory
    apply assetResultMemory_word j hj
    rw [h1]
    omega

end Benchmarks.CompoundIII.Comet
