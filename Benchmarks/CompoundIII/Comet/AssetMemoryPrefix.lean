import Benchmarks.CompoundIII.Comet.AssetMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: building a single-word call payload preserves earlier allocations.
theorem callWordMemory_prefix {mem : ByteArray} {ptr selector arg : UInt256}
    (hb : ptr.toNat + 4 < UInt256.size) :
    MemoryPrefix mem (callWordMemory mem ptr selector arg) ptr.toNat :=
  (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (le_refl _))).trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by
      rw [uadd_word_ofNat_toNat ptr 4 hb]; omega)))

theorem assetZeroMemory_prefix {mem : ByteArray} {ptr : UInt256}
    (hb : ptr.toNat + 256 < UInt256.size) :
    MemoryPrefix mem (assetZeroMemory mem ptr) ptr.toNat := by
  apply memoryPrefix_sparse_cascade
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (by change 64 + 32 ≤ 96; decide)
  · exact Or.inl (le_refl _)
  all_goals
    left
    dsimp only
    rw [uadd_word_ofNat_toNat _ _ (by omega)]
    omega

theorem assetResultMemory_prefix {mem out : ByteArray} {ptr i : UInt256}
    (hb : ptr.toNat + 512 < UInt256.size) (hout : 256 ≤ out.size)
    (hhi : out.size < UInt256.size) :
    MemoryPrefix mem (assetResultMemory mem ptr i out) ptr.toNat := by
  have ha : (ptr + (⟨256⟩ : UInt256)).toNat = ptr.toNat + 256 :=
    uadd_word_ofNat_toNat ptr 256 (by omega)
  have hp : MemoryPrefix mem (assetInputMemory mem ptr i) ptr.toNat :=
    callWordMemory_prefix (by omega)
  have hcopy : MemoryPrefix (assetInputMemory mem ptr i)
      (assetCopyMemory (assetInputMemory mem ptr i) ptr out) ptr.toNat := by
    have hl : (min (⟨256⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 256 :=
      umin_ofNat_right_toNat_of_ge (c := 256) (n := out.size) (by decide) hout hhi
    unfold assetCopyMemory callOutputMem
    rw [hl]
    exact copyWindow_prefix out _ 0 ptr.toNat 256 ptr.toNat (by decide) hout
      (by rw [assetInputMemory_size (by omega)]; omega) (Or.inl (le_refl _))
  have hdecode : MemoryPrefix (assetCopyMemory (assetInputMemory mem ptr i) ptr out)
      (assetDecodeMemory (assetInputMemory mem ptr i) ptr out) ptr.toNat :=
    (memoryPrefix_sparse_writeWord _ 64 _ _ (Or.inr (by decide))).trans
      (memoryPrefix_sparse_writeWord _ 64 _ _ (Or.inr (by decide)))
  exact ((hp.trans hcopy).trans hdecode).trans
    (assetStore_prefix (by decide) (by rw [ha]; omega) (by rw [ha]; omega))

theorem assetInternalMemory_prefix {mem out : ByteArray} {ptr i : UInt256}
    (hb : ptr.toNat + 768 < UInt256.size) (hout : 256 ≤ out.size)
    (hhi : out.size < UInt256.size) :
    MemoryPrefix mem (assetInternalMemory mem ptr i out) ptr.toNat := by
  have ha : (ptr + (⟨256⟩ : UInt256)).toNat = ptr.toNat + 256 :=
    uadd_word_ofNat_toNat ptr 256 (by omega)
  exact (assetZeroMemory_prefix (by omega)).trans
    ((assetResultMemory_prefix (by rw [ha]; omega) hout hhi).mono (by rw [ha]; omega))

theorem assetInternalMemory_size {mem out : ByteArray} {ptr i : UInt256}
    (hlo : 96 ≤ ptr.toNat) (hb : ptr.toNat + 768 < UInt256.size)
    (hout : 256 ≤ out.size) (hhi : out.size < UInt256.size) :
    (assetInternalMemory mem ptr i out).size = max mem.size (ptr.toNat + 768) := by
  have ha : (ptr + (⟨256⟩ : UInt256)).toNat = ptr.toNat + 256 :=
    uadd_word_ofNat_toNat ptr 256 (by omega)
  rw [assetInternalMemory, assetResultMemory_size (by rw [ha]; omega)
    (by rw [ha]; omega) hout hhi, assetZeroMemory_size hlo (by omega), ha]
  omega

end Benchmarks.CompoundIII.Comet
