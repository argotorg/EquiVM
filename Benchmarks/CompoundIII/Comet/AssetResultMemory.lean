import Benchmarks.CompoundIII.Comet.AssetInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem assetStore_load_below {mem out : ByteArray} {dest read : UInt256} {n : Nat}
    (hn : n ≤ 8) (hb : dest.toNat + 256 < UInt256.size)
    (hin : read.toNat + 32 ≤ mem.size) (hbelow : read.toNat + 32 ≤ dest.toNat) :
    memLoad read (assetStore mem dest out n) = memLoad read mem := by
  have hs := (assetStore_prefix (mem := mem) (out := out) hn hb (Nat.zero_le _)).size
  unfold memLoad
  rw [if_neg (by omega), if_neg (by omega)]
  unfold assetStore
  rw [sparseCascade_read_below _ _ _ hin (by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
    have hj' := List.mem_range.mp hj
    dsimp only
    rw [uadd_word_ofNat_toNat _ _ (by omega)]
    omega)]

theorem assetResultMemory_free {mem out : ByteArray} {ptr i : UInt256}
    (hlo : 96 ≤ ptr.toNat) (hb : ptr.toNat + 512 < UInt256.size) :
    memLoad ⟨64⟩ (assetResultMemory mem ptr i out) = (ptr + ⟨256⟩) + ⟨256⟩ := by
  have ha : (ptr + (⟨256⟩ : UInt256)).toNat = ptr.toNat + 256 :=
    uadd_word_ofNat_toNat ptr 256 (by omega)
  rw [assetResultMemory, assetStore_load_below (by decide)
    (by rw [ha]; omega) (by
      rw [assetDecodeMemory, writeWord_sparse_size]
      change 64 + 32 ≤ _; omega) (by rw [ha]; change 64 + 32 ≤ _; omega)]
  exact assetDecodeMemory_free _ _ _

theorem assetResultMemory_word {mem out : ByteArray} {ptr i : UInt256} (j : Nat)
    (hj : j < 8) (hb : ptr.toNat + 512 < UInt256.size) :
    memLoad ((ptr + ⟨256⟩) + UInt256.ofNat (32 * j)) (assetResultMemory mem ptr i out) =
      calldataWord out (32 * j) := by
  have ha : (ptr + (⟨256⟩ : UInt256)).toNat = ptr.toNat + 256 :=
    uadd_word_ofNat_toNat ptr 256 (by omega)
  exact assetStore_word (by decide) hj (by rw [ha]; omega)

theorem assetResultMemory_size {mem out : ByteArray} {ptr i : UInt256}
    (hlo : 96 ≤ ptr.toNat) (hb : ptr.toNat + 512 < UInt256.size)
    (hout : 256 ≤ out.size) (hhi : out.size < UInt256.size) :
    (assetResultMemory mem ptr i out).size = max mem.size (ptr.toNat + 512) := by
  have ha : (ptr + (⟨256⟩ : UInt256)).toNat = ptr.toNat + 256 :=
    uadd_word_ofNat_toNat ptr 256 (by omega)
  have hi := assetInputMemory_size (mem := mem) (i := i) (by omega : ptr.toNat + 36 < UInt256.size)
  rw [assetResultMemory, assetStore_size (by decide) (by decide) (by rw [ha]; omega),
    assetDecodeMemory_size hlo (by rw [hi]; omega) hout hhi, ha, hi]
  omega

end Benchmarks.CompoundIII.Comet
