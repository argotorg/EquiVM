import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsDecodeABI
import Benchmarks.EAS.Attester.WordArrayMemory

/-! Memory facts shared by fixed-size external return decoders. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

-- LIBRARY CANDIDATE: bounded STATICCALL output and fixed-size struct decoding.
def fixedReturnBuffer (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (len : Nat) : ByteArray :=
  out.write 0 mem ptr.toNat (min (UInt256.ofNat len) (UInt256.ofNat out.size)).toNat

theorem fixedReturnBuffer_long (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    {len : Nat} (hl : len ≤ out.size) (hh : out.size < UInt256.size) :
    fixedReturnBuffer mem ptr out len = out.write 0 mem ptr.toNat len := by
  rw [fixedReturnBuffer, umin_ofNat_right_toNat_of_ge (by omega) hl hh]

theorem fixedReturnBuffer_size {mem out : ByteArray} {ptr : UInt256} {len : Nat}
    (hlen : 0 < len) (hin : ptr.toNat ≤ mem.size) (hl : len ≤ out.size)
    (hh : out.size < UInt256.size) :
    (fixedReturnBuffer mem ptr out len).size = max mem.size (ptr.toNat + len) := by
  rw [fixedReturnBuffer_long _ _ _ hl hh]
  exact copyWindow_size _ _ _ _ _ (by omega) (by omega) hin

theorem fixedReturnBuffer_load {mem out : ByteArray} {ptr : UInt256} {off len : Nat}
    (hin : ptr.toNat ≤ mem.size) (hl : len ≤ out.size) (hh : out.size < UInt256.size)
    (hp : ptr.toNat + len < UInt256.size) (hoff : off + 32 ≤ len) :
    memLoad (ptr + UInt256.ofNat off) (fixedReturnBuffer mem ptr out len) =
      calldataWord out off := by
  have hadd : (ptr + UInt256.ofNat off).toNat = ptr.toNat + off :=
    uadd_word_ofNat_toNat ptr off (by omega)
  apply loadedWord_of_read
  · rw [hadd, fixedReturnBuffer_size (by omega) hin hl hh]; omega
  · rw [hadd, fixedReturnBuffer_long _ _ _ hl hh,
      copyWindow_read_word _ _ _ _ _ _ (by omega) (by omega) hin hoff,
      Nat.zero_add, readWithPadding_eq_extract _ _ (by omega),
      calldataWord_bytes_at (by omega)]

theorem wordWindowRead_write {mem : ByteArray} {ptr : UInt256} {len : Nat}
    {values : Nat → UInt256} (dst : Nat) (word : UInt256)
    (hmem : ptr.toNat + len ≤ mem.size) (hsep : ptr.toNat + len ≤ dst)
    (hp : ptr.toNat + len < UInt256.size)
    (hread : ∀ off, off + 32 ≤ len → memLoad (ptr + UInt256.ofNat off) mem = values off) :
    ∀ off, off + 32 ≤ len →
      memLoad (ptr + UInt256.ofNat off) (writeWord mem dst word) = values off := by
  intro off hoff
  have hadd : (ptr + UInt256.ofNat off).toNat = ptr.toNat + off :=
    uadd_word_ofNat_toNat ptr off (by omega)
  rw [memLoad_write_above _ _ _ _ (by rw [hadd]; omega) (by rw [hadd]; omega)]
  exact hread off hoff

theorem wordWindowRead_freeWrite {mem : ByteArray} {ptr : UInt256} {len off : Nat}
    (word : UInt256) (hlo : 96 ≤ ptr.toNat) (hmem : ptr.toNat + len ≤ mem.size)
    (hp : ptr.toNat + len < UInt256.size) (hoff : off + 32 ≤ len) :
    memLoad (ptr + UInt256.ofNat off) (writeWord mem 64 word) =
      memLoad (ptr + UInt256.ofNat off) mem := by
  have hadd : (ptr + UInt256.ofNat off).toNat = ptr.toNat + off :=
    uadd_word_ofNat_toNat ptr off (by omega)
  exact memLoad_write_disjoint _ _ _ _ (by rw [hadd]; omega)
    (.inr (by rw [hadd]; omega))

def structReturnMemory (mem : ByteArray) (dst : Nat) (out : ByteArray)
    (count : Nat) : ByteArray :=
  wordSequenceMemory mem dst (wordArrayWords (fun i ↦ calldataWord out (32 * i)) 0 count)

theorem structReturnMemory_size (mem : ByteArray) (dst : Nat) (out : ByteArray)
    {count : Nat} (hc : 0 < count) :
    (structReturnMemory mem dst out count).size = max mem.size (dst + 32 * count) := by
  rw [structReturnMemory, wordSequenceMemory_size_nonempty _ _ _ (by
    have hlength := wordArrayWords_length (fun i ↦ calldataWord out (32 * i)) 0 count
    intro h; rw [h, List.length_nil] at hlength; omega)]
  rw [wordArrayWords_length]

theorem structReturnMemory_free {mem out : ByteArray} {dst count : Nat}
    (hmem : 96 ≤ mem.size) (hdst : 96 ≤ dst) :
    memLoad ⟨64⟩ (structReturnMemory mem dst out count) = memLoad ⟨64⟩ mem :=
  wordSequenceMemory_load_below _ hmem hdst (by decide)

theorem structReturnMemory_field (mem : ByteArray) (dst : Nat) (out : ByteArray)
    {count : Nat} (i : Nat) (hi : i < count) (hfit : dst + 32 * count < UInt256.size) :
    memLoad (UInt256.ofNat (dst + 32 * i)) (structReturnMemory mem dst out count) =
      calldataWord out (32 * i) := by
  simpa only [Nat.zero_add] using wordArrayDataMemory_load (mem := mem) (off := dst)
    (i := 0) (n := count) (fun i ↦ calldataWord out (32 * i)) hi hfit

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
