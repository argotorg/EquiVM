import Benchmarks.Morpho.MorphoBlue.ErrorRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- GENERALIZES morphoErrorMem_properties_of_gap: allocation may reuse a call buffer.
theorem morphoErrorMem_properties_general (length payload ptr : UInt256) (mem : ByteArray)
    (hptrLo : 96 ≤ ptr.toNat) (hptr : memLoad (UInt256.ofNat 64) mem = ptr)
    (hlo : 96 ≤ mem.size) (hgap : ptr.toNat - mem.size < USize.size)
    (hhi : ptr.toNat + 100 < UInt256.size) :
    (morphoErrorMem length payload mem).size = max mem.size (ptr.toNat + 64) ∧
    memLoad (UInt256.ofNat 64) (morphoErrorMem length payload mem) = ptr + UInt256.ofNat 64 ∧
    morphoErrorLength (morphoErrorMem length payload mem) ptr = length := by
  have h32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have h64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have h68 : (ptr + UInt256.ofNat 64 + UInt256.ofNat 4).toNat = ptr.toNat + 68 := by
    rw [uadd_word_ofNat_toNat _ 4 (by omega), h64]
  have huz : 0 < USize.size := lt_usize _ (by decide)
  have hmem : morphoErrorMem length payload mem = writeCascade mem
      [(64, ptr + UInt256.ofNat 64), (ptr.toNat, length), (ptr.toNat + 32, payload)] := by
    rw [morphoErrorMem_asCascade _ _ _ _ hptr, h32]
  have hs : (morphoErrorMem length payload mem).size = max mem.size (ptr.toNat + 64) := by
    rw [hmem, writeCascade_size]
    · simp only [writeCascadeSize]
      omega
    · simp only [WriteGapsOk, and_true]
      omega
  have hp : memLoad (UInt256.ofNat 64) (morphoErrorMem length payload mem) = ptr + UInt256.ofNat 64 := by
    apply mloadWordValue_of_readWithPadding
    · change 64 < _
      rw [hs]
      omega
    · rw [hmem]
      apply writeCascade_read_word_of_head
      · omega
      · simp only [WindowDisjointFromWrites, and_true]
        omega
  refine ⟨hs, hp, ?_⟩
  unfold morphoErrorLength
  rw [hp, hmem, h64, h68]
  let mem0 := Reasoning.Theory.writeWord mem 64 (ptr + UInt256.ofNat 64)
  have hm0 : mem0.size = mem.size := by
    rw [Reasoning.Theory.writeWord_size mem 64 _ (by omega)]
    omega
  let rest := [(ptr.toNat + 32, payload),
    (ptr.toNat + 64, UInt256.ofNat 3963877391197344453575983046348115674221700746820753546331534351508065746944),
    (ptr.toNat + 68, UInt256.ofNat 32)]
  change memLoad ptr (writeCascade mem0 ((ptr.toNat, length) :: rest)) = length
  have hs' : (writeCascade mem0 ((ptr.toNat, length) :: rest)).size = max mem.size (ptr.toNat + 100) := by
    rw [writeCascade_size]
    · simp only [rest, writeCascadeSize, hm0]
      omega
    · simp only [rest, WriteGapsOk, hm0, and_true]
      omega
  apply mloadWordValue_of_readWithPadding
  · rw [hs']
    omega
  · apply writeCascade_read_word_of_head
    · rw [hm0]
      omega
    · simp only [rest, WindowDisjointFromWrites, hm0, and_true]
      omega

end Benchmarks.Morpho.MorphoBlue
