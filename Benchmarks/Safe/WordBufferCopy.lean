import Benchmarks.Safe.WordWrites
import Benchmarks.Safe.Memory
import Benchmarks.Safe.Decoders
import Reasoning.WordArithmetic
import Benchmarks.Safe.Blocks.Runtime_042
import Benchmarks.Safe.Blocks.Runtime_043

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 2000

-- The shared byte-copy loop includes a final partial word before its cleanup write.
theorem safeByteBufferCopyLoopAfter (words : List UInt256)
    {I g s0 σ k C aw mem rdata i len src dst} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9735⟩
      (UInt256.ofNat i :: UInt256.ofNat src :: UInt256.ofNat dst :: UInt256.ofNat len :: R)
      mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024)
    (hw : WordArrayMemory mem (src + i) words) (hm : dst + i ≤ mem.size)
    (hsrc : src + i + 32 * words.length ≤ dst + i)
    (hi : len ≤ i + 32 * words.length)
    (hlast : words ≠ [] → i + 32 * (words.length - 1) < len)
    (hend : dst + i + 32 * words.length < UInt256.size) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨9759⟩
      (UInt256.ofNat (i + 32 * words.length) :: UInt256.ofNat src ::
        UInt256.ofNat dst :: UInt256.ofNat len :: R)
      (writeWords mem (dst + i) words) aw' rdata σ k' C' := by
  induction words generalizing i mem aw k C with
  | nil =>
      have he : len ≤ i := by simpa using hi
      have h₁ := safeRuntime_block_9735_taken (by omega)
        (by
          rw [ult_zero (by
            rw [ulit_toNat' i (by omega), ulit_toNat' len (by omega)]; omega)]
          decide) (by jump_dest) h
      simpa only [List.length_nil, Nat.mul_zero, Nat.add_zero, writeWords] using
        (show ∃ aw' k' C', RD safeBytecode I g s0 ⟨9759⟩ _ mem aw' rdata σ k' C' from
          ⟨_, _, _, h₁⟩)
  | cons w ws ih =>
      have hi' : i < len := by
        have hlast' := hlast (by simp)
        simp only [List.length_cons, Nat.add_sub_cancel] at hlast'
        omega
      have hsource : (UInt256.ofNat i + UInt256.ofNat src).toNat = src + i := by
        simpa only [Nat.add_comm] using
          (uadd_ofNat_toNat (a := i) (b := src) (by omega) (by omega) (by omega))
      have hdest : (UInt256.ofNat i + UInt256.ofNat dst).toNat = dst + i := by
        simpa only [Nat.add_comm] using
          (uadd_ofNat_toNat (a := i) (b := dst) (by omega) (by omega) (by omega))
      have hload : memLoad (UInt256.ofNat i + UInt256.ofNat src) mem = w := by
        apply memLoad_of_wordRead
        simpa only [hsource, Nat.mul_zero, Nat.add_zero] using hw 0 (by simp)
      have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat len) = ⟨1⟩ :=
        ult_one (by rw [ulit_toNat' i (by omega), ulit_toNat' len (by omega)]; exact hi')
      have h₁ := safeRuntime_block_9735_fallthrough (by omega) (by rw [hlt]; decide) h
      obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_9744_packed (by simp; omega)
        (by jump_dest) h₁
      have hinc : UInt256.ofNat 32 + UInt256.ofNat i = UInt256.ofNat (i + 32) :=
        u256_32_add_ofNat i
      simp only [safeRuntime_block_9744_stack, safeRuntime_block_9744_memory,
        hload, hdest, hinc] at h₂
      have hw' := (hw.tail mem (src + i) w ws).writeAfter mem (src + i + 32) ws
        (by simp only [List.length_cons] at hsrc; omega) (dst + i) w
        (by simp only [List.length_cons] at hsrc; omega)
      have hm' : dst + (i + 32) ≤ (writeWord mem (dst + i) w).size := by
        rw [writeWord_sparse_size]
        omega
      obtain ⟨aw', k', C', h'⟩ := ih h₂
        (by simpa only [Nat.add_assoc] using hw') hm'
        (by simp only [List.length_cons] at hsrc; omega)
        (by simp only [List.length_cons] at hi; omega)
        (by
          intro hne
          have hl := List.length_pos_iff.mpr hne
          have hlast' := hlast (by simp)
          simp only [List.length_cons] at hlast'
          omega)
        (by simp only [List.length_cons] at hend; omega)
      exact ⟨_, _, _, by
        simpa only [writeWords, List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using h'⟩

-- The original whole-source separation condition is a specialization.
theorem safeByteBufferCopyLoopInto (words : List UInt256)
    {I g s0 σ k C aw mem rdata i len src dst} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9735⟩
      (UInt256.ofNat i :: UInt256.ofNat src :: UInt256.ofNat dst :: UInt256.ofNat len :: R)
      mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024)
    (hw : WordArrayMemory mem (src + i) words) (hm : dst + i ≤ mem.size)
    (hsrc : src + i + 32 * words.length ≤ dst)
    (hi : len ≤ i + 32 * words.length)
    (hlast : words ≠ [] → i + 32 * (words.length - 1) < len)
    (hend : dst + i + 32 * words.length < UInt256.size) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨9759⟩
      (UInt256.ofNat (i + 32 * words.length) :: UInt256.ofNat src ::
        UInt256.ofNat dst :: UInt256.ofNat len :: R)
      (writeWords mem (dst + i) words) aw' rdata σ k' C' := by
  exact safeByteBufferCopyLoopAfter words h hov hw hm (by omega) hi hlast hend

-- The shared byte-copy loop includes a final partial word before its cleanup write.
theorem safeByteBufferCopyLoop (words : List UInt256)
    {I g s0 σ k C aw mem rdata i len src dst} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9735⟩
      (UInt256.ofNat i :: UInt256.ofNat src :: UInt256.ofNat dst :: UInt256.ofNat len :: R)
      mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024)
    (hw : WordArrayMemory mem (src + i) words) (hm : mem.size = dst + i)
    (hsrc : src + i + 32 * words.length ≤ dst)
    (hi : len ≤ i + 32 * words.length)
    (hlast : words ≠ [] → i + 32 * (words.length - 1) < len)
    (hend : dst + i + 32 * words.length < UInt256.size) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨9759⟩
      (UInt256.ofNat (i + 32 * words.length) :: UInt256.ofNat src ::
        UInt256.ofNat dst :: UInt256.ofNat len :: R)
      (mem ++ wordBytes words) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', hr⟩ := safeByteBufferCopyLoopInto words h hov hw (by omega)
    hsrc hi hlast hend
  rw [writeWords_atEnd mem (dst + i) words hm] at hr
  exact ⟨aw', k', C', hr⟩

-- Whole-word return buffers are a specialization of the same byte-copy loop.
theorem safeWordBufferCopyLoop (words : List UInt256)
    {I g s0 σ k C aw mem rdata i len src dst} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9735⟩
      (UInt256.ofNat i :: UInt256.ofNat src :: UInt256.ofNat dst :: UInt256.ofNat len :: R)
      mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024)
    (hw : WordArrayMemory mem (src + i) words) (hm : mem.size = dst + i)
    (hsrc : src + len ≤ dst) (hi : i + 32 * words.length = len)
    (hend : dst + len < UInt256.size) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨9759⟩
      (UInt256.ofNat len :: UInt256.ofNat src :: UInt256.ofNat dst :: UInt256.ofNat len :: R)
      (mem ++ wordBytes words) aw' rdata σ k' C' := by
  simpa only [hi] using safeByteBufferCopyLoop words h hov hw hm (by omega) (by omega)
    (by intro hn; have hl := List.length_pos_iff.mpr hn; omega) (by omega)

end Benchmarks.Safe
