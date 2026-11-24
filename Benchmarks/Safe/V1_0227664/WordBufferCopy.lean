import Benchmarks.Safe.V1_0227664.WordWrites
import Benchmarks.Safe.V1_0227664.Memory
import Benchmarks.Safe.V1_0227664.Decoders
import Reasoning.WordArithmetic
import Benchmarks.Safe.V1_0227664.Blocks.Runtime_041

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V1_0227664.RuntimeBlocks

namespace Benchmarks.Safe.V1_0227664

set_option maxRecDepth 2000

-- The shared byte-copy loop includes a final partial word before its cleanup write.
theorem safeByteBufferCopyLoopAfter (words : List UInt256)
    {I g s0 σ k C aw mem rdata i len src dst} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9364⟩
      (UInt256.ofNat i :: UInt256.ofNat len :: ⟨0⟩ ::
        UInt256.ofNat src :: UInt256.ofNat dst :: R)
      mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024)
    (hw : WordArrayMemory mem (src + 32 + i) words) (hm : dst + 32 + i ≤ mem.size)
    (hsrc : src + 32 + i + 32 * words.length ≤ dst + 32 + i)
    (hi : len ≤ i + 32 * words.length)
    (hlast : words ≠ [] → i + 32 * (words.length - 1) < len)
    (hend : dst + 32 + i + 32 * words.length < UInt256.size) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨9392⟩
      (UInt256.ofNat (i + 32 * words.length) :: UInt256.ofNat len :: ⟨0⟩ ::
        UInt256.ofNat src :: UInt256.ofNat dst :: R)
      (writeWords mem (dst + 32 + i) words) aw' rdata σ k' C' := by
  induction words generalizing i mem aw k C with
  | nil =>
      have he : len ≤ i := by simpa using hi
      have h₁ := safeRuntime_block_9364_taken (by simp only [List.length_cons]; omega)
        (by
          rw [ult_zero (by
            rw [ulit_toNat' i (by omega), ulit_toNat' len (by omega)]; omega)]
          decide) (by jump_dest) h
      simpa only [List.length_nil, Nat.mul_zero, Nat.add_zero, writeWords] using
        (show ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨9392⟩ _ mem aw' rdata σ k' C' from
          ⟨_, _, _, h₁⟩)
  | cons w ws ih =>
      have hi' : i < len := by
        have hlast' := hlast (by simp)
        simp only [List.length_cons, Nat.add_sub_cancel] at hlast'
        omega
      have hsource : (UInt256.ofNat 32 + (UInt256.ofNat src + UInt256.ofNat i)).toNat =
          src + 32 + i := by
        rw [← uadd_assoc, uadd3_ofNat_toNat (by omega) (by omega) (by omega)
          (by omega) (by omega)]
        omega
      have hdest : (UInt256.ofNat 32 + (UInt256.ofNat i + UInt256.ofNat dst)).toNat =
          dst + 32 + i := by
        rw [← uadd_assoc, uadd3_ofNat_toNat (by omega) (by omega) (by omega)
          (by omega) (by omega)]
        omega
      have hload : memLoad (UInt256.ofNat 32 + (UInt256.ofNat src + UInt256.ofNat i)) mem = w := by
        apply memLoad_of_wordRead
        simpa only [hsource, Nat.mul_zero, Nat.add_zero] using hw 0 (by simp)
      have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat len) = ⟨1⟩ :=
        ult_one (by rw [ulit_toNat' i (by omega), ulit_toNat' len (by omega)]; exact hi')
      have h₁ := safeRuntime_block_9364_fallthrough (by simp only [List.length_cons]; omega) (by rw [hlt]; decide) h
      obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_9373_packed (by simp; omega)
        (by jump_dest) h₁
      have hinc : UInt256.ofNat 32 + UInt256.ofNat i = UInt256.ofNat (i + 32) :=
        u256_32_add_ofNat i
      simp only [safeRuntime_block_9373_stack, safeRuntime_block_9373_memory,
        hload, hdest, hinc] at h₂
      have hw' := (hw.tail mem (src + 32 + i) w ws).writeAfter mem (src + 32 + i + 32) ws
        (by simp only [List.length_cons] at hsrc; omega) (dst + 32 + i) w
        (by simp only [List.length_cons] at hsrc; omega)
      have hm' : dst + 32 + (i + 32) ≤ (writeWord mem (dst + 32 + i) w).size := by
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
    (h : RD fork safeBytecode I g s0 ⟨9364⟩
      (UInt256.ofNat i :: UInt256.ofNat len :: ⟨0⟩ ::
        UInt256.ofNat src :: UInt256.ofNat dst :: R)
      mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024)
    (hw : WordArrayMemory mem (src + 32 + i) words) (hm : dst + 32 + i ≤ mem.size)
    (hsrc : src + 32 + i + 32 * words.length ≤ dst)
    (hi : len ≤ i + 32 * words.length)
    (hlast : words ≠ [] → i + 32 * (words.length - 1) < len)
    (hend : dst + 32 + i + 32 * words.length < UInt256.size) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨9392⟩
      (UInt256.ofNat (i + 32 * words.length) :: UInt256.ofNat len :: ⟨0⟩ ::
        UInt256.ofNat src :: UInt256.ofNat dst :: R)
      (writeWords mem (dst + 32 + i) words) aw' rdata σ k' C' := by
  exact safeByteBufferCopyLoopAfter words h hov hw hm (by omega) hi hlast hend

-- The shared byte-copy loop includes a final partial word before its cleanup write.
theorem safeByteBufferCopyLoop (words : List UInt256)
    {I g s0 σ k C aw mem rdata i len src dst} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9364⟩
      (UInt256.ofNat i :: UInt256.ofNat len :: ⟨0⟩ ::
        UInt256.ofNat src :: UInt256.ofNat dst :: R)
      mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024)
    (hw : WordArrayMemory mem (src + 32 + i) words) (hm : mem.size = dst + 32 + i)
    (hsrc : src + 32 + i + 32 * words.length ≤ dst)
    (hi : len ≤ i + 32 * words.length)
    (hlast : words ≠ [] → i + 32 * (words.length - 1) < len)
    (hend : dst + 32 + i + 32 * words.length < UInt256.size) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨9392⟩
      (UInt256.ofNat (i + 32 * words.length) :: UInt256.ofNat len :: ⟨0⟩ ::
        UInt256.ofNat src :: UInt256.ofNat dst :: R)
      (mem ++ wordBytes words) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', hr⟩ := safeByteBufferCopyLoopInto words h hov hw (by omega)
    hsrc hi hlast hend
  rw [writeWords_atEnd mem (dst + 32 + i) words hm] at hr
  exact ⟨aw', k', C', hr⟩

-- Whole-word return buffers are a specialization of the same byte-copy loop.
theorem safeWordBufferCopyLoop (words : List UInt256)
    {I g s0 σ k C aw mem rdata i len src dst} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9364⟩
      (UInt256.ofNat i :: UInt256.ofNat len :: ⟨0⟩ ::
        UInt256.ofNat src :: UInt256.ofNat dst :: R)
      mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024)
    (hw : WordArrayMemory mem (src + 32 + i) words) (hm : mem.size = dst + 32 + i)
    (hsrc : src + 32 + len ≤ dst) (hi : i + 32 * words.length = len)
    (hend : dst + 32 + len < UInt256.size) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨9392⟩
      (UInt256.ofNat len :: UInt256.ofNat len :: ⟨0⟩ ::
        UInt256.ofNat src :: UInt256.ofNat dst :: R)
      (mem ++ wordBytes words) aw' rdata σ k' C' := by
  simpa only [hi] using safeByteBufferCopyLoop words h hov hw hm (by omega) (by omega)
    (by intro hn; have hl := List.length_pos_iff.mpr hn; omega) (by omega)

end Benchmarks.Safe.V1_0227664
