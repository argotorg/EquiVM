import Benchmarks.Safe.WordArrayMemory
import Benchmarks.Safe.Memory
import Benchmarks.Safe.Decoders
import Reasoning.WordArithmetic
import Benchmarks.Safe.Blocks.Runtime_045

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

-- The compiler's shared address-array encoder, starting at any iteration and source pointer.
set_option maxHeartbeats 800000 in
theorem safeAddressArrayCopyLoop (words : List UInt256)
    {I g s0 σ k C aw mem rdata i n src dst scratch arr ret} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10256⟩
      (UInt256.ofNat i :: UInt256.ofNat src :: UInt256.ofNat n :: scratch :: arr ::
        UInt256.ofNat dst :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024)
    (hw : WordArrayMemory mem src words) (hm : mem.size = dst)
    (hsrc : src + 32 * words.length ≤ dst) (hi : i + words.length = n)
    (hn : n < UInt256.size) (hend : dst + 32 * words.length < UInt256.size)
    (hc : ∀ w ∈ words, w.toNat < EVM.addressModulus)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD safeBytecode I g s0 ret
      (UInt256.ofNat (dst + 32 * words.length) :: R)
      (mem ++ wordBytes words) aw' rdata σ k' C' := by
  induction words generalizing i src dst mem aw k C with
  | nil =>
      have hin : i = n := by simpa using hi
      have h₁ := safeRuntime_block_10256_taken (by simp; omega)
        (by rw [hin, ult_zero (by omega)]; decide) (by jump_dest) h
      have h₂ := safeRuntime_block_10295 (by omega) hret h₁
      simpa only [List.length_nil, Nat.mul_zero, Nat.add_zero, wordBytes,
        ByteArray.append_empty] using (show ∃ aw' k' C', RD safeBytecode I g s0 ret
          (UInt256.ofNat dst :: R) mem aw' rdata σ k' C' from ⟨_, _, _, h₂⟩)
  | cons w ws ih =>
      have hi' : i < n := by simp only [List.length_cons] at hi; omega
      have hip := ulit_toNat' i (by omega)
      have hnp := ulit_toNat' n hn
      have hsp := ulit_toNat' src (by omega)
      have hdp := ulit_toNat' dst (by omega)
      have hload : memLoad (UInt256.ofNat src) mem = w := by
        apply mloadWordValue_of_readWithPadding (mem := mem)
          (by rw [hsp]; simp only [List.length_cons] at hsrc; omega)
        simpa only [hsp, Nat.mul_zero, Nat.add_zero] using hw 0 (by simp)
      have h₁ := safeRuntime_block_10256_fallthrough (by simp; omega)
        (by rw [ult_one (by rw [hip, hnp]; exact hi')]; decide) h
      obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_10265_packed
        (by simp; omega) (by jump_dest) h₁
      simp only [safeRuntime_block_10265_stack, safeRuntime_block_10265_memory,
        safeAddressMask, hload, solcAddrMask_clean_left (hc w (by simp)), hdp] at h₂
      have hsadd : UInt256.ofNat src + UInt256.ofNat 32 = UInt256.ofNat (src + 32) := by
        rw [u256_add_comm]
        exact u256_32_add_ofNat src
      have hiadd : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) :=
        u256_one_add_ofNat i
      have hdadd : UInt256.ofNat 32 + UInt256.ofNat dst = UInt256.ofNat (dst + 32) :=
        u256_32_add_ofNat dst
      rw [hsadd, hiadd, hdadd] at h₂
      have hw' := (hw.tail mem src w ws).writeAfter mem (src + 32) ws
        (by simp only [List.length_cons] at hsrc; omega) dst w
        (by simp only [List.length_cons] at hsrc; omega)
      have hm' : (writeWord mem dst w).size = dst + 32 := by
        rw [writeWord_sparse_size, hm, Nat.max_eq_right (by omega)]
      have hn' : i + 1 + ws.length = n := by simp only [List.length_cons] at hi; omega
      have hend' : dst + 32 + 32 * ws.length < UInt256.size := by
        simp only [List.length_cons] at hend
        omega
      obtain ⟨aw', k', C', h'⟩ := ih h₂ hw' hm'
        (by simp only [List.length_cons] at hsrc; omega) hn' hend'
        (fun v hv ↦ hc v (by simp [hv]))
      have hout : dst + 32 + 32 * ws.length = dst + 32 * (w :: ws).length := by simp; omega
      rw [hout] at h'
      change RD safeBytecode I g s0 ret _ ((writeWord mem dst w) ++ wordBytes ws)
        aw' rdata σ k' C' at h'
      rw [show writeWord mem dst w = mem ++ w.toByteArray from writeWordAtEnd mem w hm,
        ByteArray.append_assoc] at h'
      exact ⟨_, _, _, h'⟩

end Benchmarks.Safe
