import Benchmarks.EAS.EAS.CopyEncodeViews
import Benchmarks.EAS.EAS.EncodeValuesSource
import Benchmarks.EAS.EAS.RuntimeBlocks_018

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

inductive WordCopySite where
  | resolver | returned
def WordCopySite.pc : WordCopySite → UInt256
  | .resolver => ⟨14327⟩ | .returned => ⟨4365⟩

-- Both ABI word-copy loops use the same sequential-copy memory model.
theorem easEncodeWordLoop {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ret : UInt256} {R : List UInt256} (v : EASImmutables) (site : WordCopySite)
    (src dst len i n : Nat) (hn : i+n=len)
    (hstack : R.length+7 ≤ 1024)
    (hsrc : src+32*len < UInt256.size) (hdst : dst+32*len < UInt256.size)
    (hlen : len < UInt256.size)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 site.pc
      (UInt256.ofNat i::UInt256.ofNat len::UInt256.ofNat (src+32*i)::UInt256.ofNat (dst+32*i)::ret::R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (UInt256.ofNat (dst+32*len)::R)
      (easCopyWords (UInt256.ofNat src) (UInt256.ofNat dst) mem (32*i) n) aw' rdata σ k' C' := by
  induction n generalizing i mem aw k C with
  | zero =>
    have hi : i=len := by omega
    subst i
    have hc : UInt256.lt (UInt256.ofNat len) (UInt256.ofNat len) = ⟨0⟩ := ult_zero (le_refl _)
    cases site with
    | resolver =>
      have rd1 := easBlocks.eas_block_14327_fallthrough (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc rd
      exact easBlocks.eas_block_14335_packed (immWords := wordsOf (immStore v)) (by omega) hvalid rd1
    | returned =>
      have rd1 := easBlocks.eas_block_4365_fallthrough (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc rd
      exact easBlocks.eas_block_4373_packed (immWords := wordsOf (immStore v)) (by omega) hvalid rd1
  | succ n ih =>
    have hi : i < len := by omega
    have hin : i < UInt256.size := by omega
    have hc : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat len) ≠ ⟨0⟩ := by
      rw [ult_one (by rw [ulit_toNat' _ hin, ulit_toNat' _ hlen]; exact hi)]
      decide
    have hstep : ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 site.pc
        ((UInt256.ofNat 1+UInt256.ofNat i)::UInt256.ofNat len::
          (UInt256.ofNat (src+32*i)+UInt256.ofNat 32)::(UInt256.ofNat 32+UInt256.ofNat (dst+32*i))::ret::R)
        (Reasoning.Theory.writeWord mem (UInt256.ofNat (dst+32*i)).toNat
          (memLoad (UInt256.ofNat (src+32*i)) mem)) aw' rdata σ k' C' := by
      cases site with
      | resolver =>
        have rd1 := easBlocks.eas_block_14327_taken (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
        obtain ⟨a,j,D,h⟩ := easBlocks.eas_block_14340_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
        exact ⟨a,j,D,by simpa only [easBlocks.eas_block_14340_stack,easBlocks.eas_block_14340_memory,
          Reasoning.Theory.writeWord] using h⟩
      | returned =>
        have rd1 := easBlocks.eas_block_4365_taken (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
        obtain ⟨a,j,D,h⟩ := easBlocks.eas_block_4378_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
        exact ⟨a,j,D,by simpa only [easBlocks.eas_block_4378_stack,easBlocks.eas_block_4378_memory,
          Reasoning.Theory.writeWord] using h⟩
    obtain ⟨aw1,k1,C1,rd2⟩ := hstep
    have hinc : UInt256.ofNat 1+UInt256.ofNat i = UInt256.ofNat (i+1) := u256_one_add_ofNat i
    have hsrcinc : UInt256.ofNat (src+32*i)+UInt256.ofNat 32 = UInt256.ofNat (src+32*(i+1)) := by
      rw [u256_add_comm]
      change (⟨32⟩ : UInt256)+UInt256.ofNat (src+32*i) = _
      rw [u256_32_add_ofNat]
      congr 1
    have hdstinc : UInt256.ofNat 32+UInt256.ofNat (dst+32*i) = UInt256.ofNat (dst+32*(i+1)) := by
      change (⟨32⟩ : UInt256)+UInt256.ofNat (dst+32*i) = _
      rw [u256_32_add_ofNat]
      congr 1
    simp only [hinc, hsrcinc, hdstinc] at rd2
    have hcsrc : UInt256.ofNat (32*i)+UInt256.ofNat src = UInt256.ofNat (src+32*i) := by
      apply u256_inj
      change (UInt256.add (UInt256.ofNat (32*i)) (UInt256.ofNat src)).toNat = _
      rw [uadd_ofNat_toNat (by omega) (by omega) (by omega), ulit_toNat' _ (by omega)]
      omega
    have hcdst : UInt256.ofNat (32*i)+UInt256.ofNat dst = UInt256.ofNat (dst+32*i) := by
      apply u256_inj
      change (UInt256.add (UInt256.ofNat (32*i)) (UInt256.ofNat dst)).toNat = _
      rw [uadd_ofNat_toNat (by omega) (by omega) (by omega), ulit_toNat' _ (by omega)]
      omega
    have hr := ih (i+1) (by omega) rd2
    simpa only [easCopyWords, hcsrc, hcdst, show 32*i+32=32*(i+1) by omega,
      Reasoning.Theory.writeWord] using hr



theorem easEncodeWordValues {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {src dst ret : UInt256} {R : List UInt256} (v : EASImmutables) (site : WordCopySite)
    (words : List UInt256) (hstack : R.length+7 ≤ 1024)
    (hlo : 96 ≤ src.toNat) (hdisj : src.toNat+32*words.length ≤ dst.toNat)
    (hin : src.toNat+32*words.length ≤ mem.size)
    (hbound : dst.toNat+32*words.length < UInt256.size)
    (hwords : memoryWords mem src.toNat words.length = words)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 site.pc
      (⟨0⟩::UInt256.ofNat words.length::src::dst::ret::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (UInt256.ofNat (dst.toNat+32*words.length)::R)
      (writeWordSequence mem dst.toNat words) aw' rdata σ k' C' := by
  have hl : words.length < UInt256.size := by omega
  obtain ⟨aw1,k1,C1,rd1⟩ := easEncodeWordLoop v site src.toNat dst.toNat words.length 0 words.length (by omega)
    hstack (by omega) hbound hl hvalid
    (by simpa only [Nat.mul_zero, Nat.add_zero, u256_ofNat_toNat] using rd)
  have hm := easCopyWords_eq_sequence src dst mem 0 words.length
    (by omega) (by omega) (by omega) (by omega)
  simp only [Nat.add_zero, hwords] at hm
  simpa only [Nat.mul_zero, u256_ofNat_toNat, hm] using (show ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret
    (UInt256.ofNat (dst.toNat+32*words.length)::R)
    (easCopyWords (UInt256.ofNat src.toNat) (UInt256.ofNat dst.toNat) mem (32*0) words.length) aw' rdata σ k' C' from ⟨aw1,k1,C1,rd1⟩)

end Benchmarks.EAS.EAS
