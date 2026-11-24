import Benchmarks.EAS.EAS.Entry

variable {fork : Ethereum.Fork}

/-! # EAS memory-copy loop and dynamic-byte ABI encoder -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def easCopyWords (src dst : UInt256) (mem : ByteArray) (i : Nat) : Nat → ByteArray
  | 0 => mem
  | n + 1 => easCopyWords src dst
      (Reasoning.Theory.writeWord mem (UInt256.ofNat i + dst).toNat
        (memLoad (UInt256.ofNat i + src) mem)) (i + 32) n

theorem easCopyLoop {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {src dst len ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (i n : Nat) (hstack : R.length + 8 ≤ 1024)
    (hbound : i + 32 * n < UInt256.size)
    (hbefore : n > 0 → i + 32 * (n - 1) < len.toNat)
    (hafter : len.toNat ≤ i + 32 * n)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4403⟩
      (UInt256.ofNat i :: src :: dst :: len :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret R
      (Reasoning.Theory.writeWord (easCopyWords src dst mem i n) (len + dst).toNat ⟨0⟩)
      aw' rdata σ k' C' := by
  induction n generalizing mem aw k C i with
  | zero =>
    have hi : i < UInt256.size := by simpa only [Nat.mul_zero, Nat.add_zero] using hbound
    have rd1 := easBlocks.eas_block_4403_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (ult_zero (by rw [ulit_toNat' _ hi]; simpa only [Nat.mul_zero, Nat.add_zero] using hafter)) rd
    obtain ⟨aw', k', C', rd2⟩ := easBlocks.eas_block_4411_packed (immWords := wordsOf (immStore v))
      (by omega) hvalid rd1
    exact ⟨aw', k', C', rd2⟩
  | succ n ih =>
    have hi : i < UInt256.size := by omega
    have hlt : i < len.toNat := by have := hbefore (by omega); omega
    have rd1 := easBlocks.eas_block_4403_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [ult_one (by rw [ulit_toNat' _ hi]; exact hlt)]; decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw', k', C', rd2⟩ := easBlocks.eas_block_4419_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
    have hstep : UInt256.ofNat 32 + UInt256.ofNat i = UInt256.ofNat (i + 32) := u256_32_add_ofNat i
    simp only [easBlocks.eas_block_4419_stack, hstep] at rd2
    exact ih (i + 32) (by omega) (by intro hn; have := hbefore (by omega); omega)
      (by omega) rd2

theorem easCopy {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {src dst len ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 8 ≤ 1024) (hbound : len.toNat + 31 < UInt256.size)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4400⟩ (src :: dst :: len :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret R
      (Reasoning.Theory.writeWord (easCopyWords src dst mem 0 ((len.toNat + 31) / 32))
        (len + dst).toNat ⟨0⟩) aw' rdata σ k' C' := by
  have rd1 := easBlocks.eas_block_4400 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) rd
  exact easCopyLoop v 0 ((len.toNat + 31) / 32) hstack (by omega)
    (by intro hn; omega) (by omega) hvalid rd1

def easEncodeBytesMemory (src dst : UInt256) (mem : ByteArray) : ByteArray :=
  let len := memLoad src mem
  let mem' := Reasoning.Theory.writeWord mem dst.toNat len
  Reasoning.Theory.writeWord
    (easCopyWords (src + ⟨32⟩) (dst + ⟨32⟩) mem' 0 ((len.toNat + 31) / 32))
    (len + (dst + ⟨32⟩)).toNat ⟨0⟩

theorem easEncodeBytes {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {src dst ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 14 ≤ 1024) (hbound : (memLoad src mem).toNat + 31 < UInt256.size)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4435⟩ (src :: dst :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret
      (((UInt256.land (memLoad src mem + ⟨31⟩) (UInt256.lnot ⟨31⟩) + dst) + ⟨32⟩) :: R)
      (easEncodeBytesMemory src dst mem) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := easBlocks.eas_block_4435_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨aw2, k2, C2, rd2⟩ := easCopy v (by simp only [List.length_cons]; omega) hbound
    (by rw [easPatchedValidJumps v]; jump_dest) rd1
  obtain ⟨aw3, k3, C3, rd3⟩ := easBlocks.eas_block_4495_packed (immWords := wordsOf (immStore v))
    (by omega) hvalid rd2
  exact ⟨aw3, k3, C3, rd3⟩

end Benchmarks.EAS.EAS
