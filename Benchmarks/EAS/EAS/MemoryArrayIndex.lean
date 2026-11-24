import Benchmarks.EAS.EAS.ResolveOneCall
import Benchmarks.EAS.EAS.WordArrayMemory

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: indexing the list of consecutive EVM memory words.
theorem memoryWords_get (mem : ByteArray) (off n i : Nat) (hi : i < n) :
    (memoryWords mem off n)[i]'(by rw [memoryWords_length]; exact hi) =
      memLoad (UInt256.ofNat (off+32*i)) mem := by
  induction n generalizing off i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp only [memoryWords, List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero]
    | succ i =>
      simp only [memoryWords, List.getElem_cons_succ]
      rw [ih (off+32) i (by omega)]
      congr 2
      omega

theorem WordArrayMemoryView.get {mem : ByteArray} {ptr : UInt256} {words : List UInt256} {limit : Nat}
    (h : WordArrayMemoryView mem ptr words limit) (i : Nat) (hi : i < words.length) :
    memLoad (UInt256.ofNat (ptr.toNat+32+32*i)) mem = words[i] := by
  have hg := memoryWords_get mem (ptr.toNat+32) words.length i hi
  simpa only [h.words] using hg.symm

theorem easMemoryArrayFirst {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+4 ≤ 1024) (hn : memLoad ptr mem ≠ ⟨0⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5712⟩ (ptr::ret::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret
      (UInt256.ofNat (ptr.toNat+32)::R) mem aw' rdata σ k' C' := by
  obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_5712_fallthrough_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hn) rd
  obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_5720_packed (immWords := wordsOf (immStore v)) (by omega) hret rd1
  refine ⟨aw2,k2,C2,?_⟩
  have he : UInt256.ofNat 32+ptr = UInt256.ofNat (ptr.toNat+32) := by
    simpa only [u256_ofNat_toNat] using u256_32_add_ofNat ptr.toNat
  simpa only [easBlocks.eas_block_5720_stack, he] using rd2

theorem easMemoryArrayIndex {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {i len : Nat} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+5 ≤ 1024) (hi : i < len) (hlen : len < UInt256.size)
    (hprod : 32*i < UInt256.size) (hl : memLoad ptr mem = UInt256.ofNat len)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5725⟩ (ptr::UInt256.ofNat i::ret::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret
      (UInt256.ofNat (ptr.toNat+32+32*i)::R) mem aw' rdata σ k' C' := by
  obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_5725_fallthrough_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [hl, ult_one (by rw [ulit_toNat' _ (by omega), ulit_toNat' _ hlen]; exact hi)]; decide) rd
  obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_5735_packed (immWords := wordsOf (immStore v)) hstack hret rd1
  refine ⟨aw2,k2,C2,?_⟩
  have he : (UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)+ptr)+UInt256.ofNat 32 =
      UInt256.ofNat (ptr.toNat+32+32*i) := by
    change (UInt256.shiftLeft (UInt256.ofNat i) ⟨5⟩+ptr)+UInt256.ofNat 32 = _
    rw [shiftLeft5_ofNat_eq hprod]
    apply u256_inj
    rw [uadd_toNat, uadd_toNat, ulit_toNat' _ hprod]
    change ((32*i+ptr.toNat)%UInt256.size+32)%UInt256.size = (ptr.toNat+32+32*i)%UInt256.size
    rw [Nat.mod_add_mod]
    congr 1
    omega
  simpa only [easBlocks.eas_block_5735_stack, he] using rd2

end Benchmarks.EAS.EAS
