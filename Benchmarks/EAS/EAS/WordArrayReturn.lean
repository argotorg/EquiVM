import Benchmarks.EAS.EAS.WordCopyLoop
import Benchmarks.EAS.EAS.WordArrayMemory
import Benchmarks.EAS.EAS.StructEncode
import Benchmarks.EAS.EAS.RuntimeBlocks_012
import Benchmarks.EAS.EAS.RuntimeBlocks_003
import Benchmarks.EAS.Attester.WordArrayABI

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: specialize a functional word sequence to a finite list.
theorem wordArrayWords_list (words : List UInt256) :
    wordArrayWords (fun i => words[i]?.getD ⟨0⟩) 0 words.length = words := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < words.length
  · rw [wordArrayWords_getElem _ _ _ _ hi, Nat.zero_add, List.getElem?_eq_getElem hi, Option.getD_some]
  · rw [List.getElem?_eq_none (by rw [wordArrayWords_length]; omega), List.getElem?_eq_none (by omega)]

-- LIBRARY CANDIDATE: list form of the canonical bytes32-array return encoding.
theorem wordListReturn_encoding (words : List UInt256) :
    encodeReturnValue? (.dynamicArray abiBytes32) (.array (words.map wordBytes32Value)) =
      some (wordBytes ([UInt256.ofNat 32,UInt256.ofNat words.length]++words)) := by
  simpa only [wordArrayValues,wordArrayWords_list] using
    wordArrayReturn_encoding (fun i => words[i]?.getD ⟨0⟩) words.length

theorem easWordArrayReturn {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr heap : UInt256} {words : List UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+10 ≤ 1024)
    (hv : WordArrayMemoryView mem ptr words heap.toNat)
    (hh : heap.toNat ≤ 2^64-1) (hf : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨2797⟩ (ptr::⟨398⟩::R) mem aw rdata σ k C) :
    RDret fork (deployedRuntime v) g s0 σ (wordBytes ([UInt256.ofNat 32,UInt256.ofNat words.length]++words)) := by
  have hlo := hv.low
  have hspan := hv.span
  have hcovered := hv.covered
  have hb : heap.toNat+64+32*words.length < UInt256.size := by change _ < 2^256; omega
  have h32 : (heap+UInt256.ofNat 32).toNat = heap.toNat+32 := uadd_word_ofNat_toNat _ _ (by omega)
  have h64 : (heap+UInt256.ofNat 64).toNat = heap.toNat+64 := uadd_word_ofNat_toNat _ _ (by omega)
  have hp32 : (ptr+UInt256.ofNat 32).toNat = ptr.toNat+32 := uadd_word_ofNat_toNat _ _ (by omega)
  have hlength : memLoad ptr (Reasoning.Theory.writeWord mem heap.toNat (UInt256.ofNat 32)) = UInt256.ofNat words.length :=
    (memLoad_write_below mem heap.toNat ptr (UInt256.ofNat 32) (by omega) (by omega)).trans hv.length
  let head := writeWordSequence mem heap.toNat [⟨32⟩,UInt256.ofNat words.length]
  have hm : easBlocks.eas_block_4342_memory (mem := mem) (x0 := heap) (x1 := ptr) = head := by
    simp only [easBlocks.eas_block_4342_memory,← writeWord_as_write,hlength,h32]
    rfl
  have hpreserve := writeWordSequence_prefix mem heap.toNat heap.toNat [⟨32⟩,UInt256.ofNat words.length] (le_refl _)
  have hview := hv.preserve hpreserve (by omega)
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_2797_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_2797_stack,hf] at r1
  obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_4342_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) r1
  simp only [easBlocks.eas_block_4342_stack,← writeWord_as_write,hlength,hm] at r2
  obtain ⟨a3,k3,C3,r3⟩ := easEncodeWordValues (src := ptr+UInt256.ofNat 32) (dst := heap+UInt256.ofNat 64) (ret := ⟨398⟩) (R := heap::heap::R) v .returned words
    (by simp only [List.length_cons]; omega)
    (by rw [hp32]; omega) (by rw [hp32,h64]; omega)
    (by rw [hp32]; exact hview.covered) (by rw [h64]; exact hb)
    (by rw [hp32]; exact hview.words) (by rw [easPatchedValidJumps v]; jump_dest) r2
  have hr := easBlocks.eas_block_398 (immWords := wordsOf (immStore v)) (by omega) r3
  have hend : (UInt256.ofNat ((heap+UInt256.ofNat 64).toNat+32*words.length)).toNat =
      heap.toNat+64+32*words.length := by rw [h64,ulit_toNat' _ hb]
  have hsub : (UInt256.sub (UInt256.ofNat ((heap+UInt256.ofNat 64).toNat+32*words.length)) heap).toNat =
      32*([UInt256.ofNat 32,UInt256.ofNat words.length]++words).length := by
    rw [usub_toNat (by rw [hend]; omega),hend]
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega
  have hmemory : writeWordSequence head (heap+UInt256.ofNat 64).toNat words =
      writeWordSequence mem heap.toNat ([UInt256.ofNat 32,UInt256.ofNat words.length]++words) := by
    rw [writeWordSequence_append,h64]
    rfl
  simpa only [hsub,hmemory,writeWordSequence_read] using hr

end Benchmarks.EAS.EAS
