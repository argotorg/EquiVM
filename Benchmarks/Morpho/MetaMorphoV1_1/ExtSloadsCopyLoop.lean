import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsDecodeAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_065

/-! Word-copy loop used by the compiled `bytes32[]` return decoder. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem extSloadsCopyLoop {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C src dst : Nat} {ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (words : List UInt256)
    (hstack : R.length + 8 ≤ 1024)
    (hsrc : src + 32 * words.length ≤ mem.size)
    (hsep : src + 32 * words.length ≤ dst)
    (hdst : dst + 32 * words.length < UInt256.size)
    (hread : ∀ i (hi : i < words.length),
      memLoad (UInt256.ofNat (src + 32 * i)) mem = words[i])
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨13313⟩
      (UInt256.ofNat dst :: UInt256.ofNat src :: UInt256.ofNat (src + 32 * words.length) ::
        ptr :: ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (ptr :: R)
      (wordSequenceMemory mem dst words) aw' out σ k' C' := by
  induction words generalizing src dst mem aw k C with
  | nil =>
      simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at rd
      have h1 := metaMorphoV1_1_block_13313_fallthrough
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (ult_zero (by omega)) rd
      obtain ⟨aw', k', C', h2⟩ := metaMorphoV1_1_block_13321_packed
        (immWords := wordsOf (immStore v)) (by omega) hret h1
      exact ⟨aw', k', C', h2⟩
  | cons word words ih =>
      have hsfit : src < UInt256.size := by simp only [List.length_cons] at hsep hdst; omega
      have hefit : src + 32 * (word :: words).length < UInt256.size := by omega
      have hd0 : dst < UInt256.size := by omega
      have hload : memLoad (UInt256.ofNat src) mem = word := by
        simpa only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] using hread 0 (by simp)
      have h1 := metaMorphoV1_1_block_13313_taken
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [ult_one (by
              rw [UInt256.toNat_ofNat_of_lt hsfit, UInt256.toNat_ofNat_of_lt hefit]
              simp only [List.length_cons]; omega)]
            decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      obtain ⟨aw1, k1, C1, h2⟩ := metaMorphoV1_1_block_13326_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
      have hend : src + 32 * (word :: words).length = src + 32 + 32 * words.length := by
        simp only [List.length_cons]; omega
      simp only [metaMorphoV1_1_block_13326_stack, metaMorphoV1_1_block_13326_memory,
        hload, UInt256.toNat_ofNat_of_lt hd0, ofNat_add_words, hend,
        show 32 + dst = dst + 32 from by omega,
        show 32 + src = src + 32 from by omega] at h2
      have hcopy : ∀ i (hi : i < words.length),
          memLoad (UInt256.ofNat (src + 32 + 32 * i)) (writeWord mem dst word) = words[i] := by
        intro i hi
        have hb : src + 32 + 32 * i + 32 ≤ mem.size := by
          simp only [List.length_cons] at hsrc
          omega
        have hf : src + 32 + 32 * i < UInt256.size := by
          simp only [List.length_cons] at hsep hdst
          omega
        rw [memLoad_write_above mem _ dst word
          (by rw [UInt256.toNat_ofNat_of_lt hf]; exact hb)
          (by rw [UInt256.toNat_ofNat_of_lt hf]; simp only [List.length_cons] at hsep; omega)]
        have hr := hread (i + 1) (by simp only [List.length_cons]; omega)
        simpa only [show src + 32 * (i + 1) = src + 32 + 32 * i from by omega,
          List.getElem_cons_succ] using hr
      exact ih
        (by rw [writeWord_sparse_size]; simp only [List.length_cons] at hsrc; omega)
        (by simp only [List.length_cons] at hsep; omega)
        (by simp only [List.length_cons] at hdst; omega) hcopy h2

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
