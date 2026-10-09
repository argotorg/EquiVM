import Benchmarks.Morpho.MorphoBlue.ExtSloadsPrepare

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoExtSloadsCopyLoop {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {rdata : ByteArray} {σ : AccountMap} {n : Nat} {free : UInt256}
    {R : List UInt256} (values : Nat → UInt256)
    (hstack : R.length + 9 ≤ 1024) (hn : n < UInt256.size) (remaining : Nat) :
    ∀ {i src dst k C : Nat} {mem : ByteArray} {aw : UInt256},
      i + remaining = n → src + 32 * remaining ≤ mem.size →
      src + 32 * remaining ≤ dst → dst + 32 * remaining < UInt256.size →
      (∀ j, j < remaining → memLoad (UInt256.ofNat (src + 32 * j)) mem = values (i + j)) →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6991)
        ([UInt256.ofNat i, UInt256.ofNat 32, UInt256.ofNat n, UInt256.ofNat src,
          UInt256.ofNat dst, free, free] ++ R) mem aw rdata σ k C →
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6999)
        ([UInt256.ofNat n, UInt256.ofNat 32, UInt256.ofNat n,
          UInt256.ofNat (src + 32 * remaining), UInt256.ofNat (dst + 32 * remaining), free, free] ++ R)
        (wordSequenceMemory mem dst (wordArrayWords values i remaining)) aw' rdata σ k' C' := by
  induction remaining with
  | zero =>
      intro i src dst k C mem aw hi hmem hdis hfit hload h
      have hei : i = n := by omega
      subst i
      have rd := morphoBlocks.morpho_block_6991_fallthrough (immWords := wordsOf (immStore v))
        (by change R.length + 9 ≤ 1024; exact hstack) (ult_zero (le_refl _)) h
      exact ⟨_, _, _, rd⟩
  | succ remaining ih =>
      intro i src dst k C mem aw hi hmem hdis hfit hload h
      have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat n) = ⟨1⟩ :=
        ult_one (by rw [UInt256.toNat_ofNat_of_lt (by omega : i < UInt256.size),
          UInt256.toNat_ofNat_of_lt hn]; omega)
      have rd0 := morphoBlocks.morpho_block_6991_taken (immWords := wordsOf (immStore v))
        (by change R.length + 9 ≤ 1024; exact hstack) (by rw [hlt]; decide)
        (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
      obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_7006_packed
        (immWords := wordsOf (immStore v)) (by change R.length + 9 ≤ 1024; exact hstack)
        (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd0
      have hword : memLoad (UInt256.ofNat src) mem = values i := by
        simpa only [Nat.mul_zero, Nat.add_zero] using hload 0 (by omega)
      change RD _ _ _ _ _
        ([UInt256.ofNat 1 + UInt256.ofNat i, UInt256.ofNat 32, UInt256.ofNat n,
          UInt256.ofNat 32 + UInt256.ofNat src, UInt256.ofNat 32 + UInt256.ofNat dst, free, free] ++ R)
        ((memLoad (UInt256.ofNat src) mem).toByteArray.write 0 mem (UInt256.ofNat dst).toNat 32)
        aw1 rdata σ k1 C1 at rd1
      rw [hword, ofNat_add_words, ofNat_add_words, ofNat_add_words,
        UInt256.toNat_ofNat_of_lt (by omega : dst < UInt256.size),
        show 1 + i = i + 1 by omega, show 32 + src = src + 32 by omega,
        show 32 + dst = dst + 32 by omega] at rd1
      have hnext : ∀ j, j < remaining →
          memLoad (UInt256.ofNat (src + 32 + 32 * j)) (writeWord mem dst (values i)) =
            values (i + 1 + j) := by
        intro j hj
        unfold Reasoning.Theory.writeWord
        rw [memLoad_write_disjoint _ _ _ _
          (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)
          (.inl (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)),
          show src + 32 + 32 * j = src + 32 * (j + 1) by omega, hload (j + 1) (by omega)]
        congr 1; omega
      obtain ⟨aw2, k2, C2, rd2⟩ := ih (by omega)
        (by rw [writeWord_sparse_size]; omega) (by omega) (by omega) hnext rd1
      refine ⟨aw2, k2, C2, ?_⟩
      simpa only [wordArrayWords, wordSequenceMemory,
        show src + 32 + 32 * remaining = src + 32 * (remaining + 1) by omega,
        show dst + 32 + 32 * remaining = dst + 32 * (remaining + 1) by omega] using rd2

theorem morphoExtSloadsReturn {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C n : Nat} {off : UInt256} {R : List UInt256} (values : Nat → UInt256)
    (hstack : R.length + 13 ≤ 1024) (hn : n ≤ solcMaxU64)
    (hs : mem.size = 160 + 32 * n)
    (hfree : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat (160 + 32 * n))
    (hcount : memLoad (UInt256.ofNat 128) mem = UInt256.ofNat n)
    (hloads : ∀ j, j < n → memLoad (UInt256.ofNat (160 + 32 * j)) mem = values j)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6963)
      (extSloadsReadStack off n n R) mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ
      (wordBytes ([UInt256.ofNat 32, UInt256.ofNat n] ++ wordArrayWords values 0 n)) := by
  let f := 160 + 32 * n
  have hf : f + 64 + 32 * n < UInt256.size := by
    norm_num [solcMaxU64, UInt256.size] at hn ⊢
    dsimp only [f]; omega
  have hfn : (UInt256.ofNat f).toNat = f := UInt256.toNat_ofNat_of_lt (by omega)
  have hpre : memLoad (UInt256.ofNat 128) ((UInt256.ofNat 32).toByteArray.write 0 mem f 32) =
      UInt256.ofNat n := by
    rw [memLoad_write_disjoint _ _ _ _ (by rw [hs]; change 160 ≤ _; omega)
      (.inl (by change 160 ≤ f; dsimp only [f]; omega)), hcount]
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_6963_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 9 ≤ 1024; omega) h
  dsimp only [morphoBlocks.morpho_block_6963_stack, morphoBlocks.morpho_block_6963_memory] at rd1
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat f at hfree
  rw [hfree, hfn, hpre, ofNat_add_words, ofNat_add_words,
    UInt256.toNat_ofNat_of_lt (by omega : f + 32 < UInt256.size)] at rd1
  let header := writeWord (writeWord mem f (UInt256.ofNat 32)) (f + 32) (UInt256.ofNat n)
  have hheader : header.size = f + 64 := by
    simp only [header, writeWord_sparse_size, hs]
    dsimp only [f]; omega
  have hdata : ∀ j, j < n → memLoad (UInt256.ofNat (160 + 32 * j)) header = values j := by
    intro j hj
    have hjn : (UInt256.ofNat (160 + 32 * j)).toNat = 160 + 32 * j :=
      UInt256.toNat_ofNat_of_lt (by dsimp only [f] at hf; omega)
    unfold header Reasoning.Theory.writeWord
    rw [memLoad_write_disjoint _ _ _ _
      (by rw [hjn, wordWrite_size, hs]; omega)
      (.inl (by rw [hjn]; dsimp only [f]; omega)),
      memLoad_write_disjoint _ _ _ _ (by rw [hjn, hs]; omega)
      (.inl (by rw [hjn]; dsimp only [f]; omega)), hloads j hj]
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoExtSloadsCopyLoop (v := v) values (by omega)
    (by dsimp only [f] at hf; omega) n (mem := header) (R := R) (i := 0) (src := 160) (dst := f + 64)
    (by omega) (by rw [hheader]; dsimp only [f]; omega) (by dsimp only [f]; omega) hf
    (by simpa only [Nat.zero_add] using hdata) rd1
  have hr := morphoBlocks.morpho_block_6999 (immWords := wordsOf (immStore v))
    (by change R.length + 7 ≤ 1024; omega) rd2
  have hret : (UInt256.sub (UInt256.ofNat (f + 64 + 32 * n)) (UInt256.ofNat f)).toNat =
      64 + 32 * n := by
    rw [usub_ofNat_lit_toNat (by omega) hf]; omega
  change RDret _ _ _ _ ((wordSequenceMemory header (f + 64) (wordArrayWords values 0 n)).readWithPadding
    (UInt256.ofNat f).toNat (UInt256.sub (UInt256.ofNat (f + 64 + 32 * n)) (UInt256.ofNat f)).toNat) at hr
  rw [hfn, hret] at hr
  have hmem : wordSequenceMemory header (f + 64) (wordArrayWords values 0 n) =
      wordSequenceMemory mem f ([UInt256.ofNat 32, UInt256.ofNat n] ++ wordArrayWords values 0 n) := by
    simp only [List.cons_append, List.nil_append, wordSequenceMemory, header]
  rw [hmem] at hr
  have hlen : 64 + 32 * n = 32 *
      ([UInt256.ofNat 32, UInt256.ofNat n] ++ wordArrayWords values 0 n).length := by
    simp only [List.length_append, List.length_cons, List.length_nil, wordArrayWords_length]; omega
  rwa [hlen, wordSequenceMemory_read] at hr

end Benchmarks.Morpho.MorphoBlue
