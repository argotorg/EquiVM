import Benchmarks.Morpho.MorphoBlue.ExtSloadsDecode
import Benchmarks.Morpho.MorphoBlue.ExtSloadsSourceStep
import Benchmarks.EAS.Attester.WordArrayABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def extSloadsReadStack (off : UInt256) (n i : Nat) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat i, off, UInt256.ofNat 36, UInt256.ofNat n, UInt256.ofNat 5,
   UInt256.ofNat 0, UInt256.ofNat 160, UInt256.ofNat 32, UInt256.ofNat 128] ++ R

def extSloadsWords (σ : AccountMap) (I : ExecutionEnv) (i : Nat) : UInt256 :=
  solcSlotWordAt (extSloadsSlot I i) σ I

theorem morphoExtSloadsReadStep {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C n i : Nat} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (ho : (calldataWord ee.calldata 4).toNat ≤ solcMaxU64) (hn : n ≤ solcMaxU64) (hi : i < n)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6955)
      (extSloadsReadStack (calldataWord ee.calldata 4) n i R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6955)
      (extSloadsReadStack (calldataWord ee.calldata 4) n (i + 1) R)
      (writeWord mem (160 + 32 * i) (extSloadsWords σ ee i)) aw' rdata σ k' C' := by
  have hf : 160 + 32 * (i + 1) < UInt256.size := by
    norm_num [solcMaxU64, UInt256.size] at hn ⊢; omega
  have hnf : n < UInt256.size := by
    norm_num [solcMaxU64, UInt256.size] at hn ⊢; omega
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat n) = ⟨1⟩ :=
    ult_one (by rw [UInt256.toNat_ofNat_of_lt (by omega : i < UInt256.size),
      UInt256.toNat_ofNat_of_lt hnf]; exact hi)
  have rd0 := morphoBlocks.morpho_block_6955_taken (immWords := wordsOf (immStore v))
    (by simp only [extSloadsReadStack, List.append, List.length_cons, List.length_append, List.length_nil, Nat.zero_add]; omega)
    (by rw [hlt]; decide) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  have rd1 := morphoBlocks.morpho_block_7029 (immWords := wordsOf (immStore v))
    (by change R.length + 12 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd0
  have hne : UInt256.eq (UInt256.ofNat i)
      (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) =
      UInt256.ofNat 0 := by
    apply uInt256_eq_zero_of_ne
    intro he
    have he' := congrArg UInt256.toNat (uInt256_eq_one_eq he)
    rw [UInt256.toNat_ofNat_of_lt (by omega : i < UInt256.size)] at he'
    change i = 115792089237316195423570985008687907853269984665640564039457584007913129639935 at he'
    norm_num [solcMaxU64] at hn
    omega
  have rd2 := morphoBlocks.morpho_block_13051_fallthrough (immWords := wordsOf (immStore v))
    (by change R.length + 13 ≤ 1024; omega) hne rd1
  have rd3 := morphoBlocks.morpho_block_13091 (immWords := wordsOf (immStore v))
    (by change R.length + 12 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  have rd4 := morphoBlocks.morpho_block_7043_fallthrough (immWords := wordsOf (immStore v))
    (by change R.length + 12 ≤ 1024; omega) (by rw [hlt]; rfl) rd3
  obtain ⟨aw', k', C', rd5⟩ := morphoBlocks.morpho_block_7053_packed
    (immWords := wordsOf (immStore v))
    (by change R.length + 12 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd4
  have hinc : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) := by
    rw [ofNat_add_words, Nat.add_comm]
  have hsh : UInt256.shiftLeft (UInt256.ofNat (i + 1)) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * (i + 1)) := shiftLeft5_ofNat_eq (by omega)
  have hdst : (UInt256.ofNat 128 +
      UInt256.shiftLeft (UInt256.ofNat (i + 1)) (UInt256.ofNat 5)).toNat = 160 + 32 * i := by
    rw [hsh, ofNat_add_words, UInt256.toNat_ofNat_of_lt (by omega)]
    omega
  have hsrc : (UInt256.ofNat 36 + (calldataWord ee.calldata 4 +
      UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5))).toNat =
      4 + (calldataWord ee.calldata 4).toNat + 32 + 32 * i := by
    rw [u256_add_comm, wordArrayEnd_toNat ho
      (by rw [UInt256.toNat_ofNat_of_lt (by omega : i < UInt256.size)]; omega),
      UInt256.toNat_ofNat_of_lt (by omega : i < UInt256.size)]
    omega
  refine ⟨aw', k', C', ?_⟩
  simpa only [morphoBlocks.morpho_block_7053_stack, morphoBlocks.morpho_block_7053_memory,
    hinc, hdst, hsrc] using rd5

theorem morphoExtSloadsReadLoop {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {rdata : ByteArray} {σ : AccountMap} {n : Nat} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (ho : (calldataWord ee.calldata 4).toNat ≤ solcMaxU64) (hn : n ≤ solcMaxU64)
    (remaining : Nat) :
    ∀ {i k C : Nat} {mem : ByteArray} {aw : UInt256}, i + remaining = n →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6955)
        (extSloadsReadStack (calldataWord ee.calldata 4) n i R) mem aw rdata σ k C →
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6963)
        (extSloadsReadStack (calldataWord ee.calldata 4) n n R)
        (wordSequenceMemory mem (160 + 32 * i) (wordArrayWords (extSloadsWords σ ee) i remaining))
        aw' rdata σ k' C' := by
  induction remaining with
  | zero =>
      intro i k C mem aw hi h
      have he : i = n := by omega
      subst i
      have rd := morphoBlocks.morpho_block_6955_fallthrough (immWords := wordsOf (immStore v))
        (by simp only [extSloadsReadStack, List.append, List.length_cons, List.length_append, List.length_nil, Nat.zero_add]; omega) (ult_zero (le_refl _)) h
      exact ⟨_, _, _, rd⟩
  | succ remaining ih =>
      intro i k C mem aw hi h
      obtain ⟨aw', k', C', rd⟩ := morphoExtSloadsReadStep (v := v) hstack ho hn (by omega) h
      obtain ⟨aw'', k'', C'', rd'⟩ := ih (by omega) rd
      refine ⟨aw'', k'', C'', ?_⟩
      simpa only [wordArrayWords, wordSequenceMemory,
        show 160 + 32 * (i + 1) = 160 + 32 * i + 32 by omega] using rd'

end Benchmarks.Morpho.MorphoBlue
