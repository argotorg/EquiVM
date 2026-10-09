import Benchmarks.Morpho.MorphoBlue.ExtSloadsReturn
import Benchmarks.Morpho.MorphoBlue.ExtSloadsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoExtSloadsFinish {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C n : Nat}
    (ho : (calldataWord ee.calldata 4).toNat ≤ solcMaxU64) (hn : n ≤ solcMaxU64)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6955)
      (extSloadsReadStack (calldataWord ee.calldata 4) n 0
        [calldataWord ee.calldata 4, UInt256.ofNat 0]) (extSloadsHeaderMem n) aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ
      (wordBytes ([UInt256.ofNat 32, UInt256.ofNat n] ++ wordArrayWords (extSloadsWords σ ee) 0 n)) := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoExtSloadsReadLoop (v := v) (by simp) ho hn n (by omega) h
  let words := wordArrayWords (extSloadsWords σ ee) 0 n
  let mem := wordSequenceMemory (extSloadsHeaderMem n) 160 words
  have hsize : mem.size = 160 + 32 * n := by
    dsimp only [mem]
    rw [wordSequenceMemory_size _ (by rw [extSloadsHeader_size]),
      extSloadsHeader_size, wordArrayWords_length]
    omega
  have hfree : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat (160 + 32 * n) := by
    dsimp only [mem]
    rw [wordSequenceMemory_load_below _ (by rw [extSloadsHeader_size]; decide)
      (by decide) (by decide), extSloadsHeader_free]
  have hcount : memLoad (UInt256.ofNat 128) mem = UInt256.ofNat n := by
    dsimp only [mem]
    rw [wordSequenceMemory_load_below _ (by rw [extSloadsHeader_size])
      (by decide) (by decide), extSloadsHeader_length]
  have hloads : ∀ j, j < n → memLoad (UInt256.ofNat (160 + 32 * j)) mem = extSloadsWords σ ee j := by
    intro j hj
    have hj' : j < words.length := by rw [wordArrayWords_length]; exact hj
    have hf : 160 + 32 * words.length < UInt256.size := by
      rw [wordArrayWords_length]
      norm_num [solcMaxU64, UInt256.size] at hn ⊢; omega
    have hg := wordArrayWords_getElem (extSloadsWords σ ee) 0 n j hj
    rw [List.getElem?_eq_getElem hj', Nat.zero_add] at hg
    exact (wordSequenceMemory_getElem words hj' hf).trans (Option.some.inj hg)
  exact morphoExtSloadsReturn (v := v) (mem := mem) (extSloadsWords σ ee) (by simp)
    hn hsize hfree hcount hloads rd1

end Benchmarks.Morpho.MorphoBlue
