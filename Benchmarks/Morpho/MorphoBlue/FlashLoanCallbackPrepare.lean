import Benchmarks.Morpho.MorphoBlue.FinalizeVoid

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def flashLoanCallbackMem (ee : ExecutionEnv) (mem : ByteArray) (ptr assets srcOff len : UInt256) : ByteArray :=
  wordBytesCallMem flashLoanCallbackSelectorWord assets ee.calldata mem srcOff.toNat ptr.toNat len.toNat

theorem morphoFlashLoanCallbackNoCode {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw srcOff len assets token : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 20 ≤ 1024)
    (hc : extCodeSizeWord σ (UInt256.ofNat ee.source.val) = UInt256.ofNat 0)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1113)
      ([srcOff, len, UInt256.ofNat 0, assets, token, UInt256.ofNat 0] ++ R) mem aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨a, k, C, rd⟩ := morphoBlocks.morpho_block_1113_taken_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 6 + 2 ≤ 1024; omega)
    (by rw [hc]; decide) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoBlocks.morpho_block_1234 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 5 ≤ 1024; omega) rd

theorem morphoFlashLoanCallbackPrepare {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr srcOff len assets token : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 20 ≤ 1024)
    (hm : MorphoHeap mem ptr 0) (hlen : len.toNat ≤ solcMaxU64)
    (hc : extCodeSizeWord σ (UInt256.ofNat ee.source.val) ≠ UInt256.ofNat 0)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1113)
      ([srcOff, len, UInt256.ofNat 0, assets, token, UInt256.ofNat 0] ++ R) mem aw out σ k C) :
    ∃ gasArg aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1185)
      ([gasArg, UInt256.ofNat ee.source.val, UInt256.ofNat 0, ptr,
        UInt256.ofNat (100 + paddedSize len.toNat), ptr, UInt256.ofNat 0,
        ptr, UInt256.ofNat 0, assets, token, UInt256.ofNat 0] ++ R)
      (flashLoanCallbackMem ee mem ptr assets srcOff len) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_1113_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 6 + 2 ≤ 1024; omega)
    (isZero_eq_zero_of_ne hc) h
  obtain ⟨a2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_1121_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 12 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  dsimp only [morphoBlocks.morpho_block_1121_stack, morphoBlocks.morpho_block_1121_memory] at rd2
  rw [hm.free] at rd2
  obtain ⟨a3, k3, C3, rd3⟩ := morphoWordBytesEncode (v := v) flashLoanCallbackSelectorWord
    (by change R.length + 8 + 11 ≤ 1024; omega) (by have hs := hm.space; omega) hlen
    (by rw [morphoPatchedValidJumps v]; jump_dest) rd2
  obtain ⟨a4, k4, C4, rd4⟩ := morphoBlocks.morpho_block_1179_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 5 + 7 ≤ 1024; omega) rd3
  dsimp only [morphoBlocks.morpho_block_1179_stack] at rd4
  rw [word_add_sub_left] at rd4
  exact ⟨_, a4, k4, C4, rd4⟩

end Benchmarks.Morpho.MorphoBlue
