import Benchmarks.Morpho.MorphoBlue.FlashLoanCallbackPrepare

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoFlashLoanCallbackFailure {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr assets token : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 20 ≤ 1024)
    (hout : out.size < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1186)
      ([UInt256.ofNat 0, ptr, UInt256.ofNat 0, assets, token, UInt256.ofNat 0] ++ R) mem aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_1186_taken_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 5 + 3 ≤ 1024; omega)
    (by decide) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoBlocks.morpho_block_1238 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 7 ≤ 1024; omega)
    (by rw [UInt256.toNat_ofNat_of_lt hout]; change 0 + out.size ≤ out.size; omega) rd1

theorem morphoFlashLoanCallbackSuccess {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr assets token : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 20 ≤ 1024)
    (hptr : ptr.toNat < 2 ^ 64)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1186)
      ([UInt256.ofNat 1, ptr, UInt256.ofNat 0, assets, token, UInt256.ofNat 0] ++ R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15033)
      ([token, UInt256.ofNat ee.source.val, UInt256.ofNat ee.codeOwner.val, assets,
        UInt256.ofNat 1211, UInt256.ofNat 0] ++ R) (writeWord mem 64 ptr) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_1186_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 5 + 3 ≤ 1024; omega) (by rfl) h
  obtain ⟨a2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_1192_taken_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 5 + 2 ≤ 1024; omega)
    (by decide) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  obtain ⟨a3, k3, C3, rd3⟩ := morphoBlocks.morpho_block_1214_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 4 + 3 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  obtain ⟨a4, k4, C4, rd4⟩ := morphoFinalizeVoid (v := v)
    (by change R.length + 4 + 4 ≤ 1024; omega) hptr
    (by rw [morphoPatchedValidJumps v]; jump_dest) rd3
  obtain ⟨a5, k5, C5, rd5⟩ := morphoBlocks.morpho_block_1223_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega) rfl rd4
  obtain ⟨a6, k6, C6, rd6⟩ := morphoBlocks.morpho_block_1228_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 6 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd5
  exact morphoBlocks.morpho_block_1196_packed (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 6 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd6

end Benchmarks.Morpho.MorphoBlue
