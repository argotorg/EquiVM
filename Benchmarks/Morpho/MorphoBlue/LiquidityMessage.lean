import Benchmarks.Morpho.MorphoBlue.ReturnDataMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def morphoLiquidityMem (mem : ByteArray) : ByteArray :=
  morphoErrorMem (UInt256.ofNat 22)
    (UInt256.ofNat 47687999144296217495830161024901027589677182894640623885992664163599792472064) mem

theorem morphoLiquidityMessage {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr) (hfit : ptr.toNat + 64 < 2 ^ 64)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12880) (ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret (ptr :: R)
      (morphoLiquidityMem mem) aw' out σ k' C' := by
  obtain ⟨a0, k0, C0, rd0⟩ := morphoBlocks.morpho_block_12880_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [morphoBlocks.morpho_block_12880_stack] at rd0
  rw [hfree] at rd0
  have hp := uadd_word_ofNat_toNat ptr 64 (by change _ < 2 ^ 256; omega)
  obtain ⟨a1, k1, C1, rd1⟩ := morphoAlloc64 (v := v)
    (by change R.length + 2 + 5 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest)
    (by rw [ugt_zero (by rw [hp]; change _ ≤ 18446744073709551615; omega),
      ult_zero (by rw [hp]; omega)]; rfl) rd0
  obtain ⟨a2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_12893_packed
    (immWords := wordsOf (immStore v)) (by omega) hvalid rd1
  refine ⟨a2, k2, C2, ?_⟩
  dsimp only [morphoLiquidityMem, morphoErrorMem]
  rw [hfree]
  exact rd2

end Benchmarks.Morpho.MorphoBlue
