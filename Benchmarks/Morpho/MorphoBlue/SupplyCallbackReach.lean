import Benchmarks.Morpho.MorphoBlue.FinalizeVoid
import Benchmarks.Morpho.MorphoBlue.SupplyCallbackABI
import Benchmarks.Morpho.MorphoBlue.SupplyEvent

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def supplyCallbackMem (ee : ExecutionEnv) (mem : ByteArray) (ptr assets srcOff len : UInt256) : ByteArray :=
  wordBytesCallMem supplyCallbackSelectorWord assets ee.calldata mem srcOff.toNat ptr.toNat len.toNat

theorem morphoSupplyCallbackNoCode {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw srcOff len assets shares : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 24 ≤ 1024)
    (hc : extCodeSizeWord σ (UInt256.ofNat ee.source.val) = UInt256.ofNat 0)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 4218)
      (supplyCallbackTail assets shares srcOff len R) mem aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨a, k, C, rd⟩ := morphoBlocks.morpho_block_4218_taken_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 8 + 2 ≤ 1024; omega)
    (by rw [hc]; decide) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoBlocks.morpho_block_1234 (immWords := wordsOf (immStore v))
    (by change R.length + 5 + 5 ≤ 1024; omega) rd

theorem morphoSupplyCallbackPrepare {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr srcOff len assets shares : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 24 ≤ 1024)
    (hm : MorphoHeap mem ptr 0) (hlen : len.toNat ≤ solcMaxU64)
    (hc : extCodeSizeWord σ (UInt256.ofNat ee.source.val) ≠ UInt256.ofNat 0)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 4218)
      (supplyCallbackTail assets shares srcOff len R) mem aw out σ k C) :
    ∃ gasArg aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 4290)
      ([gasArg, UInt256.ofNat ee.source.val, UInt256.ofNat 0, ptr,
        UInt256.ofNat (100 + paddedSize len.toNat), ptr, UInt256.ofNat 0,
        ptr, UInt256.ofNat 0, UInt256.ofNat 128, UInt256.ofNat 32, shares, assets, solcAddrMask] ++ R)
      (supplyCallbackMem ee mem ptr assets srcOff len) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_4218_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 8 + 2 ≤ 1024; omega)
    (isZero_eq_zero_of_ne hc) h
  obtain ⟨a2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_4226_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 15 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  dsimp only [morphoBlocks.morpho_block_4226_stack, morphoBlocks.morpho_block_4226_memory] at rd2
  rw [hm.free] at rd2
  obtain ⟨a3, k3, C3, rd3⟩ := morphoWordBytesEncode (v := v) supplyCallbackSelectorWord
    (by change R.length + 10 + 11 ≤ 1024; omega) (by have hs := hm.space; omega) hlen
    (by rw [morphoPatchedValidJumps v]; jump_dest) rd2
  obtain ⟨a4, k4, C4, rd4⟩ := morphoBlocks.morpho_block_4284_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 7 + 7 ≤ 1024; omega) rd3
  dsimp only [morphoBlocks.morpho_block_4284_stack] at rd4
  rw [word_add_sub_left] at rd4
  exact ⟨_, a4, k4, C4, rd4⟩

theorem morphoSupplyCallbackFailure {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr assets shares : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 24 ≤ 1024)
    (hout : out.size < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 4291)
      ([UInt256.ofNat 0, ptr, UInt256.ofNat 0, UInt256.ofNat 128, UInt256.ofNat 32, shares, assets, solcAddrMask] ++ R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_4291_taken_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 7 + 3 ≤ 1024; omega)
    (by decide) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoBlocks.morpho_block_1238 (immWords := wordsOf (immStore v))
    (by change R.length + 5 + 7 ≤ 1024; omega)
    (by rw [UInt256.toNat_ofNat_of_lt hout]; change 0 + out.size ≤ out.size; omega) rd1

theorem morphoSupplyCallbackSuccess {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr assets shares : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 24 ≤ 1024)
    (hptr : ptr.toNat < 2 ^ 64)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 4291)
      ([UInt256.ofNat 1, ptr, UInt256.ofNat 0, UInt256.ofNat 128, UInt256.ofNat 32, shares, assets, solcAddrMask] ++ R)
      mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 4186)
      (supplyCallbackTail assets shares (UInt256.ofNat 0) (UInt256.ofNat 0) R)
      (writeWord mem 64 ptr) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_4291_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 7 + 3 ≤ 1024; omega) (by rfl) h
  obtain ⟨a2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_4297_taken_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 7 + 2 ≤ 1024; omega)
    (by decide) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  obtain ⟨a3, k3, C3, rd3⟩ := morphoBlocks.morpho_block_4307_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 5 + 5 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  obtain ⟨a4, k4, C4, rd4⟩ := morphoFinalizeVoid (v := v)
    (by change R.length + 7 + 4 ≤ 1024; omega) hptr
    (by rw [morphoPatchedValidJumps v]; jump_dest) rd3
  obtain ⟨a5, k5, C5, rd5⟩ := morphoBlocks.morpho_block_4317_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 6 + 2 ≤ 1024; omega) rfl rd4
  obtain ⟨a6, k6, C6, rd6⟩ := morphoBlocks.morpho_block_4322_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 5 + 3 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd5
  exact morphoBlocks.morpho_block_4301_packed (immWords := wordsOf (immStore v))
    (by change R.length + 6 + 3 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd6

end Benchmarks.Morpho.MorphoBlue
