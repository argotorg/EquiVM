import Benchmarks.Morpho.MorphoBlue.WordBytesEncode
import Benchmarks.Morpho.MorphoBlue.FlashLoanCallbackABI
import Benchmarks.Morpho.MorphoBlue.ZeroValueCallBridge

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: writing a known free pointer preserves the allocated prefix.
theorem MorphoHeap.setFree {mem : ByteArray} {ptr : UInt256} {spare : Nat}
    (hm : MorphoHeap mem ptr spare) :
    MorphoHeap (writeWord mem 64 ptr) ptr spare ∧
      MemoryPrefix mem (writeWord mem 64 ptr) ptr.toNat := by
  have hg : 64 - mem.size < USize.size := by have hs := hm.size; have hu := USize.size_pos; omega
  have hs : (writeWord mem 64 ptr).size = mem.size := by
    rw [writeWord_size _ _ _ hg]; have hh := hm.size; omega
  exact ⟨⟨by rw [hs]; exact hm.size,
    memLoad_writeWord_self_of_offset _ _ _ _ hg rfl, hm.lower,
    by rw [hs]; exact hm.gap, hm.space⟩,
    memoryPrefix_writeWord mem 64 ptr.toNat ptr hg (Or.inr (by decide))⟩

-- The solc void-return finalizer stores the existing cursor after checking its bound.
theorem morphoFinalizeVoid {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 4 ≤ 1024)
    (hptr : ptr.toNat < 2 ^ 64)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11459) (ptr :: ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret R (writeWord mem 64 ptr) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_11459_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 3 ≤ 1024; omega)
    (ugt_zero (by change ptr.toNat ≤ 18446744073709551615; omega)) h
  exact morphoBlocks.morpho_block_11475_packed (immWords := wordsOf (immStore v))
    (by omega) hvalid rd1

end Benchmarks.Morpho.MorphoBlue
