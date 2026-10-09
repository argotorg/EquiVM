import Benchmarks.Morpho.MorphoBlue.WithdrawCollateralHealthRefine
import Benchmarks.Morpho.MorphoBlue.HealthMessage
import Benchmarks.Morpho.MorphoBlue.HeapWordWrites

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoWithdrawCollateralHealthCheck {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (z : Bool) (hstack : R.length + 24 ≤ 1024) (hm : MorphoHeap mem ptr 320) (hfit : ptr.toNat + 64 < 2 ^ 64)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5693)
      ((if z then UInt256.ofNat 1 else UInt256.ofNat 0) :: UInt256.ofNat 5701 :: R) mem aw out σ k C) :
    if z then
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5701) R
        (morphoHealthMem mem) aw' out σ k' C' ∧ MorphoHeap (morphoHealthMem mem) (ptr + UInt256.ofNat 64) 32 ∧
        HeapAdvance mem ptr (morphoHealthMem mem) (ptr + UInt256.ofNat 64) 64
    else RDrev (deployedRuntime v) g s0 := by
  have rd0 := morphoBlocks.morpho_block_5693 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨a1, k1, C1, rd1⟩ := morphoHealthMessage (v := v)
    (by change R.length + 2 + 8 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hm.free hfit rd0
  have rd2 := morphoBlocks.morpho_block_585 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 3 ≤ 1024; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  have hh := morphoErrorMem_properties_general (UInt256.ofNat 23)
    (UInt256.ofNat 47687999144296217495830161024900827403930695608853198639623507940336098869248)
    ptr mem hm.lower hm.free hm.size (by have hg := hm.gap; omega) (by change _ < 2 ^ 256; omega)
  cases z
  · exact morphoRequireFalseShort (v := v) (by omega) rfl
      (by rw [morphoHealthMem, hh.2.2]; decide) (by rw [morphoHealthMem, hh.2.2]; decide) rd2
  · obtain ⟨k3, C3, rd3⟩ := morphoRequireTrue (v := v) (by omega)
      (by rw [morphoPatchedValidJumps v]; jump_dest) (by decide) rd2
    refine ⟨a1, k3, C3, rd3, ?_, ?_⟩
    · have hadd := uadd_word_ofNat_toNat ptr 64 (by change _ < 2 ^ 256; omega)
      refine ⟨?_, hh.2.1, ?_, ?_, ?_⟩
      · rw [morphoHealthMem, hh.1]; have hb := hm.size; omega
      · rw [hadd]; have hb := hm.lower; omega
      · rw [hadd, morphoHealthMem, hh.1]; have hb := hm.gap; omega
      · rw [hadd]; have hb := hm.space; omega
    · exact ⟨morphoErrorMem_prefix _ _ hm.size hm.free (by have hg := hm.gap; omega)
      (by change _ < 2 ^ 256; omega), uadd_word_ofNat_toNat ptr 64 (by change _ < 2 ^ 256; omega)⟩


end Benchmarks.Morpho.MorphoBlue
