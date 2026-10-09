import Benchmarks.Morpho.MorphoBlue.LiquidateOracleRefine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: an error string consumes 64 bytes of a reserved heap.
theorem MorphoHeap.messageReserve {mem : ByteArray} {fp : UInt256} {spare : Nat}
    (hm : MorphoHeap mem fp spare) (hs : 64 ≤ spare) (length payload : UInt256) :
    MorphoHeap (morphoErrorMem length payload mem) (fp + UInt256.ofNat 64) (spare - 64) ∧
    HeapAdvance mem fp (morphoErrorMem length payload mem) (fp + UInt256.ofNat 64) 64 := by
  have hfit : fp.toNat + 64 < UInt256.size := by have hb := hm.space; change _ < 2 ^ 256; omega
  have hadd := uadd_word_ofNat_toNat fp 64 hfit
  have hg : fp.toNat - mem.size < USize.size := by have hb := hm.gap; omega
  have hh := morphoErrorMem_properties_general length payload fp mem hm.lower hm.free hm.size hg (by have hb := hm.space; change _ < 2 ^ 256; omega)
  refine ⟨⟨?_, hh.2.1, ?_, ?_, ?_⟩, morphoErrorMem_prefix length payload hm.size hm.free hg (by omega), hadd⟩
  · rw [hh.1]; have hb := hm.size; omega
  · rw [hadd]; have hb := hm.lower; omega
  · rw [hadd, hh.1]; have hb := hm.gap; omega
  · rw [hadd]; have hb := hm.space; omega

def liquidateHealthyMem (mem : ByteArray) : ByteArray :=
  morphoErrorMem (UInt256.ofNat 19)
    (UInt256.ofNat 50855955609400116513629942149747216777838659076327460824461147259397702942720) mem

theorem morphoLiquidateHealthGuard {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw fp : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (z : Bool) (hstack : R.length + 20 ≤ 1024)
    (hm : MorphoHeap mem fp 896)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1577)
      ((if z then UInt256.ofNat 1 else UInt256.ofNat 0) :: UInt256.ofNat 1638 :: R) mem aw out σ k C) :
    if z then RDrev (deployedRuntime v) g s0
    else ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1638) R
      (liquidateHealthyMem mem) aw' out σ k' C' ∧
      MorphoHeap (liquidateHealthyMem mem) (fp + UInt256.ofNat 64) 832 ∧
      HeapAdvance mem fp (liquidateHealthyMem mem) (fp + UInt256.ofNat 64) 64 := by
  obtain ⟨a0, k0, C0, rd0⟩ := morphoBlocks.morpho_block_1577_packed (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 5 ≤ 1024; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [morphoBlocks.morpho_block_1577_stack] at rd0
  rw [hm.free] at rd0
  obtain ⟨a1, k1, C1, rd1⟩ := morphoAlloc64 (v := v)
    (by change R.length + 3 + 5 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by simpa only [hm.free] using hm.alloc64Guard (by decide)) rd0
  obtain ⟨a2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_1591_packed (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 5 ≤ 1024; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  have rd2' : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      (UInt256.isZero (if z then UInt256.ofNat 1 else UInt256.ofNat 0) :: fp :: UInt256.ofNat 1638 :: R)
      (liquidateHealthyMem mem) a2 out σ k2 C2 := by
    dsimp only [liquidateHealthyMem, morphoErrorMem]
    rw [hm.free]
    exact rd2
  have hh := morphoErrorMem_properties_general (UInt256.ofNat 19)
    (UInt256.ofNat 50855955609400116513629942149747216777838659076327460824461147259397702942720)
    fp mem hm.lower hm.free hm.size (by have hb := hm.gap; omega) (by have hb := hm.space; change _ < 2 ^ 256; omega)
  cases z
  · obtain ⟨k3, C3, rd3⟩ := morphoRequireTrue (v := v) (by omega)
      (by rw [morphoPatchedValidJumps v]; jump_dest) (by decide) rd2'
    exact ⟨a2, k3, C3, rd3, hm.messageReserve (by decide) _ _⟩
  · exact morphoRequireFalseShort (v := v) (by omega) rfl
      (by rw [liquidateHealthyMem, hh.2.2]; decide) (by rw [liquidateHealthyMem, hh.2.2]; decide) rd2'

end Benchmarks.Morpho.MorphoBlue
