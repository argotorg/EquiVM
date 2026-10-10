import Benchmarks.UniswapV3.Pool.SwapSlotMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapSlotReadBoundedX {limit : Nat} {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨2358⟩ R mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (ha0 : BoundedActiveWords aw limit)
    (hb : p.toNat + 224 ≤ limit) (hov : R.length + 6 ≤ 1024) :
    (slot0FieldWord 30 1 σ ee = ⟨0⟩ ∧ RDrev (deployedRuntime v) g s0) ∨
    (slot0FieldWord 30 1 σ ee ≠ ⟨0⟩ ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 ⟨2543⟩ (p :: R)
        (wordArrayAllocMem mem p (slot0StructWords σ ee)) aw' rdata σ k' C' ∧
      HeapMemory (wordArrayAllocMem mem p (slot0StructWords σ ee)) aw' (p + ⟨224⟩) ∧
      Slot0Memory (wordArrayAllocMem mem p (slot0StructWords σ ee)) p σ ee ∧
      BoundedActiveWords aw' limit) := by
  have hsmall := ha0.small
  have hb200 : p.toNat + 224 ≤ 2 ^ 200 := hb.trans hsmall
  obtain ⟨ar, kr, Cr, rr, ha⟩ := swapSlotReadHeadBoundedX (v := v) rd hm ha0 hb hov
  have hu := slot0FieldShift 30 1
    (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240)) (UInt256.ofNat 255)
    σ ee (by native_decide) (by native_decide)
  by_cases hz : slot0FieldWord 30 1 σ ee = ⟨0⟩
  · have r1 := uniswapV3Pool_block_2440_fallthrough (immWords := wordsOf (immStore v))
      hov (by rw [← hu, hz]; rfl) rr
    have r2 := uniswapV3Pool_block_2493 (immWords := wordsOf (immStore v))
      (by change R.length + 1 + 5 ≤ 1024; omega) r1
    exact Or.inl ⟨hz, r2⟩
  · have r1 := uniswapV3Pool_block_2440_taken (immWords := wordsOf (immStore v))
      hov (by rw [← hu, isZero_eq_zero_of_ne hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rr
    have h128 := uadd_word_ofNat_toNat p 128
      (show p.toNat + 128 < UInt256.size by change _ < 2 ^ 256; omega)
    have h160 := uadd_word_ofNat_toNat p 160
      (show p.toNat + 160 < UInt256.size by change _ < 2 ^ 256; omega)
    have h192 := uadd_word_ofNat_toNat p 192
      (show p.toNat + 192 < UInt256.size by change _ < 2 ^ 256; omega)
    have ha' := BoundedActiveWords.expand32
      (BoundedActiveWords.expand32
        (BoundedActiveWords.expand32 ha
          (show (p + UInt256.ofNat 128).toNat + 32 ≤ limit by rw [h128]; omega))
        (show (p + UInt256.ofNat 160).toNat + 32 ≤ limit by rw [h160]; omega))
      (show (p + UInt256.ofNat 192).toNat + 32 ≤ limit by rw [h192]; omega)
    have hheap := wordArrayAllocMem_heap mem p _ (slot0StructWords σ ee) hm.lower
      (by simp [slot0StructWords]) hb200 ha'.active
    have hregion := wordArrayAllocMem_region mem p (slot0StructWords σ ee) hm.lower
      (by simp [slot0StructWords])
    simp only [uniswapV3Pool_block_2440_taken_stack, swapSlotTailMem_eq mem p σ ee hb200] at r1
    exact Or.inr ⟨hz, _, _, _, r1, hheap, hregion, ha'⟩

theorem swapSlotReadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨2358⟩ R mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 6 ≤ 1024) :
    (slot0FieldWord 30 1 σ ee = ⟨0⟩ ∧ RDrev (deployedRuntime v) g s0) ∨
    (slot0FieldWord 30 1 σ ee ≠ ⟨0⟩ ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 ⟨2543⟩ (p :: R)
        (wordArrayAllocMem mem p (slot0StructWords σ ee)) aw' rdata σ k' C' ∧
      HeapMemory (wordArrayAllocMem mem p (slot0StructWords σ ee)) aw' (p + ⟨224⟩) ∧
      Slot0Memory (wordArrayAllocMem mem p (slot0StructWords σ ee)) p σ ee) := by
  rcases swapSlotReadBoundedX (v := v) rd hm (BoundedActiveWords.of_active hm.active) hb hov
    with h | ⟨hz, aw', k', C', rd', hm', hs', _⟩
  · exact Or.inl h
  · exact Or.inr ⟨hz, aw', k', C', rd', hm', hs'⟩

end Benchmarks.UniswapV3.Pool
