import Benchmarks.UniswapV3.Pool.SwapIterationBitmapSource
import Benchmarks.UniswapV3.Pool.SwapIterationStartTrace
import Benchmarks.UniswapV3.Pool.HashMemoryPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapIterationPrefixX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (s : SwapStateData) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3035⟩
      (swapLoopWords a p exactWord cache snap dataStart dataLength ret R) mem aw rdata σ k C)
    (hst : SourceState s0 ee σ evm) (hf : frame.contract = contract)
    (hi : frame.immutables = immStore v)
    (hstate : frame.locals.get? "state" = some s.value)
    (hzero : frame.locals.get? "zeroForOne" = some (.bool a.zeroForOne))
    (hm : HeapMemory mem aw q) (hs : SwapStateMemory mem p s) (hfit : s.Fits)
    (hpl : 96 ≤ p.toNat) (hdisj : p.toNat + 224 ≤ q.toNat)
    (hb : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 34 ≤ 1024) :
    (ExecBlock config frame evm (swapLoopBody.take 3) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecBlock config frame evm (swapLoopBody.take 3)
        (.ok (swapIterationBitmapFrame frame v a s evm) evm) ∧
      UInt256.signextend (UInt256.ofNat 2) (swapIterationRawNext v a s evm) =
        EVM.wordOfInt (swapIterationNextTick v a s evm) ∧
      ∃ mem' aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
        RD (deployedRuntime v) ee g s0 ⟨3109⟩
          ([bitmapNextFlag (swapIterationMask v a s evm), swapIterationRawNext v a s evm, q] ++
            swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
          mem' aw' rdata σ k' C' ∧
        HeapMemory mem' aw' (q + ⟨224⟩) ∧ SwapStateMemory mem' p s ∧
        SwapIterationMemory mem' q (swapIterationInitial s.price) ∧
        MemoryPrefix mem mem' q.toNat ∧
        (q + UInt256.ofNat 224).toNat ≤ aw'.toNat * 32 + 32) := by
  have ralloc := uniswapV3Pool_block_3035 (immWords := wordsOf (immStore v))
    (by change R.length + 13 + 2 ≤ 1024; omega)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨ka, Ca, hCa, ra, hma, hqa, hprea, hcovera⟩ := swapIterationAllocateX (v := v)
    ralloc hm hb (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
    (by change R.length + 13 + 6 ≤ 1024; omega)
  have hsa : SwapStateMemory (wordArrayAllocMem mem q swapIterationZeroWords) p s :=
    MemoryPrefix.wordArray hprea hs hpl hdisj
  obtain ⟨ab, kb, Cb, hCb, rb, hmb, hsb, hqb, hpreb, hmono⟩ :=
    swapIterationStartBoundX a s ra hma hsa hqa hfit (by have hl := hm.lower; omega)
      hdisj hb (by omega)
  have hpre := hprea.trans hpreb
  have hargs := evalSwapIterationBitmapArgs (frame := swapIterationInputFrame frame s)
    (evm := evm) v a s
    (by simpa only [swapIterationInputFrame, swapIterationFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hstate)
    (by simpa only [swapIterationInputFrame, swapIterationFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hzero) hi
  have ht : UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt s.tick) =
      EVM.wordOfInt s.tick := by
    rw [signextend_wordOfInt ⟨24, by decide⟩ _ s.tick (by decide) (by decide),
      normalizeSint_eq_self ⟨24, by decide⟩ _ hfit.2.2.2.1.1 hfit.2.2.2.1.2]
  have hspacing : normalizeInt (.sint ⟨24, by decide⟩)
      (Int.ofNat (wordsOf (immStore v) "tickSpacing").toNat) = positionTick v.tickSpacing := by
    rw [wordsOf_immStore_tickSpacing, wordOfInt_ofNat_toNat]
    rfl
  have rb' : RD (deployedRuntime v) ee g s0 ⟨11307⟩
      ((if a.zeroForOne then ⟨1⟩ else ⟨0⟩) :: wordsOf (immStore v) "tickSpacing" ::
        EVM.wordOfInt s.tick :: ⟨6⟩ :: ⟨3109⟩ :: q ::
        swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      (writeWord (wordArrayAllocMem mem q swapIterationZeroWords) q.toNat s.price)
      ab rdata σ kb Cb := by
    simpa only [Bool.toUInt256] using rb
  have hinit := swapIterationInitSource (evm := evm) s hstate
  have hbody : swapLoopBody.take 3 = swapLoopBody.take 2 ++
      [.internalCall "TickBitmap_nextInitializedTickWithinOneWord"
        swapIterationBitmapArgs "__c2"] := rfl
  rcases bitmapNextInternalMonoX (v := v) s.tick (positionTick v.tickSpacing) a.zeroForOne
      (swapIterationInputFrame frame s) evm swapIterationBitmapArgs "__c2" hf hargs hst rb'
      hfit.2.2.2.1 (normalizeSint_bounds ⟨24, by decide⟩ _) ht hspacing hmb
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
      (by change R.length + 14 + 20 ≤ 1024; omega) with
    ⟨hex, hr⟩ | ⟨hex, hword, kr, Cr, hCr, rr, hmr⟩
  · refine Or.inl ⟨?_, hr⟩
    rw [hbody]
    exact execBlock_append_ok hinit (ExecBlock.consRevert hex)
  · refine Or.inr ⟨?_, hword, _, ab, kr, Cr, ?_, rr, hmr, ?_, ?_, ?_, ?_⟩
    · rw [hbody]
      exact execBlock_append_ok hinit (ExecBlock.consNormal hex ExecBlock.nil)
    · omega
    · exact MemoryPrefix.wordArray
        (twoWordHashMem_prefix _ _ _ q.toNat) hsb hpl hdisj
    · exact MemoryPrefix.wordArray
        (twoWordHashMem_prefix _ _ _ (q.toNat + 224)) hqb
        (by have hl := hm.lower; omega) (le_refl _)
    · exact hpre.trans (twoWordHashMem_prefix _ _ _ q.toNat)
    · omega

end Benchmarks.UniswapV3.Pool
