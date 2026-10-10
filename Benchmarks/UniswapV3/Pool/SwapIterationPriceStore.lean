import Benchmarks.UniswapV3.Pool.SwapIterationStartTrace
import Benchmarks.UniswapV3.Pool.SwapIterationMemory
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_014

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapIterationPriceStoreSource {frame : Frame} {evm : EVM.State}
    (d : SwapIterationData) (price : UInt256)
    (hd : frame.locals.get? "step" = some d.value)
    (hr : frame.locals.get? "__c3" = some (.int (Int.ofNat price.toNat))) :
    ExecStmt config frame evm swapLoopBody[7]!
      (.ok (swapIterationFrame frame {d with priceNext := price}) evm) := by
  exact ExecStmt.assign (evalExpr_var_get hr) (assignLocalField_frame hd rfl rfl)

theorem SwapIterationMemory.load_priceNext {mem : ByteArray} {p : UInt256}
    {d : SwapIterationData} (hm : SwapIterationMemory mem p d)
    (hb : p.toNat + 224 < UInt256.size) :
    memLoad (p + UInt256.ofNat 96) mem = d.priceNext :=
  WordArrayMemory.load hm 3 (by change 3 < 7; decide) hb

theorem swapIterationPriceStoreX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw p q free exactWord cache snap dataStart dataLength ret priceRaw price : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (s : SwapStateData) (d : SwapIterationData)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3202⟩
      (priceRaw :: q :: swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d)
    (hprice : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) priceRaw = price)
    (hq : 96 ≤ q.toNat) (hdisj : p.toNat + 224 ≤ q.toNat)
    (hb : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 18 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 (if a.zeroForOne then ⟨3260⟩ else ⟨3231⟩)
        ([s.price, ⟨3347⟩, q] ++
          swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
        (writeWord mem (q + UInt256.ofNat 96).toNat price) aw' rdata σ k' C' ∧
      HeapMemory (writeWord mem (q + UInt256.ofNat 96).toNat price) aw' free ∧
      SwapStateMemory (writeWord mem (q + UInt256.ofNat 96).toNat price) p s ∧
      SwapIterationMemory (writeWord mem (q + UInt256.ofNat 96).toNat price) q
        {d with priceNext := price} ∧
      MemoryPrefix mem (writeWord mem (q + UInt256.ofNat 96).toNat price) q.toNat ∧
      aw.toNat ≤ aw'.toNat := by
  have hq96 := uadd_word_ofNat_toNat q 96
    (show q.toNat + 96 < UInt256.size by change _ < 2 ^ 256; omega)
  have hp64 := uadd_word_ofNat_toNat p 64
    (show p.toNat + 64 < UInt256.size by change _ < 2 ^ 256; omega)
  have hs' : SwapStateMemory (writeWord mem (q + UInt256.ofNat 96).toNat price) p s :=
    WordArrayMemory.write_disjoint hs _ price (Or.inr (by
      rw [hq96]
      change p.toNat + 224 ≤ q.toNat + 96
      omega))
  have hload := SwapStateMemory.load_price hs' (by change _ < 2 ^ 256; omega)
  dsimp only [Reasoning.Theory.writeWord] at hload
  have rr : RD (deployedRuntime v) ee g s0 (if a.zeroForOne then ⟨3260⟩ else ⟨3231⟩)
      ([s.price, ⟨3347⟩, q] ++
        swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      (writeWord mem (q + UInt256.ofNat 96).toNat price)
      (M (M aw (q + UInt256.ofNat 96) ⟨32⟩) (p + UInt256.ofNat 64) ⟨32⟩) rdata σ
      (k + 20) (C + (65 + memExpansionCost aw (q + UInt256.ofNat 96) ⟨32⟩ +
        memExpansionCost (M aw (q + UInt256.ofNat 96) ⟨32⟩) (p + UInt256.ofNat 64) ⟨32⟩)) := by
    cases hz : a.zeroForOne
    · have r1 := uniswapV3Pool_block_3202_fallthrough (immWords := wordsOf (immStore v))
        (by change R.length + 2 + 16 ≤ 1024; omega) (by rw [hz]; rfl) rd
      simpa only [uniswapV3Pool_block_3202_fallthrough_stack,
        uniswapV3Pool_block_3202_fallthrough_memory, amountDeltaMask160, hprice, hz,
        Bool.false_eq_true, if_false, Reasoning.Theory.writeWord, hload,
        swapLoopWords, swapWords, hz, List.cons_append, List.nil_append] using r1
    · have r1 := uniswapV3Pool_block_3202_taken (immWords := wordsOf (immStore v))
        (by change R.length + 2 + 16 ≤ 1024; omega) (by rw [hz]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simpa only [uniswapV3Pool_block_3202_taken_stack,
        uniswapV3Pool_block_3202_taken_memory, amountDeltaMask160, hprice, hz,
        if_true, Reasoning.Theory.writeWord, hload,
        swapLoopWords, swapWords, hz, List.cons_append, List.nil_append] using r1
  have hm' := HeapMemory.writeWithin hm (q + UInt256.ofNat 96).toNat price
    (by rw [hq96]; omega)
    (by rw [hq96]; have hh : q.toNat + 224 ≤ mem.size := hd.1; omega)
  have h1 : (q + UInt256.ofNat 96).toNat + 32 ≤ 2 ^ 200 := by rw [hq96]; omega
  have h2 : (p + UInt256.ofNat 64).toNat + 32 ≤ 2 ^ 200 := by rw [hp64]; omega
  have hm1 := hm'.expand32 (q + UInt256.ofNat 96) h1
  have hm2 := hm1.expand32 (p + UInt256.ofNat 64) h2
  refine ⟨_, _, _, ?_, rr, hm2, hs', ?_,
    memoryPrefix_sparse_writeWord mem _ q.toNat price (Or.inl (by rw [hq96]; omega)),
    (expandedWords_mono hm.active h1).trans (expandedWords_mono hm1.active h2)⟩
  · dsimp only [memExpansionCost]; omega
  · rw [hq96]
    exact WordArrayMemory.write hd 3 price

end Benchmarks.UniswapV3.Pool
