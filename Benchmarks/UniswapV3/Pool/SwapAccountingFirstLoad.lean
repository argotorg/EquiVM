import Benchmarks.UniswapV3.Pool.SwapAccountingModel
import Benchmarks.UniswapV3.Pool.SwapIterationMemory
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_014

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem SwapIterationMemory.load_amountIn {mem : ByteArray} {p : UInt256}
    {d : SwapIterationData} (hm : SwapIterationMemory mem p d)
    (hb : p.toNat + 224 < UInt256.size) :
    memLoad (p + UInt256.ofNat 128) mem = d.amountIn :=
  WordArrayMemory.load hm 4 (by change 4 < 7; decide) hb

theorem SwapIterationMemory.load_amountOut {mem : ByteArray} {p : UInt256}
    {d : SwapIterationData} (hm : SwapIterationMemory mem p d)
    (hb : p.toNat + 224 < UInt256.size) :
    memLoad (p + UInt256.ofNat 160) mem = d.amountOut :=
  WordArrayMemory.load hm 5 (by change 5 < 7; decide) hb

theorem SwapIterationMemory.load_fee {mem : ByteArray} {p : UInt256}
    {d : SwapIterationData} (hm : SwapIterationMemory mem p d)
    (hb : p.toNat + 224 < UInt256.size) :
    memLoad (p + UInt256.ofNat 192) mem = d.feeAmount :=
  WordArrayMemory.load hm 6 (by change 6 < 7; decide) hb

theorem swapAccountingFirstLoadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw q free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (exactInput : Bool) (d : SwapIterationData)
    (rd : RD (deployedRuntime v) ee g s0 (if exactInput then ⟨3383⟩ else ⟨3445⟩)
      (q :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hd : SwapIterationMemory mem q d)
    (hb : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 5 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨12945⟩
        (swapAccountingFirst exactInput d :: (if exactInput then ⟨3401⟩ else ⟨3458⟩) :: q :: R)
        mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free ∧ aw.toNat ≤ aw'.toNat := by
  have hword : q.toNat + 224 < UInt256.size := by change _ < 2 ^ 256; omega
  have hbnd (n : Nat) (hn : n + 32 ≤ 224) :
      (UInt256.ofNat n + q).toNat + 32 ≤ 2 ^ 200 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat q n (by omega)]
    omega
  cases exactInput
  · have hl : memLoad (UInt256.ofNat 160 + q) mem = d.amountOut := by
      rw [u256_add_comm]
      exact SwapIterationMemory.load_amountOut hd hword
    have rr := uniswapV3Pool_block_3445 (immWords := wordsOf (immStore v)) (by omega)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    refine ⟨_, k + 8, C + (27 + memExpansionCost aw (UInt256.ofNat 160 + q) ⟨32⟩), ?_, ?_,
      hm.expand32 (UInt256.ofNat 160 + q) (hbnd 160 (by decide)),
      expandedWords_mono hm.active (hbnd 160 (by decide))⟩
    · dsimp only [memExpansionCost, M, expandedWords]; omega
    · simpa only [uniswapV3Pool_block_3445_stack, swapAccountingFirst, hl,
        Bool.false_eq_true, if_false] using rr
  · have hin : memLoad (UInt256.ofNat 128 + q) mem = d.amountIn := by
      rw [u256_add_comm]
      exact SwapIterationMemory.load_amountIn hd hword
    have hfee : memLoad (UInt256.ofNat 192 + q) mem = d.feeAmount := by
      rw [u256_add_comm]
      exact SwapIterationMemory.load_fee hd hword
    have rr := uniswapV3Pool_block_3383 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    have hm1 := hm.expand32 (UInt256.ofNat 192 + q) (hbnd 192 (by decide))
    have hm2 := hm1.expand32 (UInt256.ofNat 128 + q) (hbnd 128 (by decide))
    refine ⟨_, k + 12, C + (41 + memExpansionCost aw (UInt256.ofNat 192 + q) ⟨32⟩ +
      memExpansionCost (M aw (UInt256.ofNat 192 + q) ⟨32⟩) (UInt256.ofNat 128 + q) ⟨32⟩),
      ?_, ?_, hm2, ?_⟩
    · dsimp only [memExpansionCost, M, expandedWords]; omega
    · simpa only [uniswapV3Pool_block_3383_stack, swapAccountingFirst, hin, hfee, if_true] using rr
    · exact (expandedWords_mono (off := UInt256.ofNat 192 + q) (size := ⟨32⟩)
        hm.active (hbnd 192 (by decide))).trans
        (expandedWords_mono hm1.active (hbnd 128 (by decide)))

end Benchmarks.UniswapV3.Pool
